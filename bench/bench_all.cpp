// Compare the nine dd_lib arithmetic operations against QD.
//
// The program first compares both implementations on the same inputs. It then
// reports the median time per call over the requested number of trials.
//
// Use an FMA-enabled QD build because dd_lib uses fma in its multiplication
// kernels:
//   make QD_PREFIX=$HOME/.local/qd-fma bench_all
//   ./bench_all [input_count] [trial_count]
//
// Defaults: input_count = 2^22 and trial_count = 11.
//
// QD routine used for each comparison:
//   two_sum       -> qd::two_sum            fast_2sum -> qd::quick_two_sum (|a|>=|b|)
//   fast_2mult    -> qd::two_prod           dw_plus_fp  -> dd_real + double
//   dw_plus_dw    -> dd_real::ieee_add      dw_times_fp -> dd_real * double
//   dw_times_dw   -> dd_real * dd_real       dw_div_fp  -> dd_real / double
//   dw_div_dw     -> dd_real::accurate_div
//
// Addition and division call QD's accurate variants explicitly. QD is a reference
// implementation for this comparison, not an exact arithmetic oracle. The proved
// error bounds for dd_lib come from the Coq development.

#include <qd/dd_real.h>
#include <mpfr.h>

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <random>
#include <vector>

extern "C" {
#include "dw_arith.h"  // declarations for the compiled C library
}

// USE_KERNEL selects the unchecked arithmetic kernels. The normal build uses
// the public checked functions.
#ifdef USE_KERNEL
#define OP_two_sum      two_sum
#define OP_fast_2sum    fast_2sum
#define OP_fast_2mult   fast_2mult
#define OP_dw_plus_fp   dw_plus_fp_kernel
#define OP_dw_times_fp   dw_times_fp_kernel
#define OP_dw_plus_dw   dw_plus_dw_kernel
#define OP_dw_times_dw   dw_times_dw_kernel
#define OP_dw_div_fp    dw_div_fp_kernel
#define OP_dw_div_dw    dw_div_dw_kernel
#else
#define OP_two_sum      two_sum_guarded
#define OP_fast_2sum    fast_2sum_guarded
#define OP_fast_2mult   fast_2mult_guarded
#define OP_dw_plus_fp   dw_plus_fp
#define OP_dw_times_fp  dw_times_fp
#define OP_dw_plus_dw   dw_plus_dw
#define OP_dw_times_dw  dw_times_dw
#define OP_dw_div_fp    dw_div_fp
#define OP_dw_div_dw    dw_div_dw
#endif

static inline double now_sec() {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}
// Keep the result live without adding a memory access to the timed loop.
static inline void sink(double x) { asm volatile("" : : "X"(x) : "memory"); }
static inline void sink_dd(const dd_real &r) { sink(r.x[0]); sink(r.x[1]); }

// Use the binary64 encoding so that +0 and -0 count as different components.
static inline uint64_t bits(double d) { uint64_t u; __builtin_memcpy(&u, &d, 8); return u; }

static size_t N;
static int trials;

// Return the median nanoseconds per call. Each implementation gets one untimed
// warm-up pass before its measurements.
template <class Body>
static double median_ns(Body body) {
    body();
    std::vector<double> t(trials);
    for (int i = 0; i < trials; ++i) {
        double t0 = now_sec();
        body();
        t[i] = now_sec() - t0;
    }
    std::sort(t.begin(), t.end());
    return t[trials / 2] * 1e9 / (double)N;
}

template <class BOurs, class BQd>
static void row(const char *name, BOurs ours, BQd qd) {
    double o = median_ns(ours), q = median_ns(qd);
    printf("  %-26s %8.3f  %8.3f   %6.2fx\n", name, o, q, o / q);
}

// A double-double result represents hi + lo.
struct pr { double hi, lo; };

static double draw_nonzero_double(
        std::mt19937_64 &rng,
        std::uniform_real_distribution<double> &dist) {
    double value;
    do {
        value = dist(rng);
    } while (value == 0.0);
    return value;
}

// Construct a valid double word directly, without using either implementation
// under test. The high word is always nonzero. A requested nonzero low word is
// smaller than one-quarter ulp of the high word, so the pair represents a value
// that is not a binary64 number.
static void make_input_dw(std::mt19937_64 &rng,
                          std::uniform_real_distribution<double> &dist,
                          bool nonzero_low,
                          dword &w, dd_real &d) {
    double hi;
    do {
        hi = dist(rng);
    } while (hi == 0.0);

    uint64_t tag = rng();
    double lo = 0.0;
    if (nonzero_low) {
        int hi_exp = std::ilogb(std::abs(hi));
        double fraction = 0.5 + static_cast<double>(tag >> 12) * 0x1p-53;
        lo = std::ldexp(fraction, hi_exp - 54);
        if (tag & 1) lo = -lo;
    }

    bool valid = std::isfinite(hi) && hi != 0.0 && std::isfinite(lo)
                 && hi + lo == hi;
    bool requested_kind = hi != 0.0 && nonzero_low == (lo != 0.0);
    if (!valid || !requested_kind) {
        std::fprintf(stderr, "failed to construct a valid benchmark input\n");
        std::abort();
    }

    w.s = hi;
    w.t = lo;
    d = dd_real(hi, lo);
}

// Compare dd_lib and QD for one operation. The component counts compare the
// binary64 encodings. The value count compares the exact sums hi + lo, so two
// different component pairs may still represent the same value.
//
// The reported relative gap is
// |(ours_hi + ours_lo) - (qd_hi + qd_lo)| / |qd_hi + qd_lo|.
//
// For finite binary64 components, 2112 bits are enough to compute both sums and
// their difference exactly. Only the division used for the relative gap rounds.
template <class O, class Q>
static void diff_row(const char *name, O ours, Q qd) {
    constexpr mpfr_prec_t compare_prec = 2112;
    size_t mh = 0, ml = 0, mv = 0;
    mpfr_t ahi, alo, bhi, blo, av, bv, gap, mag, rel, max_rel;
    mpfr_inits2(compare_prec, ahi, alo, bhi, blo, av, bv, gap, mag,
                rel, max_rel, (mpfr_ptr)0);
    mpfr_set_zero(max_rel, 0);

    for (size_t i = 0; i < N; ++i) {
        pr a = ours(i), b = qd(i);
        bool hi_diff = bits(a.hi) != bits(b.hi);
        bool lo_diff = bits(a.lo) != bits(b.lo);
        if (hi_diff) ++mh;
        if (lo_diff) ++ml;
        // Equal components imply equal represented values.
        if (!hi_diff && !lo_diff) continue;

        mpfr_set_d(ahi, a.hi, MPFR_RNDN);
        mpfr_set_d(alo, a.lo, MPFR_RNDN);
        mpfr_set_d(bhi, b.hi, MPFR_RNDN);
        mpfr_set_d(blo, b.lo, MPFR_RNDN);
        mpfr_add(av, ahi, alo, MPFR_RNDN);
        mpfr_add(bv, bhi, blo, MPFR_RNDN);
        mpfr_sub(gap, av, bv, MPFR_RNDN);
        mpfr_abs(gap, gap, MPFR_RNDN);
        if (mpfr_zero_p(gap)) continue;

        ++mv;
        mpfr_abs(mag, bv, MPFR_RNDN);
        if (mpfr_zero_p(mag)) {
            // Relative difference from a zero reference value is unbounded.
            mpfr_set_inf(rel, 1);
        } else {
            // Round upward so the printed maximum does not understate the gap.
            mpfr_div(rel, gap, mag, MPFR_RNDU);
        }
        if (mpfr_greater_p(rel, max_rel)) mpfr_set(max_rel, rel, MPFR_RNDN);
    }

    char max_rel_text[32];
    mpfr_snprintf(max_rel_text, sizeof(max_rel_text), "%.3Re", max_rel);
    printf("  %-30s %9zu %9zu %9zu   %12s\n",
           name, mh, ml, mv, max_rel_text);
    mpfr_clears(ahi, alo, bhi, blo, av, bv, gap, mag, rel, max_rel,
                (mpfr_ptr)0);
}

int main(int argc, char **argv) {
    N      = (argc > 1) ? strtoull(argv[1], nullptr, 10) : (1ull << 22);
    trials = (argc > 2) ? atoi(argv[2]) : 11;

    std::mt19937_64 rng(0xC0FFEEULL);
    std::uniform_real_distribution<double> dist(-1.0, 1.0);

    // Scalar inputs for the error-free transforms and double-double/scalar operations.
    std::vector<double> fa(N), fb(N), faS(N), fbS(N), sc(N), scd(N);

    // Each dword and dd_real pair is built from the same two binary64 values.
    std::vector<dword> X(N), Y(N), Yden(N);
    std::vector<dd_real> DX(N), DY(N), DYden(N);

    for (size_t i = 0; i < N; ++i) {
        fa[i] = dist(rng); fb[i] = dist(rng);
        faS[i] = fa[i]; fbS[i] = fb[i];
        // Fast2Sum requires the first operand to have at least the magnitude
        // of the second operand.
        if (std::abs(fbS[i]) > std::abs(faS[i])) std::swap(faS[i], fbS[i]);
        sc[i]  = dist(rng);
        scd[i] = draw_nonzero_double(rng, dist);

        // Every high word is nonzero. Each low word is zero in one-fifth of the
        // corpus. The 25-case pattern includes both-zero-low, mixed, and
        // both-nonzero-low pairs.
        bool x_has_low = (i % 5) != 0;
        bool y_has_low = ((i / 5) % 5) != 0;
        make_input_dw(rng, dist, x_has_low, X[i], DX[i]);
        make_input_dw(rng, dist, y_has_low, Y[i], DY[i]);
        make_input_dw(rng, dist, y_has_low, Yden[i], DYden[i]);
    }

    // Compare outputs before timing. The paired error-free transforms use the same
    // formulas; Fast2Mult also requires matching FMA settings. The double-double
    // operations can differ because the libraries use different evaluation
    // sequences, so a mismatch is reported rather than treated as a test failure.
    // These are bounded random inputs. This benchmark does not cover boundary cases.
    printf("differential test: ours vs QD outputs (N = %zu)\n", N);
    printf("  %-30s %9s %9s %9s   %12s\n",
           "op", "hi_mism", "lo_mism", "val_mism", "max_rel");
    printf("  %-30s %9s %9s %9s   %12s\n",
           "--", "-------", "-------", "--------", "-------");
    diff_row("two_sum",
        [&](size_t i){ dword st; OP_two_sum(&st,fa[i],fb[i]); return pr{st.s,st.t}; },
        [&](size_t i){ double e; double s=qd::two_sum(fa[i],fb[i],e); return pr{s,e}; });
    diff_row("fast_2sum",
        [&](size_t i){ dword st; OP_fast_2sum(&st,faS[i],fbS[i]); return pr{st.s,st.t}; },
        [&](size_t i){ double e; double s=qd::quick_two_sum(faS[i],fbS[i],e); return pr{s,e}; });
    diff_row("fast_2mult",
        [&](size_t i){ dword st; OP_fast_2mult(&st,fa[i],fb[i]); return pr{st.s,st.t}; },
        [&](size_t i){ double e; double p=qd::two_prod(fa[i],fb[i],e); return pr{p,e}; });
    diff_row("dw_plus_fp",
        [&](size_t i){ dword st; OP_dw_plus_fp(&st,&X[i],sc[i]); return pr{st.s,st.t}; },
        [&](size_t i){ dd_real r=DX[i]+sc[i]; return pr{r.x[0],r.x[1]}; });
    diff_row("dw_times_fp",
        [&](size_t i){ dword st; OP_dw_times_fp(&st,&X[i],sc[i]); return pr{st.s,st.t}; },
        [&](size_t i){ dd_real r=DX[i]*sc[i]; return pr{r.x[0],r.x[1]}; });
    diff_row("dw_div_fp",
        [&](size_t i){ dword st; OP_dw_div_fp(&st,&X[i],scd[i]); return pr{st.s,st.t}; },
        [&](size_t i){ dd_real r=DX[i]/scd[i]; return pr{r.x[0],r.x[1]}; });
    diff_row("dw_plus_dw (vs ieee_add)",
        [&](size_t i){ dword st; OP_dw_plus_dw(&st,&X[i],&Y[i]); return pr{st.s,st.t}; },
        [&](size_t i){ dd_real r=dd_real::ieee_add(DX[i],DY[i]); return pr{r.x[0],r.x[1]}; });
    diff_row("dw_times_dw",
        [&](size_t i){ dword st; OP_dw_times_dw(&st,&X[i],&Y[i]); return pr{st.s,st.t}; },
        [&](size_t i){ dd_real r=DX[i]*DY[i]; return pr{r.x[0],r.x[1]}; });
    diff_row("dw_div_dw (vs accurate_div)",
        [&](size_t i){ dword st; OP_dw_div_dw(&st,&X[i],&Yden[i]); return pr{st.s,st.t}; },
        [&](size_t i){ dd_real r=dd_real::accurate_div(DX[i],DYden[i]); return pr{r.x[0],r.x[1]}; });
    printf("\n");

    printf("dd_lib vs QD -- all double-word ops\n");
    printf("  N = %zu, trials = %d (median ns/op)\n\n", N, trials);
    printf("  %-26s %8s  %8s   %7s\n", "op", "ours", "qd", "ours/qd");
    printf("  %-26s %8s  %8s   %7s\n", "--", "----", "--", "-------");

    // Floating-point inputs, double-double output.
    row("two_sum",
        [&]{ dword st; for (size_t i=0;i<N;++i){ OP_two_sum(&st,fa[i],fb[i]); sink(st.s); sink(st.t);} },
        [&]{ double e,s; for (size_t i=0;i<N;++i){ s=qd::two_sum(fa[i],fb[i],e); sink(s); sink(e);} });
    row("fast_2sum",
        [&]{ dword st; for (size_t i=0;i<N;++i){ OP_fast_2sum(&st,faS[i],fbS[i]); sink(st.s); sink(st.t);} },
        [&]{ double e,s; for (size_t i=0;i<N;++i){ s=qd::quick_two_sum(faS[i],fbS[i],e); sink(s); sink(e);} });
    row("fast_2mult",
        [&]{ dword st; for (size_t i=0;i<N;++i){ OP_fast_2mult(&st,fa[i],fb[i]); sink(st.s); sink(st.t);} },
        [&]{ double e,p; for (size_t i=0;i<N;++i){ p=qd::two_prod(fa[i],fb[i],e); sink(p); sink(e);} });

    // Double-double and floating-point inputs.
    row("dw_plus_fp",
        [&]{ dword st; for (size_t i=0;i<N;++i){ OP_dw_plus_fp(&st,&X[i],sc[i]); sink(st.s); sink(st.t);} },
        [&]{ for (size_t i=0;i<N;++i){ sink_dd(DX[i] + sc[i]); } });
    row("dw_times_fp",
        [&]{ dword st; for (size_t i=0;i<N;++i){ OP_dw_times_fp(&st,&X[i],sc[i]); sink(st.s); sink(st.t);} },
        [&]{ for (size_t i=0;i<N;++i){ sink_dd(DX[i] * sc[i]); } });
    row("dw_div_fp",
        [&]{ dword st; for (size_t i=0;i<N;++i){ OP_dw_div_fp(&st,&X[i],scd[i]); sink(st.s); sink(st.t);} },
        [&]{ for (size_t i=0;i<N;++i){ sink_dd(DX[i] / scd[i]); } });

    // Two double-double inputs. Call QD's named accurate routines explicitly
    // for addition and division; QD configuration flags can change its default
    // operators.
    row("dw_plus_dw",
        [&]{ dword st; for (size_t i=0;i<N;++i){ OP_dw_plus_dw(&st,&X[i],&Y[i]); sink(st.s); sink(st.t);} },
        [&]{ for (size_t i=0;i<N;++i){ sink_dd(dd_real::ieee_add(DX[i],DY[i])); } });
    row("dw_times_dw",
        [&]{ dword st; for (size_t i=0;i<N;++i){ OP_dw_times_dw(&st,&X[i],&Y[i]); sink(st.s); sink(st.t);} },
        [&]{ for (size_t i=0;i<N;++i){ sink_dd(DX[i] * DY[i]); } });
    row("dw_div_dw",
        [&]{ dword st; for (size_t i=0;i<N;++i){ OP_dw_div_dw(&st,&X[i],&Yden[i]); sink(st.s); sink(st.t);} },
        [&]{ for (size_t i=0;i<N;++i){ sink_dd(dd_real::accurate_div(DX[i],DYden[i])); } });

    return 0;
}
