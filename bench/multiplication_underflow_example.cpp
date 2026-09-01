// A constructed binary64 underflow example for double-word multiplication.
//
// The same operands are used in two settings:
//   1. composite double-word multiplication, whose public dd_lib interface
//      provides a mixed relative/absolute error bound; and
//   2. Fast2Mult, whose guarded interface promises exact reconstruction and
//      therefore rejects these operands.

#include <mpfr.h>

#include <cerrno>
#include <cfenv>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <limits>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

extern "C" {
#include "dw_arith.h"
#include "fp_utils.h"
}

#include "qd_evaluation.hpp"

#define STRINGIFY_INNER(value) #value
#define STRINGIFY(value) STRINGIFY_INNER(value)

namespace {

constexpr mpfr_prec_t oracle_precision = 256;
constexpr uint64_t input_bits = UINT64_C(0x1fc0000000000001);
constexpr uint64_t expected_high_bits = UINT64_C(0x0000100000000000);
constexpr int unexpected_guard_return = 77;

[[noreturn]] void fail(const char *message) {
    std::fprintf(stderr, "example check failed: %s\n", message);
    std::exit(EXIT_FAILURE);
}

void require(bool condition, const char *message) {
    if (!condition) {
        fail(message);
    }
}

uint64_t bits_of(double value) {
    uint64_t bits;
    std::memcpy(&bits, &value, sizeof(bits));
    return bits;
}

double double_from_bits(uint64_t bits) {
    double value;
    std::memcpy(&value, &bits, sizeof(value));
    return value;
}

dword as_dword(const dd_real &value) {
    return dword{value._hi(), value._lo()};
}

// This is the relation checked for double-word inputs by the public library
// predicates. isfinite_dword alone checks only that both components are finite.
bool valid_double_word(const dword &value) {
    return isfinite_dword(&value) && value.s + value.t == value.s;
}

void print_pair(const char *name, const dword &value) {
    std::printf("  %-10s hi=% .17a [0x%016llx]"
                "  lo=% .17a [0x%016llx]\n",
                name, value.s,
                static_cast<unsigned long long>(bits_of(value.s)),
                value.t,
                static_cast<unsigned long long>(bits_of(value.t)));
}

class product_analysis {
public:
    product_analysis(double a, const dword &result) {
        mpfr_inits2(oracle_precision,
                    reference_, represented_, absolute_error_, relative_error_,
                    absolute_reference_, u_, u_squared_, eta_,
                    pure_four_relative_, pure_four_absolute_, mixed_bound_,
                    fast2mult_error_bound_, mixed_utilization_, scratch_,
                    (mpfr_ptr)0);

        // MPFR computes the exact reference a^2.
        // reference = a * a
        mpfr_set_d(scratch_, a, MPFR_RNDN);
        mpfr_mul(reference_, scratch_, scratch_, MPFR_RNDN);

        // Reconstruct the real value represented by the returned pair.
        // represented = result.s + result.t
        mpfr_set_d(represented_, result.s, MPFR_RNDN);
        mpfr_set_d(scratch_, result.t, MPFR_RNDN);
        mpfr_add(represented_, represented_, scratch_, MPFR_RNDN);

        // absolute_error = |represented - reference|
        // relative_error = absolute_error / |reference|
        mpfr_sub(absolute_error_, represented_, reference_, MPFR_RNDN);
        mpfr_abs(absolute_error_, absolute_error_, MPFR_RNDN);
        mpfr_abs(absolute_reference_, reference_, MPFR_RNDN);
        mpfr_div(relative_error_, absolute_error_, absolute_reference_,
                 MPFR_RNDN);

        // Form the pure 4u^2 term and the public 4u^2|a^2| + 2.5 eta bound.
        // pure_relative = 4 * u^2
        // mixed_bound = 4 * u^2 * |reference| + (5/2) * eta
        mpfr_set_ui_2exp(u_, 1, -53, MPFR_RNDN);
        mpfr_mul(u_squared_, u_, u_, MPFR_RNDN);
        mpfr_mul_ui(pure_four_relative_, u_squared_, 4, MPFR_RNDN);
        mpfr_mul(pure_four_absolute_, pure_four_relative_, absolute_reference_,
                 MPFR_RNDN);

        mpfr_set_ui_2exp(eta_, 1, -1074, MPFR_RNDN);
        mpfr_mul(mixed_bound_, pure_four_relative_, absolute_reference_,
                 MPFR_RNDN);
        mpfr_mul_ui(scratch_, eta_, 5, MPFR_RNDN);
        mpfr_div_2ui(scratch_, scratch_, 1, MPFR_RNDN);
        mpfr_add(mixed_bound_, mixed_bound_, scratch_, MPFR_RNDN);

        mpfr_div_2ui(fast2mult_error_bound_, eta_, 1, MPFR_RNDN);
        mpfr_div(mixed_utilization_, absolute_error_, mixed_bound_, MPFR_RNDN);
    }

    ~product_analysis() {
        mpfr_clears(reference_, represented_, absolute_error_, relative_error_,
                    absolute_reference_, u_, u_squared_, eta_,
                    pure_four_relative_, pure_four_absolute_, mixed_bound_,
                    fast2mult_error_bound_, mixed_utilization_, scratch_,
                    (mpfr_ptr)0);
    }

    product_analysis(const product_analysis &) = delete;
    product_analysis &operator=(const product_analysis &) = delete;

    bool reconstructs_exact_product() const {
        return mpfr_zero_p(absolute_error_) != 0;
    }

    bool exceeds_four_u_squared() const {
        return mpfr_cmp(absolute_error_, pure_four_absolute_) > 0;
    }

    bool satisfies_mixed_bound() const {
        return mpfr_cmp(absolute_error_, mixed_bound_) <= 0;
    }

    bool satisfies_fast2mult_error_bound() const {
        return mpfr_cmp(absolute_error_, fast2mult_error_bound_) <= 0;
    }

    mpfr_srcptr reference() const { return reference_; }
    mpfr_srcptr absolute_error() const { return absolute_error_; }
    mpfr_srcptr relative_error() const { return relative_error_; }
    mpfr_srcptr pure_four_relative() const { return pure_four_relative_; }
    mpfr_srcptr mixed_bound() const { return mixed_bound_; }
    mpfr_srcptr fast2mult_error_bound() const {
        return fast2mult_error_bound_;
    }
    mpfr_srcptr mixed_utilization() const { return mixed_utilization_; }

private:
    mpfr_t reference_;
    mpfr_t represented_;
    mpfr_t absolute_error_;
    mpfr_t relative_error_;
    mpfr_t absolute_reference_;
    mpfr_t u_;
    mpfr_t u_squared_;
    mpfr_t eta_;
    mpfr_t pure_four_relative_;
    mpfr_t pure_four_absolute_;
    mpfr_t mixed_bound_;
    mpfr_t fast2mult_error_bound_;
    mpfr_t mixed_utilization_;
    mpfr_t scratch_;
};

void verify_reference_formula(mpfr_srcptr reference) {
    mpfr_t expected;
    mpfr_t term;
    mpfr_inits2(oracle_precision, expected, term, (mpfr_ptr)0);

    mpfr_set_ui_2exp(expected, 1, -1030, MPFR_RNDN);
    mpfr_set_ui_2exp(term, 1, -1081, MPFR_RNDN);
    mpfr_add(expected, expected, term, MPFR_RNDN);
    mpfr_set_ui_2exp(term, 1, -1134, MPFR_RNDN);
    mpfr_add(expected, expected, term, MPFR_RNDN);

    require(mpfr_cmp(reference, expected) == 0,
            "MPFR product does not match the derived exact formula");
    mpfr_clears(expected, term, (mpfr_ptr)0);
}

void print_analysis(const product_analysis &analysis) {
    mpfr_printf("  exact product                 = %.20Re\n",
                analysis.reference());
    mpfr_printf("  absolute error                = %.20Re\n",
                analysis.absolute_error());
    mpfr_printf("  relative error                = %.20Re\n",
                analysis.relative_error());
    mpfr_printf("  current pure target 4u^2      = %.20Re"
                "  (not applicable here)\n",
                analysis.pure_four_relative());
    mpfr_printf("  public mixed bound            = %.20Re\n",
                analysis.mixed_bound());
    mpfr_printf("  fraction of mixed bound used  = %.20Re\n",
                analysis.mixed_utilization());
}

void show_composite_multiplication(double a) {
    std::puts("[1] Composite double-word multiplication");

    // This is the input from the paper example; both calls compute x*x.
    // x = (a, 0), so the exact result is x * x = a^2.
    dword input{a, 0.0};
    require(valid_double_word(input), "input is not a valid double word");
    require(dw_times_dw_weak_precond_check(&input, &input) != 0,
            "default dw_times_dw input check unexpectedly rejects");

    // Call the checked dd_lib interface and QD's double-word operator.
    dword ours;
    dw_times_dw(&ours, &input, &input);

    dd_real qd_input(a, 0.0);
    dword qd_result = as_dword(qd_input * qd_input);

    print_pair("dd_lib", ours);
    print_pair("QD", qd_result);

    require(valid_double_word(ours),
            "dd_lib composite result is not a valid double word");
    require(valid_double_word(qd_result),
            "QD composite result is not a valid double word");
    require(bits_of(ours.s) == expected_high_bits && bits_of(ours.t) == 0,
            "unexpected dd_lib composite result bits");
    require(bits_of(qd_result.s) == expected_high_bits
                && bits_of(qd_result.t) == 0,
            "unexpected QD composite result bits");

    product_analysis ours_analysis(a, ours);
    product_analysis qd_analysis(a, qd_result);
    verify_reference_formula(ours_analysis.reference());

    require(!ours_analysis.reconstructs_exact_product(),
            "constructed composite result unexpectedly reconstructs a^2");
    require(!qd_analysis.reconstructs_exact_product(),
            "QD composite result unexpectedly reconstructs a^2");
    require(ours_analysis.exceeds_four_u_squared(),
            "constructed error does not exceed the 4u^2 comparison");
    require(ours_analysis.satisfies_mixed_bound(),
            "dd_lib composite result exceeds its public mixed bound");
    require(mpfr_cmp(ours_analysis.absolute_error(),
                     qd_analysis.absolute_error()) == 0,
            "dd_lib and QD errors unexpectedly differ");

    std::puts("  dd_lib returned normally      = yes");
    std::puts("  dd_lib result is valid DW     = yes");
    std::puts("  QD result is valid DW         = yes");
    print_analysis(ours_analysis);
    std::puts("");
}

bool guarded_fast2mult_rejects(double a) {
    // The guarded function exits on rejection, so invoke it in a child.
    std::fflush(nullptr);
    pid_t child = fork();
    if (child < 0) {
        fail("fork failed while testing fast_2mult_guarded");
    }
    if (child == 0) {
        dword result;
        fast_2mult_guarded(&result, a, a);
        _Exit(unexpected_guard_return);
    }

    int status = 0;
    pid_t waited;
    do {
        waited = waitpid(child, &status, 0);
    } while (waited < 0 && errno == EINTR);
    require(waited == child, "waitpid failed for fast_2mult_guarded");
    return WIFEXITED(status) && WEXITSTATUS(status) == EXIT_FAILURE;
}

void show_fast2mult_rejection(double a) {
    std::puts("[2] Error-free product interface");

    // QD exposes the underlying product transformation as two_prod.
    // (qd_high, qd_low) = two_prod(a, a)
    double qd_low;
    double qd_high = qd::two_prod(a, a, qd_low);
    dword qd_result{qd_high, qd_low};
    product_analysis analysis(a, qd_result);

    print_pair("QD", qd_result);
    require(valid_double_word(qd_result),
            "QD two_prod result is not a valid double word");
    require(bits_of(qd_result.s) == expected_high_bits
                && bits_of(qd_result.t) == 0,
            "unexpected QD two_prod result bits");
    require(!analysis.reconstructs_exact_product(),
            "QD two_prod unexpectedly reconstructs a^2");
    require(analysis.satisfies_fast2mult_error_bound(),
            "QD two_prod exceeds the unconditional eta/2 error bound");
    // RN(a*a) = 2^-1030 is below the guard threshold 2^-969.
    require(fast2_mult_exact_check(a, a) == 0,
            "fast2_mult_exact_check unexpectedly accepts the input");
    require(guarded_fast2mult_rejects(a),
            "fast_2mult_guarded did not terminate with EXIT_FAILURE");

    std::puts("  fast_2mult_guarded rejected   = yes");
    std::puts("  QD result is valid DW         = yes");
    std::puts("  QD reconstructs exact a^2     = no");
    mpfr_printf("  exact-reconstruction target   = 0\n");
    mpfr_printf("  QD reconstruction error       = %.20Re\n",
                analysis.absolute_error());
    mpfr_printf("  absolute-error bound eta/2    = %.20Re\n",
                analysis.fast2mult_error_bound());
    std::puts("");
}

void check_environment() {
    require(sizeof(double) == sizeof(uint64_t),
            "example requires a 64-bit double encoding");
    require(std::numeric_limits<double>::is_iec559,
            "example requires IEEE-754 binary64 arithmetic");
    require(std::numeric_limits<double>::digits == 53,
            "example requires binary64 precision");
    require(std::fegetround() == FE_TONEAREST,
            "example requires round-to-nearest mode");

    volatile double minimum_normal = std::numeric_limits<double>::min();
    volatile double one_half = 0.5;
    double subnormal = minimum_normal * one_half;
    require(bits_of(subnormal) == UINT64_C(0x0008000000000000),
            "example requires gradual underflow (FTZ must be disabled)");
}

}  // namespace

int main() {
    check_environment();

    // Construct a from its exact binary64 encoding.
    // a = (1 + 2^-52) * 2^-515
    double a = double_from_bits(input_bits);
    require(bits_of(a) == input_bits, "failed to construct the input value");

    std::printf("Constructed multiplication-underflow example\n");
    std::printf("  MPFR version = %s, precision = %ld bits\n",
                mpfr_get_version(), static_cast<long>(oracle_precision));
    std::printf("  QD_FMS       = %s\n", STRINGIFY(QD_FMS(x, y, z)));
    std::printf("  a            = % .17a [0x%016llx]\n\n",
                a, static_cast<unsigned long long>(bits_of(a)));

    show_composite_multiplication(a);
    show_fast2mult_rejection(a);

    std::puts("All checks passed.");
    return EXIT_SUCCESS;
}
