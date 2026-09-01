// Harness test: checks deterministic numerical and timing input generation,
// exponent coverage, double-word validity, Fast2Sum ordering, and stable
// fingerprints. It does not test the arithmetic library operations.

#include "input_generation.hpp"

#include <cfenv>
#include <cmath>
#include <cstdio>
#include <cstdlib>

namespace {

[[noreturn]] void fail(const char *message) {
    std::fprintf(stderr, "input generation test failed: %s\n", message);
    std::exit(EXIT_FAILURE);
}

void check_words(const std::vector<bench_eval::GeneratedDW> &values) {
    for (const bench_eval::GeneratedDW &item : values) {
        if (!std::isfinite(item.value.s) || item.value.s == 0.0
            || !std::isfinite(item.value.t)
            || item.value.s + item.value.t != item.value.s) {
            fail("generated pair is not a finite double word");
        }
        if ((item.value.t == 0.0) != item.ordinary) {
            fail("ordinary flag does not agree with the low word");
        }
        if (bench_eval::bits_of(item.value.s) != item.hi_bits
            || bench_eval::bits_of(item.value.t) != item.lo_bits) {
            fail("stored component bits do not agree with the pair");
        }
    }
}

} // namespace

int main() {
    if (std::fegetround() != FE_TONEAREST)
        fail("round-to-nearest mode is required");

    bench_eval::GeneratedTestInputs numerical =
        bench_eval::make_generated_test_inputs(40);
    if (numerical.fp_first.size() != 83920
        || numerical.fp_second.size() != 83920
        || numerical.mixed_dw.size() != 79680
        || numerical.mixed_fp.size() != 79680
        || numerical.dw_first.size() != 79680
        || numerical.dw_second.size() != 79680) {
        fail("unexpected generated-input size");
    }
    if (numerical.fp_coverage.first_bins != 2098
        || numerical.fp_coverage.second_bins != 2098
        || numerical.mixed_coverage.first_bins != 1992
        || numerical.mixed_coverage.second_bins != 2098
        || numerical.dw_coverage.first_bins != 1992
        || numerical.dw_coverage.second_bins != 1992) {
        fail("coverage changed from the mpfr106-v1 baseline");
    }
    if (numerical.mixed_coverage.first_ordinary != 3984
        || numerical.dw_coverage.first_ordinary != 3984
        || numerical.dw_coverage.second_ordinary != 3984) {
        fail("ordinary-double proportion changed");
    }
    check_words(numerical.mixed_dw);
    check_words(numerical.dw_first);
    check_words(numerical.dw_second);
    if (bench_eval::fingerprint_generated_inputs(numerical)
        != numerical.fingerprint) {
        fail("numerical fingerprint is not reproducible");
    }
    if (numerical.fingerprint != UINT64_C(0x593695fe7857beb7))
        fail("mpfr106-v1 numerical bit stream changed");

    bench_eval::TimingInputs timing = bench_eval::make_timing_inputs(65536);
    if (bench_eval::fingerprint_timing_inputs(timing)
        != timing.fingerprint) {
        fail("timing fingerprint is not reproducible");
    }
    if (timing.fingerprint != UINT64_C(0x9730f9b2cfdf95cb))
        fail("timing bit stream changed");
    for (std::size_t i = 0; i < timing.fast_first.size(); ++i) {
        if (std::fabs(timing.fast_second[i])
            > std::fabs(timing.fast_first[i])) {
            fail("timing Fast2Sum operands are not magnitude ordered");
        }
    }

    std::printf("numerical fingerprint 0x%016llx\n",
        static_cast<unsigned long long>(numerical.fingerprint));
    std::printf("timing fingerprint    0x%016llx\n",
        static_cast<unsigned long long>(timing.fingerprint));
    return EXIT_SUCCESS;
}
