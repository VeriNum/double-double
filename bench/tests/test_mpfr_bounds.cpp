// Harness test: checks that the MPFR oracle encodes the six proved error-bound
// formulas and their zero-reference behavior exactly. It does not execute the
// arithmetic library operations.

#include "mpfr_accuracy.hpp"

#include <cstdio>
#include <cstdlib>

namespace {

[[noreturn]] void fail(const char *message) {
    std::fprintf(stderr, "MPFR bound test failed: %s\n", message);
    std::exit(EXIT_FAILURE);
}

void expect_equal(mpfr_srcptr actual, mpfr_srcptr expected,
                  const char *message) {
    if (!mpfr_equal_p(actual, expected)) fail(message);
}

} // namespace

int main() {
    bench_eval::verify_error_regime_classifier();

    mpfr_t reference;
    mpfr_t relative;
    mpfr_t absolute;
    mpfr_t bound;
    mpfr_t expected;
    mpfr_t u_squared;
    mpfr_t eta;
    mpfr_t temporary;
    mpfr_inits2(256, reference, relative, absolute, bound, expected,
                u_squared, eta, temporary, (mpfr_ptr)0);
    mpfr_set_ui_2exp(u_squared, 1, -106, MPFR_RNDN);
    mpfr_set_ui_2exp(eta, 1, -1074, MPFR_RNDN);
    mpfr_set_ui(reference, 1, MPFR_RNDN);

    bench_eval::compute_verified_bound(
        relative, absolute, bound, bench_eval::VerifiedBound::dw_plus_fp,
        reference);
    mpfr_mul_ui(expected, u_squared, 2, MPFR_RNDN);
    expect_equal(bound, expected, "dw_plus_fp bound changed");
    if (!mpfr_zero_p(absolute)) fail("dw_plus_fp gained an absolute term");

    bench_eval::compute_verified_bound(
        relative, absolute, bound, bench_eval::VerifiedBound::dw_plus_dw,
        reference);
    mpfr_set_ui_2exp(temporary, 4, -53, MPFR_RNDN);
    mpfr_ui_sub(temporary, 1, temporary, MPFR_RNDN);
    mpfr_mul_ui(expected, u_squared, 3, MPFR_RNDN);
    mpfr_div(expected, expected, temporary, MPFR_RNDN);
    expect_equal(bound, expected, "dw_plus_dw bound changed");

    bench_eval::compute_verified_bound(
        relative, absolute, bound, bench_eval::VerifiedBound::dw_times_fp,
        reference);
    mpfr_mul_ui(expected, u_squared, 2, MPFR_RNDN);
    mpfr_mul_ui(temporary, eta, 251, MPFR_RNDN);
    mpfr_div_ui(temporary, temporary, 100, MPFR_RNDN);
    mpfr_add(expected, expected, temporary, MPFR_RNDN);
    expect_equal(bound, expected, "dw_times_fp bound changed");

    bench_eval::compute_verified_bound(
        relative, absolute, bound, bench_eval::VerifiedBound::dw_times_dw,
        reference);
    mpfr_mul_ui(expected, u_squared, 4, MPFR_RNDN);
    mpfr_mul_ui(temporary, eta, 5, MPFR_RNDN);
    mpfr_div_ui(temporary, temporary, 2, MPFR_RNDN);
    mpfr_add(expected, expected, temporary, MPFR_RNDN);
    expect_equal(bound, expected, "dw_times_dw bound changed");

    bench_eval::compute_verified_bound(
        relative, absolute, bound, bench_eval::VerifiedBound::dw_div_fp,
        reference);
    mpfr_mul_ui(expected, u_squared, 3, MPFR_RNDN);
    mpfr_add(expected, expected, eta, MPFR_RNDN);
    expect_equal(bound, expected, "dw_div_fp bound changed");

    bench_eval::compute_verified_bound(
        relative, absolute, bound, bench_eval::VerifiedBound::dw_div_dw,
        reference);
    mpfr_mul_ui(expected, u_squared, 98, MPFR_RNDN);
    mpfr_div_ui(expected, expected, 10, MPFR_RNDN);
    mpfr_mul_ui(temporary, eta, 5, MPFR_RNDN);
    mpfr_div_ui(temporary, temporary, 2, MPFR_RNDN);
    mpfr_add(expected, expected, temporary, MPFR_RNDN);
    expect_equal(bound, expected, "dw_div_dw bound changed");

    mpfr_set_zero(reference, 0);
    if (bench_eval::compute_verified_bound(
            relative, absolute, bound,
            bench_eval::VerifiedBound::dw_plus_fp, reference)) {
        fail("zero-reference addition bound should be zero");
    }
    if (!bench_eval::compute_verified_bound(
            relative, absolute, bound,
            bench_eval::VerifiedBound::dw_times_dw, reference)) {
        fail("mixed multiplication bound lost its absolute term");
    }

    mpfr_clears(reference, relative, absolute, bound, expected, u_squared,
                eta, temporary, (mpfr_ptr)0);
    std::puts("verified bound formulas passed");
    return EXIT_SUCCESS;
}
