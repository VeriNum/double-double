// Harness test: checks MPFR-based error classification, bound diagnostics,
// double-word validity, and result serialization using synthetic results. It
// does not test the arithmetic library implementations.

#include "mpfr_accuracy.hpp"

#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <limits>

namespace {

[[noreturn]] void fail(const char *message) {
    std::fprintf(stderr, "accuracy metric test failed: %s\n", message);
    std::exit(EXIT_FAILURE);
}

bench_eval::ReferenceEvaluator reference_one() {
    return [](std::size_t, mpfr_ptr reference, mpfr_ptr, mpfr_ptr, mpfr_ptr) {
        mpfr_set_ui(reference, 1, MPFR_RNDN);
    };
}

bench_eval::CaseDescriber describe_case() {
    return [](std::size_t index) {
        return std::string("synthetic case ") + std::to_string(index);
    };
}

} // namespace

int main() {
    bench_eval::CollectedResults relative_results;
    relative_results.outcomes.push_back(
        bench_eval::CallOutcome::returned_normally);
    relative_results.values.push_back(bench_eval::ResultPair{
        std::nextafter(1.0, 2.0), 0.0});

    bench_eval::AccuracyOptions relative_options;
    relative_options.bound_kind = bench_eval::VerifiedBound::dw_plus_fp;
    bench_eval::AccuracyCounts relative = bench_eval::measure_accuracy(
        relative_results,
        [](std::size_t) {
            return bench_eval::ResultPair{1.0, 0.0};
        },
        reference_one(), describe_case(), relative_options);
    if (relative.relative_term_references != 1
        || relative.absolute_term_references != 0
        || relative.zero_bound_references != 0
        || relative.dd_lib.relative_term_relative.count != 1
        || relative.dd_lib.relative_term_bound_utilization.count != 1
        || relative.dd_lib.relative_term_bound_ratio_above_one != 1
        || relative.dd_lib.bound_violations.size() != 1
        || relative.dd_lib.bound_violations[0].regime
            != bench_eval::ErrorRegime::relative_term_dominates
        || relative.dd_lib.bound_violations[0].witness.case_index != 0
        || relative.qd.relative_term_bound_ratio_above_one != 0) {
        fail("relative-regime metrics returned unexpected counts");
    }

    bench_eval::CollectedResults exact_results;
    exact_results.outcomes.push_back(
        bench_eval::CallOutcome::returned_normally);
    exact_results.values.push_back(bench_eval::ResultPair{1.0, 0.0});
    bench_eval::AccuracyCounts invalid_qd = bench_eval::measure_accuracy(
        exact_results,
        [](std::size_t) {
            return bench_eval::ResultPair{1.0, std::ldexp(1.0, -52)};
        },
        reference_one(), describe_case(), relative_options);
    if (invalid_qd.qd_invalid_double_word != 1
        || invalid_qd.first_qd_invalid_double_word.case_index != 0
        || invalid_qd.qd.relative_term_relative.count != 1
        || invalid_qd.qd.relative_term_bound_utilization.count != 1
        || invalid_qd.qd.relative_term_bound_ratio_above_one != 1) {
        fail("finite invalid QD result was not recorded and measured");
    }

    exact_results.values[0] = bench_eval::ResultPair{
        1.0, std::ldexp(1.0, -52)};
    bench_eval::AccuracyCounts invalid_dd = bench_eval::measure_accuracy(
        exact_results,
        [](std::size_t) {
            return bench_eval::ResultPair{1.0, 0.0};
        },
        reference_one(), describe_case(), relative_options);
    if (invalid_dd.dd_lib_invalid_double_word != 1
        || invalid_dd.first_dd_lib_invalid_double_word.case_index != 0) {
        fail("invalid dd_lib result witness was not retained");
    }

    bench_eval::CollectedResults zero_results;
    zero_results.outcomes.push_back(
        bench_eval::CallOutcome::returned_normally);
    zero_results.values.push_back(bench_eval::ResultPair{
        std::numeric_limits<double>::denorm_min(), 0.0});
    bench_eval::AccuracyOptions mixed_options;
    mixed_options.bound_kind = bench_eval::VerifiedBound::dw_times_dw;
    bench_eval::AccuracyCounts mixed_zero = bench_eval::measure_accuracy(
        zero_results,
        [](std::size_t) {
            return bench_eval::ResultPair{
                std::numeric_limits<double>::infinity(), 0.0};
        },
        [](std::size_t, mpfr_ptr reference, mpfr_ptr, mpfr_ptr, mpfr_ptr) {
            mpfr_set_zero(reference, 0);
        }, describe_case(), mixed_options);
    if (mixed_zero.relative_term_references != 0
        || mixed_zero.absolute_term_references != 1
        || mixed_zero.zero_bound_references != 0
        || mixed_zero.dd_lib.absolute_term_absolute.count != 1
        || mixed_zero.dd_lib.absolute_term_bound_utilization.count != 1
        || mixed_zero.qd_nonfinite_absolute_term != 1
        || mixed_zero.qd.absolute_term_absolute.count != 0) {
        fail("mixed-bound zero reference was not in the absolute regime");
    }

    zero_results.values[0] = bench_eval::ResultPair{0.0, 0.0};
    bench_eval::AccuracyCounts pure_zero = bench_eval::measure_accuracy(
        zero_results,
        [](std::size_t) {
            return bench_eval::ResultPair{
                std::numeric_limits<double>::denorm_min(), 0.0};
        },
        [](std::size_t, mpfr_ptr reference, mpfr_ptr, mpfr_ptr, mpfr_ptr) {
            mpfr_set_zero(reference, 0);
        }, describe_case(), relative_options);
    if (pure_zero.zero_bound_references != 1
        || pure_zero.dd_lib.zero_bound_nonzero_error != 0
        || pure_zero.qd.zero_bound_nonzero_error != 1
        || pure_zero.qd.bound_violations.size() != 1
        || pure_zero.qd.bound_violations[0].regime
            != bench_eval::ErrorRegime::zero_bound_reference
        || pure_zero.qd.first_zero_bound_nonzero_error.case_index != 0
        || pure_zero.qd.first_zero_bound_nonzero_error.absolute_error.empty()
        || pure_zero.dd_lib.relative_term_relative.count != 0
        || pure_zero.dd_lib.absolute_term_absolute.count != 0) {
        fail("zero-bound reference diagnostics returned unexpected counts");
    }

    zero_results.values[0] = bench_eval::ResultPair{
        std::numeric_limits<double>::denorm_min(), 0.0};
    bench_eval::AccuracyCounts dd_zero_error = bench_eval::measure_accuracy(
        zero_results,
        [](std::size_t) {
            return bench_eval::ResultPair{0.0, 0.0};
        },
        [](std::size_t, mpfr_ptr reference, mpfr_ptr, mpfr_ptr, mpfr_ptr) {
            mpfr_set_zero(reference, 0);
        }, describe_case(), relative_options);
    if (dd_zero_error.dd_lib.zero_bound_nonzero_error != 1
        || dd_zero_error.dd_lib.bound_violations.size() != 1
        || dd_zero_error.dd_lib.first_zero_bound_nonzero_error.case_index != 0
        || dd_zero_error.dd_lib.first_zero_bound_nonzero_error.absolute_error.empty()) {
        fail("dd_lib zero-bound error witness was not retained");
    }

    bench_eval::CollectedResults division_results;
    division_results.outcomes.push_back(
        bench_eval::CallOutcome::returned_normally);
    division_results.values.push_back(bench_eval::ResultPair{
        std::nextafter(1.0, 2.0), 0.0});

    bench_eval::AccuracyOptions division_options;
    division_options.bound_kind = bench_eval::VerifiedBound::dw_div_fp;
    division_options.division_reference = true;
    bool saw_oracle_precision = false;
    bool saw_division_precision = false;
    bench_eval::AccuracyCounts division = bench_eval::measure_accuracy(
        division_results,
        [](std::size_t) {
            return bench_eval::ResultPair{1.0, 0.0};
        },
        [&](std::size_t, mpfr_ptr reference, mpfr_ptr, mpfr_ptr, mpfr_ptr) {
            saw_oracle_precision = saw_oracle_precision
                || mpfr_get_prec(reference) == 2112;
            saw_division_precision = saw_division_precision
                || mpfr_get_prec(reference) == 4224;
            mpfr_set_ui(reference, 1, MPFR_RNDN);
        }, describe_case(), division_options);
    if (division.higher_precision_bound_rechecks != 1
        || division.higher_precision_bound_decision_changes != 0
        || division.dd_lib.relative_term_bound_ratio_above_one != 1
        || !saw_oracle_precision || !saw_division_precision) {
        fail("division recheck path returned unexpected counts");
    }

    mpfr_t reference;
    mpfr_t represented;
    mpfr_t error;
    mpfr_t relative_term;
    mpfr_t absolute_term;
    mpfr_t bound;
    mpfr_t scratch;
    mpfr_inits2(2112, reference, represented, error, relative_term,
                absolute_term, bound, scratch, (mpfr_ptr)0);
    mpfr_set_ui(reference, 1, MPFR_RNDN);
    bench_eval::ResultPair valid{1.0, std::ldexp(1.0, -54)};
    bench_eval::ResultPair invalid{1.0, std::ldexp(1.0, -52)};
    if (!bench_eval::valid_double_word_mpfr(valid, represented, scratch)
        || bench_eval::valid_double_word_mpfr(invalid, represented, scratch)) {
        fail("MPFR double-word validity helper returned the wrong result");
    }
    bench_eval::set_pair_value(reference, valid, scratch);
    if (!bench_eval::reconstructs_reference_mpfr(
            valid, reference, represented, scratch)) {
        fail("MPFR reconstruction helper rejected an exact pair");
    }
    mpfr_set_ui(reference, 1, MPFR_RNDN);
    if (bench_eval::compare_pair_error_to_verified_bound(
            relative_results.values[0], reference,
            bench_eval::VerifiedBound::dw_plus_fp, represented, error,
            relative_term, absolute_term, bound, scratch) <= 0) {
        fail("MPFR error-to-bound helper missed an above-bound result");
    }
    mpfr_clears(reference, represented, error, relative_term, absolute_term,
                bound, scratch, (mpfr_ptr)0);

    mpfr_t precise;
    mpfr_t decoded;
    mpfr_t serialization_error;
    mpfr_t serialization_tolerance;
    mpfr_inits2(4224, precise, decoded, serialization_error,
                serialization_tolerance, (mpfr_ptr)0);
    mpfr_const_pi(precise, MPFR_RNDN);
    std::string precise_text = bench_eval::format_mpfr(precise);
    (void)mpfr_set_str(decoded, precise_text.c_str(), 10, MPFR_RNDN);
    mpfr_sub(serialization_error, decoded, precise, MPFR_RNDN);
    mpfr_abs(serialization_error, serialization_error, MPFR_RNDN);
    mpfr_div(serialization_error, serialization_error, precise, MPFR_RNDN);
    (void)mpfr_set_str(serialization_tolerance, "1e-99", 10, MPFR_RNDU);
    if (precise_text.size() < 100
        || mpfr_cmp(serialization_error, serialization_tolerance) > 0) {
        fail("formatted MPFR value lost 100-digit fidelity");
    }
    mpfr_clears(precise, decoded, serialization_error,
                serialization_tolerance, (mpfr_ptr)0);

    std::puts("accuracy metric classifications passed");
    return EXIT_SUCCESS;
}
