#include "mpfr_accuracy.hpp"

#include <cmath>
#include <cstdio>
#include <cstdlib>

namespace bench_eval {
namespace {

constexpr mpfr_prec_t oracle_precision =
    static_cast<mpfr_prec_t>(reference_precision);
constexpr mpfr_prec_t recheck_precision = 2 * oracle_precision;
constexpr int serialized_significant_digits = 100;

class MetricAccumulator {
public:
    explicit MetricAccumulator(mpfr_prec_t precision)
        : precision_(precision), count_(0), seen_(false) {
        mpfr_inits2(precision_, sum_, maximum_, (mpfr_ptr)0);
        mpfr_set_zero(sum_, 0);
        mpfr_set_zero(maximum_, 0);
    }

    ~MetricAccumulator() {
        mpfr_clears(sum_, maximum_, (mpfr_ptr)0);
    }

    MetricAccumulator(const MetricAccumulator &) = delete;
    MetricAccumulator &operator=(const MetricAccumulator &) = delete;

    bool add(mpfr_srcptr metric, mpfr_srcptr absolute_error,
             mpfr_srcptr reference, const ResultPair &result,
             std::size_t case_index) {
        bool new_maximum = !seen_ || mpfr_greater_p(metric, maximum_);
        mpfr_add(sum_, sum_, metric, MPFR_RNDN);
        ++count_;
        if (new_maximum) {
            seen_ = true;
            mpfr_set(maximum_, metric, MPFR_RNDN);
            witness_.case_index = case_index;
            witness_.result = result;
            witness_.reference = format_mpfr(reference);
            witness_.absolute_error = format_mpfr(absolute_error);
        }
        return new_maximum;
    }

    void set_witness_inputs(const std::string &inputs) {
        witness_.inputs = inputs;
    }

    MetricSummary finish(mpfr_srcptr scale,
                         bool include_scaled_units) const {
        MetricSummary summary;
        summary.count = count_;
        if (count_ == 0) return summary;

        mpfr_t mean;
        mpfr_t scaled;
        mpfr_inits2(precision_, mean, scaled, (mpfr_ptr)0);
        mpfr_div_ui(mean, sum_, count_, MPFR_RNDN);
        summary.maximum = format_mpfr(maximum_);
        summary.mean = format_mpfr(mean);
        summary.maximum_nonzero = !mpfr_zero_p(maximum_);
        summary.witness = witness_;

        if (include_scaled_units) {
            mpfr_div(scaled, maximum_, scale, MPFR_RNDN);
            summary.maximum_scaled = format_mpfr(scaled);
            mpfr_div(scaled, mean, scale, MPFR_RNDN);
            summary.mean_scaled = format_mpfr(scaled);
        }
        mpfr_clears(mean, scaled, (mpfr_ptr)0);
        return summary;
    }

private:
    mpfr_prec_t precision_;
    std::size_t count_;
    bool seen_;
    mpfr_t sum_;
    mpfr_t maximum_;
    ErrorWitness witness_;
};

template <class Describe>
void add_metric(MetricAccumulator &accumulator, mpfr_srcptr metric,
                mpfr_srcptr absolute_error, mpfr_srcptr reference,
                const ResultPair &result, std::size_t case_index,
                const Describe &describe) {
    if (accumulator.add(metric, absolute_error, reference, result,
                        case_index)) {
        accumulator.set_witness_inputs(describe(case_index));
    }
}

bool set_verified_bound_components(
        mpfr_ptr relative_term, mpfr_ptr absolute_term, mpfr_ptr bound,
        VerifiedBound kind, mpfr_srcptr reference_magnitude,
        mpfr_srcptr u, mpfr_srcptr u_squared, mpfr_srcptr eta,
        mpfr_ptr temporary) {
    mpfr_set_zero(relative_term, 0);
    mpfr_set_zero(absolute_term, 0);
    mpfr_set_zero(bound, 0);
    if (kind == VerifiedBound::none) return false;

    mpfr_mul(relative_term, u_squared, reference_magnitude, MPFR_RNDN);
    switch (kind) {
    case VerifiedBound::none:
        return false;
    case VerifiedBound::dw_plus_fp:
        mpfr_mul_ui(relative_term, relative_term, 2, MPFR_RNDN);
        break;
    case VerifiedBound::dw_plus_dw:
        mpfr_mul_ui(relative_term, relative_term, 3, MPFR_RNDN);
        mpfr_mul_ui(temporary, u, 4, MPFR_RNDN);
        mpfr_ui_sub(temporary, 1, temporary, MPFR_RNDN);
        mpfr_div(relative_term, relative_term, temporary, MPFR_RNDN);
        break;
    case VerifiedBound::dw_times_fp:
        mpfr_mul_ui(relative_term, relative_term, 2, MPFR_RNDN);
        mpfr_mul_ui(absolute_term, eta, 251, MPFR_RNDN);
        mpfr_div_ui(absolute_term, absolute_term, 100, MPFR_RNDN);
        break;
    case VerifiedBound::dw_times_dw:
        mpfr_mul_ui(relative_term, relative_term, 4, MPFR_RNDN);
        mpfr_mul_ui(absolute_term, eta, 5, MPFR_RNDN);
        mpfr_div_ui(absolute_term, absolute_term, 2, MPFR_RNDN);
        break;
    case VerifiedBound::dw_div_fp:
        mpfr_mul_ui(relative_term, relative_term, 3, MPFR_RNDN);
        mpfr_set(absolute_term, eta, MPFR_RNDN);
        break;
    case VerifiedBound::dw_div_dw:
        mpfr_mul_ui(relative_term, relative_term, 98, MPFR_RNDN);
        mpfr_div_ui(relative_term, relative_term, 10, MPFR_RNDN);
        mpfr_mul_ui(absolute_term, eta, 5, MPFR_RNDN);
        mpfr_div_ui(absolute_term, absolute_term, 2, MPFR_RNDN);
        break;
    }
    mpfr_add(bound, relative_term, absolute_term, MPFR_RNDN);
    return !mpfr_zero_p(bound);
}

ErrorRegime classify_error_regime(
        mpfr_srcptr reference, VerifiedBound bound_kind,
        mpfr_srcptr relative_term, mpfr_srcptr absolute_term) {
    if (mpfr_zero_p(reference)) {
        return mpfr_greater_p(absolute_term, relative_term)
            ? ErrorRegime::absolute_term_dominates
            : ErrorRegime::zero_bound_reference;
    }
    if (bound_kind == VerifiedBound::none
        || mpfr_cmp(relative_term, absolute_term) >= 0) {
        return ErrorRegime::relative_term_dominates;
    }
    return ErrorRegime::absolute_term_dominates;
}

void set_bound_crossover(mpfr_ptr crossover, VerifiedBound kind) {
    unsigned long numerator = 0;
    unsigned long denominator = 1;
    switch (kind) {
    case VerifiedBound::dw_times_fp:
        numerator = 251;
        denominator = 200;
        break;
    case VerifiedBound::dw_times_dw:
        numerator = 5;
        denominator = 8;
        break;
    case VerifiedBound::dw_div_fp:
        numerator = 1;
        denominator = 3;
        break;
    case VerifiedBound::dw_div_dw:
        numerator = 25;
        denominator = 98;
        break;
    case VerifiedBound::none:
    case VerifiedBound::dw_plus_fp:
    case VerifiedBound::dw_plus_dw:
        std::abort();
    }
    mpfr_set_ui_2exp(crossover, numerator, -968, MPFR_RNDN);
    mpfr_div_ui(crossover, crossover, denominator, MPFR_RNDN);
}

void set_contract_witness(ContractWitness &witness, std::size_t case_index,
                          const ResultPair &result, mpfr_srcptr reference,
                          const CaseDescriber &describe) {
    if (witness.case_index != SIZE_MAX) return;
    witness.case_index = case_index;
    witness.result = result;
    witness.reference = format_mpfr(reference);
    witness.inputs = describe(case_index);
}

void set_nonfinite_witness(ErrorWitness &witness, std::size_t case_index,
                           const ResultPair &result, mpfr_srcptr reference,
                           const CaseDescriber &describe) {
    if (witness.case_index != SIZE_MAX) return;
    witness.case_index = case_index;
    witness.result = result;
    witness.reference = format_mpfr(reference);
    witness.absolute_error = "inf";
    witness.inputs = describe(case_index);
}

void set_error_witness(ErrorWitness &witness, std::size_t case_index,
                       const ResultPair &result, mpfr_srcptr reference,
                       mpfr_srcptr absolute_error,
                       const CaseDescriber &describe) {
    if (witness.case_index != SIZE_MAX) return;
    witness.case_index = case_index;
    witness.result = result;
    witness.reference = format_mpfr(reference);
    witness.absolute_error = format_mpfr(absolute_error);
    witness.inputs = describe(case_index);
}

void add_bound_violation(ImplementationMetrics &metrics,
                         ErrorRegime regime,
                         std::size_t case_index,
                         const ResultPair &result,
                         mpfr_srcptr reference,
                         mpfr_srcptr absolute_error,
                         const CaseDescriber &describe) {
    BoundViolation violation;
    violation.regime = regime;
    set_error_witness(violation.witness, case_index, result, reference,
                      absolute_error, describe);
    metrics.bound_violations.push_back(violation);
}

// Return true when a comparison is either an apparent violation or within
// 2^-256 of equality.  This test deliberately compares
// the absolute error with the complete bound directly; the quotient is a
// reporting metric and must not decide whether the bound was exceeded.
bool bound_comparison_needs_recheck(mpfr_srcptr error, mpfr_srcptr bound) {
    if (mpfr_cmp(error, bound) >= 0) return true;
    mpfr_t distance;
    mpfr_t threshold;
    mpfr_prec_t precision = mpfr_get_prec(bound);
    mpfr_inits2(precision, distance, threshold, (mpfr_ptr)0);
    mpfr_sub(distance, bound, error, MPFR_RNDD);
    mpfr_mul_2si(threshold, bound, -256, MPFR_RNDU);
    bool close = mpfr_cmp(distance, threshold) <= 0;
    mpfr_clears(distance, threshold, (mpfr_ptr)0);
    return close;
}

}  // namespace

void set_pair_value(mpfr_ptr value, const ResultPair &pair,
                    mpfr_ptr scratch) {
    mpfr_set_d(value, pair.hi, MPFR_RNDN);
    mpfr_set_d(scratch, pair.lo, MPFR_RNDN);
    mpfr_add(value, value, scratch, MPFR_RNDN);
}

void set_dword_value(mpfr_ptr value, const dword &word,
                     mpfr_ptr scratch) {
    mpfr_set_d(value, word.s, MPFR_RNDN);
    mpfr_set_d(scratch, word.t, MPFR_RNDN);
    mpfr_add(value, value, scratch, MPFR_RNDN);
}

bool valid_double_word_mpfr(const ResultPair &result,
                            mpfr_ptr represented,
                            mpfr_ptr scratch) {
    if (!std::isfinite(result.hi) || !std::isfinite(result.lo)) return false;
    set_pair_value(represented, result, scratch);
    return mpfr_get_d(represented, MPFR_RNDN) == result.hi;
}

bool reconstructs_reference_mpfr(const ResultPair &result,
                                 mpfr_srcptr reference,
                                 mpfr_ptr represented,
                                 mpfr_ptr scratch) {
    if (!std::isfinite(result.hi) || !std::isfinite(result.lo)) return false;
    set_pair_value(represented, result, scratch);
    return mpfr_equal_p(represented, reference) != 0;
}

std::string format_mpfr(mpfr_srcptr value) {
    char *text = nullptr;
    // In scientific notation MPFR's precision is the number of digits after
    // the radix point, so subtract one for the leading significant digit.
    if (mpfr_asprintf(&text, "%.*Re", serialized_significant_digits - 1,
                      value) < 0
        || text == nullptr) {
        std::abort();
    }
    std::string formatted(text);
    mpfr_free_str(text);
    return formatted;
}

void verify_error_regime_classifier() {
    mpfr_t reference;
    mpfr_t magnitude;
    mpfr_t u;
    mpfr_t u_squared;
    mpfr_t eta;
    mpfr_t relative_term;
    mpfr_t absolute_term;
    mpfr_t bound;
    mpfr_t temporary;
    mpfr_t crossover;
    mpfr_t below;
    mpfr_t above;
    mpfr_t check_sum;
    mpfr_inits2(oracle_precision, reference, magnitude, u, u_squared, eta,
                relative_term, absolute_term, bound, temporary, crossover,
                below, above, check_sum, (mpfr_ptr)0);
    mpfr_set_ui_2exp(u, 1, -53, MPFR_RNDN);
    mpfr_mul(u_squared, u, u, MPFR_RNDN);
    mpfr_set_ui_2exp(eta, 1, -1074, MPFR_RNDN);

    bool valid = true;
    auto classify = [&](VerifiedBound kind) {
        mpfr_abs(magnitude, reference, MPFR_RNDN);
        set_verified_bound_components(relative_term, absolute_term, bound,
                                      kind, magnitude, u, u_squared, eta,
                                      temporary);
        mpfr_add(check_sum, relative_term, absolute_term, MPFR_RNDN);
        valid = valid && mpfr_equal_p(check_sum, bound);
        return classify_error_regime(reference, kind, relative_term,
                                     absolute_term);
    };

    mpfr_set_zero(reference, 0);
    valid = valid && classify(VerifiedBound::dw_div_dw)
                     == ErrorRegime::absolute_term_dominates;
    mpfr_set_zero(reference, -1);
    valid = valid && classify(VerifiedBound::dw_times_fp)
                     == ErrorRegime::absolute_term_dominates;
    valid = valid && classify(VerifiedBound::dw_plus_fp)
                     == ErrorRegime::zero_bound_reference;
    valid = valid && classify(VerifiedBound::dw_plus_dw)
                     == ErrorRegime::zero_bound_reference;

    const VerifiedBound mixed_bounds[] = {
        VerifiedBound::dw_times_fp,
        VerifiedBound::dw_times_dw,
        VerifiedBound::dw_div_fp,
        VerifiedBound::dw_div_dw
    };
    for (VerifiedBound kind : mixed_bounds) {
        set_bound_crossover(crossover, kind);
        mpfr_div_ui(below, crossover, 2, MPFR_RNDN);
        mpfr_mul_ui(above, crossover, 2, MPFR_RNDN);
        mpfr_set(reference, below, MPFR_RNDN);
        valid = valid && classify(kind)
                         == ErrorRegime::absolute_term_dominates;
        mpfr_set(reference, crossover, MPFR_RNDN);
        valid = valid && classify(kind)
                         == ErrorRegime::relative_term_dominates;
        mpfr_set(reference, above, MPFR_RNDN);
        valid = valid && classify(kind)
                         == ErrorRegime::relative_term_dominates;
    }

    mpfr_set_ui(reference, 1, MPFR_RNDN);
    valid = valid && classify(VerifiedBound::dw_plus_fp)
                     == ErrorRegime::relative_term_dominates;
    valid = valid && classify(VerifiedBound::dw_plus_dw)
                     == ErrorRegime::relative_term_dominates;
    valid = valid && classify(VerifiedBound::none)
                     == ErrorRegime::relative_term_dominates;

    mpfr_clears(reference, magnitude, u, u_squared, eta, relative_term,
                absolute_term, bound, temporary, crossover, below, above,
                check_sum, (mpfr_ptr)0);
    if (!valid) {
        std::fprintf(stderr, "failed error-regime classifier self-check\n");
        std::abort();
    }
}

bool compute_verified_bound(mpfr_ptr relative_term,
                            mpfr_ptr absolute_term,
                            mpfr_ptr bound,
                            VerifiedBound kind,
                            mpfr_srcptr reference) {
    mpfr_prec_t precision = mpfr_get_prec(bound);
    mpfr_t magnitude;
    mpfr_t u;
    mpfr_t u_squared;
    mpfr_t eta;
    mpfr_t temporary;
    mpfr_inits2(precision, magnitude, u, u_squared, eta, temporary,
                (mpfr_ptr)0);
    mpfr_abs(magnitude, reference, MPFR_RNDN);
    mpfr_set_ui_2exp(u, 1, -53, MPFR_RNDN);
    mpfr_mul(u_squared, u, u, MPFR_RNDN);
    mpfr_set_ui_2exp(eta, 1, -1074, MPFR_RNDN);
    bool nonzero = set_verified_bound_components(
        relative_term, absolute_term, bound, kind, magnitude,
        u, u_squared, eta, temporary);
    mpfr_clears(magnitude, u, u_squared, eta, temporary, (mpfr_ptr)0);
    return nonzero;
}

int compare_pair_error_to_verified_bound(
        const ResultPair &result,
        mpfr_srcptr reference,
        VerifiedBound kind,
        mpfr_ptr represented,
        mpfr_ptr absolute_error,
        mpfr_ptr relative_term,
        mpfr_ptr absolute_term,
        mpfr_ptr bound,
        mpfr_ptr scratch) {
    set_pair_value(represented, result, scratch);
    mpfr_sub(absolute_error, represented, reference, MPFR_RNDN);
    mpfr_abs(absolute_error, absolute_error, MPFR_RNDN);
    compute_verified_bound(relative_term, absolute_term, bound, kind,
                           reference);
    return mpfr_cmp(absolute_error, bound);
}

AccuracyCounts measure_accuracy(const CollectedResults &results,
                                const QdEvaluator &qd,
                                const ReferenceEvaluator &reference,
                                const CaseDescriber &describe,
                                const AccuracyOptions &options) {
    const bool division_bound =
        options.bound_kind == VerifiedBound::dw_div_fp
        || options.bound_kind == VerifiedBound::dw_div_dw;
    if (options.bound_kind == VerifiedBound::none
        || options.division_reference != division_bound
        || results.values.size() != results.outcomes.size()) {
        std::abort();
    }
    for (CallOutcome outcome : results.outcomes) {
        if (outcome == CallOutcome::pending) std::abort();
    }
    const mpfr_prec_t measurement_precision = options.division_reference
        ? recheck_precision : oracle_precision;

    AccuracyCounts counts;
    mpfr_t dd_value;
    mpfr_t qd_value;
    mpfr_t reference_value;
    mpfr_t temporary0;
    mpfr_t temporary1;
    mpfr_t scratch;
    mpfr_t dd_error;
    mpfr_t qd_error;
    mpfr_t magnitude;
    mpfr_t metric;
    mpfr_t eta;
    mpfr_t u;
    mpfr_t u_squared;
    mpfr_t relative_term;
    mpfr_t absolute_term;
    mpfr_t bound;
    mpfr_t bound_temporary;
    mpfr_inits2(measurement_precision, dd_value, qd_value, reference_value,
                temporary0, temporary1, scratch, dd_error, qd_error,
                magnitude, metric, eta, u, u_squared, relative_term,
                absolute_term, bound, bound_temporary, (mpfr_ptr)0);
    mpfr_set_ui_2exp(eta, 1, -1074, MPFR_RNDN);
    mpfr_set_ui_2exp(u, 1, -53, MPFR_RNDN);
    mpfr_mul(u_squared, u, u, MPFR_RNDN);

    // Division results are measured entirely at 4224 bits.  These 2112-bit
    // values reproduce the former screening decision only so the report can
    // say whether the higher-precision direct comparison changed it.
    mpfr_t screening_value;
    mpfr_t screening_reference;
    mpfr_t screening_temporary0;
    mpfr_t screening_temporary1;
    mpfr_t screening_scratch;
    mpfr_t screening_error;
    mpfr_t screening_magnitude;
    mpfr_t screening_eta;
    mpfr_t screening_u;
    mpfr_t screening_u_squared;
    mpfr_t screening_relative_term;
    mpfr_t screening_absolute_term;
    mpfr_t screening_bound;
    mpfr_t screening_bound_temporary;
    mpfr_inits2(oracle_precision, screening_value, screening_reference,
                screening_temporary0, screening_temporary1,
                screening_scratch, screening_error, screening_magnitude,
                screening_eta, screening_u, screening_u_squared,
                screening_relative_term, screening_absolute_term,
                screening_bound, screening_bound_temporary, (mpfr_ptr)0);
    mpfr_set_ui_2exp(screening_eta, 1, -1074, MPFR_RNDN);
    mpfr_set_ui_2exp(screening_u, 1, -53, MPFR_RNDN);
    mpfr_mul(screening_u_squared, screening_u, screening_u, MPFR_RNDN);

    MetricAccumulator dd_relative_error(measurement_precision);
    MetricAccumulator dd_relative_bound(measurement_precision);
    MetricAccumulator dd_absolute_error(measurement_precision);
    MetricAccumulator dd_absolute_bound(measurement_precision);
    MetricAccumulator qd_relative_error(measurement_precision);
    MetricAccumulator qd_relative_bound(measurement_precision);
    MetricAccumulator qd_absolute_error(measurement_precision);
    MetricAccumulator qd_absolute_bound(measurement_precision);

    auto add_bound_utilization = [&](ErrorRegime regime,
                                     const ResultPair &result,
                                     mpfr_srcptr error,
                                     std::size_t case_index,
                                     MetricAccumulator &relative_accumulator,
                                     MetricAccumulator &absolute_accumulator,
                                     ImplementationMetrics &metrics) {
        if (regime == ErrorRegime::zero_bound_reference) {
            if (!mpfr_zero_p(error)) {
                ++metrics.zero_bound_nonzero_error;
                set_error_witness(metrics.first_zero_bound_nonzero_error,
                                  case_index, result, reference_value, error,
                                  describe);
                add_bound_violation(metrics, regime, case_index, result,
                                    reference_value, error, describe);
            }
            return;
        }
        if (mpfr_zero_p(bound)) std::abort();

        const int comparison = mpfr_cmp(error, bound);
        const bool above_one = comparison > 0;
        if (options.division_reference) {
            set_pair_value(screening_value, result, screening_scratch);
            mpfr_sub(screening_error, screening_value, screening_reference,
                     MPFR_RNDN);
            mpfr_abs(screening_error, screening_error, MPFR_RNDN);
            const int screening_comparison =
                mpfr_cmp(screening_error, screening_bound);
            const bool screening_needs_recheck =
                bound_comparison_needs_recheck(screening_error,
                                               screening_bound);
            const bool measured_needs_recheck =
                bound_comparison_needs_recheck(error, bound);
            if (screening_needs_recheck || measured_needs_recheck) {
                ++counts.higher_precision_bound_rechecks;
                if ((screening_comparison > 0) != above_one) {
                    ++counts.higher_precision_bound_decision_changes;
                }
            }
        }

        // The quotient is retained only as the requested utilization metric.
        // It never controls the above-bound classification.
        mpfr_div(metric, error, bound, MPFR_RNDN);

        if (regime == ErrorRegime::relative_term_dominates) {
            add_metric(relative_accumulator, metric, error, reference_value,
                       result, case_index, describe);
            if (above_one) {
                ++metrics.relative_term_bound_ratio_above_one;
                add_bound_violation(metrics, regime, case_index, result,
                                    reference_value, error, describe);
            }
        } else if (regime == ErrorRegime::absolute_term_dominates) {
            add_metric(absolute_accumulator, metric, error, reference_value,
                       result, case_index, describe);
            if (above_one) {
                ++metrics.absolute_term_bound_ratio_above_one;
                add_bound_violation(metrics, regime, case_index, result,
                                    reference_value, error, describe);
            }
        } else {
            std::abort();
        }
    };

    for (std::size_t i = 0; i < results.outcomes.size(); ++i) {
        if (results.outcomes[i] != CallOutcome::returned_normally) continue;
        ++counts.compared;

        ResultPair dd_result = results.values[i];
        set_pair_value(dd_value, dd_result, scratch);
        reference(i, reference_value, temporary0, temporary1, scratch);
        if (!mpfr_number_p(dd_value) || !mpfr_number_p(reference_value)) {
            std::fprintf(stderr,
                         "normal return or MPFR reference was nonfinite "
                         "at case %zu\n", i);
            std::abort();
        }

        if (!valid_double_word_mpfr(dd_result, dd_value, scratch)) {
            ++counts.dd_lib_invalid_double_word;
            set_contract_witness(counts.first_dd_lib_invalid_double_word,
                                 i, dd_result, reference_value, describe);
        }

        mpfr_sub(dd_error, dd_value, reference_value, MPFR_RNDN);
        mpfr_abs(dd_error, dd_error, MPFR_RNDN);
        mpfr_abs(magnitude, reference_value, MPFR_RNDN);
        set_verified_bound_components(
            relative_term, absolute_term, bound, options.bound_kind,
            magnitude, u, u_squared, eta, bound_temporary);
        ErrorRegime regime = classify_error_regime(
            reference_value, options.bound_kind, relative_term,
            absolute_term);

        if (options.division_reference) {
            reference(i, screening_reference, screening_temporary0,
                      screening_temporary1, screening_scratch);
            if (!mpfr_number_p(screening_reference)) std::abort();
            mpfr_abs(screening_magnitude, screening_reference, MPFR_RNDN);
            set_verified_bound_components(
                screening_relative_term, screening_absolute_term,
                screening_bound, options.bound_kind, screening_magnitude,
                screening_u, screening_u_squared, screening_eta,
                screening_bound_temporary);
        }

        if (regime == ErrorRegime::relative_term_dominates) {
            ++counts.relative_term_references;
        } else if (regime == ErrorRegime::absolute_term_dominates) {
            ++counts.absolute_term_references;
        } else {
            ++counts.zero_bound_references;
        }

        if (regime == ErrorRegime::relative_term_dominates) {
            if (mpfr_zero_p(magnitude)) std::abort();
            mpfr_div(metric, dd_error, magnitude, MPFR_RNDN);
            add_metric(dd_relative_error, metric, dd_error, reference_value,
                       dd_result, i, describe);
        } else if (regime == ErrorRegime::absolute_term_dominates) {
            add_metric(dd_absolute_error, dd_error, dd_error,
                       reference_value, dd_result, i, describe);
        }
        add_bound_utilization(regime, dd_result, dd_error, i,
                              dd_relative_bound, dd_absolute_bound,
                              counts.dd_lib);

        ResultPair qd_result = qd(i);
        if (!std::isfinite(qd_result.hi) || !std::isfinite(qd_result.lo)) {
            ++counts.qd_nonfinite;
            if (regime == ErrorRegime::relative_term_dominates) {
                ++counts.qd_nonfinite_relative_term;
            } else if (regime == ErrorRegime::absolute_term_dominates) {
                ++counts.qd_nonfinite_absolute_term;
            } else {
                ++counts.qd_nonfinite_zero_bound;
            }
            set_nonfinite_witness(counts.first_qd_nonfinite, i, qd_result,
                                  reference_value, describe);
            continue;
        }

        set_pair_value(qd_value, qd_result, scratch);
        if (!valid_double_word_mpfr(qd_result, qd_value, scratch)) {
            ++counts.qd_invalid_double_word;
            set_contract_witness(counts.first_qd_invalid_double_word, i,
                                 qd_result, reference_value, describe);
        }
        mpfr_sub(qd_error, qd_value, reference_value, MPFR_RNDN);
        mpfr_abs(qd_error, qd_error, MPFR_RNDN);
        if (regime == ErrorRegime::relative_term_dominates) {
            mpfr_div(metric, qd_error, magnitude, MPFR_RNDN);
            add_metric(qd_relative_error, metric, qd_error, reference_value,
                       qd_result, i, describe);
        } else if (regime == ErrorRegime::absolute_term_dominates) {
            add_metric(qd_absolute_error, qd_error, qd_error,
                       reference_value, qd_result, i, describe);
        }
        add_bound_utilization(regime, qd_result, qd_error, i,
                              qd_relative_bound, qd_absolute_bound,
                              counts.qd);
    }

    counts.dd_lib.relative_term_relative =
        dd_relative_error.finish(u_squared, true);
    counts.dd_lib.relative_term_bound_utilization =
        dd_relative_bound.finish(eta, false);
    counts.dd_lib.absolute_term_absolute =
        dd_absolute_error.finish(eta, true);
    counts.dd_lib.absolute_term_bound_utilization =
        dd_absolute_bound.finish(eta, false);
    counts.qd.relative_term_relative =
        qd_relative_error.finish(u_squared, true);
    counts.qd.relative_term_bound_utilization =
        qd_relative_bound.finish(eta, false);
    counts.qd.absolute_term_absolute =
        qd_absolute_error.finish(eta, true);
    counts.qd.absolute_term_bound_utilization =
        qd_absolute_bound.finish(eta, false);

    std::size_t regime_total = counts.relative_term_references
        + counts.absolute_term_references + counts.zero_bound_references;
    std::size_t qd_nonfinite_total = counts.qd_nonfinite_relative_term
        + counts.qd_nonfinite_absolute_term
        + counts.qd_nonfinite_zero_bound;
    bool regime_counts_match =
        counts.dd_lib.relative_term_relative.count
            == counts.relative_term_references
        && counts.dd_lib.relative_term_bound_utilization.count
            == counts.relative_term_references
        && counts.qd.relative_term_relative.count
                + counts.qd_nonfinite_relative_term
            == counts.relative_term_references
        && counts.qd.relative_term_bound_utilization.count
                + counts.qd_nonfinite_relative_term
            == counts.relative_term_references
        && counts.dd_lib.absolute_term_absolute.count
            == counts.absolute_term_references
        && counts.dd_lib.absolute_term_bound_utilization.count
            == counts.absolute_term_references
        && counts.qd.absolute_term_absolute.count
                + counts.qd_nonfinite_absolute_term
            == counts.absolute_term_references
        && counts.qd.absolute_term_bound_utilization.count
                + counts.qd_nonfinite_absolute_term
            == counts.absolute_term_references;
    bool zero_bound_counts_match =
        counts.dd_lib.zero_bound_nonzero_error
            <= counts.zero_bound_references
        && counts.qd_nonfinite_zero_bound <= counts.zero_bound_references
        && counts.qd.zero_bound_nonzero_error
            <= counts.zero_bound_references
                 - counts.qd_nonfinite_zero_bound;
    const std::size_t finite_qd = counts.qd_nonfinite <= counts.compared
        ? counts.compared - counts.qd_nonfinite : 0;
    const std::size_t finite_bound_comparisons =
        counts.dd_lib.relative_term_bound_utilization.count
        + counts.dd_lib.absolute_term_bound_utilization.count
        + counts.qd.relative_term_bound_utilization.count
        + counts.qd.absolute_term_bound_utilization.count;
    bool witness_counts_match =
        (counts.dd_lib_invalid_double_word == 0)
            == (counts.first_dd_lib_invalid_double_word.case_index == SIZE_MAX)
        && (counts.qd_invalid_double_word == 0)
            == (counts.first_qd_invalid_double_word.case_index == SIZE_MAX)
        && (counts.qd_nonfinite == 0)
            == (counts.first_qd_nonfinite.case_index == SIZE_MAX)
        && (counts.dd_lib.zero_bound_nonzero_error == 0)
            == (counts.dd_lib.first_zero_bound_nonzero_error.case_index
                == SIZE_MAX)
        && (counts.qd.zero_bound_nonzero_error == 0)
            == (counts.qd.first_zero_bound_nonzero_error.case_index
                == SIZE_MAX);
    bool above_counts_match =
        counts.dd_lib.relative_term_bound_ratio_above_one
            <= counts.dd_lib.relative_term_bound_utilization.count
        && counts.dd_lib.absolute_term_bound_ratio_above_one
            <= counts.dd_lib.absolute_term_bound_utilization.count
        && counts.qd.relative_term_bound_ratio_above_one
            <= counts.qd.relative_term_bound_utilization.count
        && counts.qd.absolute_term_bound_ratio_above_one
            <= counts.qd.absolute_term_bound_utilization.count;
    auto violation_count_matches = [](const ImplementationMetrics &metrics) {
        return metrics.bound_violations.size()
            == metrics.relative_term_bound_ratio_above_one
                + metrics.absolute_term_bound_ratio_above_one
                + metrics.zero_bound_nonzero_error;
    };
    if (regime_total != counts.compared
        || counts.qd_nonfinite > counts.compared
        || counts.dd_lib_invalid_double_word > counts.compared
        || counts.qd_invalid_double_word > finite_qd
        || qd_nonfinite_total != counts.qd_nonfinite
        || !regime_counts_match || !zero_bound_counts_match
        || !witness_counts_match || !above_counts_match
        || !violation_count_matches(counts.dd_lib)
        || !violation_count_matches(counts.qd)
        || counts.higher_precision_bound_decision_changes
            > counts.higher_precision_bound_rechecks
        || counts.higher_precision_bound_rechecks
            > finite_bound_comparisons
        || (!options.division_reference
            && (counts.higher_precision_bound_rechecks != 0
                || counts.higher_precision_bound_decision_changes != 0))) {
        std::abort();
    }

    mpfr_clears(dd_value, qd_value, reference_value, temporary0, temporary1,
                scratch, dd_error, qd_error, magnitude, metric, eta, u,
                u_squared, relative_term, absolute_term, bound,
                bound_temporary, (mpfr_ptr)0);
    mpfr_clears(screening_value, screening_reference, screening_temporary0,
                screening_temporary1, screening_scratch, screening_error,
                screening_magnitude, screening_eta, screening_u,
                screening_u_squared, screening_relative_term,
                screening_absolute_term, screening_bound,
                screening_bound_temporary, (mpfr_ptr)0);
    return counts;
}

}  // namespace bench_eval
