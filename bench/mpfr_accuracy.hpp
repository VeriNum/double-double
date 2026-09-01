#ifndef BENCH_MPFR_ACCURACY_HPP
#define BENCH_MPFR_ACCURACY_HPP

#include <mpfr.h>

#include <cstddef>
#include <functional>
#include <string>
#include <vector>

#include "evaluation_types.hpp"
#include "interface_runner.hpp"

namespace bench_eval {

enum class VerifiedBound {
    none,
    dw_plus_fp,
    dw_plus_dw,
    dw_times_fp,
    dw_times_dw,
    dw_div_fp,
    dw_div_dw
};

enum class ErrorRegime {
    relative_term_dominates,
    absolute_term_dominates,
    zero_bound_reference
};

struct ErrorWitness {
    std::size_t case_index = SIZE_MAX;
    ResultPair result{0.0, 0.0};
    std::string reference;
    std::string absolute_error;
    std::string inputs;
};

struct ContractWitness {
    std::size_t case_index = SIZE_MAX;
    ResultPair result{0.0, 0.0};
    std::string reference;
    std::string inputs;
};

struct MetricSummary {
    std::size_t count = 0;
    std::string maximum = "n/a";
    std::string mean = "n/a";
    std::string maximum_scaled = "n/a";
    std::string mean_scaled = "n/a";
    bool maximum_nonzero = false;
    ErrorWitness witness;
};

struct BoundViolation {
    ErrorRegime regime = ErrorRegime::relative_term_dominates;
    ErrorWitness witness;
};

struct ImplementationMetrics {
    MetricSummary relative_term_relative;
    MetricSummary relative_term_bound_utilization;
    std::size_t relative_term_bound_ratio_above_one = 0;
    MetricSummary absolute_term_absolute;
    MetricSummary absolute_term_bound_utilization;
    std::size_t absolute_term_bound_ratio_above_one = 0;
    std::size_t zero_bound_nonzero_error = 0;
    ErrorWitness first_zero_bound_nonzero_error;
    std::vector<BoundViolation> bound_violations;
};

struct AccuracyCounts {
    std::size_t compared = 0;
    std::size_t qd_nonfinite = 0;

    std::size_t relative_term_references = 0;
    std::size_t absolute_term_references = 0;
    std::size_t zero_bound_references = 0;
    std::size_t qd_nonfinite_relative_term = 0;
    std::size_t qd_nonfinite_absolute_term = 0;
    std::size_t qd_nonfinite_zero_bound = 0;

    std::size_t dd_lib_invalid_double_word = 0;
    std::size_t qd_invalid_double_word = 0;

    ContractWitness first_dd_lib_invalid_double_word;
    ContractWitness first_qd_invalid_double_word;
    ErrorWitness first_qd_nonfinite;

    ImplementationMetrics dd_lib;
    ImplementationMetrics qd;

    std::size_t higher_precision_bound_rechecks = 0;
    std::size_t higher_precision_bound_decision_changes = 0;
};

struct AccuracyOptions {
    VerifiedBound bound_kind = VerifiedBound::none;
    bool division_reference = false;
};

using QdEvaluator = std::function<ResultPair(std::size_t)>;
using ReferenceEvaluator = std::function<void(
    std::size_t, mpfr_ptr, mpfr_ptr, mpfr_ptr, mpfr_ptr)>;
using CaseDescriber = std::function<std::string(std::size_t)>;

void set_pair_value(mpfr_ptr value, const ResultPair &pair,
                    mpfr_ptr scratch);
void set_dword_value(mpfr_ptr value, const dword &word,
                     mpfr_ptr scratch);
std::string format_mpfr(mpfr_srcptr value);

bool valid_double_word_mpfr(const ResultPair &result,
                            mpfr_ptr represented,
                            mpfr_ptr scratch);
bool reconstructs_reference_mpfr(const ResultPair &result,
                                 mpfr_srcptr reference,
                                 mpfr_ptr represented,
                                 mpfr_ptr scratch);

void verify_error_regime_classifier();

bool compute_verified_bound(mpfr_ptr relative_term,
                            mpfr_ptr absolute_term,
                            mpfr_ptr bound,
                            VerifiedBound kind,
                            mpfr_srcptr reference);

int compare_pair_error_to_verified_bound(
    const ResultPair &result,
    mpfr_srcptr reference,
    VerifiedBound kind,
    mpfr_ptr represented,
    mpfr_ptr absolute_error,
    mpfr_ptr relative_term,
    mpfr_ptr absolute_term,
    mpfr_ptr bound,
    mpfr_ptr scratch);

AccuracyCounts measure_accuracy(const CollectedResults &results,
                                const QdEvaluator &qd,
                                const ReferenceEvaluator &reference,
                                const CaseDescriber &describe,
                                const AccuracyOptions &options);

}  // namespace bench_eval

#endif  // BENCH_MPFR_ACCURACY_HPP
