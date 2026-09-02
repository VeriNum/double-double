// RQ2 evaluates QD on inputs rejected by the checked dd_lib interfaces.

#include <mpfr.h>

#include "boundary_cases.hpp"
#include "input_generation.hpp"
#include "interface_runner.hpp"
#include "mpfr_accuracy.hpp"
#include "operation_metadata.hpp"
#include "qd_evaluation.hpp"

extern "C" {
#include "dw_arith.h"
#include "fp_utils.h"
}

#include <cerrno>
#include <cfenv>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <limits>
#include <string>
#include <utility>
#include <vector>

namespace {

using bench_eval::BoundaryOutcome;
using bench_eval::CallOutcome;
using bench_eval::CollectedResults;
using bench_eval::CompositeOperation;
using bench_eval::ResultPair;
using bench_eval::VerifiedBound;
using bench_eval::first_high_limit;
using bench_eval::leading_product_limit;
using bench_eval::leading_quotient_limit;
using bench_eval::nonzero_divisor;
using bench_eval::second_high_limit;

constexpr mpfr_prec_t oracle_precision =
    static_cast<mpfr_prec_t>(bench_eval::reference_precision);
constexpr mpfr_prec_t division_precision = 2 * oracle_precision;

struct FailureCounts {
    std::size_t first_high = 0;
    std::size_t second_high = 0;
    std::size_t product = 0;
    std::size_t nonzero_divisor = 0;
    std::size_t quotient = 0;
};

struct QdAssessment {
    bool evaluated = false;
    ResultPair result{0.0, 0.0};
    bool finite = false;
    bool valid_dw = false;
    bool within_bound = false;
    bool exact_reconstruction = false;
    std::string reference = "-";
    std::string absolute_error = "-";
    std::string bound = "-";
};

struct DwQdCounts {
    std::size_t rejected = 0;
    std::size_t nonfinite = 0;
    std::size_t finite_invalid_dw = 0;
    std::size_t finite_valid_above_bound = 0;
    std::size_t finite_valid_within_bound = 0;
};

struct EftQdCounts {
    std::size_t rejected = 0;
    std::size_t nonfinite = 0;
    std::size_t finite_invalid_dw = 0;
    std::size_t finite_valid_failed_reconstruction = 0;
    std::size_t finite_valid_exact_reconstruction = 0;
};

struct GuardReport {
    CompositeOperation operation;
    std::size_t generated = 0;
    std::size_t both_return = 0;
    std::size_t default_only = 0;
    std::size_t strong_only = 0;
    std::size_t neither_default_input = 0;
    std::size_t neither_default_post = 0;
    std::size_t unequal_shared_results = 0;
    FailureCounts failures;
    DwQdCounts default_rejected;
    DwQdCounts strong_rejected;
};

struct EftReport {
    const char *operation;
    std::size_t generated = 0;
    std::size_t returned_normally = 0;
    EftQdCounts rejected;
};

struct TsvRow {
    std::string suite = "-";
    std::string operation = "-";
    std::string case_id = "-";
    std::string first_exponent = "-";
    std::string second_exponent = "-";
    std::string default_outcome = "-";
    std::string strong_outcome = "-";
    std::string failure_mask = "-";
    std::string failed_additional_conditions = "-";
    std::string checked_exponents = "-";
    std::string case_name = "-";
    std::string inputs = "-";
    std::string shared_result_equal = "-";
    std::string qd_result_hi_bits = "-";
    std::string qd_result_lo_bits = "-";
    std::string qd_finite = "not_evaluated";
    std::string qd_valid_dw = "not_evaluated";
    std::string qd_within_bound = "not_evaluated";
    std::string qd_exact_reconstruction = "not_evaluated";
    std::string reference = "-";
    std::string absolute_error = "-";
    std::string bound = "-";
    std::string expected_default_outcome = "-";
    std::string expected_strong_outcome = "-";
    std::string expected_failure_mask = "-";
    std::string assertion_passed = "-";
};

const char *outcome_name(CallOutcome outcome) {
    switch (outcome) {
    case CallOutcome::input_check_termination:
        return "input_check";
    case CallOutcome::post_computation_termination:
        return "post_compute";
    case CallOutcome::returned_normally:
        return "normal";
    case CallOutcome::pending:
        return "pending";
    }
    return "unknown";
}

std::string failure_names(std::uint32_t mask) {
    if (mask == 0) return "-";
    std::string result;
    auto add = [&](std::uint32_t bit, const char *name) {
        if ((mask & bit) == 0) return;
        if (!result.empty()) result += ',';
        result += name;
    };
    add(first_high_limit, "first_high_limit");
    add(second_high_limit, "second_high_limit");
    add(leading_product_limit, "leading_product_limit");
    add(nonzero_divisor, "nonzero_divisor");
    add(leading_quotient_limit, "leading_quotient_limit");
    return result;
}

void add_failure_counts(FailureCounts &counts, std::uint32_t mask) {
    if (mask & first_high_limit) ++counts.first_high;
    if (mask & second_high_limit) ++counts.second_high;
    if (mask & leading_product_limit) ++counts.product;
    if (mask & nonzero_divisor) ++counts.nonzero_divisor;
    if (mask & leading_quotient_limit) ++counts.quotient;
}

bool same_result(const ResultPair &first, const ResultPair &second) {
    return bench_eval::bits_of(first.hi) == bench_eval::bits_of(second.hi)
        && bench_eval::bits_of(first.lo) == bench_eval::bits_of(second.lo);
}

std::string bits_text(double value) {
    char text[19];
    std::snprintf(text, sizeof(text), "0x%016llx",
        static_cast<unsigned long long>(bench_eval::bits_of(value)));
    return text;
}

std::string mask_text(std::uint32_t mask) {
    char text[5];
    std::snprintf(text, sizeof(text), "0x%02x",
                  static_cast<unsigned>(mask));
    return text;
}

std::string exponent_text(double value) {
    if (value == 0.0) return "zero";
    if (!std::isfinite(value)) return "nonfinite";
    return std::to_string(std::ilogb(std::fabs(value)));
}

std::string dw_fp_checked_exponents(CompositeOperation operation,
                                    const dword &first, double second) {
    switch (operation) {
    case CompositeOperation::dw_plus_fp:
        return "first_high=" + exponent_text(first.s)
            + ",second_high=" + exponent_text(second);
    case CompositeOperation::dw_times_fp:
        return "leading_product=" + exponent_text(first.s * second);
    case CompositeOperation::dw_div_fp: {
        const double high_limit = std::ldexp(1.0, 1022);
        const double low_limit = std::ldexp(1.0, -968);
        bool valid_dw = std::isfinite(first.s) && std::isfinite(first.t)
            && first.s + first.t == first.s;
        bool ready = valid_dw && std::isfinite(second)
            && std::fabs(first.s) <= high_limit
            && (first.s == 0.0 || low_limit <= std::fabs(first.s))
            && second != 0.0;
        return "first_high=" + exponent_text(first.s)
            + ",leading_quotient="
            + (ready ? exponent_text(first.s / second)
                     : "not_evaluated");
    }
    case CompositeOperation::dw_plus_dw:
    case CompositeOperation::dw_times_dw:
    case CompositeOperation::dw_div_dw:
        std::abort();
    }
    std::abort();
}

std::string dw_dw_checked_exponents(CompositeOperation operation,
                                    const dword &first,
                                    const dword &second) {
    switch (operation) {
    case CompositeOperation::dw_plus_dw:
        return "first_high=" + exponent_text(first.s)
            + ",second_high=" + exponent_text(second.s);
    case CompositeOperation::dw_times_dw:
        return "leading_product=" + exponent_text(first.s * second.s);
    case CompositeOperation::dw_div_dw:
        return "leading_quotient="
            + (dw_div_dw_weak_precond_check(&first, &second)
                   ? exponent_text(first.s / second.s)
                   : "not_evaluated");
    case CompositeOperation::dw_plus_fp:
    case CompositeOperation::dw_times_fp:
    case CompositeOperation::dw_div_fp:
        std::abort();
    }
    std::abort();
}

void write_header(std::FILE *file) {
    std::fprintf(file,
        "suite\toperation\tcase_id\tfirst_exponent\tsecond_exponent"
        "\tdefault_outcome\tstrong_outcome\tfailure_mask"
        "\tfailed_additional_conditions\tchecked_exponents\tcase_name"
        "\tinputs\tshared_result_equal\tqd_result_hi_bits"
        "\tqd_result_lo_bits\tqd_finite\tqd_valid_dw\tqd_within_bound"
        "\tqd_exact_reconstruction\treference\tabsolute_error\tbound"
        "\texpected_default_outcome\texpected_strong_outcome"
        "\texpected_failure_mask\tassertion_passed\n");
}

void write_row(std::FILE *file, const TsvRow &row,
               std::size_t &data_rows) {
    if (file == nullptr) return;
    std::fprintf(file,
        "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s"
        "\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n",
        row.suite.c_str(), row.operation.c_str(), row.case_id.c_str(),
        row.first_exponent.c_str(), row.second_exponent.c_str(),
        row.default_outcome.c_str(), row.strong_outcome.c_str(),
        row.failure_mask.c_str(),
        row.failed_additional_conditions.c_str(),
        row.checked_exponents.c_str(), row.case_name.c_str(),
        row.inputs.c_str(), row.shared_result_equal.c_str(),
        row.qd_result_hi_bits.c_str(), row.qd_result_lo_bits.c_str(),
        row.qd_finite.c_str(), row.qd_valid_dw.c_str(),
        row.qd_within_bound.c_str(),
        row.qd_exact_reconstruction.c_str(), row.reference.c_str(),
        row.absolute_error.c_str(), row.bound.c_str(),
        row.expected_default_outcome.c_str(),
        row.expected_strong_outcome.c_str(),
        row.expected_failure_mask.c_str(), row.assertion_passed.c_str());
    ++data_rows;
}

template <class Qd, class Reference>
QdAssessment assess_qd(std::size_t case_index, Qd qd,
                       Reference reference, VerifiedBound bound_kind,
                       bool exact_transform, bool division_reference) {
    QdAssessment assessment;
    assessment.evaluated = true;
    assessment.result = qd(case_index);
    assessment.finite = std::isfinite(assessment.result.hi)
        && std::isfinite(assessment.result.lo);

    mpfr_prec_t precision = division_reference
        ? division_precision : oracle_precision;
    mpfr_t represented;
    mpfr_t reference_value;
    mpfr_t first;
    mpfr_t second;
    mpfr_t scratch;
    mpfr_t absolute_error;
    mpfr_t relative_term;
    mpfr_t absolute_term;
    mpfr_t bound;
    mpfr_inits2(precision, represented, reference_value, first, second,
                scratch, absolute_error, relative_term, absolute_term,
                bound, (mpfr_ptr)0);

    reference(case_index, reference_value, first, second, scratch);
    if (!mpfr_number_p(reference_value)) {
        std::fprintf(stderr, "nonfinite MPFR reference at case %zu\n",
                     case_index);
        std::abort();
    }
    assessment.reference = bench_eval::format_mpfr(reference_value);

    if (!exact_transform) {
        bench_eval::compute_verified_bound(
            relative_term, absolute_term, bound, bound_kind,
            reference_value);
        assessment.bound = bench_eval::format_mpfr(bound);
    }

    if (assessment.finite) {
        assessment.valid_dw = bench_eval::valid_double_word_mpfr(
            assessment.result, represented, scratch);
        bench_eval::set_pair_value(represented, assessment.result, scratch);
        mpfr_sub(absolute_error, represented, reference_value, MPFR_RNDN);
        mpfr_abs(absolute_error, absolute_error, MPFR_RNDN);
        assessment.absolute_error =
            bench_eval::format_mpfr(absolute_error);

        if (exact_transform) {
            assessment.exact_reconstruction =
                bench_eval::reconstructs_reference_mpfr(
                    assessment.result, reference_value, represented,
                    scratch);
        } else {
            int comparison =
                bench_eval::compare_pair_error_to_verified_bound(
                    assessment.result, reference_value, bound_kind,
                    represented, absolute_error, relative_term,
                    absolute_term, bound, scratch);
            assessment.within_bound = comparison <= 0;
            assessment.absolute_error =
                bench_eval::format_mpfr(absolute_error);
            assessment.bound = bench_eval::format_mpfr(bound);
        }
    } else {
        assessment.absolute_error = "inf";
    }

    mpfr_clears(represented, reference_value, first, second, scratch,
                absolute_error, relative_term, absolute_term, bound,
                (mpfr_ptr)0);
    return assessment;
}

void add_assessment(DwQdCounts &counts,
                    const QdAssessment &assessment) {
    ++counts.rejected;
    if (!assessment.finite) {
        ++counts.nonfinite;
    } else if (!assessment.valid_dw) {
        ++counts.finite_invalid_dw;
    } else if (!assessment.within_bound) {
        ++counts.finite_valid_above_bound;
    } else {
        ++counts.finite_valid_within_bound;
    }
}

void add_assessment(EftQdCounts &counts,
                    const QdAssessment &assessment) {
    ++counts.rejected;
    if (!assessment.finite) {
        ++counts.nonfinite;
    } else if (!assessment.valid_dw) {
        ++counts.finite_invalid_dw;
    } else if (!assessment.exact_reconstruction) {
        ++counts.finite_valid_failed_reconstruction;
    } else {
        ++counts.finite_valid_exact_reconstruction;
    }
}

void add_assessment_fields(TsvRow &row,
                           const QdAssessment &assessment,
                           bool exact_transform) {
    if (!assessment.evaluated) return;
    row.qd_result_hi_bits = bits_text(assessment.result.hi);
    row.qd_result_lo_bits = bits_text(assessment.result.lo);
    row.qd_finite = assessment.finite ? "yes" : "no";
    row.qd_valid_dw = assessment.valid_dw ? "yes" : "no";
    row.reference = assessment.reference;
    row.absolute_error = assessment.absolute_error;
    row.bound = assessment.bound;
    if (!assessment.finite) {
        row.qd_within_bound = "not_applicable";
        row.qd_exact_reconstruction = "not_applicable";
    } else if (exact_transform) {
        row.qd_within_bound = "not_applicable";
        row.qd_exact_reconstruction =
            assessment.exact_reconstruction ? "yes" : "no";
    } else {
        row.qd_within_bound = assessment.within_bound ? "yes" : "no";
        row.qd_exact_reconstruction = "not_applicable";
    }
}

void validate_counts(const DwQdCounts &counts) {
    if (counts.nonfinite + counts.finite_invalid_dw
            + counts.finite_valid_above_bound
            + counts.finite_valid_within_bound
        != counts.rejected) {
        std::abort();
    }
}

void validate_counts(const EftQdCounts &counts) {
    if (counts.nonfinite + counts.finite_invalid_dw
            + counts.finite_valid_failed_reconstruction
            + counts.finite_valid_exact_reconstruction
        != counts.rejected) {
        std::abort();
    }
}

std::uint32_t dw_fp_strong_failures(CompositeOperation operation,
                                    const dword &first, double second) {
    const double high_limit = std::ldexp(1.0, 1022);
    const double product_limit = std::ldexp(1.0, 1023);
    std::uint32_t failures = 0;

    switch (operation) {
    case CompositeOperation::dw_plus_fp:
        if (!(std::fabs(first.s) <= high_limit))
            failures |= first_high_limit;
        if (!(std::fabs(second) <= high_limit))
            failures |= second_high_limit;
        break;
    case CompositeOperation::dw_times_fp:
        if (!(std::fabs(first.s * second) < product_limit))
            failures |= leading_product_limit;
        break;
    case CompositeOperation::dw_div_fp:
        if (!(std::fabs(first.s) <= high_limit))
            failures |= first_high_limit;
        if (second == 0.0) {
            failures |= nonzero_divisor;
        } else if (!(std::fabs(first.s / second) < high_limit)) {
            failures |= leading_quotient_limit;
        }
        break;
    case CompositeOperation::dw_plus_dw:
    case CompositeOperation::dw_times_dw:
    case CompositeOperation::dw_div_dw:
        std::abort();
    }
    return failures;
}

std::uint32_t dw_dw_strong_failures(CompositeOperation operation,
                                    const dword &first,
                                    const dword &second) {
    const double high_limit = std::ldexp(1.0, 1022);
    const double product_limit = std::ldexp(1.0, 1023);
    std::uint32_t failures = 0;

    switch (operation) {
    case CompositeOperation::dw_plus_dw:
        if (!(std::fabs(first.s) <= high_limit))
            failures |= first_high_limit;
        if (!(std::fabs(second.s) <= high_limit))
            failures |= second_high_limit;
        break;
    case CompositeOperation::dw_times_dw:
        if (!(std::fabs(first.s * second.s) < product_limit))
            failures |= leading_product_limit;
        break;
    case CompositeOperation::dw_div_dw:
        if (!(std::fabs(first.s / second.s) < high_limit))
            failures |= leading_quotient_limit;
        break;
    case CompositeOperation::dw_plus_fp:
    case CompositeOperation::dw_times_fp:
    case CompositeOperation::dw_div_fp:
        std::abort();
    }
    return failures;
}

template <class FailureMask, class Exponents, class CheckedExponents,
          class Describe, class Qd, class Reference>
GuardReport summarize_operation(
        CompositeOperation operation, VerifiedBound bound_kind,
        bool division_reference,
        const CollectedResults &default_results,
        const CollectedResults &strong_results,
        FailureMask failure_mask, Exponents exponents,
        CheckedExponents checked_exponents, Describe describe,
        Qd qd, Reference reference,
        std::FILE *case_file, std::size_t &data_rows) {
    if (default_results.outcomes.size() != strong_results.outcomes.size())
        std::abort();

    GuardReport report;
    report.operation = operation;
    report.generated = default_results.outcomes.size();

    for (std::size_t i = 0; i < report.generated; ++i) {
        CallOutcome default_outcome = default_results.outcomes[i];
        CallOutcome strong_outcome = strong_results.outcomes[i];
        bool default_return =
            default_outcome == CallOutcome::returned_normally;
        bool strong_return =
            strong_outcome == CallOutcome::returned_normally;
        std::uint32_t failures = failure_mask(i);

        if (default_return && strong_return) {
            ++report.both_return;
            if (!same_result(default_results.values[i],
                             strong_results.values[i])) {
                ++report.unequal_shared_results;
            }
            if (failures != 0) {
                std::fprintf(stderr,
                    "%s case %zu passed the strong interface but its "
                    "diagnostic mask reports a failed condition\n",
                    bench_eval::operation_name(operation), i);
                std::abort();
            }
        } else if (default_return) {
            ++report.default_only;
            add_failure_counts(report.failures, failures);
            if (failures == 0) {
                std::fprintf(stderr,
                    "%s default-only case %zu has no failed strong "
                    "condition\n",
                    bench_eval::operation_name(operation), i);
                std::abort();
            }
        } else if (strong_return) {
            ++report.strong_only;
        } else if (default_outcome
                   == CallOutcome::input_check_termination) {
            ++report.neither_default_input;
        } else if (default_outcome
                   == CallOutcome::post_computation_termination) {
            ++report.neither_default_post;
        } else {
            std::abort();
        }

        QdAssessment assessment;
        if (!default_return || !strong_return) {
            assessment = assess_qd(i, qd, reference, bound_kind, false,
                                   division_reference);
            if (!default_return)
                add_assessment(report.default_rejected, assessment);
            if (!strong_return)
                add_assessment(report.strong_rejected, assessment);
        }

        TsvRow row;
        row.suite = "log_stratified";
        row.operation = bench_eval::operation_name(operation);
        row.case_id = std::to_string(i);
        std::pair<int, int> exponent_pair = exponents(i);
        row.first_exponent = std::to_string(exponent_pair.first);
        row.second_exponent = std::to_string(exponent_pair.second);
        row.default_outcome = outcome_name(default_outcome);
        row.strong_outcome = outcome_name(strong_outcome);
        row.failure_mask = mask_text(failures);
        row.failed_additional_conditions = failure_names(failures);
        row.checked_exponents = checked_exponents(i);
        row.inputs = describe(i);
        row.shared_result_equal = default_return && strong_return
            ? "yes" : "not_applicable";
        add_assessment_fields(row, assessment, false);
        write_row(case_file, row, data_rows);
    }

    std::size_t partition = report.both_return + report.default_only
        + report.strong_only + report.neither_default_input
        + report.neither_default_post;
    if (partition != report.generated || report.strong_only != 0
        || report.unequal_shared_results != 0) {
        std::fprintf(stderr, "%s guard partition or shared result failed\n",
                     bench_eval::operation_name(operation));
        std::abort();
    }
    validate_counts(report.default_rejected);
    validate_counts(report.strong_rejected);
    if (report.default_rejected.rejected
            != report.neither_default_input + report.neither_default_post
        || report.strong_rejected.rejected
            != report.default_only + report.neither_default_input
                + report.neither_default_post) {
        std::abort();
    }
    return report;
}

template <class Qd, class Reference, class Exponents, class Describe>
EftReport summarize_eft(const char *operation,
                        const CollectedResults &results,
                        Qd qd, Reference reference,
                        Exponents exponents, Describe describe,
                        std::FILE *case_file, std::size_t &data_rows) {
    EftReport report;
    report.operation = operation;
    report.generated = results.outcomes.size();

    for (std::size_t i = 0; i < report.generated; ++i) {
        CallOutcome outcome = results.outcomes[i];
        bool returned = outcome == CallOutcome::returned_normally;
        if (returned) {
            ++report.returned_normally;
        } else if (outcome != CallOutcome::input_check_termination) {
            std::abort();
        }

        QdAssessment assessment;
        if (!returned) {
            assessment = assess_qd(
                i, qd, reference, VerifiedBound::none, true, false);
            add_assessment(report.rejected, assessment);
        }

        TsvRow row;
        row.suite = "log_stratified";
        row.operation = operation;
        row.case_id = std::to_string(i);
        std::pair<int, int> exponent_pair = exponents(i);
        row.first_exponent = std::to_string(exponent_pair.first);
        row.second_exponent = std::to_string(exponent_pair.second);
        row.default_outcome = outcome_name(outcome);
        row.strong_outcome = "not_applicable";
        row.failure_mask = "not_applicable";
        row.failed_additional_conditions = "not_applicable";
        row.checked_exponents = "not_applicable";
        row.inputs = describe(i);
        row.shared_result_equal = "not_applicable";
        add_assessment_fields(row, assessment, true);
        write_row(case_file, row, data_rows);
    }

    validate_counts(report.rejected);
    if (report.returned_normally + report.rejected.rejected
        != report.generated) {
        std::abort();
    }
    return report;
}

void print_dw_counts(const GuardReport &report, const char *wrapper,
                     const DwQdCounts &counts) {
    std::printf("  %-18s %-8s %9zu %10zu %14zu %12zu %13zu\n",
                bench_eval::operation_name(report.operation), wrapper,
                counts.rejected, counts.nonfinite,
                counts.finite_invalid_dw,
                counts.finite_valid_above_bound,
                counts.finite_valid_within_bound);
}

void print_eft_counts(const EftReport &report) {
    const EftQdCounts &counts = report.rejected;
    std::printf("  %-18s %9zu %10zu %14zu %17zu %18zu\n",
                report.operation, counts.rejected, counts.nonfinite,
                counts.finite_invalid_dw,
                counts.finite_valid_failed_reconstruction,
                counts.finite_valid_exact_reconstruction);
}

void print_reports(const std::vector<GuardReport> &dw_reports,
                   const std::vector<EftReport> &eft_reports) {
    std::printf("QD on test cases rejected by double-word wrappers\n");
    std::printf("  %-18s %-8s %9s %10s %14s %12s %13s\n",
                "operation", "wrapper", "rejected", "nonfinite",
                "finite_invalid", "valid_above", "valid_within");
    for (const GuardReport &report : dw_reports) {
        print_dw_counts(report, "default", report.default_rejected);
        print_dw_counts(report, "strong", report.strong_rejected);
    }

    std::printf("\nQD on test cases rejected by EFT wrappers\n");
    std::printf("  %-18s %9s %10s %14s %17s %18s\n",
                "operation", "rejected", "nonfinite", "finite_invalid",
                "valid_not_exact", "valid_exact");
    for (const EftReport &report : eft_reports)
        print_eft_counts(report);
    std::printf("\n");
}

int weak_check(const bench_eval::DwFpBoundaryCase &item) {
    switch (item.operation) {
    case CompositeOperation::dw_plus_fp:
        return dw_plus_fp_weak_precond_check(&item.first, item.second);
    case CompositeOperation::dw_times_fp:
        return dw_times_fp_weak_precond_check(&item.first, item.second);
    case CompositeOperation::dw_div_fp:
        return dw_div_fp_weak_check(&item.first, item.second);
    default:
        std::abort();
    }
}

int strong_check(const bench_eval::DwFpBoundaryCase &item) {
    switch (item.operation) {
    case CompositeOperation::dw_plus_fp:
        return dw_plus_fp_strong_precond_check(&item.first, item.second);
    case CompositeOperation::dw_times_fp:
        return dw_times_fp_strong_precond_check(&item.first, item.second);
    case CompositeOperation::dw_div_fp:
        return dw_div_fp_strong_check(&item.first, item.second);
    default:
        std::abort();
    }
}

ResultPair call_default(bench_eval::DwFpBoundaryCase &item) {
    dword result;
    switch (item.operation) {
    case CompositeOperation::dw_plus_fp:
        dw_plus_fp(&result, &item.first, item.second);
        break;
    case CompositeOperation::dw_times_fp:
        dw_times_fp(&result, &item.first, item.second);
        break;
    case CompositeOperation::dw_div_fp:
        dw_div_fp(&result, &item.first, item.second);
        break;
    default:
        std::abort();
    }
    return ResultPair{result.s, result.t};
}

ResultPair call_strong(bench_eval::DwFpBoundaryCase &item) {
    dword result;
    switch (item.operation) {
    case CompositeOperation::dw_plus_fp:
        dw_plus_fp_strong(&result, &item.first, item.second);
        break;
    case CompositeOperation::dw_times_fp:
        dw_times_fp_strong(&result, &item.first, item.second);
        break;
    case CompositeOperation::dw_div_fp:
        dw_div_fp_strong(&result, &item.first, item.second);
        break;
    default:
        std::abort();
    }
    return ResultPair{result.s, result.t};
}

int weak_check(const bench_eval::DwDwBoundaryCase &item) {
    switch (item.operation) {
    case CompositeOperation::dw_plus_dw:
        return dw_plus_dw_weak_precond_check(&item.first, &item.second);
    case CompositeOperation::dw_times_dw:
        return dw_times_dw_weak_precond_check(&item.first, &item.second);
    case CompositeOperation::dw_div_dw:
        return dw_div_dw_weak_precond_check(&item.first, &item.second);
    default:
        std::abort();
    }
}

int strong_check(const bench_eval::DwDwBoundaryCase &item) {
    switch (item.operation) {
    case CompositeOperation::dw_plus_dw:
        return dw_plus_dw_strong_precond_check(&item.first, &item.second);
    case CompositeOperation::dw_times_dw:
        return dw_times_dw_strong_precond_check(&item.first, &item.second);
    case CompositeOperation::dw_div_dw:
        return dw_div_dw_strong_precond_check(&item.first, &item.second);
    default:
        std::abort();
    }
}

ResultPair call_default(bench_eval::DwDwBoundaryCase &item) {
    dword result;
    switch (item.operation) {
    case CompositeOperation::dw_plus_dw:
        dw_plus_dw(&result, &item.first, &item.second);
        break;
    case CompositeOperation::dw_times_dw:
        dw_times_dw(&result, &item.first, &item.second);
        break;
    case CompositeOperation::dw_div_dw:
        dw_div_dw(&result, &item.first, &item.second);
        break;
    default:
        std::abort();
    }
    return ResultPair{result.s, result.t};
}

ResultPair call_strong(bench_eval::DwDwBoundaryCase &item) {
    dword result;
    switch (item.operation) {
    case CompositeOperation::dw_plus_dw:
        dw_plus_dw_strong(&result, &item.first, &item.second);
        break;
    case CompositeOperation::dw_times_dw:
        dw_times_dw_strong(&result, &item.first, &item.second);
        break;
    case CompositeOperation::dw_div_dw:
        dw_div_dw_strong(&result, &item.first, &item.second);
        break;
    default:
        std::abort();
    }
    return ResultPair{result.s, result.t};
}

CallOutcome as_call_outcome(BoundaryOutcome outcome) {
    switch (outcome) {
    case BoundaryOutcome::input_check:
        return CallOutcome::input_check_termination;
    case BoundaryOutcome::post_compute:
        return CallOutcome::post_computation_termination;
    case BoundaryOutcome::normal:
        return CallOutcome::returned_normally;
    }
    std::abort();
}

std::string boundary_inputs(const bench_eval::DwFpBoundaryCase &item) {
    char text[192];
    std::snprintf(text, sizeof(text),
        "x=(0x%016llx,0x%016llx) y=0x%016llx",
        static_cast<unsigned long long>(bench_eval::bits_of(item.first.s)),
        static_cast<unsigned long long>(bench_eval::bits_of(item.first.t)),
        static_cast<unsigned long long>(bench_eval::bits_of(item.second)));
    return text;
}

std::string boundary_inputs(const bench_eval::DwDwBoundaryCase &item) {
    char text[256];
    std::snprintf(text, sizeof(text),
        "x=(0x%016llx,0x%016llx) y=(0x%016llx,0x%016llx)",
        static_cast<unsigned long long>(bench_eval::bits_of(item.first.s)),
        static_cast<unsigned long long>(bench_eval::bits_of(item.first.t)),
        static_cast<unsigned long long>(bench_eval::bits_of(item.second.s)),
        static_cast<unsigned long long>(bench_eval::bits_of(item.second.t)));
    return text;
}

std::pair<std::string, std::string> boundary_exponents(
        const bench_eval::DwFpBoundaryCase &item) {
    return std::make_pair(exponent_text(item.first.s),
                          exponent_text(item.second));
}

std::pair<std::string, std::string> boundary_exponents(
        const bench_eval::DwDwBoundaryCase &item) {
    return std::make_pair(exponent_text(item.first.s),
                          exponent_text(item.second.s));
}

std::string boundary_checked_exponents(
        const bench_eval::DwFpBoundaryCase &item) {
    return dw_fp_checked_exponents(item.operation, item.first, item.second);
}

std::string boundary_checked_exponents(
        const bench_eval::DwDwBoundaryCase &item) {
    return dw_dw_checked_exponents(item.operation, item.first, item.second);
}

template <class Item, class FailureMask>
void print_boundary_case(Item &item, FailureMask failure_mask,
                         std::size_t case_index, std::FILE *case_file,
                         std::size_t &data_rows) {
    CollectedResults default_results = bench_eval::collect_interface_results(
        1, [&](std::size_t) { return weak_check(item); },
        [&](std::size_t) { return call_default(item); }, true,
        "default boundary interface");
    CollectedResults strong_results = bench_eval::collect_interface_results(
        1, [&](std::size_t) { return strong_check(item); },
        [&](std::size_t) { return call_strong(item); }, false,
        "strong boundary interface");
    bool weak_accepts = weak_check(item) != 0;
    std::uint32_t failures = weak_accepts ? failure_mask(item) : 0;
    CallOutcome default_outcome = default_results.outcomes[0];
    CallOutcome strong_outcome = strong_results.outcomes[0];
    bool strong_accepts = strong_check(item) != 0;
    bool diagnostic_accepts = weak_accepts && failures == 0;
    if (strong_accepts != diagnostic_accepts) {
        std::fprintf(stderr,
            "boundary case %s has an inconsistent strong-condition mask\n",
            item.name.c_str());
        std::abort();
    }
    if (default_outcome != as_call_outcome(item.expected_default)
        || strong_outcome != as_call_outcome(item.expected_strong)
        || failures != item.expected_additional_failures) {
        std::fprintf(stderr,
            "boundary case %s did not have its expected outcome\n",
            item.name.c_str());
        std::abort();
    }
    if (default_outcome == CallOutcome::returned_normally
        && strong_outcome == CallOutcome::returned_normally
        && !same_result(default_results.values[0],
                        strong_results.values[0])) {
        std::fprintf(stderr, "boundary case %s returned unequal results\n",
                     item.name.c_str());
        std::abort();
    }

    std::printf("  %-18s %-48s %-12s %-12s %-32s\n",
                bench_eval::operation_name(item.operation), item.name.c_str(),
                outcome_name(default_outcome), outcome_name(strong_outcome),
                failure_names(failures).c_str());

    TsvRow row;
    row.suite = "boundary";
    row.operation = bench_eval::operation_name(item.operation);
    row.case_id = std::to_string(case_index);
    std::pair<std::string, std::string> exponents =
        boundary_exponents(item);
    row.first_exponent = exponents.first;
    row.second_exponent = exponents.second;
    row.default_outcome = outcome_name(default_outcome);
    row.strong_outcome = outcome_name(strong_outcome);
    row.failure_mask = mask_text(failures);
    row.failed_additional_conditions = failure_names(failures);
    row.checked_exponents = boundary_checked_exponents(item);
    row.case_name = item.name;
    row.inputs = boundary_inputs(item);
    row.shared_result_equal =
        default_outcome == CallOutcome::returned_normally
        && strong_outcome == CallOutcome::returned_normally
            ? "yes" : "not_applicable";
    row.expected_default_outcome =
        outcome_name(as_call_outcome(item.expected_default));
    row.expected_strong_outcome =
        outcome_name(as_call_outcome(item.expected_strong));
    row.expected_failure_mask =
        mask_text(item.expected_additional_failures);
    row.assertion_passed = "yes";
    write_row(case_file, row, data_rows);
}

void run_boundary_suite(std::FILE *case_file, std::size_t &data_rows) {
    std::vector<bench_eval::DwFpBoundaryCase> fp_cases =
        bench_eval::make_dw_fp_boundary_cases();
    std::vector<bench_eval::DwDwBoundaryCase> dw_cases =
        bench_eval::make_dw_dw_boundary_cases();

    std::printf("targeted arithmetic-magnitude boundaries"
                " (excluded from reported percentages)\n");
    std::printf("  %-18s %-48s %-12s %-12s %-32s\n",
                "operation", "case", "default", "strong",
                "failed strong conditions");
    std::size_t index = 0;
    for (auto &item : fp_cases) {
        print_boundary_case(item,
            [](const bench_eval::DwFpBoundaryCase &value) {
                return dw_fp_strong_failures(
                    value.operation, value.first, value.second);
            }, index++, case_file, data_rows);
    }
    for (auto &item : dw_cases) {
        print_boundary_case(item,
            [](const bench_eval::DwDwBoundaryCase &value) {
                return dw_dw_strong_failures(
                    value.operation, value.first, value.second);
            }, index++, case_file, data_rows);
    }
}

std::size_t parse_samples(int argc, char **argv) {
    if (argc > 3) {
        std::fprintf(stderr,
            "usage: %s [samples_per_exponent] [case_tsv]\n", argv[0]);
        std::exit(EXIT_FAILURE);
    }
    if (argc == 1) return 40;
    if (argv[1][0] == '\0') {
        std::fprintf(stderr,
            "samples_per_exponent must be a positive multiple of 40\n");
        std::exit(EXIT_FAILURE);
    }
    for (const char *character = argv[1]; *character != '\0'; ++character) {
        if (*character < '0' || *character > '9') {
            std::fprintf(stderr,
                "samples_per_exponent must be a positive multiple of 40\n");
            std::exit(EXIT_FAILURE);
        }
    }
    errno = 0;
    char *end = nullptr;
    unsigned long long parsed = std::strtoull(argv[1], &end, 10);
    if (errno != 0 || end == argv[1] || *end != '\0' || parsed == 0
        || parsed % 40 != 0
        || parsed > static_cast<unsigned long long>(
            SIZE_MAX / bench_eval::fp_exponent_bins)) {
        std::fprintf(stderr,
            "samples_per_exponent must be a positive multiple of 40\n");
        std::exit(EXIT_FAILURE);
    }
    return static_cast<std::size_t>(parsed);
}

struct CommandLine {
    bool boundary_only;
    std::size_t samples_per_exponent;
    const char *case_path;
};

CommandLine parse_command_line(int argc, char **argv) {
    if (argc >= 2 && std::strcmp(argv[1], "--boundary-only") == 0) {
        if (argc > 3) {
            std::fprintf(stderr,
                "usage: %s --boundary-only [case_tsv]\n", argv[0]);
            std::exit(EXIT_FAILURE);
        }
        return CommandLine{true, 0, argc == 3 ? argv[2] : nullptr};
    }
    return CommandLine{
        false, parse_samples(argc, argv), argc == 3 ? argv[2] : nullptr};
}

void check_environment() {
    if (sizeof(double) != sizeof(std::uint64_t)
        || !std::numeric_limits<double>::is_iec559
        || std::numeric_limits<double>::digits != 53) {
        std::fprintf(stderr, "RQ2 requires IEEE-754 binary64 arithmetic\n");
        std::exit(EXIT_FAILURE);
    }
    if (std::fegetround() != FE_TONEAREST) {
        std::fprintf(stderr, "RQ2 requires round-to-nearest mode\n");
        std::exit(EXIT_FAILURE);
    }
    volatile double normal_min = std::numeric_limits<double>::min();
    volatile double half = 0.5;
    volatile double subnormal = normal_min * half;
    if (subnormal == 0.0) {
        std::fprintf(stderr, "RQ2 requires gradual underflow\n");
        std::exit(EXIT_FAILURE);
    }
    volatile double eta = std::numeric_limits<double>::denorm_min();
    volatile double twice_eta = eta + eta;
    if (twice_eta == 0.0) {
        std::fprintf(stderr, "RQ2 requires subnormal input operands\n");
        std::exit(EXIT_FAILURE);
    }
}

void write_metadata(std::FILE *file, const char *suite_mode,
                    const bench_eval::GeneratedTestInputs *inputs,
                    std::size_t samples_per_exponent) {
    if (file == nullptr) return;
    std::fprintf(file, "# rq2_schema_version=5\n");
    if (suite_mode != nullptr)
        std::fprintf(file, "# suite_mode=%s\n", suite_mode);
    if (inputs != nullptr) {
        std::fprintf(file, "# generator=%s\n",
                     bench_eval::generator_version);
        std::fprintf(file, "# seed=0x%llx\n",
            static_cast<unsigned long long>(bench_eval::generator_seed));
        std::fprintf(file, "# input_fingerprint=0x%016llx\n",
            static_cast<unsigned long long>(inputs->fingerprint));
        std::fprintf(file, "# samples_per_exponent=%zu\n",
                     samples_per_exponent);
        std::fprintf(file, "# oracle_precision_bits=%ld\n",
                     bench_eval::reference_precision);
        std::fprintf(file, "# division_oracle_precision_bits=%ld\n",
                     2 * bench_eval::reference_precision);
        std::fprintf(file, "# qd_inline=1\n");
        std::fprintf(file, "# qd_fma=std::fma\n");
    }
    write_header(file);
}

}  // namespace

int main(int argc, char **argv) {
    const CommandLine command_line = parse_command_line(argc, argv);
    check_environment();

    std::FILE *case_file = nullptr;
    if (command_line.case_path != nullptr) {
        case_file = std::fopen(command_line.case_path, "w");
        if (case_file == nullptr) {
            std::perror(command_line.case_path);
            return EXIT_FAILURE;
        }
    }

    std::size_t data_rows = 0;
    if (command_line.boundary_only) {
        std::printf("RQ2 wrapper usefulness: boundary cases\n");
        write_metadata(case_file, "boundary_only", nullptr, 0);
        run_boundary_suite(case_file, data_rows);
        if (case_file != nullptr) {
            std::fprintf(case_file, "# data_rows=%zu\n", data_rows);
            std::fprintf(case_file, "# completed=true\n");
            if (std::fclose(case_file) != 0) {
                std::perror(command_line.case_path);
                return EXIT_FAILURE;
            }
        }
        return EXIT_SUCCESS;
    }

    bench_eval::GeneratedTestInputs inputs =
        bench_eval::make_generated_test_inputs(
            command_line.samples_per_exponent);
    write_metadata(case_file, nullptr, &inputs,
                   command_line.samples_per_exponent);

    std::printf("RQ2 wrapper usefulness\n");
    std::printf("  generator = %s, seed = 0x%llx, fingerprint = 0x%016llx\n",
        bench_eval::generator_version,
        static_cast<unsigned long long>(bench_eval::generator_seed),
        static_cast<unsigned long long>(inputs.fingerprint));
    std::printf("  QD categories use MPFR references; percentages in the "
                "report use rejected test cases as their denominator\n\n");

    const std::size_t fp_count = inputs.fp_first.size();
    const std::size_t mixed_count = inputs.mixed_dw.size();
    const std::size_t dw_count = inputs.dw_first.size();
    if (inputs.fp_second.size() != fp_count
        || inputs.mixed_fp.size() != mixed_count
        || inputs.dw_second.size() != dw_count) {
        std::abort();
    }

    auto describe_fp = [&](std::size_t i) {
        return bench_eval::describe_inputs(inputs.fp_first[i],
                                           inputs.fp_second[i]);
    };
    auto describe_mixed = [&](std::size_t i) {
        return bench_eval::describe_inputs(inputs.mixed_dw[i],
                                           inputs.mixed_fp[i]);
    };
    auto describe_dw = [&](std::size_t i) {
        return bench_eval::describe_inputs(inputs.dw_first[i],
                                           inputs.dw_second[i]);
    };

    std::vector<GuardReport> dw_reports;
    dw_reports.reserve(6);

    auto run_dw_fp = [&](CompositeOperation operation,
                         VerifiedBound bound_kind,
                         bool division_reference,
                         auto weak_precheck, auto strong_precheck,
                         auto default_call, auto strong_call,
                         auto qd, auto reference) {
        CollectedResults default_results =
            bench_eval::collect_interface_results(
                mixed_count, weak_precheck, default_call, true,
                "default DW-by-FP interface");
        CollectedResults strong_results =
            bench_eval::collect_interface_results(
                mixed_count, strong_precheck, strong_call, false,
                "strong DW-by-FP interface");
        dw_reports.push_back(summarize_operation(
            operation, bound_kind, division_reference,
            default_results, strong_results,
            [&](std::size_t i) {
                bool weak = weak_precheck(i) != 0;
                std::uint32_t mask = weak
                    ? dw_fp_strong_failures(
                        operation, inputs.mixed_dw[i].value,
                        inputs.mixed_fp[i].value)
                    : 0;
                bool diagnosed = weak && mask == 0;
                if (diagnosed != (strong_precheck(i) != 0)) {
                    std::fprintf(stderr,
                        "%s strong diagnostic disagrees at case %zu\n",
                        bench_eval::operation_name(operation), i);
                    std::abort();
                }
                return mask;
            },
            [&](std::size_t i) {
                return std::make_pair(
                    inputs.mixed_dw[i].source_exponent,
                    inputs.mixed_fp[i].exponent);
            },
            [&](std::size_t i) {
                return dw_fp_checked_exponents(
                    operation, inputs.mixed_dw[i].value,
                    inputs.mixed_fp[i].value);
            }, describe_mixed, qd, reference, case_file, data_rows));
    };

    run_dw_fp(CompositeOperation::dw_plus_fp,
        VerifiedBound::dw_plus_fp, false,
        [&](std::size_t i) {
            return dw_plus_fp_weak_precond_check(
                &inputs.mixed_dw[i].value, inputs.mixed_fp[i].value);
        },
        [&](std::size_t i) {
            return dw_plus_fp_strong_precond_check(
                &inputs.mixed_dw[i].value, inputs.mixed_fp[i].value);
        },
        [&](std::size_t i) {
            dword result;
            dw_plus_fp(&result, &inputs.mixed_dw[i].value,
                       inputs.mixed_fp[i].value);
            return ResultPair{result.s, result.t};
        },
        [&](std::size_t i) {
            dword result;
            dw_plus_fp_strong(&result, &inputs.mixed_dw[i].value,
                              inputs.mixed_fp[i].value);
            return ResultPair{result.s, result.t};
        },
        [&](std::size_t i) {
            dd_real first(inputs.mixed_dw[i].value.s,
                          inputs.mixed_dw[i].value.t);
            dd_real result = first + inputs.mixed_fp[i].value;
            return ResultPair{result.x[0], result.x[1]};
        },
        [&](std::size_t i, mpfr_ptr reference, mpfr_ptr first,
            mpfr_ptr second, mpfr_ptr scratch) {
            bench_eval::set_dword_value(
                first, inputs.mixed_dw[i].value, scratch);
            mpfr_set_d(second, inputs.mixed_fp[i].value, MPFR_RNDN);
            mpfr_add(reference, first, second, MPFR_RNDN);
        });

    run_dw_fp(CompositeOperation::dw_times_fp,
        VerifiedBound::dw_times_fp, false,
        [&](std::size_t i) {
            return dw_times_fp_weak_precond_check(
                &inputs.mixed_dw[i].value, inputs.mixed_fp[i].value);
        },
        [&](std::size_t i) {
            return dw_times_fp_strong_precond_check(
                &inputs.mixed_dw[i].value, inputs.mixed_fp[i].value);
        },
        [&](std::size_t i) {
            dword result;
            dw_times_fp(&result, &inputs.mixed_dw[i].value,
                        inputs.mixed_fp[i].value);
            return ResultPair{result.s, result.t};
        },
        [&](std::size_t i) {
            dword result;
            dw_times_fp_strong(&result, &inputs.mixed_dw[i].value,
                               inputs.mixed_fp[i].value);
            return ResultPair{result.s, result.t};
        },
        [&](std::size_t i) {
            dd_real first(inputs.mixed_dw[i].value.s,
                          inputs.mixed_dw[i].value.t);
            dd_real result = first * inputs.mixed_fp[i].value;
            return ResultPair{result.x[0], result.x[1]};
        },
        [&](std::size_t i, mpfr_ptr reference, mpfr_ptr first,
            mpfr_ptr second, mpfr_ptr scratch) {
            bench_eval::set_dword_value(
                first, inputs.mixed_dw[i].value, scratch);
            mpfr_set_d(second, inputs.mixed_fp[i].value, MPFR_RNDN);
            mpfr_mul(reference, first, second, MPFR_RNDN);
        });

    run_dw_fp(CompositeOperation::dw_div_fp,
        VerifiedBound::dw_div_fp, true,
        [&](std::size_t i) {
            return dw_div_fp_weak_check(
                &inputs.mixed_dw[i].value, inputs.mixed_fp[i].value);
        },
        [&](std::size_t i) {
            return dw_div_fp_strong_check(
                &inputs.mixed_dw[i].value, inputs.mixed_fp[i].value);
        },
        [&](std::size_t i) {
            dword result;
            dw_div_fp(&result, &inputs.mixed_dw[i].value,
                      inputs.mixed_fp[i].value);
            return ResultPair{result.s, result.t};
        },
        [&](std::size_t i) {
            dword result;
            dw_div_fp_strong(&result, &inputs.mixed_dw[i].value,
                             inputs.mixed_fp[i].value);
            return ResultPair{result.s, result.t};
        },
        [&](std::size_t i) {
            dd_real first(inputs.mixed_dw[i].value.s,
                          inputs.mixed_dw[i].value.t);
            dd_real result = first / inputs.mixed_fp[i].value;
            return ResultPair{result.x[0], result.x[1]};
        },
        [&](std::size_t i, mpfr_ptr reference, mpfr_ptr first,
            mpfr_ptr second, mpfr_ptr scratch) {
            bench_eval::set_dword_value(
                first, inputs.mixed_dw[i].value, scratch);
            mpfr_set_d(second, inputs.mixed_fp[i].value, MPFR_RNDN);
            mpfr_div(reference, first, second, MPFR_RNDN);
        });

    auto run_dw_dw = [&](CompositeOperation operation,
                         VerifiedBound bound_kind,
                         bool division_reference,
                         auto weak_precheck, auto strong_precheck,
                         auto default_call, auto strong_call,
                         auto qd, auto reference) {
        CollectedResults default_results =
            bench_eval::collect_interface_results(
                dw_count, weak_precheck, default_call, true,
                "default DW-by-DW interface");
        CollectedResults strong_results =
            bench_eval::collect_interface_results(
                dw_count, strong_precheck, strong_call, false,
                "strong DW-by-DW interface");
        dw_reports.push_back(summarize_operation(
            operation, bound_kind, division_reference,
            default_results, strong_results,
            [&](std::size_t i) {
                bool weak = weak_precheck(i) != 0;
                std::uint32_t mask = weak
                    ? dw_dw_strong_failures(
                        operation, inputs.dw_first[i].value,
                        inputs.dw_second[i].value)
                    : 0;
                bool diagnosed = weak && mask == 0;
                if (diagnosed != (strong_precheck(i) != 0)) {
                    std::fprintf(stderr,
                        "%s strong diagnostic disagrees at case %zu\n",
                        bench_eval::operation_name(operation), i);
                    std::abort();
                }
                return mask;
            },
            [&](std::size_t i) {
                return std::make_pair(
                    inputs.dw_first[i].source_exponent,
                    inputs.dw_second[i].source_exponent);
            },
            [&](std::size_t i) {
                return dw_dw_checked_exponents(
                    operation, inputs.dw_first[i].value,
                    inputs.dw_second[i].value);
            }, describe_dw, qd, reference, case_file, data_rows));
    };

    run_dw_dw(CompositeOperation::dw_plus_dw,
        VerifiedBound::dw_plus_dw, false,
        [&](std::size_t i) {
            return dw_plus_dw_weak_precond_check(
                &inputs.dw_first[i].value, &inputs.dw_second[i].value);
        },
        [&](std::size_t i) {
            return dw_plus_dw_strong_precond_check(
                &inputs.dw_first[i].value, &inputs.dw_second[i].value);
        },
        [&](std::size_t i) {
            dword result;
            dw_plus_dw(&result, &inputs.dw_first[i].value,
                       &inputs.dw_second[i].value);
            return ResultPair{result.s, result.t};
        },
        [&](std::size_t i) {
            dword result;
            dw_plus_dw_strong(&result, &inputs.dw_first[i].value,
                              &inputs.dw_second[i].value);
            return ResultPair{result.s, result.t};
        },
        [&](std::size_t i) {
            dd_real first(inputs.dw_first[i].value.s,
                          inputs.dw_first[i].value.t);
            dd_real second(inputs.dw_second[i].value.s,
                           inputs.dw_second[i].value.t);
            dd_real result = dd_real::ieee_add(first, second);
            return ResultPair{result.x[0], result.x[1]};
        },
        [&](std::size_t i, mpfr_ptr reference, mpfr_ptr first,
            mpfr_ptr second, mpfr_ptr scratch) {
            bench_eval::set_dword_value(
                first, inputs.dw_first[i].value, scratch);
            bench_eval::set_dword_value(
                second, inputs.dw_second[i].value, scratch);
            mpfr_add(reference, first, second, MPFR_RNDN);
        });

    run_dw_dw(CompositeOperation::dw_times_dw,
        VerifiedBound::dw_times_dw, false,
        [&](std::size_t i) {
            return dw_times_dw_weak_precond_check(
                &inputs.dw_first[i].value, &inputs.dw_second[i].value);
        },
        [&](std::size_t i) {
            return dw_times_dw_strong_precond_check(
                &inputs.dw_first[i].value, &inputs.dw_second[i].value);
        },
        [&](std::size_t i) {
            dword result;
            dw_times_dw(&result, &inputs.dw_first[i].value,
                        &inputs.dw_second[i].value);
            return ResultPair{result.s, result.t};
        },
        [&](std::size_t i) {
            dword result;
            dw_times_dw_strong(&result, &inputs.dw_first[i].value,
                               &inputs.dw_second[i].value);
            return ResultPair{result.s, result.t};
        },
        [&](std::size_t i) {
            dd_real first(inputs.dw_first[i].value.s,
                          inputs.dw_first[i].value.t);
            dd_real second(inputs.dw_second[i].value.s,
                           inputs.dw_second[i].value.t);
            dd_real result = first * second;
            return ResultPair{result.x[0], result.x[1]};
        },
        [&](std::size_t i, mpfr_ptr reference, mpfr_ptr first,
            mpfr_ptr second, mpfr_ptr scratch) {
            bench_eval::set_dword_value(
                first, inputs.dw_first[i].value, scratch);
            bench_eval::set_dword_value(
                second, inputs.dw_second[i].value, scratch);
            mpfr_mul(reference, first, second, MPFR_RNDN);
        });

    run_dw_dw(CompositeOperation::dw_div_dw,
        VerifiedBound::dw_div_dw, true,
        [&](std::size_t i) {
            return dw_div_dw_weak_precond_check(
                &inputs.dw_first[i].value, &inputs.dw_second[i].value);
        },
        [&](std::size_t i) {
            return dw_div_dw_strong_precond_check(
                &inputs.dw_first[i].value, &inputs.dw_second[i].value);
        },
        [&](std::size_t i) {
            dword result;
            dw_div_dw(&result, &inputs.dw_first[i].value,
                      &inputs.dw_second[i].value);
            return ResultPair{result.s, result.t};
        },
        [&](std::size_t i) {
            dword result;
            dw_div_dw_strong(&result, &inputs.dw_first[i].value,
                             &inputs.dw_second[i].value);
            return ResultPair{result.s, result.t};
        },
        [&](std::size_t i) {
            dd_real first(inputs.dw_first[i].value.s,
                          inputs.dw_first[i].value.t);
            dd_real second(inputs.dw_second[i].value.s,
                           inputs.dw_second[i].value.t);
            dd_real result = dd_real::accurate_div(first, second);
            return ResultPair{result.x[0], result.x[1]};
        },
        [&](std::size_t i, mpfr_ptr reference, mpfr_ptr first,
            mpfr_ptr second, mpfr_ptr scratch) {
            bench_eval::set_dword_value(
                first, inputs.dw_first[i].value, scratch);
            bench_eval::set_dword_value(
                second, inputs.dw_second[i].value, scratch);
            mpfr_div(reference, first, second, MPFR_RNDN);
        });

    std::vector<EftReport> eft_reports;
    eft_reports.reserve(3);

    auto run_eft = [&](const char *operation, auto precheck, auto call,
                       auto qd, auto reference) {
        CollectedResults results = bench_eval::collect_interface_results(
            fp_count, precheck, call, false, operation);
        eft_reports.push_back(summarize_eft(
            operation, results, qd, reference,
            [&](std::size_t i) {
                return std::make_pair(inputs.fp_first[i].exponent,
                                      inputs.fp_second[i].exponent);
            }, describe_fp, case_file, data_rows));
    };

    run_eft("two_sum",
        [&](std::size_t i) {
            return two_sum_exact_check(inputs.fp_first[i].value,
                                       inputs.fp_second[i].value);
        },
        [&](std::size_t i) {
            dword result;
            two_sum_guarded(&result, inputs.fp_first[i].value,
                            inputs.fp_second[i].value);
            return ResultPair{result.s, result.t};
        },
        [&](std::size_t i) {
            double error;
            double high = qd::two_sum(inputs.fp_first[i].value,
                                      inputs.fp_second[i].value, error);
            return ResultPair{high, error};
        },
        [&](std::size_t i, mpfr_ptr reference, mpfr_ptr first,
            mpfr_ptr second, mpfr_ptr) {
            mpfr_set_d(first, inputs.fp_first[i].value, MPFR_RNDN);
            mpfr_set_d(second, inputs.fp_second[i].value, MPFR_RNDN);
            mpfr_add(reference, first, second, MPFR_RNDN);
        });

    run_eft("fast_2sum",
        [&](std::size_t i) {
            return fast2_sum_magnitude_order_check(
                inputs.fp_first[i].value, inputs.fp_second[i].value);
        },
        [&](std::size_t i) {
            dword result;
            fast_2sum_guarded(&result, inputs.fp_first[i].value,
                              inputs.fp_second[i].value);
            return ResultPair{result.s, result.t};
        },
        [&](std::size_t i) {
            double error;
            double high = qd::quick_two_sum(inputs.fp_first[i].value,
                                            inputs.fp_second[i].value,
                                            error);
            return ResultPair{high, error};
        },
        [&](std::size_t i, mpfr_ptr reference, mpfr_ptr first,
            mpfr_ptr second, mpfr_ptr) {
            mpfr_set_d(first, inputs.fp_first[i].value, MPFR_RNDN);
            mpfr_set_d(second, inputs.fp_second[i].value, MPFR_RNDN);
            mpfr_add(reference, first, second, MPFR_RNDN);
        });

    run_eft("fast_2mult",
        [&](std::size_t i) {
            return fast2_mult_exact_check(inputs.fp_first[i].value,
                                          inputs.fp_second[i].value);
        },
        [&](std::size_t i) {
            dword result;
            fast_2mult_guarded(&result, inputs.fp_first[i].value,
                               inputs.fp_second[i].value);
            return ResultPair{result.s, result.t};
        },
        [&](std::size_t i) {
            double error;
            double high = qd::two_prod(inputs.fp_first[i].value,
                                       inputs.fp_second[i].value, error);
            return ResultPair{high, error};
        },
        [&](std::size_t i, mpfr_ptr reference, mpfr_ptr first,
            mpfr_ptr second, mpfr_ptr) {
            mpfr_set_d(first, inputs.fp_first[i].value, MPFR_RNDN);
            mpfr_set_d(second, inputs.fp_second[i].value, MPFR_RNDN);
            mpfr_mul(reference, first, second, MPFR_RNDN);
        });

    print_reports(dw_reports, eft_reports);
    run_boundary_suite(case_file, data_rows);

    if (bench_eval::fingerprint_generated_inputs(inputs)
        != inputs.fingerprint) {
        std::fprintf(stderr, "RQ2 changed the shared generated test inputs\n");
        return EXIT_FAILURE;
    }
    if (case_file != nullptr) {
        std::fprintf(case_file, "# data_rows=%zu\n", data_rows);
        std::fprintf(case_file, "# completed=true\n");
        if (std::fclose(case_file) != 0) {
            std::perror(command_line.case_path);
            return EXIT_FAILURE;
        }
    }
    return EXIT_SUCCESS;
}
