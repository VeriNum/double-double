// RQ1 measures bound tightness for the default double-word interface.
// MPFR supplies the reference value; QD is evaluated on the same inputs.

#include <mpfr.h>

#include <cerrno>
#include <cfenv>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <limits>
#include <string>
#include <vector>

extern "C" {
#include "dw_arith.h"
#include "fp_utils.h"
}

#include "input_generation.hpp"
#include "interface_runner.hpp"
#include "mpfr_accuracy.hpp"
#include "qd_evaluation.hpp"

namespace {

using bench_eval::AccuracyCounts;
using bench_eval::AccuracyOptions;
using bench_eval::BoundViolation;
using bench_eval::CollectedResults;
using bench_eval::ContractWitness;
using bench_eval::ErrorWitness;
using bench_eval::MetricSummary;
using bench_eval::GeneratedTestInputs;
using bench_eval::OutcomeCounts;
using bench_eval::PairCoverage;
using bench_eval::ResultPair;
using bench_eval::VerifiedBound;

struct OperationReport {
    const char *name;
    AccuracyOptions options;
    OutcomeCounts outcomes;
    AccuracyCounts accuracy;
};

AccuracyOptions operation_options(VerifiedBound bound,
                                  bool division_reference = false) {
    AccuracyOptions options;
    options.bound_kind = bound;
    options.division_reference = division_reference;
    return options;
}

template <class Precheck, class Call, class Qd, class Reference,
          class Describe>
OperationReport evaluate_operation(const char *name, std::size_t count,
                                   Precheck precheck, Call call, Qd qd,
                                   Reference reference, Describe describe,
                                   const AccuracyOptions &options) {
    std::string interface_name = std::string("default ") + name;
    CollectedResults results = bench_eval::collect_interface_results(
        count, precheck, call, true,
        interface_name.c_str());

    OperationReport report;
    report.name = name;
    report.options = options;
    report.outcomes = bench_eval::count_outcomes(results.outcomes);
    report.accuracy = bench_eval::measure_accuracy(
        results, bench_eval::QdEvaluator(qd),
        bench_eval::ReferenceEvaluator(reference),
        bench_eval::CaseDescriber(describe), options);
    if (report.accuracy.compared != report.outcomes.normal) std::abort();
    return report;
}

std::string case_text(std::size_t case_index) {
    return case_index == SIZE_MAX ? "-" : std::to_string(case_index);
}

void print_coverage_row(const char *name, const PairCoverage &coverage,
                        std::size_t total_first_bins,
                        std::size_t total_second_bins,
                        bool first_is_dw, bool second_is_dw) {
    std::string first_ordinary = first_is_dw
        ? std::to_string(coverage.first_ordinary) : "-";
    std::string second_ordinary = second_is_dw
        ? std::to_string(coverage.second_ordinary) : "-";
    std::printf("  %-10s %8zu   %4zu/%-4zu   %4zu/%-4zu"
                "   %7zu   %7zu   %12s   %12s\n",
                name, coverage.cases,
                coverage.first_bins, total_first_bins,
                coverage.second_bins, total_second_bins,
                coverage.first_positive, coverage.second_positive,
                first_ordinary.c_str(), second_ordinary.c_str());
}

void print_regime_metric_row(const char *name, const char *library,
                             const MetricSummary &error,
                             const MetricSummary &bound_utilization,
                             std::size_t nonfinite,
                             std::size_t above_bound) {
    if (error.count != bound_utilization.count) std::abort();
    std::string maximum_case = case_text(error.witness.case_index);
    std::printf("  %-18s %-6s %9zu %9zu   %14s %14s"
                "   %14s %14s %10zu %10s\n",
                name, library, error.count, nonfinite,
                error.maximum_scaled.c_str(), error.mean_scaled.c_str(),
                bound_utilization.maximum.c_str(),
                bound_utilization.mean.c_str(), above_bound,
                maximum_case.c_str());
}

void print_error_witness(const char *name, const char *library,
                         const char *metric_name,
                         const MetricSummary &summary) {
    if (!summary.maximum_nonzero) return;
    const ErrorWitness &witness = summary.witness;
    std::printf("  %s %s %s: case=%zu metric=%s ref=%s abs_err=%s "
                "result=(0x%016llx,0x%016llx) %s\n",
                name, library, metric_name, witness.case_index,
                summary.maximum.c_str(), witness.reference.c_str(),
                witness.absolute_error.c_str(),
                static_cast<unsigned long long>(
                    bench_eval::bits_of(witness.result.hi)),
                static_cast<unsigned long long>(
                    bench_eval::bits_of(witness.result.lo)),
                witness.inputs.c_str());
}

void print_contract_witness(const char *name, const char *library,
                            const char *contract,
                            const ContractWitness &witness) {
    if (witness.case_index == SIZE_MAX) return;
    std::printf("  %s %s %s: case=%zu ref=%s "
                "result=(0x%016llx,0x%016llx) %s\n",
                name, library, contract, witness.case_index,
                witness.reference.c_str(),
                static_cast<unsigned long long>(
                    bench_eval::bits_of(witness.result.hi)),
                static_cast<unsigned long long>(
                    bench_eval::bits_of(witness.result.lo)),
                witness.inputs.c_str());
}

void print_error_case_witness(const char *name, const char *library,
                              const char *metric_name,
                              const ErrorWitness &witness) {
    if (witness.case_index == SIZE_MAX) return;
    std::printf("  %s %s %s: case=%zu ref=%s abs_err=%s "
                "result=(0x%016llx,0x%016llx) %s\n",
                name, library, metric_name, witness.case_index,
                witness.reference.c_str(), witness.absolute_error.c_str(),
                static_cast<unsigned long long>(
                    bench_eval::bits_of(witness.result.hi)),
                static_cast<unsigned long long>(
                    bench_eval::bits_of(witness.result.lo)),
                witness.inputs.c_str());
}

void print_nonfinite_witness(const char *name,
                             const ErrorWitness &witness) {
    if (witness.case_index == SIZE_MAX) return;
    std::printf("  %s QD nonfinite: case=%zu ref=%s "
                "result=(0x%016llx,0x%016llx) %s\n",
                name, witness.case_index, witness.reference.c_str(),
                static_cast<unsigned long long>(
                    bench_eval::bits_of(witness.result.hi)),
                static_cast<unsigned long long>(
                    bench_eval::bits_of(witness.result.lo)),
                witness.inputs.c_str());
}

void print_reports(const GeneratedTestInputs &inputs,
                   std::size_t samples_per_exponent,
                   const std::vector<OperationReport> &reports) {
    std::printf("numerical input coverage\n");
    std::printf("  generator = %s, seed = 0x%llx, construction bits = %ld,"
                " reference bits = %ld\n",
                bench_eval::generator_version,
                static_cast<unsigned long long>(bench_eval::generator_seed),
                bench_eval::construction_precision,
                bench_eval::reference_precision);
    std::printf("  division reference bits = %ld\n",
                2 * bench_eval::reference_precision);
    std::printf("  fingerprint of generated inputs = 0x%016llx\n",
                static_cast<unsigned long long>(inputs.fingerprint));
    std::printf("  primary samples/exponent = %zu\n", samples_per_exponent);
    std::printf("  double-word core = [%d, %d]: %zu/%zu binary64"
                " magnitude-exponent bins (%.2f%%)\n",
                bench_eval::dw_min_exponent, bench_eval::dw_max_exponent,
                bench_eval::dw_exponent_bins, bench_eval::fp_exponent_bins,
                100.0 * static_cast<double>(bench_eval::dw_exponent_bins)
                    / static_cast<double>(bench_eval::fp_exponent_bins));
    std::printf("  %-10s %8s   %9s   %9s"
                "   %7s   %7s   %12s   %12s\n",
                "inputs", "cases", "first_exp", "second_exp",
                "first_pos", "second_pos",
                "first_dw_lo0", "second_dw_lo0");
    print_coverage_row("FP x FP", inputs.fp_coverage,
                       bench_eval::fp_exponent_bins,
                       bench_eval::fp_exponent_bins, false, false);
    print_coverage_row("DW x FP", inputs.mixed_coverage,
                       bench_eval::dw_exponent_bins,
                       bench_eval::fp_exponent_bins, true, false);
    print_coverage_row("DW x DW", inputs.dw_coverage,
                       bench_eval::dw_exponent_bins,
                       bench_eval::dw_exponent_bins, true, true);
    std::printf("\n");

    std::printf("default-interface outcomes\n");
    std::printf("  %-18s %9s %12s %12s %12s   %10s %10s\n",
                "op", "generated", "input_check", "post_compute", "normal",
                "first_in", "first_post");
    for (const OperationReport &report : reports) {
        std::printf("  %-18s %9zu %12zu %12zu %12zu   %10s %10s\n",
                    report.name, report.outcomes.generated,
                    report.outcomes.input_check,
                    report.outcomes.post_computation,
                    report.outcomes.normal,
                    case_text(report.outcomes.first_input_check).c_str(),
                    case_text(report.outcomes.first_post_computation).c_str());
    }
    std::printf("\n");

    std::printf("finite returned-pair validity\n");
    std::printf("  finite invalid QD pairs remain in represented-value "
                "error measurements.\n");
    std::printf("  %-18s %12s %12s %12s\n", "op", "dd_invalid",
                "qd_invalid", "qd_nonfinite");
    for (const OperationReport &report : reports) {
        const AccuracyCounts &a = report.accuracy;
        std::printf("  %-18s %12zu %12zu %12zu\n", report.name,
                    a.dd_lib_invalid_double_word,
                    a.qd_invalid_double_word, a.qd_nonfinite);
    }
    std::printf("\n");

    std::printf("relative error where the relative bound term dominates\n");
    std::printf("  reference != 0 and relative term >= absolute term;"
                " u = 2^-53\n");
    std::printf("  QD fractions use the dd_lib bound as a comparison"
                " threshold, not as a guarantee for QD; QD may use a"
                " different algorithm.\n");
    std::printf("  %-18s %-6s %9s %9s   %14s %14s"
                "   %14s %14s %10s %10s\n",
                "op", "impl", "N", "nonfinite", "max_rel/u^2",
                "mean_rel/u^2", "max_fraction", "mean_fraction",
                "above", "max_case");
    for (const OperationReport &report : reports) {
        const AccuracyCounts &a = report.accuracy;
        print_regime_metric_row(
            report.name, "dd_lib", a.dd_lib.relative_term_relative,
            a.dd_lib.relative_term_bound_utilization, 0,
            a.dd_lib.relative_term_bound_ratio_above_one);
        print_regime_metric_row(
            report.name, "QD", a.qd.relative_term_relative,
            a.qd.relative_term_bound_utilization,
            a.qd_nonfinite_relative_term,
            a.qd.relative_term_bound_ratio_above_one);
    }
    std::printf("\n");

    std::printf("absolute error where the absolute bound term dominates\n");
    std::printf("  absolute term > relative term, including zero"
                " references; eta = 2^-1074\n");
    std::printf("  QD fractions use the dd_lib bound as a comparison"
                " threshold, not as a guarantee for QD; QD may use a"
                " different algorithm.\n");
    std::printf("  %-18s %-6s %9s %9s   %14s %14s"
                "   %14s %14s %10s %10s\n",
                "op", "impl", "N", "nonfinite", "max_abs/eta",
                "mean_abs/eta", "max_fraction", "mean_fraction",
                "above", "max_case");
    for (const OperationReport &report : reports) {
        const AccuracyCounts &a = report.accuracy;
        print_regime_metric_row(
            report.name, "dd_lib", a.dd_lib.absolute_term_absolute,
            a.dd_lib.absolute_term_bound_utilization, 0,
            a.dd_lib.absolute_term_bound_ratio_above_one);
        print_regime_metric_row(
            report.name, "QD", a.qd.absolute_term_absolute,
            a.qd.absolute_term_bound_utilization,
            a.qd_nonfinite_absolute_term,
            a.qd.absolute_term_bound_ratio_above_one);
    }
    std::printf("\n");

    std::printf("zero-reference cases with a zero bound\n");
    std::printf("  %-18s %9s %12s %12s %12s\n", "op", "N",
                "dd_error", "qd_error", "qd_nonfinite");
    for (const OperationReport &report : reports) {
        const AccuracyCounts &a = report.accuracy;
        if (a.zero_bound_references == 0) continue;
        std::printf("  %-18s %9zu %12zu %12zu %12zu\n", report.name,
                    a.zero_bound_references,
                    a.dd_lib.zero_bound_nonzero_error,
                    a.qd.zero_bound_nonzero_error,
                    a.qd_nonfinite_zero_bound);
    }
    std::printf("\n");

    std::printf("higher-precision division rechecks\n");
    std::printf("  %-18s %14s %14s\n", "op",
                "bound_rechecks", "bound_changed");
    for (const OperationReport &report : reports) {
        if (!report.options.division_reference) continue;
        const AccuracyCounts &a = report.accuracy;
        std::printf("  %-18s %14zu %14zu\n", report.name,
                    a.higher_precision_bound_rechecks,
                    a.higher_precision_bound_decision_changes);
    }
    std::printf("\n");

    std::printf("nonzero maximum-error witnesses\n");
    for (const OperationReport &report : reports) {
        const AccuracyCounts &a = report.accuracy;
        print_error_witness(report.name, "dd_lib", "relative_term_rel",
                            a.dd_lib.relative_term_relative);
        print_error_witness(report.name, "QD", "relative_term_rel",
                            a.qd.relative_term_relative);
        print_error_witness(report.name, "dd_lib", "absolute_term_abs",
                            a.dd_lib.absolute_term_absolute);
        print_error_witness(report.name, "QD", "absolute_term_abs",
                            a.qd.absolute_term_absolute);
        print_error_witness(report.name, "dd_lib", "relative_bound_fraction",
                            a.dd_lib.relative_term_bound_utilization);
        print_error_witness(report.name, "QD", "relative_bound_fraction",
                            a.qd.relative_term_bound_utilization);
        print_error_witness(report.name, "dd_lib", "absolute_bound_fraction",
                            a.dd_lib.absolute_term_bound_utilization);
        print_error_witness(report.name, "QD", "absolute_bound_fraction",
                            a.qd.absolute_term_bound_utilization);
    }
    std::printf("\n");

    std::printf("first invalid-pair and zero-bound-error witnesses\n");
    for (const OperationReport &report : reports) {
        const AccuracyCounts &a = report.accuracy;
        print_contract_witness(report.name, "dd_lib", "invalid_double_word",
                               a.first_dd_lib_invalid_double_word);
        print_contract_witness(report.name, "QD", "invalid_double_word",
                               a.first_qd_invalid_double_word);
        print_error_case_witness(
            report.name, "dd_lib", "zero_bound_error",
            a.dd_lib.first_zero_bound_nonzero_error);
        print_error_case_witness(
            report.name, "QD", "zero_bound_error",
            a.qd.first_zero_bound_nonzero_error);
    }
    std::printf("\n");

    std::printf("first nonfinite QD witnesses\n");
    for (const OperationReport &report : reports) {
        const AccuracyCounts &a = report.accuracy;
        print_nonfinite_witness(report.name, a.first_qd_nonfinite);
    }
    std::printf("\n");
}

void write_metric_tsv(std::FILE *file, const char *operation,
                      const char *implementation, const char *metric,
                      const MetricSummary &summary, std::size_t &data_rows,
                      std::size_t flags = 0,
                      const char *flag_kind = "none") {
    const ErrorWitness &witness = summary.witness;
    if ((summary.count == 0) != (witness.case_index == SIZE_MAX)) std::abort();
    char high_bits[19] = "-";
    char low_bits[19] = "-";
    if (witness.case_index != SIZE_MAX) {
        std::snprintf(high_bits, sizeof(high_bits), "0x%016llx",
            static_cast<unsigned long long>(
                bench_eval::bits_of(witness.result.hi)));
        std::snprintf(low_bits, sizeof(low_bits), "0x%016llx",
            static_cast<unsigned long long>(
                bench_eval::bits_of(witness.result.lo)));
    }
    std::fprintf(file,
        "metric\t%s\t%s\t%s\t%zu\t%s\t%s\t%s\t%s\t%zu\t%s\t%s"
        "\t%s\t%s\t%s\t%s\t%s\n",
        operation, implementation, metric, summary.count,
        summary.maximum.c_str(), summary.mean.c_str(),
        summary.maximum_scaled.c_str(), summary.mean_scaled.c_str(), flags,
        flag_kind,
        case_text(witness.case_index).c_str(),
        high_bits, low_bits,
        witness.reference.empty() ? "-" : witness.reference.c_str(),
        witness.absolute_error.empty() ? "-" : witness.absolute_error.c_str(),
        witness.inputs.empty() ? "-" : witness.inputs.c_str());
    ++data_rows;
}

void write_error_witness_tsv(std::FILE *file, const char *operation,
                             const char *implementation,
                             const char *metric, std::size_t count,
                             const ErrorWitness &witness,
                             std::size_t &data_rows) {
    if ((count == 0) != (witness.case_index == SIZE_MAX)) std::abort();
    if (witness.case_index == SIZE_MAX) return;
    if (witness.reference.empty() || witness.absolute_error.empty()
        || witness.inputs.empty()) {
        std::abort();
    }
    std::fprintf(file,
        "witness\t%s\t%s\t%s\t%zu\t-\t-\t-\t-\t0\tnone\t%zu"
        "\t0x%016llx\t0x%016llx\t%s\t%s\t%s\n",
        operation, implementation, metric, count, witness.case_index,
        static_cast<unsigned long long>(
            bench_eval::bits_of(witness.result.hi)),
        static_cast<unsigned long long>(
            bench_eval::bits_of(witness.result.lo)),
        witness.reference.c_str(), witness.absolute_error.c_str(),
        witness.inputs.c_str());
    ++data_rows;
}

void write_contract_witness_tsv(std::FILE *file, const char *operation,
                                const char *implementation,
                                const char *metric, std::size_t count,
                                const ContractWitness &witness,
                                std::size_t &data_rows) {
    if ((count == 0) != (witness.case_index == SIZE_MAX)) std::abort();
    if (witness.case_index == SIZE_MAX) return;
    if (witness.reference.empty() || witness.inputs.empty()) std::abort();
    std::fprintf(file,
        "witness\t%s\t%s\t%s\t%zu\t-\t-\t-\t-\t0\tnone\t%zu"
        "\t0x%016llx\t0x%016llx\t%s\t-\t%s\n",
        operation, implementation, metric, count, witness.case_index,
        static_cast<unsigned long long>(
            bench_eval::bits_of(witness.result.hi)),
        static_cast<unsigned long long>(
            bench_eval::bits_of(witness.result.lo)),
        witness.reference.c_str(), witness.inputs.c_str());
    ++data_rows;
}

const char *regime_name(bench_eval::ErrorRegime regime) {
    switch (regime) {
    case bench_eval::ErrorRegime::relative_term_dominates:
        return "relative_term_dominant";
    case bench_eval::ErrorRegime::absolute_term_dominates:
        return "absolute_term_dominant";
    case bench_eval::ErrorRegime::zero_bound_reference:
        return "zero_bound";
    }
    std::abort();
}

void write_bound_violations_tsv(
        std::FILE *file, const char *operation, const char *implementation,
        const std::vector<BoundViolation> &violations,
        std::size_t &data_rows) {
    for (const BoundViolation &violation : violations) {
        const ErrorWitness &witness = violation.witness;
        if (witness.case_index == SIZE_MAX || witness.reference.empty()
            || witness.absolute_error.empty() || witness.inputs.empty()) {
            std::abort();
        }
        std::fprintf(file,
            "above_bound\t%s\t%s\t%s\t1\t-\t-\t-\t-\t0\tnone\t%zu"
            "\t0x%016llx\t0x%016llx\t%s\t%s\t%s\n",
            operation, implementation, regime_name(violation.regime),
            witness.case_index,
            static_cast<unsigned long long>(
                bench_eval::bits_of(witness.result.hi)),
            static_cast<unsigned long long>(
                bench_eval::bits_of(witness.result.lo)),
            witness.reference.c_str(), witness.absolute_error.c_str(),
            witness.inputs.c_str());
        ++data_rows;
    }
}

void write_coverage_tsv(std::FILE *file, const char *operation,
                        const PairCoverage &coverage,
                        std::size_t total_first_bins,
                        std::size_t total_second_bins,
                        bool first_is_dw, bool second_is_dw,
                        std::size_t &data_rows) {
    auto row = [&](const char *metric, std::size_t count) {
        std::fprintf(file,
            "coverage\t%s\tinputs\t%s\t%zu\t-\t-\t-\t-\t0\tnone\t-"
            "\t-\t-\t-\t-\t-\n",
            operation, metric, count);
        ++data_rows;
    };
    row("cases", coverage.cases);
    row("first_bins_seen", coverage.first_bins);
    row("first_bins_total", total_first_bins);
    row("second_bins_seen", coverage.second_bins);
    row("second_bins_total", total_second_bins);
    row("first_positive", coverage.first_positive);
    row("second_positive", coverage.second_positive);
    row("first_zero_low",
        first_is_dw ? coverage.first_ordinary : coverage.cases);
    row("second_zero_low",
        second_is_dw ? coverage.second_ordinary : coverage.cases);
}

void write_summary_tsv(std::FILE *file, const GeneratedTestInputs &inputs,
                       std::size_t samples_per_exponent,
                       const std::vector<OperationReport> &reports) {
    std::size_t data_rows = 0;
    std::fprintf(file, "# rq1_schema_version=6\n");
    std::fprintf(file, "# generator=%s\n", bench_eval::generator_version);
    std::fprintf(file, "# seed=0x%llx\n",
        static_cast<unsigned long long>(bench_eval::generator_seed));
    std::fprintf(file, "# input_fingerprint=0x%016llx\n",
        static_cast<unsigned long long>(inputs.fingerprint));
    std::fprintf(file, "# samples_per_exponent=%zu\n",
                 samples_per_exponent);
    std::fprintf(file, "# construction_precision_bits=%ld\n",
                 bench_eval::construction_precision);
    std::fprintf(file, "# oracle_precision_bits=%ld\n",
                 bench_eval::reference_precision);
    std::fprintf(file, "# division_recheck_precision_bits=%ld\n",
                 2 * bench_eval::reference_precision);
    std::fprintf(file,
        "record\toperation\timplementation\tmetric\tcount\tmaximum"
        "\tmean\tmaximum_scaled\tmean_scaled\tflags\tflag_kind\tcase_id"
        "\tresult_hi_bits\tresult_lo_bits\treference\tabsolute_error"
        "\tinputs\n");

    write_coverage_tsv(file, "fp_x_fp", inputs.fp_coverage,
                       bench_eval::fp_exponent_bins,
                       bench_eval::fp_exponent_bins, false, false,
                       data_rows);
    write_coverage_tsv(file, "dw_x_fp", inputs.mixed_coverage,
                       bench_eval::dw_exponent_bins,
                       bench_eval::fp_exponent_bins, true, false,
                       data_rows);
    write_coverage_tsv(file, "dw_x_dw", inputs.dw_coverage,
                       bench_eval::dw_exponent_bins,
                       bench_eval::dw_exponent_bins, true, true,
                       data_rows);

    for (const OperationReport &report : reports) {
        const AccuracyCounts &a = report.accuracy;
        auto count_row = [&](const char *implementation, const char *metric,
                             std::size_t count) {
            std::fprintf(file,
                "count\t%s\t%s\t%s\t%zu\t-\t-\t-\t-\t0\tnone\t-"
                "\t-\t-\t-\t-\t-\n",
                report.name, implementation, metric, count);
            ++data_rows;
        };
        count_row("dd_lib", "generated", report.outcomes.generated);
        count_row("dd_lib", "input_check", report.outcomes.input_check);
        count_row("dd_lib", "post_compute",
                  report.outcomes.post_computation);
        count_row("dd_lib", "normal", report.outcomes.normal);
        count_row("QD", "nonfinite", a.qd_nonfinite);
        count_row("dd_lib", "invalid_double_word",
                  a.dd_lib_invalid_double_word);
        count_row("QD", "invalid_double_word",
                  a.qd_invalid_double_word);
        count_row("MPFR", "relative_term_references",
                  a.relative_term_references);
        count_row("MPFR", "absolute_term_references",
                  a.absolute_term_references);
        count_row("MPFR", "zero_bound_reference",
                  a.zero_bound_references);
        count_row("dd_lib", "zero_bound_error",
                  a.dd_lib.zero_bound_nonzero_error);
        count_row("QD", "zero_bound_error",
                  a.qd.zero_bound_nonzero_error);
        count_row("QD", "zero_bound_nonfinite",
                  a.qd_nonfinite_zero_bound);
        write_contract_witness_tsv(
            file, report.name, "dd_lib", "invalid_double_word",
            a.dd_lib_invalid_double_word,
            a.first_dd_lib_invalid_double_word, data_rows);
        write_contract_witness_tsv(
            file, report.name, "QD", "invalid_double_word",
            a.qd_invalid_double_word, a.first_qd_invalid_double_word,
            data_rows);
        write_error_witness_tsv(
            file, report.name, "QD", "nonfinite", a.qd_nonfinite,
            a.first_qd_nonfinite, data_rows);
        write_error_witness_tsv(
            file, report.name, "dd_lib", "zero_bound_error",
            a.dd_lib.zero_bound_nonzero_error,
            a.dd_lib.first_zero_bound_nonzero_error, data_rows);
        write_error_witness_tsv(
            file, report.name, "QD", "zero_bound_error",
            a.qd.zero_bound_nonzero_error,
            a.qd.first_zero_bound_nonzero_error, data_rows);
        write_bound_violations_tsv(
            file, report.name, "dd_lib", a.dd_lib.bound_violations,
            data_rows);
        write_bound_violations_tsv(
            file, report.name, "QD", a.qd.bound_violations, data_rows);
        write_metric_tsv(file, report.name, "dd_lib",
                         "relative_term_relative_error",
                         a.dd_lib.relative_term_relative, data_rows);
        write_metric_tsv(file, report.name, "QD",
                         "relative_term_relative_error",
                         a.qd.relative_term_relative, data_rows,
                         a.qd_nonfinite_relative_term,
                         "qd_nonfinite_in_regime");
        write_metric_tsv(
            file, report.name, "dd_lib",
            "relative_term_bound_utilization",
            a.dd_lib.relative_term_bound_utilization, data_rows,
            a.dd_lib.relative_term_bound_ratio_above_one,
            "bound_ratio_above_one");
        write_metric_tsv(
            file, report.name, "QD",
            "relative_term_bound_utilization",
            a.qd.relative_term_bound_utilization, data_rows,
            a.qd.relative_term_bound_ratio_above_one,
            "bound_ratio_above_one");
        write_metric_tsv(file, report.name, "dd_lib",
                         "absolute_term_absolute_error",
                         a.dd_lib.absolute_term_absolute, data_rows);
        write_metric_tsv(file, report.name, "QD",
                         "absolute_term_absolute_error",
                         a.qd.absolute_term_absolute, data_rows,
                         a.qd_nonfinite_absolute_term,
                         "qd_nonfinite_in_regime");
        write_metric_tsv(
            file, report.name, "dd_lib",
            "absolute_term_bound_utilization",
            a.dd_lib.absolute_term_bound_utilization, data_rows,
            a.dd_lib.absolute_term_bound_ratio_above_one,
            "bound_ratio_above_one");
        write_metric_tsv(
            file, report.name, "QD",
            "absolute_term_bound_utilization",
            a.qd.absolute_term_bound_utilization, data_rows,
            a.qd.absolute_term_bound_ratio_above_one,
            "bound_ratio_above_one");
        if (report.options.division_reference) {
            count_row("MPFR", "bound_rechecks",
                      a.higher_precision_bound_rechecks);
            count_row("MPFR", "bound_decision_changes",
                      a.higher_precision_bound_decision_changes);
        }
    }
    std::fprintf(file, "# data_rows=%zu\n", data_rows);
    std::fprintf(file, "# completed=true\n");
}

std::size_t parse_samples(int argc, char **argv) {
    if (argc > 3) {
        std::fprintf(stderr,
            "usage: %s [samples_per_exponent] [summary_tsv]\n", argv[0]);
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

void check_floating_point_environment() {
    if (sizeof(double) != sizeof(std::uint64_t)
        || !std::numeric_limits<double>::is_iec559
        || std::numeric_limits<double>::digits != 53) {
        std::fprintf(stderr, "RQ1 requires IEEE-754 binary64 arithmetic\n");
        std::exit(EXIT_FAILURE);
    }
    if (std::fegetround() != FE_TONEAREST) {
        std::fprintf(stderr, "RQ1 requires round-to-nearest\n");
        std::exit(EXIT_FAILURE);
    }
    volatile double normal_min = std::numeric_limits<double>::min();
    volatile double half = 0.5;
    volatile double subnormal = normal_min * half;
    if (subnormal == 0.0) {
        std::fprintf(stderr, "RQ1 requires gradual underflow\n");
        std::exit(EXIT_FAILURE);
    }
    volatile double eta = std::numeric_limits<double>::denorm_min();
    volatile double twice_eta = eta + eta;
    if (twice_eta == 0.0) {
        std::fprintf(stderr, "RQ1 requires subnormal input operands\n");
        std::exit(EXIT_FAILURE);
    }
}

void verify_report_inventory(const std::vector<OperationReport> &reports) {
    struct ExpectedOperation {
        const char *name;
        VerifiedBound bound;
        bool division_reference;
    };
    static const ExpectedOperation expected[] = {
        {"dw_plus_fp", VerifiedBound::dw_plus_fp, false},
        {"dw_times_fp", VerifiedBound::dw_times_fp, false},
        {"dw_div_fp", VerifiedBound::dw_div_fp, true},
        {"dw_plus_dw", VerifiedBound::dw_plus_dw, false},
        {"dw_times_dw", VerifiedBound::dw_times_dw, false},
        {"dw_div_dw", VerifiedBound::dw_div_dw, true}
    };
    if (reports.size() != sizeof(expected) / sizeof(expected[0])) std::abort();
    for (std::size_t i = 0; i < reports.size(); ++i) {
        const OperationReport &report = reports[i];
        const std::size_t outcome_total = report.outcomes.input_check
            + report.outcomes.post_computation + report.outcomes.normal;
        if (report.name == nullptr
            || std::string(report.name) != expected[i].name
            || report.options.bound_kind != expected[i].bound
            || report.options.division_reference
                != expected[i].division_reference
            || outcome_total != report.outcomes.generated
            || report.accuracy.compared != report.outcomes.normal) {
            std::abort();
        }
    }
}

bool dd_lib_checks_passed(const std::vector<OperationReport> &reports) {
    bool passed = true;
    for (const OperationReport &report : reports) {
        const AccuracyCounts &a = report.accuracy;
        if (a.dd_lib_invalid_double_word != 0
            || a.dd_lib.relative_term_bound_ratio_above_one != 0
            || a.dd_lib.absolute_term_bound_ratio_above_one != 0
            || a.dd_lib.zero_bound_nonzero_error != 0) {
            passed = false;
        }
    }
    return passed;
}

}  // namespace

int main(int argc, char **argv) {
    const std::size_t samples_per_exponent = parse_samples(argc, argv);
    check_floating_point_environment();
    bench_eval::verify_error_regime_classifier();

    GeneratedTestInputs inputs =
        bench_eval::make_generated_test_inputs(samples_per_exponent);
    const std::size_t mixed_count = inputs.mixed_dw.size();
    const std::size_t dw_count = inputs.dw_first.size();
    if (inputs.mixed_fp.size() != mixed_count
        || inputs.dw_second.size() != dw_count) {
        std::abort();
    }

    auto describe_mixed = [&](std::size_t i) {
        return bench_eval::describe_inputs(inputs.mixed_dw[i],
                                           inputs.mixed_fp[i]);
    };
    auto describe_dw = [&](std::size_t i) {
        return bench_eval::describe_inputs(inputs.dw_first[i],
                                           inputs.dw_second[i]);
    };

    std::vector<OperationReport> reports;
    reports.reserve(6);

    reports.push_back(evaluate_operation(
        "dw_plus_fp", mixed_count,
        [&](std::size_t i) {
            return dw_plus_fp_weak_precond_check(&inputs.mixed_dw[i].value,
                                                 inputs.mixed_fp[i].value);
        },
        [&](std::size_t i) {
            dword result;
            dw_plus_fp(&result, &inputs.mixed_dw[i].value,
                       inputs.mixed_fp[i].value);
            return ResultPair{result.s, result.t};
        },
        [&](std::size_t i) {
            dd_real input(inputs.mixed_dw[i].value.s,
                          inputs.mixed_dw[i].value.t);
            dd_real result = input + inputs.mixed_fp[i].value;
            return ResultPair{result.x[0], result.x[1]};
        },
        [&](std::size_t i, mpfr_ptr reference, mpfr_ptr first,
            mpfr_ptr second, mpfr_ptr scratch) {
            bench_eval::set_dword_value(first, inputs.mixed_dw[i].value,
                                        scratch);
            mpfr_set_d(second, inputs.mixed_fp[i].value, MPFR_RNDN);
            mpfr_add(reference, first, second, MPFR_RNDN);
        }, describe_mixed,
        operation_options(VerifiedBound::dw_plus_fp)));

    reports.push_back(evaluate_operation(
        "dw_times_fp", mixed_count,
        [&](std::size_t i) {
            return dw_times_fp_weak_precond_check(&inputs.mixed_dw[i].value,
                                                  inputs.mixed_fp[i].value);
        },
        [&](std::size_t i) {
            dword result;
            dw_times_fp(&result, &inputs.mixed_dw[i].value,
                        inputs.mixed_fp[i].value);
            return ResultPair{result.s, result.t};
        },
        [&](std::size_t i) {
            dd_real input(inputs.mixed_dw[i].value.s,
                          inputs.mixed_dw[i].value.t);
            dd_real result = input * inputs.mixed_fp[i].value;
            return ResultPair{result.x[0], result.x[1]};
        },
        [&](std::size_t i, mpfr_ptr reference, mpfr_ptr first,
            mpfr_ptr second, mpfr_ptr scratch) {
            bench_eval::set_dword_value(first, inputs.mixed_dw[i].value,
                                        scratch);
            mpfr_set_d(second, inputs.mixed_fp[i].value, MPFR_RNDN);
            mpfr_mul(reference, first, second, MPFR_RNDN);
        }, describe_mixed,
        operation_options(VerifiedBound::dw_times_fp)));

    reports.push_back(evaluate_operation(
        "dw_div_fp", mixed_count,
        [&](std::size_t i) {
            return dw_div_fp_weak_precond_check(&inputs.mixed_dw[i].value,
                                                inputs.mixed_fp[i].value);
        },
        [&](std::size_t i) {
            dword result;
            dw_div_fp(&result, &inputs.mixed_dw[i].value,
                      inputs.mixed_fp[i].value);
            return ResultPair{result.s, result.t};
        },
        [&](std::size_t i) {
            dd_real input(inputs.mixed_dw[i].value.s,
                          inputs.mixed_dw[i].value.t);
            dd_real result = input / inputs.mixed_fp[i].value;
            return ResultPair{result.x[0], result.x[1]};
        },
        [&](std::size_t i, mpfr_ptr reference, mpfr_ptr first,
            mpfr_ptr second, mpfr_ptr scratch) {
            bench_eval::set_dword_value(first, inputs.mixed_dw[i].value,
                                        scratch);
            mpfr_set_d(second, inputs.mixed_fp[i].value, MPFR_RNDN);
            mpfr_div(reference, first, second, MPFR_RNDN);
        }, describe_mixed,
        operation_options(VerifiedBound::dw_div_fp, true)));

    reports.push_back(evaluate_operation(
        "dw_plus_dw", dw_count,
        [&](std::size_t i) {
            return dw_plus_dw_weak_precond_check(&inputs.dw_first[i].value,
                                                 &inputs.dw_second[i].value);
        },
        [&](std::size_t i) {
            dword result;
            dw_plus_dw(&result, &inputs.dw_first[i].value,
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
            bench_eval::set_dword_value(first, inputs.dw_first[i].value,
                                        scratch);
            bench_eval::set_dword_value(second, inputs.dw_second[i].value,
                                        scratch);
            mpfr_add(reference, first, second, MPFR_RNDN);
        }, describe_dw,
        operation_options(VerifiedBound::dw_plus_dw)));

    reports.push_back(evaluate_operation(
        "dw_times_dw", dw_count,
        [&](std::size_t i) {
            return dw_times_dw_weak_precond_check(&inputs.dw_first[i].value,
                                                  &inputs.dw_second[i].value);
        },
        [&](std::size_t i) {
            dword result;
            dw_times_dw(&result, &inputs.dw_first[i].value,
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
            bench_eval::set_dword_value(first, inputs.dw_first[i].value,
                                        scratch);
            bench_eval::set_dword_value(second, inputs.dw_second[i].value,
                                        scratch);
            mpfr_mul(reference, first, second, MPFR_RNDN);
        }, describe_dw,
        operation_options(VerifiedBound::dw_times_dw)));

    reports.push_back(evaluate_operation(
        "dw_div_dw", dw_count,
        [&](std::size_t i) {
            return dw_div_dw_weak_precond_check(&inputs.dw_first[i].value,
                                                &inputs.dw_second[i].value);
        },
        [&](std::size_t i) {
            dword result;
            dw_div_dw(&result, &inputs.dw_first[i].value,
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
            bench_eval::set_dword_value(first, inputs.dw_first[i].value,
                                        scratch);
            bench_eval::set_dword_value(second, inputs.dw_second[i].value,
                                        scratch);
            mpfr_div(reference, first, second, MPFR_RNDN);
        }, describe_dw,
        operation_options(VerifiedBound::dw_div_dw, true)));

    verify_report_inventory(reports);
    print_reports(inputs, samples_per_exponent, reports);
    if (argc == 3) {
        std::FILE *file = std::fopen(argv[2], "w");
        if (file == nullptr) {
            std::perror(argv[2]);
            return EXIT_FAILURE;
        }
        write_summary_tsv(file, inputs, samples_per_exponent, reports);
        if (std::fclose(file) != 0) {
            std::perror(argv[2]);
            return EXIT_FAILURE;
        }
    }
    if (!dd_lib_checks_passed(reports)) {
        std::fprintf(stderr, "one or more returned dd_lib results failed "
                             "their MPFR-measured checks\n");
        return EXIT_FAILURE;
    }
    return EXIT_SUCCESS;
}
