// Analyze error and bound data for research question one.

#include "numerical_analysis.hpp"

#include <array>
#include <clocale>
#include <cstdio>
#include <cstdlib>
#include <exception>
#include <fstream>
#include <locale>
#include <string>

namespace {

using namespace bench_analysis;

const std::array<const char *, 3> regime_names{{
    "relative", "absolute", "zero_bound",
}};

// Hold a sum and a maximum without changing precision.
class Metric {
public:
    Metric() {
        mpfr_set_zero(sum_.get(), 0);
        mpfr_set_zero(maximum_.get(), 0);
    }

    void add(mpfr_srcptr value, std::size_t case_id) {
        mpfr_add(sum_.get(), sum_.get(), value, MPFR_RNDN);
        ++count_;
        if (!has_maximum_ || mpfr_greater_p(value, maximum_.get())) {
            mpfr_set(maximum_.get(), value, MPFR_RNDN);
            maximum_case_ = case_id;
            has_maximum_ = true;
        }
    }

    std::size_t count() const { return count_; }
    mpfr_srcptr sum() const { return sum_.get(); }
    mpfr_srcptr maximum() const { return maximum_.get(); }
    std::size_t maximum_case() const { return maximum_case_; }

private:
    std::size_t count_ = 0;
    bool has_maximum_ = false;
    std::size_t maximum_case_ = 0;
    Real sum_;
    Real maximum_;
};

struct Cell {
    std::size_t cases = 0;
    std::size_t finite_results = 0;
    std::size_t nonfinite_results = 0;
    std::size_t invalid_double_words = 0;
    std::size_t values_without_error = 0;
    std::size_t finite_above_bound = 0;
    std::size_t bound_checks = 0;
    std::size_t unresolved_bounds = 0;
    Metric error;
    Metric bound_ratio;
};

struct OperationResults {
    std::size_t eligible_cases = 0;
    std::array<std::array<Cell, 3>, 2> cells;
};

struct Results {
    std::array<OperationResults, 9> operations;
};

void add_result(Cell &cell, const ResultView &result,
                ErrorRegime regime, std::size_t case_id) {
    const ResultFacts &facts = result.facts;
    ++cell.cases;
    if (!facts.finite) {
        ++cell.nonfinite_results;
        return;
    }

    ++cell.finite_results;
    if (!facts.valid_double_word) ++cell.invalid_double_words;
    if (!facts.has_error) {
        ++cell.values_without_error;
        return;
    }

    if (regime == ErrorRegime::relative) {
        if (facts.has_relative_error) {
            cell.error.add(result.relative_error, case_id);
        } else {
            ++cell.values_without_error;
        }
    } else {
        cell.error.add(result.error, case_id);
    }

    if (facts.has_bound_ratio) {
        cell.bound_ratio.add(result.bound_ratio, case_id);
    }
    if (facts.bound_was_checked) ++cell.bound_checks;
    if (facts.bound_is_unresolved) {
        ++cell.unresolved_bounds;
    } else if (facts.bound_compare > 0) {
        ++cell.finite_above_bound;
    }
}

void accept_case(const OperationSpec &operation,
                 const NumericalCase &data, Results &results) {
    if (operation.eft || data.default_outcome != Outcome::normal) return;
    OperationResults &result = results.operations[data.operation_index];
    ++result.eligible_cases;
    const std::size_t regime = static_cast<std::size_t>(data.regime);
    add_result(result.cells[0][regime], data.fencedd,
               data.regime, data.case_id);
    add_result(result.cells[1][regime], data.qd,
               data.regime, data.case_id);
}

void write_metric(std::ostream &file, const Metric &metric) {
    file << '\t' << metric.count();
    if (metric.count() == 0) {
        file << "\t-\t-\t-\t-";
        return;
    }
    Real mean;
    mpfr_div_ui(mean.get(), metric.sum(), metric.count(), MPFR_RNDN);
    file << '\t' << format_real(metric.sum())
         << '\t' << format_real(mean.get())
         << '\t' << format_real(metric.maximum())
         << '\t' << metric.maximum_case();
}

void write_results(const std::string &path, const Results &results) {
    std::ofstream file(path);
    file.imbue(std::locale::classic());
    if (!file) throw Error("could not open " + path);
    file << "operation\timplementation\tregime\tprecision_bits"
            "\tcheck_precision_bits\teligible_cases"
            "\tregime_cases\tfinite_results\tnonfinite_results"
            "\tinvalid_double_words\tvalues_without_error\terror_measure"
            "\tfinite_error_count\tfinite_error_sum\tfinite_error_mean"
            "\tfinite_error_max\tfinite_error_max_case_id"
            "\tfinite_bound_ratio_count\tfinite_bound_ratio_sum"
            "\tfinite_bound_ratio_mean\tfinite_bound_ratio_max"
            "\tfinite_bound_ratio_max_case_id\tnot_within_bound"
            "\tfinite_above_bound\tbound_checks\tunresolved_bounds\n";

    for (std::size_t operation_index = 0;
         operation_index < operations.size(); ++operation_index) {
        const OperationSpec &operation = operations[operation_index];
        if (operation.eft) continue;
        const OperationResults &result = results.operations[operation_index];
        for (std::size_t implementation = 0; implementation < 2;
             ++implementation) {
            for (std::size_t regime = 0; regime < regime_names.size();
                 ++regime) {
                const Cell &cell = result.cells[implementation][regime];
                const char *error_measure = regime == 0
                    ? "relative_error" : "absolute_error";
                file << operation.name << '\t'
                     << (implementation == 0 ? "fencedd" : "qd") << '\t'
                     << regime_names[regime] << '\t'
                     << analysis_precision << '\t' << check_precision << '\t'
                     << result.eligible_cases << '\t'
                     << cell.cases << '\t'
                     << cell.finite_results << '\t'
                     << cell.nonfinite_results << '\t'
                     << cell.invalid_double_words << '\t'
                     << cell.values_without_error << '\t'
                     << error_measure;
                write_metric(file, cell.error);
                write_metric(file, cell.bound_ratio);
                file << '\t'
                     << cell.nonfinite_results + cell.finite_above_bound
                            + cell.unresolved_bounds
                     << '\t' << cell.finite_above_bound
                     << '\t' << cell.bound_checks
                     << '\t' << cell.unresolved_bounds << '\n';
            }
        }
    }
    file.close();
    check_output(file, path);
}

void analyze(const std::string &input, const std::string &output) {
    check_environment();
    check_file_paths({input, output}, 1);
    Results results;
    read_numerical_data(
        input,
        [&results](const OperationSpec &operation,
                   const NumericalCase &data) {
            accept_case(operation, data, results);
        });
    write_results(output, results);
}

}  // namespace

int main(int argc, char **argv) {
    if (argc != 3) {
        std::fprintf(stderr, "usage: %s numerical.tsv rq1.tsv\n", argv[0]);
        return EXIT_FAILURE;
    }
    std::setlocale(LC_NUMERIC, "C");
    try {
        analyze(argv[1], argv[2]);
    } catch (const std::exception &error) {
        std::fprintf(stderr, "RQ1 analysis failed: %s\n", error.what());
        return EXIT_FAILURE;
    }
    return EXIT_SUCCESS;
}
