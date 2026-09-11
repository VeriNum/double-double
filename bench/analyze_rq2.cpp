// Analyze rejection and QD data for research question two.

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

constexpr std::size_t outcome_count = 8;

struct Cell {
    std::array<std::size_t, outcome_count> outcomes{{}};
    std::size_t total_cases = 0;
    std::size_t rejected_cases = 0;
    std::size_t qd_nonfinite = 0;
    std::size_t qd_invalid = 0;
    std::size_t qd_no_reference = 0;
    std::size_t qd_failed = 0;
    std::size_t qd_passed = 0;
    std::size_t qd_bound_checks = 0;
    std::size_t qd_unresolved_bounds = 0;
    std::size_t other_normal = 0;
    std::size_t other_rejected = 0;
    std::size_t other_unexpected = 0;
};

struct OperationResults {
    Cell default_path;
    Cell strong_path;
    Cell either_path;
};

struct Results {
    std::array<OperationResults, 9> operations;
};

std::size_t outcome_index(Outcome outcome) {
    return static_cast<std::size_t>(outcome);
}

bool is_rejected(Outcome outcome, const OperationSpec &operation,
                 bool strong_path) {
    if (operation.eft) return outcome == Outcome::input_check;
    if (strong_path) {
        return outcome == Outcome::weak_input_check
            || outcome == Outcome::strong_check;
    }
    return outcome == Outcome::weak_input_check
        || outcome == Outcome::post_check;
}

void classify_qd(Cell &cell, const OperationSpec &operation,
                 const ResultFacts &qd) {
    if (!qd.finite) {
        ++cell.qd_nonfinite;
    } else if (!qd.valid_double_word) {
        ++cell.qd_invalid;
    } else if (!qd.has_error) {
        ++cell.qd_no_reference;
    } else if (operation.eft) {
        if (qd.exact) ++cell.qd_passed;
        else ++cell.qd_failed;
    } else if (qd.bound_is_unresolved) {
        if (qd.bound_was_checked) ++cell.qd_bound_checks;
        ++cell.qd_unresolved_bounds;
    } else {
        if (qd.bound_was_checked) ++cell.qd_bound_checks;
        if (qd.bound_compare > 0) ++cell.qd_failed;
        else ++cell.qd_passed;
    }
}

void accumulate_path(Cell &cell, Outcome outcome,
                     const OperationSpec &operation, bool strong_path,
                     const ResultFacts &qd) {
    ++cell.total_cases;
    ++cell.outcomes[outcome_index(outcome)];
    if (!is_rejected(outcome, operation, strong_path)) return;
    ++cell.rejected_cases;
    classify_qd(cell, operation, qd);
}

void accumulate_other_path(Cell &cell, Outcome outcome,
                           const OperationSpec &operation,
                           bool strong_path) {
    if (outcome == Outcome::normal) {
        ++cell.other_normal;
    } else if (is_rejected(outcome, operation, strong_path)) {
        ++cell.other_rejected;
    } else {
        ++cell.other_unexpected;
    }
}

void accept_case(const OperationSpec &operation,
                 const NumericalCase &data, Results &results) {
    OperationResults &result = results.operations[data.operation_index];
    accumulate_path(result.default_path, data.default_outcome,
                    operation, false, data.qd.facts);
    if (operation.eft) return;

    accumulate_path(result.strong_path, data.strong_outcome,
                    operation, true, data.qd.facts);
    const bool default_rejected =
        is_rejected(data.default_outcome, operation, false);
    const bool strong_rejected =
        is_rejected(data.strong_outcome, operation, true);
    ++result.either_path.total_cases;
    if (default_rejected || strong_rejected) {
        ++result.either_path.rejected_cases;
        classify_qd(result.either_path, operation, data.qd.facts);
    }
    if (default_rejected) {
        accumulate_other_path(result.default_path, data.strong_outcome,
                              operation, true);
    }
    if (strong_rejected) {
        accumulate_other_path(result.strong_path, data.default_outcome,
                              operation, false);
    }
}

std::size_t unexpected_outcomes(const Cell &cell,
                                const OperationSpec &operation,
                                bool strong_path) {
    std::size_t expected = cell.outcomes[outcome_index(Outcome::normal)];
    for (std::size_t i = 0; i < outcome_count; ++i) {
        const Outcome outcome = static_cast<Outcome>(i);
        if (is_rejected(outcome, operation, strong_path)) {
            expected += cell.outcomes[i];
        }
    }
    return cell.total_cases - expected;
}

void write_path(std::ostream &file, const OperationSpec &operation,
                const char *path_name, const char *criterion,
                const Cell &cell, bool strong_path) {
    const std::size_t classified = cell.qd_nonfinite + cell.qd_invalid
        + cell.qd_no_reference + cell.qd_failed + cell.qd_passed
        + cell.qd_unresolved_bounds;
    if (classified != cell.rejected_cases) {
        throw Error(std::string(operation.name)
                    + " has a bad count for question two");
    }
    if (!operation.eft
        && cell.other_normal + cell.other_rejected + cell.other_unexpected
               != cell.rejected_cases) {
        throw Error(std::string(operation.name)
                    + " has a bad path count for question two");
    }
    file << operation.name << '\t' << path_name << '\t' << criterion
         << '\t' << analysis_precision << '\t' << check_precision
         << '\t' << cell.total_cases
         << '\t' << cell.outcomes[outcome_index(Outcome::normal)]
         << '\t' << cell.outcomes[outcome_index(Outcome::input_check)]
         << '\t' << cell.outcomes[outcome_index(Outcome::weak_input_check)]
         << '\t' << cell.outcomes[outcome_index(Outcome::post_check)]
         << '\t' << cell.outcomes[outcome_index(Outcome::strong_check)]
         << '\t' << cell.outcomes[outcome_index(Outcome::execution_exit)]
         << '\t' << cell.outcomes[outcome_index(Outcome::unclassified)]
         << '\t' << cell.outcomes[outcome_index(Outcome::not_available)]
         << '\t' << cell.rejected_cases
         << '\t' << unexpected_outcomes(cell, operation, strong_path);
    if (operation.eft) {
        file << "\t-\t-\t-";
    } else {
        file << '\t' << cell.other_normal
             << '\t' << cell.other_rejected
             << '\t' << cell.other_unexpected;
    }
    file << '\t' << cell.qd_nonfinite
         << '\t' << cell.qd_invalid
         << '\t' << cell.qd_no_reference
         << '\t' << cell.qd_failed
         << '\t' << cell.qd_passed
         << '\t' << cell.qd_bound_checks
         << '\t' << cell.qd_unresolved_bounds << '\n';
}

void write_either(std::ostream &file, const OperationSpec &operation,
                  const Cell &cell) {
    const std::size_t classified = cell.qd_nonfinite + cell.qd_invalid
        + cell.qd_no_reference + cell.qd_failed + cell.qd_passed
        + cell.qd_unresolved_bounds;
    if (classified != cell.rejected_cases) {
        throw Error(std::string(operation.name)
                    + " has a bad union count for question two");
    }
    file << operation.name << "\teither\terror_bound"
         << '\t' << analysis_precision << '\t' << check_precision
         << '\t' << cell.total_cases
         << "\t-\t-\t-\t-\t-\t-\t-\t-"
         << '\t' << cell.rejected_cases
         << "\t-\t-\t-\t-"
         << '\t' << cell.qd_nonfinite
         << '\t' << cell.qd_invalid
         << '\t' << cell.qd_no_reference
         << '\t' << cell.qd_failed
         << '\t' << cell.qd_passed
         << '\t' << cell.qd_bound_checks
         << '\t' << cell.qd_unresolved_bounds << '\n';
}

void write_results(const std::string &path, const Results &results) {
    std::ofstream file(path);
    file.imbue(std::locale::classic());
    if (!file) throw Error("could not open " + path);
    file << "operation\twrapper\tcriterion\tprecision_bits"
            "\tcheck_precision_bits\ttotal_cases\tnormal_returns"
            "\tinput_check\tweak_input_check\tpost_check\tstrong_check"
            "\texecution_exit\tunclassified\tnot_available"
            "\trejected_cases\tunexpected_outcomes\tother_wrapper_normal"
            "\tother_wrapper_rejected\tother_wrapper_unexpected\tqd_nonfinite"
            "\tqd_invalid_double_word\tqd_no_reference\tqd_failed"
            "\tqd_passed\tqd_bound_checks\tqd_unresolved_bounds\n";

    for (std::size_t i = 0; i < operations.size(); ++i) {
        const OperationSpec &operation = operations[i];
        const OperationResults &result = results.operations[i];
        write_path(file, operation, "default",
                   operation.eft ? "exact_reconstruction" : "error_bound",
                   result.default_path, false);
        if (!operation.eft) {
            write_path(file, operation, "strong", "error_bound",
                       result.strong_path, true);
            write_either(file, operation, result.either_path);
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
        std::fprintf(stderr, "usage: %s numerical.tsv rq2.tsv\n", argv[0]);
        return EXIT_FAILURE;
    }
    std::setlocale(LC_NUMERIC, "C");
    try {
        analyze(argv[1], argv[2]);
    } catch (const std::exception &error) {
        std::fprintf(stderr, "RQ2 analysis failed: %s\n", error.what());
        return EXIT_FAILURE;
    }
    return EXIT_SUCCESS;
}
