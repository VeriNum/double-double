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

constexpr std::size_t known_status_count = 4;

struct Cell {
    std::array<std::size_t, known_status_count> statuses{{}};
    std::size_t other_status = 0;
    std::size_t no_status = 0;
    std::size_t total_cases = 0;
    std::size_t rejected_cases = 0;
    std::size_t qd_nonfinite = 0;
    std::size_t qd_invalid = 0;
    std::size_t qd_no_reference = 0;
    std::size_t qd_failed = 0;
    std::size_t qd_passed = 0;
    std::size_t qd_bound_checks = 0;
    std::size_t qd_unresolved_bounds = 0;
    std::size_t other_successful = 0;
    std::size_t other_rejected = 0;
    std::size_t other_unexpected_status = 0;
};

struct OperationResults {
    Cell default_path;
    Cell strong_path;
    Cell either_path;
};

struct Results {
    std::array<OperationResults, 9> operations;
};

bool is_success(const WrapperStatus &status,
                const OperationSpec &operation) {
    if (!operation.returns_status) return !status.present;
    return status.present && status.code == status_ok;
}

bool is_rejected(const WrapperStatus &status,
                 const OperationSpec &operation,
                 bool strong_path) {
    if (!operation.returns_status || !status.present) return false;
    if (operation.eft) {
        return status.code == status_weak_input_rejected;
    }
    if (strong_path) {
        return status.code == status_strong_input_rejected;
    }
    return status.code == status_weak_input_rejected
        || status.code == status_post_check_rejected;
}

void count_status(Cell &cell, const WrapperStatus &status) {
    if (!status.present) {
        ++cell.no_status;
    } else if (status.code >= status_ok
               && status.code <= status_strong_input_rejected) {
        ++cell.statuses[static_cast<std::size_t>(status.code)];
    } else {
        ++cell.other_status;
    }
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

void accumulate_path(Cell &cell, const WrapperStatus &status,
                     const OperationSpec &operation, bool strong_path,
                     const ResultFacts &qd) {
    ++cell.total_cases;
    count_status(cell, status);
    if (!is_rejected(status, operation, strong_path)) return;
    ++cell.rejected_cases;
    classify_qd(cell, operation, qd);
}

void accumulate_other_path(Cell &cell, const WrapperStatus &status,
                           const OperationSpec &operation,
                           bool strong_path) {
    if (is_success(status, operation)) {
        ++cell.other_successful;
    } else if (is_rejected(status, operation, strong_path)) {
        ++cell.other_rejected;
    } else {
        ++cell.other_unexpected_status;
    }
}

void accept_case(const OperationSpec &operation,
                 const NumericalCase &data, Results &results) {
    OperationResults &result = results.operations[data.operation_index];
    accumulate_path(result.default_path, data.default_status,
                    operation, false, data.qd.facts);
    if (operation.eft) return;

    accumulate_path(result.strong_path, data.strong_status,
                    operation, true, data.qd.facts);
    const bool default_rejected =
        is_rejected(data.default_status, operation, false);
    const bool strong_rejected =
        is_rejected(data.strong_status, operation, true);
    ++result.either_path.total_cases;
    if (default_rejected || strong_rejected) {
        ++result.either_path.rejected_cases;
        classify_qd(result.either_path, operation, data.qd.facts);
    }
    if (default_rejected) {
        accumulate_other_path(result.default_path, data.strong_status,
                              operation, true);
    }
    if (strong_rejected) {
        accumulate_other_path(result.strong_path, data.default_status,
                              operation, false);
    }
}

std::size_t successful_cases(const Cell &cell,
                             const OperationSpec &operation) {
    return operation.returns_status
        ? cell.statuses[static_cast<std::size_t>(status_ok)]
        : cell.no_status;
}

std::size_t unexpected_statuses(const Cell &cell,
                                const OperationSpec &operation) {
    return cell.total_cases - successful_cases(cell, operation)
        - cell.rejected_cases;
}

void write_path(std::ostream &file, const OperationSpec &operation,
                const char *path_name, const char *criterion,
                const Cell &cell) {
    const std::size_t classified = cell.qd_nonfinite + cell.qd_invalid
        + cell.qd_no_reference + cell.qd_failed + cell.qd_passed
        + cell.qd_unresolved_bounds;
    if (classified != cell.rejected_cases) {
        throw Error(std::string(operation.name)
                    + " has a bad count for question two");
    }
    if (!operation.eft
        && cell.other_successful + cell.other_rejected
               + cell.other_unexpected_status != cell.rejected_cases) {
        throw Error(std::string(operation.name)
                    + " has a bad path count for question two");
    }
    file << operation.name << '\t' << path_name << '\t' << criterion
         << '\t' << analysis_precision << '\t' << check_precision
         << '\t' << cell.total_cases
         << '\t' << successful_cases(cell, operation)
         << '\t' << cell.statuses[0]
         << '\t' << cell.statuses[1]
         << '\t' << cell.statuses[2]
         << '\t' << cell.statuses[3]
         << '\t' << cell.other_status
         << '\t' << cell.no_status
         << '\t' << cell.rejected_cases
         << '\t' << unexpected_statuses(cell, operation);
    if (operation.eft) {
        file << "\t-\t-\t-";
    } else {
        file << '\t' << cell.other_successful
             << '\t' << cell.other_rejected
             << '\t' << cell.other_unexpected_status;
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
         << "\t-\t-\t-\t-\t-\t-\t-"
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
            "\tcheck_precision_bits\ttotal_cases\tsuccessful_cases"
            "\tstatus_0\tstatus_1\tstatus_2\tstatus_3"
            "\tother_status\tno_status\trejected_cases"
            "\tunexpected_statuses\tother_wrapper_successful"
            "\tother_wrapper_rejected\tother_wrapper_unexpected_status"
            "\tqd_nonfinite"
            "\tqd_invalid_double_word\tqd_no_reference\tqd_failed"
            "\tqd_passed\tqd_bound_checks\tqd_unresolved_bounds\n";

    for (std::size_t i = 0; i < operations.size(); ++i) {
        const OperationSpec &operation = operations[i];
        const OperationResults &result = results.operations[i];
        write_path(file, operation, "default",
                   operation.eft ? "exact_reconstruction" : "error_bound",
                   result.default_path);
        if (!operation.eft) {
            write_path(file, operation, "strong", "error_bound",
                       result.strong_path);
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
