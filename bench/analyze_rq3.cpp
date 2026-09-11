// Analyze performance data for research question three.

#include "analysis_common.hpp"

#include <algorithm>
#include <array>
#include <clocale>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <exception>
#include <fstream>
#include <iomanip>
#include <locale>
#include <map>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

namespace {

using namespace bench_analysis;

const char timing_header[] =
    "operation\timplementation\tinterface\ttrial\tns_per_call";

enum class TimingValue {
    default_path,
    strong_path,
    kernel,
    qd,
};

constexpr std::size_t timing_value_count = 4;

struct TimingSeries {
    std::vector<double> values;
    std::vector<bool> seen;
};

struct TimingData {
    std::string build;
    std::size_t input_count = 0;
    std::size_t trial_count = 0;
    std::string input_fingerprint;
    std::size_t row_count = 0;
    std::array<std::array<TimingSeries, timing_value_count>, 9> series;
};

struct TimingSummary {
    double median;
    double first_quartile;
    double third_quartile;
};

std::pair<std::string, std::string> parse_meta(
        const std::string &line, const std::string &path,
        std::size_t line_number) {
    if (line.size() < 4 || line[0] != '#' || line[1] != ' ') {
        fail(path, line_number, "meta row is not valid");
    }
    const std::size_t equal = line.find('=', 2);
    if (equal == std::string::npos || equal == 2
        || equal + 1 == line.size()) {
        fail(path, line_number, "meta row is not valid");
    }
    return std::make_pair(line.substr(2, equal - 2), line.substr(equal + 1));
}

double parse_time(const std::string &text, const std::string &path,
                  std::size_t line) {
    std::istringstream input(text);
    input.imbue(std::locale::classic());
    double value = 0.0;
    input >> value;
    if (!input || !input.eof() || !std::isfinite(value) || value <= 0.0) {
        fail(path, line, "time value is not valid");
    }
    return value;
}

TimingValue parse_timing_value(const std::string &implementation,
                               const std::string &interface_name,
                               const OperationSpec &operation,
                               const std::string &path,
                               std::size_t line) {
    if (implementation == "fenceDD" && interface_name == "default") {
        return TimingValue::default_path;
    }
    if (implementation == "fenceDD" && interface_name == "strong") {
        if (operation.eft) fail(path, line, "strong time is not valid here");
        return TimingValue::strong_path;
    }
    if (implementation == "fenceDD" && interface_name == "kernel") {
        return TimingValue::kernel;
    }
    if (implementation == "QD" && interface_name == "reference") {
        return TimingValue::qd;
    }
    fail(path, line, "time form is not known");
}

void prepare_series(TimingData &data) {
    for (std::size_t operation = 0; operation < operations.size();
         ++operation) {
        for (std::size_t value = 0; value < timing_value_count; ++value) {
            TimingSeries &series = data.series[operation][value];
            series.values.assign(data.trial_count, 0.0);
            series.seen.assign(data.trial_count, false);
        }
    }
}

const std::string &require_meta(
        const std::map<std::string, std::string> &meta,
        const std::string &key, const std::string &path) {
    const auto found = meta.find(key);
    if (found == meta.end()) {
        throw Error(path + ": meta value " + key + " is missing");
    }
    return found->second;
}

void require_meta_value(const std::map<std::string, std::string> &meta,
                        const std::string &key,
                        const std::string &value,
                        const std::string &path) {
    if (require_meta(meta, key, path) != value) {
        throw Error(path + ": meta value " + key + " is not valid");
    }
}

void check_meta(const std::map<std::string, std::string> &meta,
                const std::string &path,
                const std::string &expected_build,
                std::size_t line_number,
                TimingData &data) {
    if (meta.size() != 11) throw Error(path + ": meta set is not valid");
    require_meta_value(meta, "rq3_schema_version", "4", path);
    require_meta_value(meta, "build", expected_build, path);
    require_meta_value(
        meta, "composite_interfaces", "default:two-stage,strong:input-only",
        path);
    require_meta_value(
        meta, "exact_transform_interface", "default:guarded", path);
    require_meta_value(
        meta, "quantile", "linear_interpolation_p_times_n_minus_1", path);
    require_meta_value(meta, "exact_schedule", "all_six_permutations", path);
    require_meta_value(
        meta, "composite_schedule", "all_twenty_four_permutations", path);
    require_meta_value(meta, "timer", "std_chrono_steady_clock", path);

    data.build = require_meta(meta, "build", path);
    data.input_count = parse_size(
        require_meta(meta, "input_count", path), path, line_number,
        "input_count");
    data.trial_count = parse_size(
        require_meta(meta, "trial_count", path), path, line_number,
        "trial_count");
    data.input_fingerprint = require_meta(meta, "input_fingerprint", path);
    parse_bits(data.input_fingerprint, path, line_number, "input_fingerprint");
    if (data.input_count == 0 || data.trial_count == 0) {
        fail(path, line_number, "time counts must be positive");
    }
    if (data.trial_count % 24 != 0) {
        fail(path, line_number, "trial count does not cover the full order");
    }
}

TimingData read_timing_file(const std::string &path,
                            const std::string &expected_build) {
    std::ifstream file(path);
    file.imbue(std::locale::classic());
    if (!file) throw Error("could not open " + path);

    std::map<std::string, std::string> meta;
    TimingData data;
    bool saw_header = false;
    int footer_part = 0;
    std::string line;
    std::size_t line_number = 0;
    while (std::getline(file, line)) {
        ++line_number;
        trim_carriage_return(line);
        if (line.empty()) fail(path, line_number, "empty row is not valid");
        if (line[0] == '#') {
            const auto item = parse_meta(line, path, line_number);
            if (saw_header) {
                const char *expected = footer_part == 0
                    ? "data_rows" : footer_part == 1 ? "completed" : "";
                if (item.first != expected) {
                    fail(path, line_number, "end row is out of order");
                }
                ++footer_part;
            } else if (item.first == "data_rows"
                       || item.first == "completed") {
                fail(path, line_number, "end row appears before the data");
            }
            if (!meta.insert(item).second) {
                fail(path, line_number, "meta name is repeated");
            }
            continue;
        }
        if (!saw_header) {
            if (line != timing_header) {
                fail(path, line_number, "header is not valid");
            }
            saw_header = true;
            check_meta(meta, path, expected_build, line_number, data);
            prepare_series(data);
            continue;
        }
        if (footer_part != 0) {
            fail(path, line_number, "data follows the end rows");
        }

        const std::vector<std::string> fields = split_tabs(line);
        if (fields.size() != 5) {
            fail(path, line_number, "time row must have 5 fields");
        }
        std::size_t operation_index = 0;
        const OperationSpec &operation =
            find_operation(fields[0], operation_index, path, line_number);
        const TimingValue value = parse_timing_value(
            fields[1], fields[2], operation, path, line_number);
        const std::size_t trial =
            parse_size(fields[3], path, line_number, "trial");
        if (trial >= data.trial_count) {
            fail(path, line_number, "trial is too large");
        }
        TimingSeries &series =
            data.series[operation_index][static_cast<std::size_t>(value)];
        if (series.seen[trial]) {
            fail(path, line_number, "time row is repeated");
        }
        series.values[trial] = parse_time(fields[4], path, line_number);
        series.seen[trial] = true;
        ++data.row_count;
    }
    if (file.bad()) throw Error("could not read " + path);
    if (!saw_header) throw Error(path + ": header is missing");
    if (footer_part != 2 || meta.size() != 13) {
        throw Error(path + ": end rows are missing");
    }
    require_meta_value(meta, "completed", "true", path);
    const std::size_t stated_rows = parse_size(
        require_meta(meta, "data_rows", path), path, line_number,
        "data_rows");
    if (stated_rows != data.row_count) {
        throw Error(path + ": time row count does not match");
    }

    for (std::size_t operation = 0; operation < operations.size();
         ++operation) {
        for (std::size_t value = 0; value < timing_value_count; ++value) {
            const bool required = value != static_cast<std::size_t>(
                TimingValue::strong_path) || !operations[operation].eft;
            const TimingSeries &series = data.series[operation][value];
            const bool any = std::find(series.seen.begin(), series.seen.end(),
                                       true) != series.seen.end();
            const bool all = std::find(series.seen.begin(), series.seen.end(),
                                       false) == series.seen.end();
            if ((required && !all) || (!required && any)) {
                throw Error(path + ": time series is not complete");
            }
        }
    }
    return data;
}

double quantile(const std::vector<double> &sorted, double probability) {
    if (sorted.empty()) throw Error("cannot find a value for an empty set");
    if (sorted.size() == 1) return sorted.front();
    const double position =
        probability * static_cast<double>(sorted.size() - 1);
    const std::size_t lower = static_cast<std::size_t>(std::floor(position));
    const std::size_t upper = static_cast<std::size_t>(std::ceil(position));
    const double part = position - static_cast<double>(lower);
    return sorted[lower] + part * (sorted[upper] - sorted[lower]);
}

TimingSummary summarize_times(std::vector<double> values) {
    std::sort(values.begin(), values.end());
    return TimingSummary{
        quantile(values, 0.5),
        quantile(values, 0.25),
        quantile(values, 0.75),
    };
}

template <class Function>
std::vector<double> combine_trials(const TimingSeries &left,
                                   const TimingSeries &right,
                                   Function function) {
    if (left.values.size() != right.values.size() || left.values.empty()) {
        throw Error("time series do not match");
    }
    std::vector<double> values;
    values.reserve(left.values.size());
    for (std::size_t trial = 0; trial < left.values.size(); ++trial) {
        values.push_back(function(left.values[trial], right.values[trial]));
    }
    return values;
}

void write_summary(std::ostream &file, const TimingData &data,
                   const OperationSpec &operation, const char *measure,
                   const std::vector<double> &values) {
    const TimingSummary summary = summarize_times(values);
    file << data.build << '\t' << operation.name << '\t' << measure
         << '\t' << data.input_count << '\t' << values.size()
         << '\t' << std::setprecision(17) << summary.median
         << '\t' << summary.first_quartile
         << '\t' << summary.third_quartile
         << '\t' << summary.third_quartile - summary.first_quartile
         << '\n';
}

void write_build(std::ostream &file, const TimingData &data) {
    for (std::size_t i = 0; i < operations.size(); ++i) {
        const OperationSpec &operation = operations[i];
        const auto &series = data.series[i];
        const TimingSeries &default_path =
            series[static_cast<std::size_t>(TimingValue::default_path)];
        const TimingSeries &strong_path =
            series[static_cast<std::size_t>(TimingValue::strong_path)];
        const TimingSeries &kernel =
            series[static_cast<std::size_t>(TimingValue::kernel)];
        const TimingSeries &qd =
            series[static_cast<std::size_t>(TimingValue::qd)];

        write_summary(file, data, operation, "default_ns_per_call",
                      default_path.values);
        if (!operation.eft) {
            write_summary(file, data, operation, "strong_ns_per_call",
                          strong_path.values);
        }
        write_summary(file, data, operation, "kernel_ns_per_call",
                      kernel.values);
        write_summary(file, data, operation, "qd_ns_per_call", qd.values);
        write_summary(file, data, operation, "default_over_kernel",
            combine_trials(default_path, kernel,
                [](double left, double right) { return left / right; }));
        write_summary(file, data, operation, "default_minus_kernel_ns",
            combine_trials(default_path, kernel,
                [](double left, double right) { return left - right; }));
        write_summary(file, data, operation, "default_over_qd",
            combine_trials(default_path, qd,
                [](double left, double right) { return left / right; }));
        if (!operation.eft) {
            write_summary(file, data, operation, "strong_over_kernel",
                combine_trials(strong_path, kernel,
                    [](double left, double right) { return left / right; }));
            write_summary(file, data, operation, "strong_minus_kernel_ns",
                combine_trials(strong_path, kernel,
                    [](double left, double right) { return left - right; }));
            write_summary(file, data, operation, "strong_over_qd",
                combine_trials(strong_path, qd,
                    [](double left, double right) { return left / right; }));
        }
    }
}

void write_results(const std::string &path, const TimingData &compcert,
                   const TimingData &clang) {
    if (compcert.input_count != clang.input_count
        || compcert.trial_count != clang.trial_count
        || compcert.input_fingerprint != clang.input_fingerprint) {
        throw Error("time files do not use the same data");
    }

    std::ofstream file(path);
    file.imbue(std::locale::classic());
    if (!file) throw Error("could not open " + path);
    file << "build\toperation\tmeasure\tinput_count\tsample_count"
            "\tmedian\tfirst_quartile\tthird_quartile\tiqr\n";
    write_build(file, compcert);
    write_build(file, clang);
    file.close();
    check_output(file, path);
}

void analyze(const std::string &compcert_path,
             const std::string &clang_path,
             const std::string &output_path) {
    check_environment();
    check_file_paths({compcert_path, clang_path, output_path}, 2);
    const TimingData compcert = read_timing_file(compcert_path, "compcert");
    const TimingData clang = read_timing_file(clang_path, "clang");
    write_results(output_path, compcert, clang);
}

}  // namespace

int main(int argc, char **argv) {
    if (argc != 4) {
        std::fprintf(
            stderr,
            "usage: %s timing-compcert.tsv timing-clang.tsv rq3.tsv\n",
            argv[0]);
        return EXIT_FAILURE;
    }
    std::setlocale(LC_NUMERIC, "C");
    try {
        analyze(argv[1], argv[2], argv[3]);
    } catch (const std::exception &error) {
        std::fprintf(stderr, "RQ3 analysis failed: %s\n", error.what());
        return EXIT_FAILURE;
    }
    return EXIT_SUCCESS;
}
