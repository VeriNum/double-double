// Record generated numerical inputs and the raw outputs of FenceDD and QD.

#include "input_generation.hpp"
#include "qd_evaluation.hpp"

extern "C" {
#include "dw_arith.h"
}

#include <cerrno>
#include <cfenv>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <limits>
#include <string>

namespace {

using bench_eval::GeneratedTestInputs;
using bench_eval::ResultPair;

struct InterfaceResult {
    bool has_status;
    enum dw_status status;
    ResultPair value;
};

struct InputBits {
    std::uint64_t first_hi;
    bool has_first_lo;
    std::uint64_t first_lo;
    std::uint64_t second_hi;
    bool has_second_lo;
    std::uint64_t second_lo;
};

std::string bits_text(std::uint64_t bits) {
    char text[19];
    std::snprintf(text, sizeof(text), "0x%016llx",
                  static_cast<unsigned long long>(bits));
    return text;
}

std::string result_bits(const InterfaceResult &result, bool high) {
    if (result.has_status && result.status != DW_OK) return "-";
    const double value = high ? result.value.hi : result.value.lo;
    return bits_text(bench_eval::bits_of(value));
}

std::string status_text(const InterfaceResult &result) {
    if (!result.has_status) return "-";
    return std::to_string(static_cast<int>(result.status));
}

void write_row(std::FILE *file, const char *operation, std::size_t case_id,
               const InputBits &inputs, const std::string &default_status,
               const std::string &default_hi,
               const std::string &default_lo, const std::string &strong_status,
               const std::string &strong_hi, const std::string &strong_lo,
               const ResultPair &qd_result) {
    const std::string first_hi = bits_text(inputs.first_hi);
    const std::string first_lo = inputs.has_first_lo
        ? bits_text(inputs.first_lo) : "-";
    const std::string second_hi = bits_text(inputs.second_hi);
    const std::string second_lo = inputs.has_second_lo
        ? bits_text(inputs.second_lo) : "-";
    const std::string qd_hi = bits_text(bench_eval::bits_of(qd_result.hi));
    const std::string qd_lo = bits_text(bench_eval::bits_of(qd_result.lo));

    std::fprintf(file,
        "%s\t%zu\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n",
        operation, case_id, first_hi.c_str(), first_lo.c_str(),
        second_hi.c_str(), second_lo.c_str(), default_status.c_str(),
        default_hi.c_str(), default_lo.c_str(), strong_status.c_str(),
        strong_hi.c_str(), strong_lo.c_str(), qd_hi.c_str(), qd_lo.c_str());
}

template <class Inputs, class Call, class Qd>
void record_eft(std::FILE *file, const char *operation,
                const Inputs &inputs, Call call, Qd qd) {
    const std::size_t count = inputs.fp_first.size();

    for (std::size_t i = 0; i < count; ++i) {
        const InterfaceResult result = call(i);
        const InputBits input_bits{
            inputs.fp_first[i].bits, false, 0,
            inputs.fp_second[i].bits, false, 0
        };
        write_row(file, operation, i, input_bits,
                  status_text(result),
                  result_bits(result, true),
                  result_bits(result, false),
                  "-", "-", "-", qd(i));
    }
}

template <class Input, class DefaultCall, class StrongCall, class Qd>
void record_composite(std::FILE *file, const char *operation,
                      std::size_t count, Input input,
                      DefaultCall default_call, StrongCall strong_call,
                      Qd qd) {
    for (std::size_t i = 0; i < count; ++i) {
        const InterfaceResult default_result = default_call(i);
        const InterfaceResult strong_result = strong_call(i);
        write_row(file, operation, i, input(i),
                  status_text(default_result),
                  result_bits(default_result, true),
                  result_bits(default_result, false),
                  status_text(strong_result),
                  result_bits(strong_result, true),
                  result_bits(strong_result, false), qd(i));
    }
}

std::size_t parse_samples(const char *text) {
    if (text[0] == '\0') {
        std::fprintf(stderr, "samples_per_exponent must be positive\n");
        std::exit(EXIT_FAILURE);
    }
    for (const char *character = text; *character != '\0'; ++character) {
        if (*character < '0' || *character > '9') {
            std::fprintf(stderr, "samples_per_exponent must be positive\n");
            std::exit(EXIT_FAILURE);
        }
    }

    errno = 0;
    char *end = nullptr;
    const unsigned long long parsed = std::strtoull(text, &end, 10);
    if (errno != 0 || end == text || *end != '\0' || parsed == 0
        || parsed > static_cast<unsigned long long>(
            SIZE_MAX / bench_eval::fp_exponent_bins)) {
        std::fprintf(stderr, "samples_per_exponent must be positive\n");
        std::exit(EXIT_FAILURE);
    }
    return static_cast<std::size_t>(parsed);
}

void check_environment() {
    if (sizeof(double) != sizeof(std::uint64_t)
        || !std::numeric_limits<double>::is_iec559
        || std::numeric_limits<double>::digits != 53
        || std::fegetround() != FE_TONEAREST) {
        std::fprintf(stderr,
                     "numerical measurements require round-to-nearest "
                     "IEEE-754 binary64\n");
        std::exit(EXIT_FAILURE);
    }
}

}  // namespace

int main(int argc, char **argv) {
    if (argc != 3) {
        std::fprintf(stderr,
                     "usage: %s samples_per_exponent output.tsv\n", argv[0]);
        return EXIT_FAILURE;
    }

    const std::size_t samples_per_exponent = parse_samples(argv[1]);
    check_environment();
    GeneratedTestInputs inputs =
        bench_eval::make_generated_test_inputs(samples_per_exponent);

    if (inputs.fp_first.size() != inputs.fp_second.size()
        || inputs.mixed_dw.size() != inputs.mixed_fp.size()
        || inputs.dw_first.size() != inputs.dw_second.size()) {
        std::fprintf(stderr, "generated input streams have different sizes\n");
        return EXIT_FAILURE;
    }

    std::FILE *file = std::fopen(argv[2], "w");
    if (file == nullptr) {
        std::perror(argv[2]);
        return EXIT_FAILURE;
    }

    std::fprintf(file, "# samples_per_exponent=%zu\n",
                 samples_per_exponent);
    std::fprintf(file,
        "operation\tcase_id\tfirst_hi_bits\tfirst_lo_bits"
        "\tsecond_hi_bits\tsecond_lo_bits\tdefault_status"
        "\tdefault_result_hi_bits\tdefault_result_lo_bits"
        "\tstrong_status\tstrong_result_hi_bits"
        "\tstrong_result_lo_bits\tqd_result_hi_bits"
        "\tqd_result_lo_bits\n");

    record_eft(file, "two_sum", inputs,
        [&](std::size_t i) {
            dword result{};
            two_sum(&result, inputs.fp_first[i].value,
                    inputs.fp_second[i].value);
            return InterfaceResult{false, DW_OK, {result.s, result.t}};
        },
        [&](std::size_t i) {
            double low;
            const double high = qd::two_sum(inputs.fp_first[i].value,
                                            inputs.fp_second[i].value, low);
            return ResultPair{high, low};
        });

    record_eft(file, "fast_2sum", inputs,
        [&](std::size_t i) {
            dword result{};
            const enum dw_status status = fast_2sum(
                &result, inputs.fp_first[i].value,
                inputs.fp_second[i].value);
            return InterfaceResult{true, status, {result.s, result.t}};
        },
        [&](std::size_t i) {
            double low;
            const double high = qd::quick_two_sum(
                inputs.fp_first[i].value, inputs.fp_second[i].value, low);
            return ResultPair{high, low};
        });

    record_eft(file, "fast_2mult", inputs,
        [&](std::size_t i) {
            dword result{};
            const enum dw_status status = fast_2mult(
                &result, inputs.fp_first[i].value,
                inputs.fp_second[i].value);
            return InterfaceResult{true, status, {result.s, result.t}};
        },
        [&](std::size_t i) {
            double low;
            const double high = qd::two_prod(inputs.fp_first[i].value,
                                             inputs.fp_second[i].value, low);
            return ResultPair{high, low};
        });

    const std::size_t mixed_count = inputs.mixed_dw.size();
    auto mixed_input = [&](std::size_t i) {
        return InputBits{
            inputs.mixed_dw[i].hi_bits, true,
            inputs.mixed_dw[i].lo_bits,
            inputs.mixed_fp[i].bits, false, 0
        };
    };

    record_composite(file, "dw_plus_fp", mixed_count, mixed_input,
        [&](std::size_t i) {
            dword result{};
            const enum dw_status status = dw_plus_fp(
                &result, &inputs.mixed_dw[i].value,
                inputs.mixed_fp[i].value);
            return InterfaceResult{true, status, {result.s, result.t}};
        },
        [&](std::size_t i) {
            dword result{};
            const enum dw_status status = dw_plus_fp_strong(
                &result, &inputs.mixed_dw[i].value,
                inputs.mixed_fp[i].value);
            return InterfaceResult{true, status, {result.s, result.t}};
        },
        [&](std::size_t i) {
            const dd_real first(inputs.mixed_dw[i].value.s,
                                inputs.mixed_dw[i].value.t);
            const dd_real result = first + inputs.mixed_fp[i].value;
            return ResultPair{result.x[0], result.x[1]};
        });

    record_composite(file, "dw_times_fp", mixed_count, mixed_input,
        [&](std::size_t i) {
            dword result{};
            const enum dw_status status = dw_times_fp(
                &result, &inputs.mixed_dw[i].value,
                inputs.mixed_fp[i].value);
            return InterfaceResult{true, status, {result.s, result.t}};
        },
        [&](std::size_t i) {
            dword result{};
            const enum dw_status status = dw_times_fp_strong(
                &result, &inputs.mixed_dw[i].value,
                inputs.mixed_fp[i].value);
            return InterfaceResult{true, status, {result.s, result.t}};
        },
        [&](std::size_t i) {
            const dd_real first(inputs.mixed_dw[i].value.s,
                                inputs.mixed_dw[i].value.t);
            const dd_real result = first * inputs.mixed_fp[i].value;
            return ResultPair{result.x[0], result.x[1]};
        });

    record_composite(file, "dw_div_fp", mixed_count, mixed_input,
        [&](std::size_t i) {
            dword result{};
            const enum dw_status status = dw_div_fp(
                &result, &inputs.mixed_dw[i].value,
                inputs.mixed_fp[i].value);
            return InterfaceResult{true, status, {result.s, result.t}};
        },
        [&](std::size_t i) {
            dword result{};
            const enum dw_status status = dw_div_fp_strong(
                &result, &inputs.mixed_dw[i].value,
                inputs.mixed_fp[i].value);
            return InterfaceResult{true, status, {result.s, result.t}};
        },
        [&](std::size_t i) {
            const dd_real first(inputs.mixed_dw[i].value.s,
                                inputs.mixed_dw[i].value.t);
            const dd_real result = first / inputs.mixed_fp[i].value;
            return ResultPair{result.x[0], result.x[1]};
        });

    const std::size_t dw_count = inputs.dw_first.size();
    auto dw_input = [&](std::size_t i) {
        return InputBits{
            inputs.dw_first[i].hi_bits, true, inputs.dw_first[i].lo_bits,
            inputs.dw_second[i].hi_bits, true, inputs.dw_second[i].lo_bits
        };
    };

    record_composite(file, "dw_plus_dw", dw_count, dw_input,
        [&](std::size_t i) {
            dword result{};
            const enum dw_status status = dw_plus_dw(
                &result, &inputs.dw_first[i].value,
                &inputs.dw_second[i].value);
            return InterfaceResult{true, status, {result.s, result.t}};
        },
        [&](std::size_t i) {
            dword result{};
            const enum dw_status status = dw_plus_dw_strong(
                &result, &inputs.dw_first[i].value,
                &inputs.dw_second[i].value);
            return InterfaceResult{true, status, {result.s, result.t}};
        },
        [&](std::size_t i) {
            const dd_real first(inputs.dw_first[i].value.s,
                                inputs.dw_first[i].value.t);
            const dd_real second(inputs.dw_second[i].value.s,
                                 inputs.dw_second[i].value.t);
            const dd_real result = dd_real::ieee_add(first, second);
            return ResultPair{result.x[0], result.x[1]};
        });

    record_composite(file, "dw_times_dw", dw_count, dw_input,
        [&](std::size_t i) {
            dword result{};
            const enum dw_status status = dw_times_dw(
                &result, &inputs.dw_first[i].value,
                &inputs.dw_second[i].value);
            return InterfaceResult{true, status, {result.s, result.t}};
        },
        [&](std::size_t i) {
            dword result{};
            const enum dw_status status = dw_times_dw_strong(
                &result, &inputs.dw_first[i].value,
                &inputs.dw_second[i].value);
            return InterfaceResult{true, status, {result.s, result.t}};
        },
        [&](std::size_t i) {
            const dd_real first(inputs.dw_first[i].value.s,
                                inputs.dw_first[i].value.t);
            const dd_real second(inputs.dw_second[i].value.s,
                                 inputs.dw_second[i].value.t);
            const dd_real result = first * second;
            return ResultPair{result.x[0], result.x[1]};
        });

    record_composite(file, "dw_div_dw", dw_count, dw_input,
        [&](std::size_t i) {
            dword result{};
            const enum dw_status status = dw_div_dw(
                &result, &inputs.dw_first[i].value,
                &inputs.dw_second[i].value);
            return InterfaceResult{true, status, {result.s, result.t}};
        },
        [&](std::size_t i) {
            dword result{};
            const enum dw_status status = dw_div_dw_strong(
                &result, &inputs.dw_first[i].value,
                &inputs.dw_second[i].value);
            return InterfaceResult{true, status, {result.s, result.t}};
        },
        [&](std::size_t i) {
            const dd_real first(inputs.dw_first[i].value.s,
                                inputs.dw_first[i].value.t);
            const dd_real second(inputs.dw_second[i].value.s,
                                 inputs.dw_second[i].value.t);
            const dd_real result = dd_real::accurate_div(first, second);
            return ResultPair{result.x[0], result.x[1]};
        });

    if (std::ferror(file)) {
        std::perror(argv[2]);
        std::fclose(file);
        return EXIT_FAILURE;
    }
    if (std::fclose(file) != 0) {
        std::perror(argv[2]);
        return EXIT_FAILURE;
    }
    return EXIT_SUCCESS;
}
