// Measure the default public interface, its unchecked kernel, and QD on one
// prevalidated timing inputs.

#include <cerrno>
#include <cfenv>
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <limits>
#include <vector>

extern "C" {
#include "dw_arith.h"
#include "fp_utils.h"
}

#include "input_generation.hpp"
#include "qd_evaluation.hpp"

namespace bench_timing {

struct Samples {
    std::vector<double> default_ns;
    std::vector<double> kernel_ns;
    std::vector<double> qd_ns;
};

struct CompositeSamples {
    std::vector<double> default_ns;
    std::vector<double> strong_ns;
    std::vector<double> kernel_ns;
    std::vector<double> qd_ns;
};

struct Summary {
    double median;
    double first_quartile;
    double third_quartile;

    double iqr() const {
        return third_quartile - first_quartile;
    }
};

void sink(double value) {
    asm volatile("" : : "X"(value) : "memory");
}

template <class Body>
double nanoseconds_per_call(std::size_t count, Body &body) {
    typedef std::chrono::steady_clock Clock;
    const Clock::time_point start = Clock::now();
    body();
    const Clock::time_point finish = Clock::now();
    const double elapsed_ns =
        std::chrono::duration<double, std::nano>(finish - start).count();
    if (!(elapsed_ns > 0.0) || !std::isfinite(elapsed_ns)) {
        std::fprintf(stderr, "invalid elapsed time");
        std::abort();
    }
    return elapsed_ns / static_cast<double>(count);
}

// Put each of three variants in each place over six trials.
template <class DefaultBody, class KernelBody, class QdBody>
Samples collect_samples(std::size_t count, std::size_t trial_count,
                        std::size_t rotation_offset,
                        DefaultBody default_body,
                        KernelBody kernel_body,
                        QdBody qd_body) {
    Samples samples;
    samples.default_ns.reserve(trial_count);
    samples.kernel_ns.reserve(trial_count);
    samples.qd_ns.reserve(trial_count);

    default_body();
    kernel_body();
    qd_body();

    for (std::size_t trial = 0; trial < trial_count; ++trial) {
        const std::size_t order = (trial + rotation_offset) % 6;
        const auto measure_default = [&] {
            samples.default_ns.push_back(
                nanoseconds_per_call(count, default_body));
        };
        const auto measure_kernel = [&] {
            samples.kernel_ns.push_back(
                nanoseconds_per_call(count, kernel_body));
        };
        const auto measure_qd = [&] {
            samples.qd_ns.push_back(nanoseconds_per_call(count, qd_body));
        };

        switch (order) {
        case 0:
            measure_default(); measure_kernel(); measure_qd();
            break;
        case 1:
            measure_default(); measure_qd(); measure_kernel();
            break;
        case 2:
            measure_kernel(); measure_default(); measure_qd();
            break;
        case 3:
            measure_kernel(); measure_qd(); measure_default();
            break;
        case 4:
            measure_qd(); measure_default(); measure_kernel();
            break;
        case 5:
            measure_qd(); measure_kernel(); measure_default();
            break;
        default:
            std::abort();
        }
    }
    return samples;
}

// Put each of four variants in each place over 24 trials.
template <class DefaultBody, class StrongBody, class KernelBody, class QdBody>
CompositeSamples collect_composite_samples(
        std::size_t count, std::size_t trial_count,
        std::size_t rotation_offset,
        DefaultBody default_body, StrongBody strong_body,
        KernelBody kernel_body, QdBody qd_body) {
    static const unsigned char orders[24][4] = {
        {0, 1, 2, 3}, {0, 1, 3, 2}, {0, 2, 1, 3}, {0, 2, 3, 1},
        {0, 3, 1, 2}, {0, 3, 2, 1}, {1, 0, 2, 3}, {1, 0, 3, 2},
        {1, 2, 0, 3}, {1, 2, 3, 0}, {1, 3, 0, 2}, {1, 3, 2, 0},
        {2, 0, 1, 3}, {2, 0, 3, 1}, {2, 1, 0, 3}, {2, 1, 3, 0},
        {2, 3, 0, 1}, {2, 3, 1, 0}, {3, 0, 1, 2}, {3, 0, 2, 1},
        {3, 1, 0, 2}, {3, 1, 2, 0}, {3, 2, 0, 1}, {3, 2, 1, 0},
    };

    CompositeSamples samples;
    samples.default_ns.reserve(trial_count);
    samples.strong_ns.reserve(trial_count);
    samples.kernel_ns.reserve(trial_count);
    samples.qd_ns.reserve(trial_count);

    default_body();
    strong_body();
    kernel_body();
    qd_body();

    for (std::size_t trial = 0; trial < trial_count; ++trial) {
        const std::size_t order = (trial + rotation_offset) % 24;
        for (std::size_t position = 0; position < 4; ++position) {
            switch (orders[order][position]) {
            case 0:
                samples.default_ns.push_back(
                    nanoseconds_per_call(count, default_body));
                break;
            case 1:
                samples.strong_ns.push_back(
                    nanoseconds_per_call(count, strong_body));
                break;
            case 2:
                samples.kernel_ns.push_back(
                    nanoseconds_per_call(count, kernel_body));
                break;
            case 3:
                samples.qd_ns.push_back(
                    nanoseconds_per_call(count, qd_body));
                break;
            default:
                std::abort();
            }
        }
    }
    return samples;
}

double quantile(const std::vector<double> &sorted, double probability) {
    if (sorted.empty()) {
        std::fprintf(stderr, "cannot summarize an empty timing sample");
        std::abort();
    }
    if (sorted.size() == 1) return sorted.front();

    const double position =
        probability * static_cast<double>(sorted.size() - 1);
    const std::size_t lower = static_cast<std::size_t>(std::floor(position));
    const std::size_t upper = static_cast<std::size_t>(std::ceil(position));
    const double fraction = position - static_cast<double>(lower);
    return sorted[lower] + fraction * (sorted[upper] - sorted[lower]);
}

Summary summarize(std::vector<double> values) {
    std::sort(values.begin(), values.end());
    return Summary{
        quantile(values, 0.5),
        quantile(values, 0.25),
        quantile(values, 0.75)
    };
}

}  // namespace bench_timing

#ifndef FENCEDD_BUILD_LABEL
#error "FENCEDD_BUILD_LABEL must identify the linked fenceDD build"
#endif

namespace {

using bench_eval::TimingInputs;
using bench_eval::bits_of;
using bench_timing::CompositeSamples;
using bench_timing::Samples;
using bench_timing::Summary;

const char *const build_label = FENCEDD_BUILD_LABEL;

struct QdInputs {
    std::vector<dd_real> first;
    std::vector<dd_real> second;
};

[[noreturn]] void fail(const char *message) {
    std::fprintf(stderr, "performance evaluation failed: %s\n", message);
    std::exit(EXIT_FAILURE);
}

bool same_pair_bits(const dword &left, const dword &right) {
    return bits_of(left.s) == bits_of(right.s)
           && bits_of(left.t) == bits_of(right.t);
}

void require_same_pair(const char *operation, std::size_t case_index,
                       const dword &interface_result,
                       const dword &kernel_result) {
    if (same_pair_bits(interface_result, kernel_result)) return;
    std::fprintf(stderr,
                 "%s preflight mismatch at case %zu:\n"
                 "  interface=(0x%016llx,0x%016llx)\n"
                 "  kernel =(0x%016llx,0x%016llx)\n",
                 operation, case_index,
                 static_cast<unsigned long long>(bits_of(interface_result.s)),
                 static_cast<unsigned long long>(bits_of(interface_result.t)),
                 static_cast<unsigned long long>(bits_of(kernel_result.s)),
                 static_cast<unsigned long long>(bits_of(kernel_result.t)));
    std::exit(EXIT_FAILURE);
}

void require_ok(const char *operation, std::size_t case_index,
                enum dw_status status) {
    if (status == DW_OK) return;
    std::fprintf(stderr, "%s rejected timing case %zu with status %d\n",
                 operation, case_index, static_cast<int>(status));
    std::exit(EXIT_FAILURE);
}

std::size_t parse_positive_size(const char *text, const char *name) {
    if (text[0] == '\0') {
        std::fprintf(stderr, "%s must be a positive integer\n", name);
        std::exit(EXIT_FAILURE);
    }
    for (const char *character = text; *character != '\0'; ++character) {
        if (*character < '0' || *character > '9') {
            std::fprintf(stderr, "%s must be a positive integer\n", name);
            std::exit(EXIT_FAILURE);
        }
    }
    errno = 0;
    char *end = nullptr;
    const unsigned long long parsed = std::strtoull(text, &end, 10);
    if (errno != 0 || end == text || *end != '\0' || parsed == 0
        || parsed > std::numeric_limits<std::size_t>::max()) {
        std::fprintf(stderr, "%s must be a positive integer\n", name);
        std::exit(EXIT_FAILURE);
    }
    return static_cast<std::size_t>(parsed);
}

void check_environment() {
    if (sizeof(double) != sizeof(uint64_t)
        || !std::numeric_limits<double>::is_iec559
        || std::numeric_limits<double>::digits != 53) {
        fail("IEEE-754 binary64 arithmetic is required");
    }
    if (std::fegetround() != FE_TONEAREST) {
        fail("round-to-nearest mode is required");
    }
}

void check_input_sizes(const TimingInputs &inputs, std::size_t count) {
    if (inputs.first_fp.size() != count
        || inputs.second_fp.size() != count
        || inputs.scalar.size() != count
        || inputs.fast_first.size() != count
        || inputs.fast_second.size() != count
        || inputs.first_dw.size() != count
        || inputs.second_dw.size() != count) {
        fail("timing input arrays have inconsistent sizes");
    }
    if (bench_eval::fingerprint_timing_inputs(inputs)
        != inputs.fingerprint) {
        fail("timing-input fingerprint does not match the inputs");
    }
}

QdInputs make_qd_inputs(const TimingInputs &inputs) {
    QdInputs qd;
    qd.first.reserve(inputs.first_dw.size());
    qd.second.reserve(inputs.second_dw.size());
    for (std::size_t i = 0; i < inputs.first_dw.size(); ++i) {
        qd.first.emplace_back(inputs.first_dw[i].s, inputs.first_dw[i].t);
        qd.second.emplace_back(inputs.second_dw[i].s, inputs.second_dw[i].t);
        if (bits_of(qd.first.back().x[0]) != bits_of(inputs.first_dw[i].s)
            || bits_of(qd.first.back().x[1]) != bits_of(inputs.first_dw[i].t)
            || bits_of(qd.second.back().x[0]) != bits_of(inputs.second_dw[i].s)
            || bits_of(qd.second.back().x[1]) != bits_of(inputs.second_dw[i].t)) {
            fail("QD changed a timing input component");
        }
    }
    return qd;
}

// Every wrapper call is executed before timing. Every timing input must be
// accepted, and each result must match the direct kernel result.
void preflight(TimingInputs &inputs) {
    for (std::size_t i = 0; i < inputs.first_fp.size(); ++i) {
        dword default_result;
        dword kernel_result;

        require_ok("two_sum", i,
            two_sum(&default_result, inputs.first_fp[i], inputs.second_fp[i]));
        two_sum_kernel(
            &kernel_result, inputs.first_fp[i], inputs.second_fp[i]);
        require_same_pair("two_sum", i, default_result, kernel_result);

        require_ok("fast_2sum", i,
            fast_2sum(&default_result, inputs.fast_first[i],
                      inputs.fast_second[i]));
        fast_2sum_kernel(
            &kernel_result, inputs.fast_first[i], inputs.fast_second[i]);
        require_same_pair("fast_2sum", i, default_result, kernel_result);

        require_ok("fast_2mult", i,
            fast_2mult(&default_result, inputs.first_fp[i],
                       inputs.second_fp[i]));
        fast_2mult_kernel(&kernel_result, inputs.first_fp[i], inputs.second_fp[i]);
        require_same_pair("fast_2mult", i, default_result, kernel_result);

        require_ok("dw_plus_fp", i,
            dw_plus_fp(&default_result, &inputs.first_dw[i],
                       inputs.scalar[i]));
        dw_plus_fp_kernel(
            &kernel_result, &inputs.first_dw[i], inputs.scalar[i]);
        require_same_pair("dw_plus_fp", i, default_result, kernel_result);
        require_ok("dw_plus_fp_strong", i,
            dw_plus_fp_strong(&default_result, &inputs.first_dw[i],
                              inputs.scalar[i]));
        require_same_pair("dw_plus_fp_strong", i,
                          default_result, kernel_result);

        require_ok("dw_times_fp", i,
            dw_times_fp(&default_result, &inputs.first_dw[i],
                        inputs.scalar[i]));
        dw_times_fp_kernel(
            &kernel_result, &inputs.first_dw[i], inputs.scalar[i]);
        require_same_pair("dw_times_fp", i, default_result, kernel_result);
        require_ok("dw_times_fp_strong", i,
            dw_times_fp_strong(&default_result, &inputs.first_dw[i],
                               inputs.scalar[i]));
        require_same_pair("dw_times_fp_strong", i,
                          default_result, kernel_result);

        require_ok("dw_div_fp", i,
            dw_div_fp(&default_result, &inputs.first_dw[i],
                      inputs.scalar[i]));
        dw_div_fp_kernel(
            &kernel_result, &inputs.first_dw[i], inputs.scalar[i]);
        require_same_pair("dw_div_fp", i, default_result, kernel_result);
        require_ok("dw_div_fp_strong", i,
            dw_div_fp_strong(&default_result, &inputs.first_dw[i],
                             inputs.scalar[i]));
        require_same_pair("dw_div_fp_strong", i,
                          default_result, kernel_result);

        require_ok("dw_plus_dw", i,
            dw_plus_dw(&default_result, &inputs.first_dw[i],
                       &inputs.second_dw[i]));
        dw_plus_dw_kernel(
            &kernel_result, &inputs.first_dw[i], &inputs.second_dw[i]);
        require_same_pair("dw_plus_dw", i, default_result, kernel_result);
        require_ok("dw_plus_dw_strong", i,
            dw_plus_dw_strong(&default_result, &inputs.first_dw[i],
                              &inputs.second_dw[i]));
        require_same_pair("dw_plus_dw_strong", i,
                          default_result, kernel_result);

        require_ok("dw_times_dw", i,
            dw_times_dw(&default_result, &inputs.first_dw[i],
                        &inputs.second_dw[i]));
        dw_times_dw_kernel(
            &kernel_result, &inputs.first_dw[i], &inputs.second_dw[i]);
        require_same_pair("dw_times_dw", i, default_result, kernel_result);
        require_ok("dw_times_dw_strong", i,
            dw_times_dw_strong(&default_result, &inputs.first_dw[i],
                               &inputs.second_dw[i]));
        require_same_pair("dw_times_dw_strong", i,
                          default_result, kernel_result);

        require_ok("dw_div_dw", i,
            dw_div_dw(&default_result, &inputs.first_dw[i],
                      &inputs.second_dw[i]));
        dw_div_dw_kernel(
            &kernel_result, &inputs.first_dw[i], &inputs.second_dw[i]);
        require_same_pair("dw_div_dw", i, default_result, kernel_result);
        require_ok("dw_div_dw_strong", i,
            dw_div_dw_strong(&default_result, &inputs.first_dw[i],
                             &inputs.second_dw[i]));
        require_same_pair("dw_div_dw_strong", i,
                          default_result, kernel_result);
    }
}

void report_series(const char *operation, const char *implementation,
                   const char *interface_name,
                   const std::vector<double> &values,
                   std::FILE *result_file) {
    const Summary summary = bench_timing::summarize(values);
    std::printf("  %-14s %-8s %-9s %8.3f %7.3f\n",
                operation, implementation, interface_name,
                summary.median, summary.iqr());
    if (result_file == nullptr) return;
    for (std::size_t trial = 0; trial < values.size(); ++trial) {
        std::fprintf(result_file, "%s\t%s\t%s\t%zu\t%.17g\n",
                     operation, implementation, interface_name,
                     trial, values[trial]);
    }
}

void report_exact(const char *name, const Samples &samples,
                  std::FILE *result_file) {
    report_series(name, "fenceDD", "default", samples.default_ns, result_file);
    report_series(name, "fenceDD", "kernel", samples.kernel_ns, result_file);
    report_series(name, "QD", "reference", samples.qd_ns, result_file);
}

void report_composite(const char *name, const CompositeSamples &samples,
                      std::FILE *result_file) {
    report_series(name, "fenceDD", "default", samples.default_ns, result_file);
    report_series(name, "fenceDD", "strong", samples.strong_ns, result_file);
    report_series(name, "fenceDD", "kernel", samples.kernel_ns, result_file);
    report_series(name, "QD", "reference", samples.qd_ns, result_file);
}

template <class DefaultBody, class KernelBody, class QdBody>
void measure_exact(const char *name, std::size_t count, std::size_t trials,
                   std::size_t rotation_offset, std::FILE *result_file,
                   DefaultBody default_body, KernelBody kernel_body,
                   QdBody qd_body) {
    const Samples samples = bench_timing::collect_samples(
        count, trials, rotation_offset, default_body, kernel_body, qd_body);
    report_exact(name, samples, result_file);
}

template <class DefaultBody, class StrongBody, class KernelBody, class QdBody>
void measure_composite(const char *name, std::size_t count,
                       std::size_t trials, std::size_t rotation_offset,
                       std::FILE *result_file,
                       DefaultBody default_body, StrongBody strong_body,
                       KernelBody kernel_body, QdBody qd_body) {
    const CompositeSamples samples =
        bench_timing::collect_composite_samples(
            count, trials, rotation_offset,
            default_body, strong_body, kernel_body, qd_body);
    report_composite(name, samples, result_file);
}

void run_measurements(TimingInputs &inputs, const QdInputs &qd_inputs,
                      std::size_t trials, std::FILE *result_file) {
    const std::size_t count = inputs.first_fp.size();
    std::puts("  operation      library  interface   median     IQR");

    {
        dword default_result{0.0, 0.0};
        dword kernel_result{0.0, 0.0};
        double qd_high = 0.0;
        double qd_low = 0.0;
        measure_exact("two_sum", count, trials, 0, result_file,
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    two_sum(&default_result,
                            inputs.first_fp[i], inputs.second_fp[i]);
                    bench_timing::sink(default_result.s);
                    bench_timing::sink(default_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    two_sum_kernel(&kernel_result,
                                   inputs.first_fp[i], inputs.second_fp[i]);
                    bench_timing::sink(kernel_result.s);
                    bench_timing::sink(kernel_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    qd_high = qd::two_sum(
                        inputs.first_fp[i], inputs.second_fp[i], qd_low);
                    bench_timing::sink(qd_high);
                    bench_timing::sink(qd_low);
                }
            });
    }

    {
        dword default_result{0.0, 0.0};
        dword kernel_result{0.0, 0.0};
        double qd_high = 0.0;
        double qd_low = 0.0;
        measure_exact("fast_2sum", count, trials, 1, result_file,
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    fast_2sum(&default_result,
                                      inputs.fast_first[i],
                                      inputs.fast_second[i]);
                    bench_timing::sink(default_result.s);
                    bench_timing::sink(default_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    fast_2sum_kernel(&kernel_result,
                              inputs.fast_first[i], inputs.fast_second[i]);
                    bench_timing::sink(kernel_result.s);
                    bench_timing::sink(kernel_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    qd_high = qd::quick_two_sum(
                        inputs.fast_first[i], inputs.fast_second[i], qd_low);
                    bench_timing::sink(qd_high);
                    bench_timing::sink(qd_low);
                }
            });
    }

    {
        dword default_result{0.0, 0.0};
        dword kernel_result{0.0, 0.0};
        double qd_high = 0.0;
        double qd_low = 0.0;
        measure_exact("fast_2mult", count, trials, 2, result_file,
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    fast_2mult(&default_result,
                                       inputs.first_fp[i],
                                       inputs.second_fp[i]);
                    bench_timing::sink(default_result.s);
                    bench_timing::sink(default_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    fast_2mult_kernel(&kernel_result,
                               inputs.first_fp[i], inputs.second_fp[i]);
                    bench_timing::sink(kernel_result.s);
                    bench_timing::sink(kernel_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    qd_high = qd::two_prod(
                        inputs.first_fp[i], inputs.second_fp[i], qd_low);
                    bench_timing::sink(qd_high);
                    bench_timing::sink(qd_low);
                }
            });
    }

    {
        dword default_result{0.0, 0.0};
        dword kernel_result{0.0, 0.0};
        measure_composite("dw_plus_fp", count, trials, 3, result_file,
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    dw_plus_fp(&default_result,
                               &inputs.first_dw[i], inputs.scalar[i]);
                    bench_timing::sink(default_result.s);
                    bench_timing::sink(default_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    dw_plus_fp_strong(&default_result,
                                      &inputs.first_dw[i], inputs.scalar[i]);
                    bench_timing::sink(default_result.s);
                    bench_timing::sink(default_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    dw_plus_fp_kernel(&kernel_result,
                                      &inputs.first_dw[i], inputs.scalar[i]);
                    bench_timing::sink(kernel_result.s);
                    bench_timing::sink(kernel_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    const dd_real result =
                        qd_inputs.first[i] + inputs.scalar[i];
                    bench_timing::sink(result.x[0]);
                    bench_timing::sink(result.x[1]);
                }
            });
    }

    {
        dword default_result{0.0, 0.0};
        dword kernel_result{0.0, 0.0};
        measure_composite("dw_times_fp", count, trials, 4, result_file,
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    dw_times_fp(&default_result,
                                &inputs.first_dw[i], inputs.scalar[i]);
                    bench_timing::sink(default_result.s);
                    bench_timing::sink(default_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    dw_times_fp_strong(&default_result,
                                       &inputs.first_dw[i], inputs.scalar[i]);
                    bench_timing::sink(default_result.s);
                    bench_timing::sink(default_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    dw_times_fp_kernel(&kernel_result,
                                       &inputs.first_dw[i], inputs.scalar[i]);
                    bench_timing::sink(kernel_result.s);
                    bench_timing::sink(kernel_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    const dd_real result =
                        qd_inputs.first[i] * inputs.scalar[i];
                    bench_timing::sink(result.x[0]);
                    bench_timing::sink(result.x[1]);
                }
            });
    }

    {
        dword default_result{0.0, 0.0};
        dword kernel_result{0.0, 0.0};
        measure_composite("dw_div_fp", count, trials, 5, result_file,
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    dw_div_fp(&default_result,
                              &inputs.first_dw[i], inputs.scalar[i]);
                    bench_timing::sink(default_result.s);
                    bench_timing::sink(default_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    dw_div_fp_strong(&default_result,
                                     &inputs.first_dw[i], inputs.scalar[i]);
                    bench_timing::sink(default_result.s);
                    bench_timing::sink(default_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    dw_div_fp_kernel(&kernel_result,
                                     &inputs.first_dw[i], inputs.scalar[i]);
                    bench_timing::sink(kernel_result.s);
                    bench_timing::sink(kernel_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    const dd_real result =
                        qd_inputs.first[i] / inputs.scalar[i];
                    bench_timing::sink(result.x[0]);
                    bench_timing::sink(result.x[1]);
                }
            });
    }

    {
        dword default_result{0.0, 0.0};
        dword kernel_result{0.0, 0.0};
        measure_composite("dw_plus_dw", count, trials, 6, result_file,
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    dw_plus_dw(&default_result,
                               &inputs.first_dw[i], &inputs.second_dw[i]);
                    bench_timing::sink(default_result.s);
                    bench_timing::sink(default_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    dw_plus_dw_strong(&default_result,
                                      &inputs.first_dw[i],
                                      &inputs.second_dw[i]);
                    bench_timing::sink(default_result.s);
                    bench_timing::sink(default_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    dw_plus_dw_kernel(&kernel_result,
                                      &inputs.first_dw[i],
                                      &inputs.second_dw[i]);
                    bench_timing::sink(kernel_result.s);
                    bench_timing::sink(kernel_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    const dd_real result =
                        dd_real::ieee_add(qd_inputs.first[i],
                                          qd_inputs.second[i]);
                    bench_timing::sink(result.x[0]);
                    bench_timing::sink(result.x[1]);
                }
            });
    }

    {
        dword default_result{0.0, 0.0};
        dword kernel_result{0.0, 0.0};
        measure_composite("dw_times_dw", count, trials, 7, result_file,
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    dw_times_dw(&default_result,
                                &inputs.first_dw[i], &inputs.second_dw[i]);
                    bench_timing::sink(default_result.s);
                    bench_timing::sink(default_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    dw_times_dw_strong(&default_result,
                                       &inputs.first_dw[i],
                                       &inputs.second_dw[i]);
                    bench_timing::sink(default_result.s);
                    bench_timing::sink(default_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    dw_times_dw_kernel(&kernel_result,
                                       &inputs.first_dw[i],
                                       &inputs.second_dw[i]);
                    bench_timing::sink(kernel_result.s);
                    bench_timing::sink(kernel_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    const dd_real result =
                        qd_inputs.first[i] * qd_inputs.second[i];
                    bench_timing::sink(result.x[0]);
                    bench_timing::sink(result.x[1]);
                }
            });
    }

    {
        dword default_result{0.0, 0.0};
        dword kernel_result{0.0, 0.0};
        measure_composite("dw_div_dw", count, trials, 8, result_file,
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    dw_div_dw(&default_result,
                              &inputs.first_dw[i], &inputs.second_dw[i]);
                    bench_timing::sink(default_result.s);
                    bench_timing::sink(default_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    dw_div_dw_strong(&default_result,
                                     &inputs.first_dw[i],
                                     &inputs.second_dw[i]);
                    bench_timing::sink(default_result.s);
                    bench_timing::sink(default_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    dw_div_dw_kernel(&kernel_result,
                                     &inputs.first_dw[i],
                                     &inputs.second_dw[i]);
                    bench_timing::sink(kernel_result.s);
                    bench_timing::sink(kernel_result.t);
                }
            },
            [&] {
                for (std::size_t i = 0; i < count; ++i) {
                    const dd_real result =
                        dd_real::accurate_div(qd_inputs.first[i],
                                              qd_inputs.second[i]);
                    bench_timing::sink(result.x[0]);
                    bench_timing::sink(result.x[1]);
                }
            });
    }
}

}  // namespace

int main(int argc, char **argv) {
    if (argc > 4) {
        std::fprintf(stderr,
            "usage: %s [input_count] [trial_count] [trial_tsv]\n", argv[0]);
        return EXIT_FAILURE;
    }

    const std::size_t count =
        argc > 1 ? parse_positive_size(argv[1], "input_count")
                 : (std::size_t{1} << 16);
    const std::size_t trials =
        argc > 2 ? parse_positive_size(argv[2], "trial_count") : 24;
    if (trials % 24 != 0) {
        std::fprintf(stderr,
            "trial_count must be a multiple of 24 to balance measurement order\n");
        return EXIT_FAILURE;
    }
    if (trials > SIZE_MAX / 33) {
        std::fprintf(stderr, "trial_count is too large\n");
        return EXIT_FAILURE;
    }

    check_environment();
    TimingInputs inputs = bench_eval::make_timing_inputs(count);
    check_input_sizes(inputs, count);
    const QdInputs qd_inputs = make_qd_inputs(inputs);
    std::FILE *result_file = nullptr;
    if (argc == 4) {
        result_file = std::fopen(argv[3], "w");
        if (result_file == nullptr) {
            std::perror(argv[3]);
            return EXIT_FAILURE;
        }
        std::fprintf(result_file, "# rq3_schema_version=4\n");
        std::fprintf(result_file, "# build=%s\n", build_label);
        std::fprintf(result_file, "# input_count=%zu\n", count);
        std::fprintf(result_file, "# trial_count=%zu\n", trials);
        std::fprintf(result_file,
            "# composite_interfaces=default:two-stage,strong:input-only\n");
        std::fprintf(result_file,
            "# exact_transform_interface=default:guarded\n");
        std::fprintf(result_file,
            "# quantile=linear_interpolation_p_times_n_minus_1\n");
        std::fprintf(result_file,
            "# exact_schedule=all_six_permutations\n");
        std::fprintf(result_file,
            "# composite_schedule=all_twenty_four_permutations\n");
        std::fprintf(result_file,
            "# timer=std_chrono_steady_clock\n");
        std::fprintf(result_file, "# input_fingerprint=0x%016llx\n",
            static_cast<unsigned long long>(inputs.fingerprint));
        std::fprintf(result_file,
            "operation\timplementation\tinterface\ttrial\tns_per_call\n");
    }

    std::printf("RQ3 performance: %s fenceDD build and QD\n", build_label);
    std::puts("  composite operations: default = two-stage, strong = input-only");
    std::puts("  exact transformations: default = guarded");
    std::printf("  inputs = %zu, trials = %zu, fingerprint of timing inputs = 0x%016llx\n",
                count, trials,
                static_cast<unsigned long long>(inputs.fingerprint));
    std::puts("  preflight: every measured guarded call must return and match"
              " its kernel");
    std::fflush(stdout);
    preflight(inputs);
    if (bench_eval::fingerprint_timing_inputs(inputs)
        != inputs.fingerprint) {
        fail("preflight changed a timing input");
    }
    std::puts("  preflight passed\n");
    std::puts("  Entries are median and IQR across trials.");

    run_measurements(inputs, qd_inputs, trials, result_file);
    if (bench_eval::fingerprint_timing_inputs(inputs)
        != inputs.fingerprint) {
        fail("a timed operation changed the timing inputs");
    }
    if (result_file != nullptr) {
        std::fprintf(result_file, "# data_rows=%zu\n", 33 * trials);
        std::fprintf(result_file, "# completed=true\n");
        if (std::fclose(result_file) != 0) {
            std::perror(argv[3]);
            return EXIT_FAILURE;
        }
    }
    return EXIT_SUCCESS;
}
