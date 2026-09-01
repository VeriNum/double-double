#ifndef DD_BENCH_TIMING_SUPPORT_HPP
#define DD_BENCH_TIMING_SUPPORT_HPP

#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdio>
#include <cstdlib>
#include <vector>

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

inline void sink(double value) {
    asm volatile("" : : "X"(value) : "memory");
}

template <class Body>
double nanoseconds_per_call(std::size_t count, Body &body) {
    typedef std::chrono::steady_clock clock;
    const clock::time_point start = clock::now();
    body();
    const clock::time_point finish = clock::now();
    const double elapsed_ns =
        std::chrono::duration<double, std::nano>(finish - start).count();
    if (!(elapsed_ns > 0.0) || !std::isfinite(elapsed_ns)) {
        std::fprintf(stderr, "invalid elapsed time\n");
        std::abort();
    }
    return elapsed_ns / static_cast<double>(count);
}

// The six permutations put every variant in every position and balance the
// pairwise order of the variants over each complete block of six trials.
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

// All 24 permutations put each of the four variants in every position and
// balance the order of every pair over a complete block of trials.
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

inline double quantile(const std::vector<double> &sorted, double probability) {
    if (sorted.empty()) {
        std::fprintf(stderr, "cannot summarize an empty timing sample\n");
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

inline Summary summarize(std::vector<double> values) {
    std::sort(values.begin(), values.end());
    return Summary{
        quantile(values, 0.5),
        quantile(values, 0.25),
        quantile(values, 0.75)
    };
}

template <class Combine>
Summary summarize_paired(const std::vector<double> &left,
                         const std::vector<double> &right,
                         Combine combine) {
    if (left.size() != right.size() || left.empty()) {
        std::fprintf(stderr, "timing sample sizes do not match\n");
        std::abort();
    }
    std::vector<double> combined(left.size());
    for (std::size_t i = 0; i < left.size(); ++i) {
        combined[i] = combine(left[i], right[i]);
    }
    return summarize(combined);
}

}  // namespace bench_timing

#endif
