#include "input_generation.hpp"

#include <mpfr.h>

#include <algorithm>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <random>
#include <utility>

namespace bench_eval {
namespace {

struct ValueDescriptor {
    int exponent;
    bool negative;
    bool ordinary;
};

double double_from_bits(std::uint64_t bits) {
    double value;
    std::memcpy(&value, &bits, sizeof(value));
    return value;
}

std::uint64_t mix_seed(std::uint64_t value) {
    value += UINT64_C(0x9E3779B97F4A7C15);
    value = (value ^ (value >> 30)) * UINT64_C(0xBF58476D1CE4E5B9);
    value = (value ^ (value >> 27)) * UINT64_C(0x94D049BB133111EB);
    return value ^ (value >> 31);
}

// Draw uniformly from [0, bound) using only the specified random engine.
std::uint64_t bounded_random(std::mt19937_64 &rng, std::uint64_t bound) {
    if (bound == 0) {
        std::fprintf(stderr, "invalid random bound\n");
        std::abort();
    }
    std::uint64_t threshold = static_cast<std::uint64_t>(-bound) % bound;
    std::uint64_t value;
    do {
        value = rng();
    } while (value < threshold);
    return value % bound;
}

template <class T>
void deterministic_shuffle(std::vector<T> &values, std::mt19937_64 &rng) {
    for (std::size_t i = values.size(); i > 1; --i) {
        std::size_t j =
            static_cast<std::size_t>(bounded_random(rng, i));
        std::swap(values[i - 1], values[j]);
    }
}

GeneratedFP make_fp_value(const ValueDescriptor &descriptor,
                          std::mt19937_64 &rng) {
    std::uint64_t sign = descriptor.negative ? (UINT64_C(1) << 63) : 0;
    std::uint64_t encoding;

    if (descriptor.exponent >= -1022) {
        std::uint64_t exponent_field =
            static_cast<std::uint64_t>(descriptor.exponent + 1023);
        std::uint64_t fraction = rng() & ((UINT64_C(1) << 52) - 1);
        encoding = sign | (exponent_field << 52) | fraction;
    } else {
        int precision = descriptor.exponent + 1075;
        std::uint64_t leading = UINT64_C(1) << (precision - 1);
        std::uint64_t lower_mask = leading - 1;
        std::uint64_t coefficient = leading | (rng() & lower_mask);
        encoding = sign | coefficient;
    }

    double value = double_from_bits(encoding);
    if (!std::isfinite(value) || value == 0.0
        || std::ilogb(std::abs(value)) != descriptor.exponent) {
        std::fprintf(stderr, "failed to construct a binary64 input\n");
        std::abort();
    }

    return GeneratedFP{
        value, descriptor.exponent, descriptor.negative, encoding
    };
}

class DWBuilder {
public:
    DWBuilder() {
        mpz_init(integer_);
        mpfr_inits2(construction_precision, source_, high_, residual_, low_,
                    reconstructed_, (mpfr_ptr)0);
    }

    ~DWBuilder() {
        mpfr_clears(source_, high_, residual_, low_, reconstructed_,
                    (mpfr_ptr)0);
        mpz_clear(integer_);
    }

    GeneratedDW make(const ValueDescriptor &descriptor,
                     std::mt19937_64 &rng) {
        if (descriptor.exponent < dw_min_exponent
            || descriptor.exponent > dw_max_exponent) {
            std::fprintf(stderr,
                         "double-word exponent is outside the core range\n");
            std::abort();
        }

        if (descriptor.ordinary) {
            ValueDescriptor fp_descriptor{
                descriptor.exponent, descriptor.negative, false
            };
            GeneratedFP high = make_fp_value(fp_descriptor, rng);
            mpfr_set_d(source_, high.value, MPFR_RNDN);
            int source_precision =
                static_cast<int>(mpfr_min_prec(source_));
            return finish(descriptor, high.value, 0.0, source_precision);
        }

        // M = 2^105 + 2R + 1, with R uniform in [0, 2^104).
        std::uint64_t low_word = rng();
        std::uint64_t high_word = rng() & ((UINT64_C(1) << 40) - 1);
        mpz_set_ui(integer_, high_word);
        mpz_mul_2exp(integer_, integer_, 64);
        mpz_add_ui(integer_, integer_, low_word);
        mpz_mul_2exp(integer_, integer_, 1);
        mpz_setbit(integer_, 105);
        mpz_setbit(integer_, 0);

        mpfr_set_z_2exp(source_, integer_, descriptor.exponent - 105,
                       MPFR_RNDN);
        if (descriptor.negative) {
            mpfr_neg(source_, source_, MPFR_RNDN);
        }

        double high = mpfr_get_d(source_, MPFR_RNDN);
        mpfr_set_d(high_, high, MPFR_RNDN);
        mpfr_sub(residual_, source_, high_, MPFR_RNDN);
        double low = mpfr_get_d(residual_, MPFR_RNDN);

        if (mpfr_cmp_d(residual_, low) != 0) {
            std::fprintf(stderr,
                         "MPFR residual was not exactly binary64\n");
            std::abort();
        }
        return finish(descriptor, high, low, 106);
    }

private:
    GeneratedDW finish(const ValueDescriptor &descriptor, double high,
                       double low, int source_precision) {
        mpfr_set_d(high_, high, MPFR_RNDN);
        mpfr_set_d(low_, low, MPFR_RNDN);
        mpfr_add(reconstructed_, high_, low_, MPFR_RNDN);

        bool expected_low = descriptor.ordinary ? low == 0.0 : low != 0.0;
        bool finite_components =
            std::isfinite(high) && high != 0.0 && std::isfinite(low);
        bool formal_double_word =
            finite_components && high + low == high;
        bool exact_reconstruction =
            mpfr_cmp(reconstructed_, source_) == 0;
        bool expected_exponent =
            mpfr_get_exp(source_) - 1 == descriptor.exponent;
        if (!expected_low || !formal_double_word || !exact_reconstruction
            || !expected_exponent) {
            std::fprintf(stderr,
                         "failed to construct an exact double-word input\n");
            std::abort();
        }

        return GeneratedDW{
            dword{high, low}, descriptor.exponent, source_precision,
            descriptor.negative, descriptor.ordinary,
            bits_of(high), bits_of(low)
        };
    }

    mpz_t integer_;
    mpfr_t source_;
    mpfr_t high_;
    mpfr_t residual_;
    mpfr_t low_;
    mpfr_t reconstructed_;
};

std::vector<ValueDescriptor> make_balanced_descriptors(
        std::size_t count, int minimum_exponent, int maximum_exponent,
        bool include_ordinary, std::uint64_t seed) {
    std::size_t bins = static_cast<std::size_t>(
        maximum_exponent - minimum_exponent + 1);
    bool even_bin_counts = count % 2 == 0 && count >= 2 * bins;
    std::size_t base = count / bins;
    if (even_bin_counts) base -= base % 2;
    std::size_t extra = count - base * bins;
    std::size_t offset =
        static_cast<std::size_t>(mix_seed(seed) % bins);
    bool extra_negative = false;
    std::vector<ValueDescriptor> descriptors;
    descriptors.reserve(count);

    for (std::size_t bin = 0; bin < bins; ++bin) {
        std::size_t rotated = (bin + bins - offset) % bins;
        std::size_t in_bin;
        if (even_bin_counts) {
            in_bin = base + (rotated < extra / 2 ? 2 : 0);
        } else {
            in_bin = base + (rotated < extra ? 1 : 0);
        }
        std::size_t positive = in_bin / 2;
        std::size_t negative = in_bin / 2;
        if (in_bin % 2 != 0) {
            if (extra_negative) ++negative;
            else ++positive;
            extra_negative = !extra_negative;
        }

        int exponent = minimum_exponent + static_cast<int>(bin);
        for (int sign = 0; sign < 2; ++sign) {
            std::size_t sign_count = sign == 0 ? positive : negative;
            std::size_t ordinary_count =
                include_ordinary ? (sign_count + 10) / 20 : 0;
            if (include_ordinary && sign_count >= 20
                && ordinary_count == 0) {
                ordinary_count = 1;
            }
            for (std::size_t i = 0; i < sign_count; ++i) {
                descriptors.push_back(ValueDescriptor{
                    exponent, sign != 0, i < ordinary_count
                });
            }
        }
    }

    if (descriptors.size() != count) {
        std::fprintf(stderr,
                     "failed to allocate the requested input count\n");
        std::abort();
    }

    std::mt19937_64 shuffle_rng(mix_seed(seed ^ UINT64_C(0x51ED270B)));
    deterministic_shuffle(descriptors, shuffle_rng);
    return descriptors;
}

std::vector<GeneratedFP> make_fp_values(
        std::size_t count, int minimum_exponent, int maximum_exponent,
        std::uint64_t seed) {
    std::vector<ValueDescriptor> descriptors = make_balanced_descriptors(
        count, minimum_exponent, maximum_exponent, false, seed);
    std::mt19937_64 value_rng(mix_seed(seed ^ UINT64_C(0xF00DFACE)));
    std::vector<GeneratedFP> values;
    values.reserve(count);
    for (const ValueDescriptor &descriptor : descriptors) {
        values.push_back(make_fp_value(descriptor, value_rng));
    }
    return values;
}

std::vector<GeneratedDW> make_dw_values(
        std::size_t count, int minimum_exponent, int maximum_exponent,
        std::uint64_t seed) {
    std::vector<ValueDescriptor> descriptors = make_balanced_descriptors(
        count, minimum_exponent, maximum_exponent, true, seed);
    std::mt19937_64 value_rng(mix_seed(seed ^ UINT64_C(0xD0B1E5)));
    DWBuilder builder;
    std::vector<GeneratedDW> values;
    values.reserve(count);
    for (const ValueDescriptor &descriptor : descriptors) {
        values.push_back(builder.make(descriptor, value_rng));
    }
    return values;
}

std::vector<double> make_timing_fp_values(std::size_t count,
                                          std::uint64_t seed) {
    std::vector<GeneratedFP> generated =
        make_fp_values(count, -100, 100, seed);
    std::vector<double> values;
    values.reserve(count);
    for (const GeneratedFP &item : generated) values.push_back(item.value);
    return values;
}

std::vector<dword> make_timing_dw_values(std::size_t count,
                                         std::uint64_t seed) {
    std::vector<GeneratedDW> generated =
        make_dw_values(count, -100, 100, seed);
    std::vector<dword> values;
    values.reserve(count);
    for (const GeneratedDW &item : generated) values.push_back(item.value);
    return values;
}

int exponent_of(const GeneratedFP &value) { return value.exponent; }
int exponent_of(const GeneratedDW &value) {
    return value.source_exponent;
}
bool ordinary_of(const GeneratedFP &) { return false; }
bool ordinary_of(const GeneratedDW &value) { return value.ordinary; }

template <class First, class Second>
PairCoverage measure_coverage(
        const std::vector<First> &first, const std::vector<Second> &second,
        int first_minimum_exponent, int first_maximum_exponent,
        int second_minimum_exponent, int second_maximum_exponent) {
    if (first.size() != second.size()) {
        std::fprintf(stderr, "paired input arrays have different lengths\n");
        std::abort();
    }

    std::size_t first_bin_count = static_cast<std::size_t>(
        first_maximum_exponent - first_minimum_exponent + 1);
    std::size_t second_bin_count = static_cast<std::size_t>(
        second_maximum_exponent - second_minimum_exponent + 1);
    std::vector<unsigned char> first_seen(first_bin_count, 0);
    std::vector<unsigned char> second_seen(second_bin_count, 0);
    PairCoverage coverage{first.size(), 0, 0, 0, 0, 0, 0};

    for (std::size_t i = 0; i < first.size(); ++i) {
        std::size_t first_index = static_cast<std::size_t>(
            exponent_of(first[i]) - first_minimum_exponent);
        std::size_t second_index = static_cast<std::size_t>(
            exponent_of(second[i]) - second_minimum_exponent);
        first_seen[first_index] = 1;
        second_seen[second_index] = 1;
        if (!first[i].negative) ++coverage.first_positive;
        if (!second[i].negative) ++coverage.second_positive;
        if (ordinary_of(first[i])) ++coverage.first_ordinary;
        if (ordinary_of(second[i])) ++coverage.second_ordinary;
    }

    for (unsigned char value : first_seen) coverage.first_bins += value != 0;
    for (unsigned char value : second_seen)
        coverage.second_bins += value != 0;
    return coverage;
}

class Fingerprint64 {
public:
    Fingerprint64() : value_(UINT64_C(14695981039346656037)) {}

    void add_word(std::uint64_t word) {
        for (unsigned int byte = 0; byte < 8; ++byte) {
            value_ ^= (word >> (8 * byte)) & UINT64_C(0xff);
            value_ *= UINT64_C(1099511628211);
        }
    }

    void begin_stream(std::uint64_t tag, std::size_t size) {
        add_word(tag);
        add_word(static_cast<std::uint64_t>(size));
    }

    std::uint64_t value() const { return value_; }

private:
    std::uint64_t value_;
};

template <class Values>
void add_fp_stream(Fingerprint64 &fingerprint, std::uint64_t tag,
                   const Values &values) {
    fingerprint.begin_stream(tag, values.size());
    for (const auto &value : values) {
        fingerprint.add_word(bits_of(value));
    }
}

void add_generated_fp_stream(Fingerprint64 &fingerprint, std::uint64_t tag,
                             const std::vector<GeneratedFP> &values) {
    fingerprint.begin_stream(tag, values.size());
    for (const GeneratedFP &value : values) {
        fingerprint.add_word(value.bits);
    }
}

template <class Values>
void add_dw_stream(Fingerprint64 &fingerprint, std::uint64_t tag,
                   const Values &values) {
    fingerprint.begin_stream(tag, values.size());
    for (const auto &value : values) {
        fingerprint.add_word(bits_of(value.s));
        fingerprint.add_word(bits_of(value.t));
    }
}

void add_generated_dw_stream(Fingerprint64 &fingerprint, std::uint64_t tag,
                             const std::vector<GeneratedDW> &values) {
    fingerprint.begin_stream(tag, values.size());
    for (const GeneratedDW &value : values) {
        fingerprint.add_word(value.hi_bits);
        fingerprint.add_word(value.lo_bits);
    }
}

}  // namespace

std::uint64_t bits_of(double value) {
    std::uint64_t bits;
    std::memcpy(&bits, &value, sizeof(bits));
    return bits;
}

GeneratedTestInputs make_generated_test_inputs(
        std::size_t samples_per_exponent) {
    std::size_t fp_case_count = fp_exponent_bins * samples_per_exponent;
    std::size_t dw_case_count = dw_exponent_bins * samples_per_exponent;

    GeneratedTestInputs inputs;
    inputs.fp_first = make_fp_values(
        fp_case_count, fp_min_exponent, fp_max_exponent,
        mix_seed(generator_seed ^ UINT64_C(0x1001)));
    inputs.fp_second = make_fp_values(
        fp_case_count, fp_min_exponent, fp_max_exponent,
        mix_seed(generator_seed ^ UINT64_C(0x1002)));
    inputs.mixed_dw = make_dw_values(
        dw_case_count, dw_min_exponent, dw_max_exponent,
        mix_seed(generator_seed ^ UINT64_C(0x2001)));
    inputs.mixed_fp = make_fp_values(
        dw_case_count, fp_min_exponent, fp_max_exponent,
        mix_seed(generator_seed ^ UINT64_C(0x2002)));
    inputs.dw_first = make_dw_values(
        dw_case_count, dw_min_exponent, dw_max_exponent,
        mix_seed(generator_seed ^ UINT64_C(0x3001)));
    inputs.dw_second = make_dw_values(
        dw_case_count, dw_min_exponent, dw_max_exponent,
        mix_seed(generator_seed ^ UINT64_C(0x3002)));

    inputs.fp_coverage = measure_coverage(
        inputs.fp_first, inputs.fp_second,
        fp_min_exponent, fp_max_exponent,
        fp_min_exponent, fp_max_exponent);
    inputs.mixed_coverage = measure_coverage(
        inputs.mixed_dw, inputs.mixed_fp,
        dw_min_exponent, dw_max_exponent,
        fp_min_exponent, fp_max_exponent);
    inputs.dw_coverage = measure_coverage(
        inputs.dw_first, inputs.dw_second,
        dw_min_exponent, dw_max_exponent,
        dw_min_exponent, dw_max_exponent);
    inputs.fingerprint = fingerprint_generated_inputs(inputs);
    return inputs;
}

TimingInputs make_timing_inputs(std::size_t count) {
    TimingInputs inputs;
    inputs.first_fp = make_timing_fp_values(
        count, mix_seed(generator_seed ^ UINT64_C(0x4001)));
    inputs.second_fp = make_timing_fp_values(
        count, mix_seed(generator_seed ^ UINT64_C(0x4002)));
    inputs.scalar = make_timing_fp_values(
        count, mix_seed(generator_seed ^ UINT64_C(0x4003)));
    inputs.first_dw = make_timing_dw_values(
        count, mix_seed(generator_seed ^ UINT64_C(0x5001)));
    inputs.second_dw = make_timing_dw_values(
        count, mix_seed(generator_seed ^ UINT64_C(0x5002)));

    inputs.fast_first.resize(count);
    inputs.fast_second.resize(count);
    for (std::size_t i = 0; i < count; ++i) {
        inputs.fast_first[i] = inputs.first_fp[i];
        inputs.fast_second[i] = inputs.second_fp[i];
        if (std::abs(inputs.fast_second[i])
            > std::abs(inputs.fast_first[i])) {
            std::swap(inputs.fast_first[i], inputs.fast_second[i]);
        }
    }
    inputs.fingerprint = fingerprint_timing_inputs(inputs);
    return inputs;
}

std::string describe_inputs(const GeneratedFP &first,
                            const GeneratedFP &second) {
    char text[160];
    std::snprintf(text, sizeof(text),
                  "a[e=%d]=0x%016llx b[e=%d]=0x%016llx",
                  first.exponent,
                  static_cast<unsigned long long>(first.bits),
                  second.exponent,
                  static_cast<unsigned long long>(second.bits));
    return text;
}

std::string describe_inputs(const GeneratedDW &first,
                            const GeneratedFP &second) {
    char text[224];
    std::snprintf(text, sizeof(text),
                  "x[e=%d]=(0x%016llx,0x%016llx) y[e=%d]=0x%016llx",
                  first.source_exponent,
                  static_cast<unsigned long long>(first.hi_bits),
                  static_cast<unsigned long long>(first.lo_bits),
                  second.exponent,
                  static_cast<unsigned long long>(second.bits));
    return text;
}

std::string describe_inputs(const GeneratedDW &first,
                            const GeneratedDW &second) {
    char text[288];
    std::snprintf(text, sizeof(text),
                  "x[e=%d]=(0x%016llx,0x%016llx) "
                  "y[e=%d]=(0x%016llx,0x%016llx)",
                  first.source_exponent,
                  static_cast<unsigned long long>(first.hi_bits),
                  static_cast<unsigned long long>(first.lo_bits),
                  second.source_exponent,
                  static_cast<unsigned long long>(second.hi_bits),
                  static_cast<unsigned long long>(second.lo_bits));
    return text;
}

std::uint64_t fingerprint_generated_inputs(
        const GeneratedTestInputs &inputs) {
    Fingerprint64 fingerprint;
    fingerprint.add_word(UINT64_C(0x4e554d4552494341));
    add_generated_fp_stream(fingerprint, 1, inputs.fp_first);
    add_generated_fp_stream(fingerprint, 2, inputs.fp_second);
    add_generated_dw_stream(fingerprint, 3, inputs.mixed_dw);
    add_generated_fp_stream(fingerprint, 4, inputs.mixed_fp);
    add_generated_dw_stream(fingerprint, 5, inputs.dw_first);
    add_generated_dw_stream(fingerprint, 6, inputs.dw_second);
    return fingerprint.value();
}

std::uint64_t fingerprint_timing_inputs(const TimingInputs &inputs) {
    Fingerprint64 fingerprint;
    fingerprint.add_word(UINT64_C(0x54494d494e474350));
    add_fp_stream(fingerprint, 1, inputs.first_fp);
    add_fp_stream(fingerprint, 2, inputs.second_fp);
    add_fp_stream(fingerprint, 3, inputs.scalar);
    add_dw_stream(fingerprint, 4, inputs.first_dw);
    add_dw_stream(fingerprint, 5, inputs.second_dw);
    add_fp_stream(fingerprint, 6, inputs.fast_first);
    add_fp_stream(fingerprint, 7, inputs.fast_second);
    return fingerprint.value();
}

}  // namespace bench_eval
