#ifndef BENCH_INPUT_GENERATION_HPP
#define BENCH_INPUT_GENERATION_HPP

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

extern "C" {
#include "dw_arith.h"
}

namespace bench_eval {

constexpr std::uint64_t generator_seed = UINT64_C(0xC0FFEE);
constexpr const char generator_version[] = "mpfr106-v1";
constexpr int dw_min_exponent = -969;
constexpr int dw_max_exponent = 1022;
constexpr int fp_min_exponent = -1074;
constexpr int fp_max_exponent = 1023;
constexpr long construction_precision = 256;
constexpr long reference_precision = 2112;

constexpr std::size_t dw_exponent_bins =
    static_cast<std::size_t>(dw_max_exponent - dw_min_exponent + 1);
constexpr std::size_t fp_exponent_bins =
    static_cast<std::size_t>(fp_max_exponent - fp_min_exponent + 1);

struct ResultPair {
    double hi;
    double lo;
};

struct GeneratedFP {
    double value;
    int exponent;
    bool negative;
    std::uint64_t bits;
};

struct GeneratedDW {
    dword value;
    int source_exponent;
    int source_precision;
    bool negative;
    bool ordinary;
    std::uint64_t hi_bits;
    std::uint64_t lo_bits;
};

struct PairCoverage {
    std::size_t cases;
    std::size_t first_bins;
    std::size_t second_bins;
    std::size_t first_positive;
    std::size_t second_positive;
    std::size_t first_ordinary;
    std::size_t second_ordinary;
};

struct GeneratedTestInputs {
    std::vector<GeneratedFP> fp_first;
    std::vector<GeneratedFP> fp_second;
    std::vector<GeneratedDW> mixed_dw;
    std::vector<GeneratedFP> mixed_fp;
    std::vector<GeneratedDW> dw_first;
    std::vector<GeneratedDW> dw_second;
    PairCoverage fp_coverage;
    PairCoverage mixed_coverage;
    PairCoverage dw_coverage;
    std::uint64_t fingerprint;
};

struct TimingInputs {
    std::vector<double> first_fp;
    std::vector<double> second_fp;
    std::vector<double> scalar;
    std::vector<double> fast_first;
    std::vector<double> fast_second;
    std::vector<dword> first_dw;
    std::vector<dword> second_dw;
    std::uint64_t fingerprint;
};

std::uint64_t bits_of(double value);

GeneratedTestInputs make_generated_test_inputs(std::size_t samples_per_exponent);
TimingInputs make_timing_inputs(std::size_t count);

std::string describe_inputs(const GeneratedFP &first,
                            const GeneratedFP &second);
std::string describe_inputs(const GeneratedDW &first,
                            const GeneratedFP &second);
std::string describe_inputs(const GeneratedDW &first,
                            const GeneratedDW &second);

/*
 * Input fingerprints use 64-bit FNV-1a. Each stream starts with a numeric
 * stream tag and its element count. Every binary64 encoding is then supplied
 * as eight bytes, least-significant byte first, in vector order. A double word
 * contributes its high encoding followed by its low encoding.
 *
 * Numerical stream order is fp_first, fp_second, mixed_dw, mixed_fp,
 * dw_first, dw_second. Timing stream order is first_fp, second_fp, scalar,
 * first_dw, second_dw, fast_first, fast_second. The explicit byte order makes
 * the fingerprint independent of host endianness.
 */
std::uint64_t fingerprint_generated_inputs(const GeneratedTestInputs &inputs);
std::uint64_t fingerprint_timing_inputs(const TimingInputs &inputs);

}  // namespace bench_eval

#endif  // BENCH_INPUT_GENERATION_HPP
