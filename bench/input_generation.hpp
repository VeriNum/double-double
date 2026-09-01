#ifndef BENCH_INPUT_GENERATION_HPP
#define BENCH_INPUT_GENERATION_HPP

#include "evaluation_types.hpp"

namespace bench_eval {

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
