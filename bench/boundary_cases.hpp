#ifndef DD_EVAL_BOUNDARY_CASES_HPP
#define DD_EVAL_BOUNDARY_CASES_HPP

#include "operation_metadata.hpp"

extern "C" {
#include "dw_arith.h"
}

#include <string>
#include <cstdint>
#include <vector>

namespace bench_eval {

enum AdditionalStrongFailure : std::uint32_t {
    first_high_limit = 1u << 0,
    second_high_limit = 1u << 1,
    leading_product_limit = 1u << 2,
    nonzero_divisor = 1u << 3,
    leading_quotient_limit = 1u << 4
};

enum class BoundaryOutcome {
    input_check,
    post_compute,
    normal
};

struct DwFpBoundaryCase {
    CompositeOperation operation;
    std::string name;
    dword first;
    double second;
    BoundaryOutcome expected_default;
    BoundaryOutcome expected_strong;
    std::uint32_t expected_additional_failures;
};

struct DwDwBoundaryCase {
    CompositeOperation operation;
    std::string name;
    dword first;
    dword second;
    BoundaryOutcome expected_default;
    BoundaryOutcome expected_strong;
    std::uint32_t expected_additional_failures;
};

std::vector<DwFpBoundaryCase> make_dw_fp_boundary_cases();
std::vector<DwDwBoundaryCase> make_dw_dw_boundary_cases();

} // namespace bench_eval

#endif
