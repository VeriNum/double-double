#include "boundary_cases.hpp"

#include <cmath>
#include <cfloat>
#include <limits>

namespace bench_eval {
namespace {

dword make_word(double high, bool nonzero_low = false) {
    double low = 0.0;
    if (nonzero_low && high != 0.0 && std::isfinite(high)) {
        int exponent = std::ilogb(std::fabs(high));
        low = std::copysign(std::ldexp(1.0, exponent - 54), high);
    }
    return dword{high, low};
}

double below(double value) {
    return std::nextafter(value, 0.0);
}

double above(double value) {
    return std::nextafter(value, std::numeric_limits<double>::infinity());
}

} // namespace

std::vector<DwFpBoundaryCase> make_dw_fp_boundary_cases() {
    using B = BoundaryOutcome;
    const double high_limit = std::ldexp(1.0, 1022);
    const double dividend_lower = std::ldexp(1.0, -968);
    const double factor = std::ldexp(1.0, 511);
    const double product_partner = std::ldexp(1.0, 512);
    const double quotient_divisor = std::ldexp(1.0, -511);

    std::vector<DwFpBoundaryCase> cases;
    auto add = [&](CompositeOperation operation, const char *name,
                   dword first, double second,
                   B expected_default = B::normal,
                   B expected_strong = B::normal,
                   std::uint32_t expected_failures = 0) {
        cases.push_back(DwFpBoundaryCase{
            operation, name, first, second, expected_default,
            expected_strong, expected_failures});
    };

    add(CompositeOperation::dw_plus_fp, "x_high_below_2^1022",
        make_word(below(high_limit)), 1.0);
    add(CompositeOperation::dw_plus_fp, "x_high_at_2^1022_nonzero_low",
        make_word(high_limit, true), 1.0);
    add(CompositeOperation::dw_plus_fp, "x_high_above_2^1022",
        make_word(above(high_limit)), 1.0,
        B::normal, B::input_check, first_high_limit);
    add(CompositeOperation::dw_plus_fp, "scalar_below_2^1022",
        make_word(1.0, true), below(high_limit));
    add(CompositeOperation::dw_plus_fp, "scalar_at_2^1022",
        make_word(1.0), high_limit);
    add(CompositeOperation::dw_plus_fp, "scalar_above_2^1022",
        make_word(1.0), above(high_limit),
        B::normal, B::input_check, second_high_limit);
    add(CompositeOperation::dw_plus_fp, "large_exact_cancellation",
        make_word(above(high_limit)), -above(high_limit),
        B::normal, B::input_check,
        first_high_limit | second_high_limit);
    add(CompositeOperation::dw_plus_fp, "post_compute_overflow",
        make_word(DBL_MAX), DBL_MAX,
        B::post_compute, B::input_check,
        first_high_limit | second_high_limit);

    add(CompositeOperation::dw_times_fp, "leading_product_below_2^1023",
        make_word(factor), below(product_partner));
    add(CompositeOperation::dw_times_fp,
        "leading_product_at_2^1023_nonzero_low",
        make_word(factor, true), product_partner,
        B::normal, B::input_check, leading_product_limit);
    add(CompositeOperation::dw_times_fp, "leading_product_above_2^1023",
        make_word(factor), above(product_partner),
        B::normal, B::input_check, leading_product_limit);
    add(CompositeOperation::dw_times_fp, "post_compute_overflow",
        make_word(DBL_MAX), 2.0,
        B::post_compute, B::input_check, leading_product_limit);

    add(CompositeOperation::dw_div_fp, "x_high_below_2^1022",
        make_word(below(high_limit)), 2.0);
    add(CompositeOperation::dw_div_fp, "x_high_at_2^1022_nonzero_low",
        make_word(high_limit, true), 2.0);
    add(CompositeOperation::dw_div_fp, "x_high_above_2^1022",
        make_word(above(high_limit)), 2.0,
        B::normal, B::input_check, first_high_limit);
    add(CompositeOperation::dw_div_fp, "x_high_below_2^-968",
        make_word(below(dividend_lower)), 1.0,
        B::input_check, B::input_check);
    add(CompositeOperation::dw_div_fp, "x_high_at_2^-968",
        make_word(dividend_lower, true), 1.0);
    add(CompositeOperation::dw_div_fp, "x_high_above_2^-968",
        make_word(above(dividend_lower)), 1.0);
    add(CompositeOperation::dw_div_fp, "zero_dividend",
        make_word(0.0), 2.0);
    add(CompositeOperation::dw_div_fp, "leading_quotient_below_2^1022",
        make_word(factor), above(quotient_divisor));
    add(CompositeOperation::dw_div_fp, "leading_quotient_at_2^1022",
        make_word(factor, true), quotient_divisor,
        B::normal, B::input_check, leading_quotient_limit);
    add(CompositeOperation::dw_div_fp, "leading_quotient_above_2^1022",
        make_word(factor), below(quotient_divisor),
        B::normal, B::input_check, leading_quotient_limit);
    add(CompositeOperation::dw_div_fp, "zero_divisor_post_compute",
        make_word(1.0), 0.0,
        B::post_compute, B::input_check, nonzero_divisor);
    add(CompositeOperation::dw_div_fp, "post_compute_overflow",
        make_word(1.0), std::numeric_limits<double>::denorm_min(),
        B::post_compute, B::input_check, leading_quotient_limit);

    return cases;
}

std::vector<DwDwBoundaryCase> make_dw_dw_boundary_cases() {
    using B = BoundaryOutcome;
    const double high_limit = std::ldexp(1.0, 1022);
    const double factor = std::ldexp(1.0, 511);
    const double product_partner = std::ldexp(1.0, 512);
    const double quotient_divisor = std::ldexp(1.0, -511);
    const double divisor_lower = std::ldexp(1.0, -968);
    const double divisor_upper = std::ldexp(1.0, 966);

    std::vector<DwDwBoundaryCase> cases;
    auto add = [&](CompositeOperation operation, const char *name,
                   dword first, dword second,
                   B expected_default = B::normal,
                   B expected_strong = B::normal,
                   std::uint32_t expected_failures = 0) {
        cases.push_back(DwDwBoundaryCase{
            operation, name, first, second, expected_default,
            expected_strong, expected_failures});
    };

    add(CompositeOperation::dw_plus_dw, "first_high_below_2^1022",
        make_word(below(high_limit)), make_word(1.0));
    add(CompositeOperation::dw_plus_dw,
        "first_high_at_2^1022_nonzero_low",
        make_word(high_limit, true), make_word(1.0));
    add(CompositeOperation::dw_plus_dw, "first_high_above_2^1022",
        make_word(above(high_limit)), make_word(1.0),
        B::normal, B::input_check, first_high_limit);
    add(CompositeOperation::dw_plus_dw, "second_high_below_2^1022",
        make_word(1.0), make_word(below(high_limit)));
    add(CompositeOperation::dw_plus_dw,
        "second_high_at_2^1022_nonzero_low",
        make_word(1.0), make_word(high_limit, true));
    add(CompositeOperation::dw_plus_dw, "second_high_above_2^1022",
        make_word(1.0), make_word(above(high_limit)),
        B::normal, B::input_check, second_high_limit);
    add(CompositeOperation::dw_plus_dw, "large_exact_cancellation",
        make_word(above(high_limit)), make_word(-above(high_limit)),
        B::normal, B::input_check,
        first_high_limit | second_high_limit);
    add(CompositeOperation::dw_plus_dw, "post_compute_overflow",
        make_word(DBL_MAX), make_word(DBL_MAX),
        B::post_compute, B::input_check,
        first_high_limit | second_high_limit);

    add(CompositeOperation::dw_times_dw, "leading_product_below_2^1023",
        make_word(factor), make_word(below(product_partner)));
    add(CompositeOperation::dw_times_dw,
        "leading_product_at_2^1023_nonzero_lows",
        make_word(factor, true), make_word(product_partner, true),
        B::normal, B::input_check, leading_product_limit);
    add(CompositeOperation::dw_times_dw, "leading_product_above_2^1023",
        make_word(factor), make_word(above(product_partner)),
        B::normal, B::input_check, leading_product_limit);
    add(CompositeOperation::dw_times_dw, "post_compute_overflow",
        make_word(DBL_MAX), make_word(2.0),
        B::post_compute, B::input_check, leading_product_limit);

    add(CompositeOperation::dw_div_dw, "leading_quotient_below_2^1022",
        make_word(factor), make_word(above(quotient_divisor)));
    add(CompositeOperation::dw_div_dw,
        "leading_quotient_at_2^1022_nonzero_lows",
        make_word(factor, true), make_word(quotient_divisor, true),
        B::normal, B::input_check, leading_quotient_limit);
    add(CompositeOperation::dw_div_dw, "leading_quotient_above_2^1022",
        make_word(factor), make_word(below(quotient_divisor)),
        B::normal, B::input_check, leading_quotient_limit);
    add(CompositeOperation::dw_div_dw, "divisor_high_below_2^-968",
        make_word(divisor_lower), make_word(below(divisor_lower)),
        B::input_check, B::input_check);
    add(CompositeOperation::dw_div_dw, "divisor_high_at_2^-968",
        make_word(divisor_lower, true), make_word(divisor_lower, true));
    add(CompositeOperation::dw_div_dw, "divisor_high_above_2^-968",
        make_word(divisor_lower), make_word(above(divisor_lower)));
    add(CompositeOperation::dw_div_dw, "divisor_high_below_2^966",
        make_word(divisor_upper), make_word(below(divisor_upper)));
    add(CompositeOperation::dw_div_dw, "divisor_high_at_2^966",
        make_word(divisor_upper, true), make_word(divisor_upper, true));
    add(CompositeOperation::dw_div_dw, "divisor_high_above_2^966",
        make_word(divisor_upper), make_word(above(divisor_upper)),
        B::input_check, B::input_check);
    add(CompositeOperation::dw_div_dw, "zero_dividend",
        make_word(0.0), make_word(1.0));
    add(CompositeOperation::dw_div_dw, "zero_divisor",
        make_word(1.0), make_word(0.0),
        B::input_check, B::input_check);
    add(CompositeOperation::dw_div_dw, "post_compute_overflow",
        make_word(DBL_MAX), make_word(divisor_lower),
        B::post_compute, B::input_check, leading_quotient_limit);

    return cases;
}

} // namespace bench_eval
