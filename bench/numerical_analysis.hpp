#ifndef BENCH_NUMERICAL_ANALYSIS_HPP
#define BENCH_NUMERICAL_ANALYSIS_HPP

#include "analysis_common.hpp"

#include <functional>
#include <string>

#include <mpfr.h>

namespace bench_analysis {

constexpr mpfr_prec_t analysis_precision = 4224;
constexpr mpfr_prec_t check_precision = 2 * analysis_precision;

enum class Outcome {
    not_available,
    normal,
    input_check,
    weak_input_check,
    post_check,
    strong_check,
    execution_exit,
    unclassified,
};

enum class ErrorRegime {
    relative,
    absolute,
    zero_bound,
};

struct ResultFacts {
    bool present = false;
    bool finite = false;
    bool valid_double_word = false;
    bool exact = false;
    bool has_error = false;
    bool has_relative_error = false;
    bool has_bound_ratio = false;
    bool bound_was_checked = false;
    bool bound_is_unresolved = false;
    int bound_compare = 0;
};

struct ResultView {
    const ResultFacts &facts;
    mpfr_srcptr error;
    mpfr_srcptr relative_error;
    mpfr_srcptr bound_ratio;
};

struct NumericalCase {
    std::size_t operation_index;
    std::size_t case_id;
    Outcome default_outcome;
    Outcome strong_outcome;
    ErrorRegime regime;
    ResultView fencedd;
    ResultView qd;
};

using NumericalConsumer =
    std::function<void(const OperationSpec &, const NumericalCase &)>;

class Real {
public:
    explicit Real(mpfr_prec_t precision = analysis_precision);
    ~Real();

    Real(const Real &) = delete;
    Real &operator=(const Real &) = delete;

    mpfr_ptr get();
    mpfr_srcptr get() const;

private:
    mpfr_t value_;
};

std::string format_real(mpfr_srcptr value);
void read_numerical_data(const std::string &path,
                         const NumericalConsumer &accept);

}  // namespace bench_analysis

#endif
