// Read raw numerical data and form exact values for RQ1 and RQ2.
//
// This code does not change a raw file. It does not run code from FenceDD or
// QD. It derives reference values and bounds from the values in the raw files.
//
// The main number work uses 4224 bits. A close bound test uses 8448 bits. A
// bound test is marked as unresolved when the two tests do not agree.

#include <mpfr.h>

#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <limits>
#include <locale>
#include <string>
#include <vector>

#include "numerical_analysis.hpp"

namespace bench_analysis {

Real::Real(mpfr_prec_t precision) {
    mpfr_init2(value_, precision);
}

Real::~Real() {
    mpfr_clear(value_);
}

mpfr_ptr Real::get() {
    return value_;
}

mpfr_srcptr Real::get() const {
    return value_;
}

namespace {

constexpr int text_digits = 100;

const char numerical_header[] =
    "operation\tcase_id\tfirst_hi_bits\tfirst_lo_bits"
    "\tsecond_hi_bits\tsecond_lo_bits\tdefault_outcome"
    "\tdefault_result_hi_bits\tdefault_result_lo_bits"
    "\tstrong_outcome\tstrong_result_hi_bits"
    "\tstrong_result_lo_bits\tqd_result_hi_bits"
    "\tqd_result_lo_bits";

double value_from_bits(std::uint64_t bits) {
    double value;
    static_assert(sizeof(value) == sizeof(bits), "binary64 size is required");
    std::memcpy(&value, &bits, sizeof(value));
    return value;
}


// Store the bits for one value with two parts.
struct PairBits {
    bool present = false;
    std::uint64_t hi = 0;
    std::uint64_t lo = 0;
};

// Store the bits for one value with one or two parts.
struct OperandBits {
    std::uint64_t hi = 0;
    bool has_lo = false;
    std::uint64_t lo = 0;
};

// Store one row from the number file.
struct NumericalRow {
    std::size_t operation = 0;
    std::size_t case_id = 0;
    OperandBits first;
    OperandBits second;
    Outcome default_outcome = Outcome::not_available;
    PairBits default_result;
    Outcome strong_outcome = Outcome::not_available;
    PairBits strong_result;
    PairBits qd_result;
};

struct CaseInput {
    OperandBits first;
    OperandBits second;
};


// Hold values for one result.
struct ResultValues {
    explicit ResultValues(mpfr_prec_t precision)
        : value(precision), error(precision), relative_error(precision),
          bound_ratio(precision) {}

    Real value;
    Real error;
    Real relative_error;
    Real bound_ratio;
};

// Reuse these values for each row.
struct NumericWorkspace {
    explicit NumericWorkspace(mpfr_prec_t precision)
        : first(precision), second(precision), reference(precision),
          magnitude(precision), relative_term(precision),
          absolute_term(precision), bound(precision), scratch(precision),
          temp(precision), distance(precision), threshold(precision),
          u(precision), u_squared(precision), eta(precision),
          fencedd(precision), qd(precision) {
        mpfr_set_ui_2exp(u.get(), 1, -53, MPFR_RNDN);
        mpfr_mul(u_squared.get(), u.get(), u.get(), MPFR_RNDN);
        mpfr_set_ui_2exp(eta.get(), 1, -1074, MPFR_RNDN);
    }

    Real first;
    Real second;
    Real reference;
    Real magnitude;
    Real relative_term;
    Real absolute_term;
    Real bound;
    Real scratch;
    Real temp;
    Real distance;
    Real threshold;
    Real u;
    Real u_squared;
    Real eta;
    ResultValues fencedd;
    ResultValues qd;
};

// Hold all work for one row.
struct CaseAnalysis {
    ErrorRegime regime = ErrorRegime::relative;
    ResultFacts fencedd;
    ResultFacts qd;
};

bool same_operand(const OperandBits &left, const OperandBits &right) {
    return left.hi == right.hi && left.has_lo == right.has_lo
        && (!left.has_lo || left.lo == right.lo);
}

bool same_input(const CaseInput &left, const NumericalRow &right) {
    return same_operand(left.first, right.first)
        && same_operand(left.second, right.second);
}

Outcome parse_outcome(const std::string &text, const std::string &path,
                      std::size_t line, const char *field) {
    if (text == "-") return Outcome::not_available;
    if (text == "normal") return Outcome::normal;
    if (text == "input_check") return Outcome::input_check;
    if (text == "weak_input_check") return Outcome::weak_input_check;
    if (text == "post_check") return Outcome::post_check;
    if (text == "strong_check") return Outcome::strong_check;
    if (text == "execution_exit") return Outcome::execution_exit;
    if (text == "unclassified") return Outcome::unclassified;
    fail(path, line, std::string(field) + " is not known");
}

PairBits parse_pair(const std::string &hi, const std::string &lo,
                    const std::string &path, std::size_t line,
                    const char *field) {
    if (hi == "-" && lo == "-") return PairBits{};
    if (hi == "-" || lo == "-") {
        fail(path, line, std::string(field) + " has one missing part");
    }
    PairBits pair;
    pair.present = true;
    pair.hi = parse_bits(hi, path, line, field);
    pair.lo = parse_bits(lo, path, line, field);
    return pair;
}

const OperationSpec &find_operation(const std::string &name,
                                    std::size_t &index,
                                    const std::string &path,
                                    std::size_t line) {
    for (std::size_t i = 0; i < operations.size(); ++i) {
        if (name == operations[i].name) {
            index = i;
            return operations[i];
        }
    }
    fail(path, line, "operation is not known");
}

NumericalRow parse_numerical_row(const std::string &text,
                                 const OperationSpec &expected_operation,
                                 std::size_t expected_operation_index,
                                 std::size_t expected_case,
                                 const std::string &path,
                                 std::size_t line) {
    const std::vector<std::string> fields = split_tabs(text);
    if (fields.size() != 14) fail(path, line, "row must have 14 fields");

    std::size_t operation_index = 0;
    const OperationSpec &operation =
        find_operation(fields[0], operation_index, path, line);
    if (operation_index != expected_operation_index
        || std::strcmp(operation.name, expected_operation.name) != 0) {
        fail(path, line, "operation is out of order");
    }

    NumericalRow row;
    row.operation = operation_index;
    row.case_id = parse_size(fields[1], path, line, "case_id");
    if (row.case_id != expected_case) fail(path, line, "case_id is out of order");

    row.first.hi = parse_bits(fields[2], path, line, "first_hi_bits");
    row.first.has_lo = fields[3] != "-";
    if (row.first.has_lo) {
        row.first.lo = parse_bits(fields[3], path, line, "first_lo_bits");
    }
    row.second.hi = parse_bits(fields[4], path, line, "second_hi_bits");
    row.second.has_lo = fields[5] != "-";
    if (row.second.has_lo) {
        row.second.lo = parse_bits(fields[5], path, line, "second_lo_bits");
    }
    if (row.first.has_lo != operation.first_has_lo
        || row.second.has_lo != operation.second_has_lo) {
        fail(path, line, "value form does not match the operation");
    }

    row.default_outcome =
        parse_outcome(fields[6], path, line, "default_outcome");
    row.default_result =
        parse_pair(fields[7], fields[8], path, line, "default_result");
    row.strong_outcome =
        parse_outcome(fields[9], path, line, "strong_outcome");
    row.strong_result =
        parse_pair(fields[10], fields[11], path, line, "strong_result");
    row.qd_result =
        parse_pair(fields[12], fields[13], path, line, "qd_result");

    if (row.default_outcome == Outcome::normal
        && !row.default_result.present) {
        fail(path, line, "normal default result is missing");
    }
    if (row.strong_outcome == Outcome::normal && !row.strong_result.present) {
        fail(path, line, "normal strong result is missing");
    }
    if (operation.eft
        && (row.strong_outcome != Outcome::not_available
            || row.strong_result.present)) {
        fail(path, line, "strong data is not valid for this operation");
    }
    if (!row.qd_result.present) fail(path, line, "QD result is missing");
    return row;
}

void set_operand(mpfr_ptr value, const OperandBits &bits, mpfr_ptr scratch) {
    mpfr_set_d(value, value_from_bits(bits.hi), MPFR_RNDN);
    if (!bits.has_lo) return;
    mpfr_set_d(scratch, value_from_bits(bits.lo), MPFR_RNDN);
    mpfr_add(value, value, scratch, MPFR_RNDN);
}

void set_pair(mpfr_ptr value, const PairBits &bits, mpfr_ptr scratch) {
    mpfr_set_d(value, value_from_bits(bits.hi), MPFR_RNDN);
    mpfr_set_d(scratch, value_from_bits(bits.lo), MPFR_RNDN);
    mpfr_add(value, value, scratch, MPFR_RNDN);
}

// Find the reference value for one row.
void compute_reference(const NumericalRow &row,
                       const OperationSpec &operation,
                       NumericWorkspace &work) {
    set_operand(work.first.get(), row.first, work.scratch.get());
    set_operand(work.second.get(), row.second, work.scratch.get());
    switch (operation.math) {
    case MathKind::add:
        mpfr_add(work.reference.get(), work.first.get(), work.second.get(),
                 MPFR_RNDN);
        break;
    case MathKind::multiply:
        mpfr_mul(work.reference.get(), work.first.get(), work.second.get(),
                 MPFR_RNDN);
        break;
    case MathKind::divide:
        mpfr_div(work.reference.get(), work.first.get(), work.second.get(),
                 MPFR_RNDN);
        break;
    }
    mpfr_abs(work.magnitude.get(), work.reference.get(), MPFR_RNDN);
}

// Find each term in the proved bound.
void compute_bound(const OperationSpec &operation, NumericWorkspace &work) {
    mpfr_set_zero(work.relative_term.get(), 0);
    mpfr_set_zero(work.absolute_term.get(), 0);
    mpfr_set_zero(work.bound.get(), 0);
    if (operation.bound == BoundKind::none) return;

    mpfr_mul(work.relative_term.get(), work.u_squared.get(),
             work.magnitude.get(), MPFR_RNDN);
    switch (operation.bound) {
    case BoundKind::none:
        return;
    case BoundKind::plus_fp:
        // The bound is 2 u^2 |r|.
        mpfr_mul_ui(work.relative_term.get(), work.relative_term.get(), 2,
                    MPFR_RNDN);
        break;
    case BoundKind::plus_dw:
        // The bound is 3 u^2 |r| / (1 - 4 u).
        mpfr_mul_ui(work.relative_term.get(), work.relative_term.get(), 3,
                    MPFR_RNDN);
        mpfr_mul_ui(work.temp.get(), work.u.get(), 4, MPFR_RNDN);
        mpfr_ui_sub(work.temp.get(), 1, work.temp.get(), MPFR_RNDN);
        mpfr_div(work.relative_term.get(), work.relative_term.get(),
                 work.temp.get(), MPFR_RNDN);
        break;
    case BoundKind::times_fp:
        // The bound is 2 u^2 |r| + 251 eta / 100.
        mpfr_mul_ui(work.relative_term.get(), work.relative_term.get(), 2,
                    MPFR_RNDN);
        mpfr_mul_ui(work.absolute_term.get(), work.eta.get(), 251,
                    MPFR_RNDN);
        mpfr_div_ui(work.absolute_term.get(), work.absolute_term.get(), 100,
                    MPFR_RNDN);
        break;
    case BoundKind::times_dw:
        // The bound is 4 u^2 |r| + 5 eta / 2.
        mpfr_mul_ui(work.relative_term.get(), work.relative_term.get(), 4,
                    MPFR_RNDN);
        mpfr_mul_ui(work.absolute_term.get(), work.eta.get(), 5,
                    MPFR_RNDN);
        mpfr_div_ui(work.absolute_term.get(), work.absolute_term.get(), 2,
                    MPFR_RNDN);
        break;
    case BoundKind::div_fp:
        // The bound is 3 u^2 |r| + eta.
        mpfr_mul_ui(work.relative_term.get(), work.relative_term.get(), 3,
                    MPFR_RNDN);
        mpfr_set(work.absolute_term.get(), work.eta.get(), MPFR_RNDN);
        break;
    case BoundKind::div_dw:
        // The bound is 98 u^2 |r| / 10 + 5 eta / 2.
        mpfr_mul_ui(work.relative_term.get(), work.relative_term.get(), 98,
                    MPFR_RNDN);
        mpfr_div_ui(work.relative_term.get(), work.relative_term.get(), 10,
                    MPFR_RNDN);
        mpfr_mul_ui(work.absolute_term.get(), work.eta.get(), 5,
                    MPFR_RNDN);
        mpfr_div_ui(work.absolute_term.get(), work.absolute_term.get(), 2,
                    MPFR_RNDN);
        break;
    }
    mpfr_add(work.bound.get(), work.relative_term.get(),
             work.absolute_term.get(), MPFR_RNDN);
}

ErrorRegime classify_regime(const NumericWorkspace &work) {
    if (mpfr_zero_p(work.reference.get())) {
        return mpfr_greater_p(work.absolute_term.get(),
                              work.relative_term.get())
            ? ErrorRegime::absolute
            : ErrorRegime::zero_bound;
    }
    return mpfr_cmp(work.relative_term.get(), work.absolute_term.get()) >= 0
        ? ErrorRegime::relative
        : ErrorRegime::absolute;
}

ResultFacts measure_result(const PairBits &bits,
                           const OperationSpec &operation,
                           NumericWorkspace &work,
                           ResultValues &values) {
    ResultFacts facts;
    facts.present = bits.present;
    if (!bits.present) return facts;

    const double hi = value_from_bits(bits.hi);
    const double lo = value_from_bits(bits.lo);
    facts.finite = std::isfinite(hi) && std::isfinite(lo);
    if (!facts.finite) return facts;

    set_pair(values.value.get(), bits, work.scratch.get());
    // A valid pair rounds back to the high part.
    facts.valid_double_word =
        mpfr_get_d(values.value.get(), MPFR_RNDN) == hi;
    if (!mpfr_number_p(work.reference.get())) return facts;

    facts.exact = mpfr_equal_p(values.value.get(), work.reference.get()) != 0;
    mpfr_sub(values.error.get(), values.value.get(), work.reference.get(),
             MPFR_RNDN);
    mpfr_abs(values.error.get(), values.error.get(), MPFR_RNDN);
    facts.has_error = true;

    if (!mpfr_zero_p(work.magnitude.get())) {
        mpfr_div(values.relative_error.get(), values.error.get(),
                 work.magnitude.get(), MPFR_RNDN);
        facts.has_relative_error = true;
    }

    if (operation.bound != BoundKind::none) {
        facts.bound_compare = mpfr_cmp(values.error.get(), work.bound.get());
        if (!mpfr_zero_p(work.bound.get())) {
            mpfr_div(values.bound_ratio.get(), values.error.get(),
                     work.bound.get(), MPFR_RNDN);
            facts.has_bound_ratio = true;
        }
    }
    return facts;
}

// Test if a bound result is close to a change.
bool needs_bound_check(mpfr_srcptr error, mpfr_srcptr bound,
                       NumericWorkspace &work) {
    if (mpfr_cmp(error, bound) >= 0 || mpfr_zero_p(bound)) return true;
    mpfr_sub(work.distance.get(), bound, error, MPFR_RNDD);
    mpfr_mul_2si(work.threshold.get(), bound, -256, MPFR_RNDU);
    return mpfr_cmp(work.distance.get(), work.threshold.get()) <= 0;
}

int compare_bound_with_more_precision(const NumericalRow &row,
                                      const OperationSpec &operation,
                                      const PairBits &bits,
                                      NumericWorkspace &work) {
    compute_reference(row, operation, work);
    compute_bound(operation, work);
    ResultFacts facts = measure_result(bits, operation, work, work.fencedd);
    if (!facts.has_error) throw Error("bound check has no error value");
    return facts.bound_compare;
}

// Check a close bound test with more precision.
void check_bound_result(const NumericalRow &row,
                        const OperationSpec &operation,
                        const PairBits &bits,
                        ResultValues &values,
                        NumericWorkspace &work,
                        NumericWorkspace &check_work,
                        ResultFacts &facts) {
    if (operation.bound == BoundKind::none || !facts.has_error) return;
    if (!needs_bound_check(values.error.get(), work.bound.get(), work)) return;
    facts.bound_was_checked = true;
    const int check = compare_bound_with_more_precision(
        row, operation, bits, check_work);
    facts.bound_is_unresolved =
        (facts.bound_compare > 0) != (check > 0);
}

CaseAnalysis analyze_case(const NumericalRow &row,
                          const OperationSpec &operation,
                          NumericWorkspace &work,
                          NumericWorkspace &check_work) {
    compute_reference(row, operation, work);
    if (!mpfr_number_p(work.reference.get())) {
        throw Error(std::string(operation.name)
                    + " reference is not finite at case "
                    + std::to_string(row.case_id));
    }
    compute_bound(operation, work);

    CaseAnalysis analysis;
    if (!operation.eft) analysis.regime = classify_regime(work);
    analysis.fencedd = measure_result(
        row.default_result, operation, work, work.fencedd);
    analysis.qd = measure_result(row.qd_result, operation, work, work.qd);
    check_bound_result(row, operation, row.default_result, work.fencedd,
                       work, check_work, analysis.fencedd);
    check_bound_result(row, operation, row.qd_result, work.qd,
                       work, check_work, analysis.qd);
    return analysis;
}

// Read each number row and pass its derived values to one question.
void read_numerical_data_impl(const std::string &path,
                              const NumericalConsumer &accept) {
    std::ifstream file(path);
    file.imbue(std::locale::classic());
    if (!file) throw Error("could not open " + path);

    std::string line;
    std::size_t line_number = 1;
    if (!std::getline(file, line)) fail(path, line_number, "file is empty");
    trim_carriage_return(line);
    const std::string sample_key = "# samples_per_exponent=";
    if (line.compare(0, sample_key.size(), sample_key) != 0) {
        fail(path, line_number, "sample count is missing");
    }
    const std::size_t samples = parse_size(
        line.substr(sample_key.size()), path, line_number,
        "samples_per_exponent");
    if (samples == 0) fail(path, line_number, "sample count must be positive");

    ++line_number;
    if (!std::getline(file, line)) fail(path, line_number, "header is missing");
    trim_carriage_return(line);
    if (line != numerical_header) fail(path, line_number, "header is not valid");

    NumericWorkspace work(analysis_precision);
    NumericWorkspace check_work(check_precision);
    std::vector<CaseInput> shared_inputs;
    for (std::size_t operation_index = 0;
         operation_index < operations.size(); ++operation_index) {
        const OperationSpec &operation = operations[operation_index];
        if (samples > std::numeric_limits<std::size_t>::max()
                          / operation.cases_per_sample) {
            fail(path, 1, "sample count is too large");
        }
        const std::size_t count = samples * operation.cases_per_sample;
        if (operation_index % 3 == 0) {
            shared_inputs.clear();
            shared_inputs.reserve(count);
        }
        for (std::size_t case_id = 0; case_id < count; ++case_id) {
            ++line_number;
            if (!std::getline(file, line)) {
                fail(path, line_number, "data ends before all cases are read");
            }
            trim_carriage_return(line);
            const NumericalRow row = parse_numerical_row(
                line, operation, operation_index, case_id,
                path, line_number);
            if (operation_index % 3 == 0) {
                shared_inputs.push_back(CaseInput{row.first, row.second});
            } else if (!same_input(shared_inputs[case_id], row)) {
                fail(path, line_number, "shared values do not match");
            }
            const CaseAnalysis analysis =
                analyze_case(row, operation, work, check_work);
            const ResultView fencedd{
                analysis.fencedd,
                work.fencedd.error.get(),
                work.fencedd.relative_error.get(),
                work.fencedd.bound_ratio.get(),
            };
            const ResultView qd{
                analysis.qd,
                work.qd.error.get(),
                work.qd.relative_error.get(),
                work.qd.bound_ratio.get(),
            };
            const NumericalCase data{
                row.operation,
                row.case_id,
                row.default_outcome,
                row.strong_outcome,
                analysis.regime,
                fencedd,
                qd,
            };
            accept(operation, data);
        }
    }

    while (std::getline(file, line)) {
        ++line_number;
        trim_carriage_return(line);
        if (!line.empty()) fail(path, line_number, "data follows the last case");
    }
    if (file.bad()) throw Error("could not read " + path);
}

}  // namespace

void read_numerical_data(const std::string &path,
                         const NumericalConsumer &accept) {
    read_numerical_data_impl(path, accept);
}

std::string format_real(mpfr_srcptr value) {
    char *raw = nullptr;
    if (mpfr_asprintf(&raw, "%.*Re", text_digits - 1, value) < 0
        || raw == nullptr) {
        throw Error("could not form number text");
    }
    const std::string text(raw);
    mpfr_free_str(raw);
    return text;
}

}  // namespace bench_analysis
