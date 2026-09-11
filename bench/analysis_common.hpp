#ifndef BENCH_ANALYSIS_COMMON_HPP
#define BENCH_ANALYSIS_COMMON_HPP

#include <array>
#include <cstddef>
#include <cstdint>
#include <fstream>
#include <limits>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

#include <sys/stat.h>

namespace bench_analysis {

constexpr std::size_t fp_exponent_count = 2098;
constexpr std::size_t dw_exponent_count = 1992;

enum class MathKind {
    add,
    multiply,
    divide,
};

enum class BoundKind {
    none,
    plus_fp,
    plus_dw,
    times_fp,
    times_dw,
    div_fp,
    div_dw,
};

struct OperationSpec {
    const char *name;
    bool eft;
    bool returns_status;
    bool first_has_lo;
    bool second_has_lo;
    MathKind math;
    BoundKind bound;
    std::size_t cases_per_sample;
};

constexpr std::array<OperationSpec, 9> operations{{
    {"two_sum", true, true, false, false, MathKind::add,
     BoundKind::none, fp_exponent_count},
    {"fast_2sum", true, true, false, false, MathKind::add,
     BoundKind::none, fp_exponent_count},
    {"fast_2mult", true, true, false, false, MathKind::multiply,
     BoundKind::none, fp_exponent_count},
    {"dw_plus_fp", false, true, true, false, MathKind::add,
     BoundKind::plus_fp, dw_exponent_count},
    {"dw_times_fp", false, true, true, false, MathKind::multiply,
     BoundKind::times_fp, dw_exponent_count},
    {"dw_div_fp", false, true, true, false, MathKind::divide,
     BoundKind::div_fp, dw_exponent_count},
    {"dw_plus_dw", false, true, true, true, MathKind::add,
     BoundKind::plus_dw, dw_exponent_count},
    {"dw_times_dw", false, true, true, true, MathKind::multiply,
     BoundKind::times_dw, dw_exponent_count},
    {"dw_div_dw", false, true, true, true, MathKind::divide,
     BoundKind::div_dw, dw_exponent_count},
}};

class Error : public std::runtime_error {
public:
    explicit Error(const std::string &message) : std::runtime_error(message) {}
};

inline std::string place(const std::string &path, std::size_t line) {
    std::ostringstream text;
    text << path << ':' << line;
    return text.str();
}

[[noreturn]] inline void fail(const std::string &path, std::size_t line,
                              const std::string &message) {
    throw Error(place(path, line) + ": " + message);
}

inline void trim_carriage_return(std::string &line) {
    if (!line.empty() && line.back() == '\r') line.pop_back();
}

inline std::vector<std::string> split_tabs(const std::string &line) {
    std::vector<std::string> fields;
    std::size_t start = 0;
    for (;;) {
        const std::size_t tab = line.find('\t', start);
        if (tab == std::string::npos) {
            fields.push_back(line.substr(start));
            return fields;
        }
        fields.push_back(line.substr(start, tab - start));
        start = tab + 1;
    }
}

inline std::size_t parse_size(const std::string &text,
                              const std::string &path,
                              std::size_t line, const char *field) {
    if (text.empty()) fail(path, line, std::string(field) + " is empty");
    std::size_t value = 0;
    for (char digit : text) {
        if (digit < '0' || digit > '9') {
            fail(path, line, std::string(field) + " is not a number");
        }
        const std::size_t next = static_cast<std::size_t>(digit - '0');
        if (value > (std::numeric_limits<std::size_t>::max() - next) / 10) {
            fail(path, line, std::string(field) + " is too large");
        }
        value = value * 10 + next;
    }
    return value;
}

inline unsigned int hex_digit(char value, const std::string &path,
                              std::size_t line, const char *field) {
    if (value >= '0' && value <= '9') {
        return static_cast<unsigned int>(value - '0');
    }
    if (value >= 'a' && value <= 'f') {
        return 10U + static_cast<unsigned int>(value - 'a');
    }
    if (value >= 'A' && value <= 'F') {
        return 10U + static_cast<unsigned int>(value - 'A');
    }
    fail(path, line, std::string(field) + " has bad hex data");
}

inline std::uint64_t parse_bits(const std::string &text,
                                const std::string &path,
                                std::size_t line, const char *field) {
    if (text.size() != 18 || text[0] != '0' || text[1] != 'x') {
        fail(path, line, std::string(field) + " has bad bit data");
    }
    std::uint64_t bits = 0;
    for (std::size_t i = 2; i < text.size(); ++i) {
        bits = (bits << 4) | hex_digit(text[i], path, line, field);
    }
    return bits;
}

inline void check_environment() {
    if (sizeof(double) != sizeof(std::uint64_t)
        || !std::numeric_limits<double>::is_iec559
        || std::numeric_limits<double>::digits != 53) {
        throw Error("IEEE 754 binary64 is required");
    }
}

inline bool same_file(const std::string &left, const std::string &right) {
    if (left == right) return true;
    struct stat left_data;
    struct stat right_data;
    if (stat(left.c_str(), &left_data) != 0
        || stat(right.c_str(), &right_data) != 0) {
        return false;
    }
    return left_data.st_dev == right_data.st_dev
        && left_data.st_ino == right_data.st_ino;
}

inline void check_file_paths(const std::vector<std::string> &paths,
                             std::size_t first_output) {
    for (std::size_t output = first_output; output < paths.size(); ++output) {
        for (std::size_t prior = 0; prior < output; ++prior) {
            if (same_file(paths[output], paths[prior])) {
                throw Error("input and output paths must be distinct");
            }
        }
    }
}

inline void check_output(const std::ofstream &file,
                         const std::string &path) {
    if (!file) throw Error("could not write " + path);
}

inline const OperationSpec &find_operation(const std::string &name,
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

}  // namespace bench_analysis

#endif
