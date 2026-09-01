#ifndef DD_EVAL_OPERATION_METADATA_HPP
#define DD_EVAL_OPERATION_METADATA_HPP

namespace bench_eval {

enum class CompositeOperation {
    dw_plus_fp,
    dw_times_fp,
    dw_div_fp,
    dw_plus_dw,
    dw_times_dw,
    dw_div_dw
};

inline const char *operation_name(CompositeOperation operation) {
    switch (operation) {
    case CompositeOperation::dw_plus_fp:
        return "dw_plus_fp";
    case CompositeOperation::dw_times_fp:
        return "dw_times_fp";
    case CompositeOperation::dw_div_fp:
        return "dw_div_fp";
    case CompositeOperation::dw_plus_dw:
        return "dw_plus_dw";
    case CompositeOperation::dw_times_dw:
        return "dw_times_dw";
    case CompositeOperation::dw_div_dw:
        return "dw_div_dw";
    }
    return "unknown";
}

} // namespace bench_eval

#endif
