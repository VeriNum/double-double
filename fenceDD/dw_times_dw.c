#include "dw_arith.h"
#include "fp_utils.h"

enum dw_status dw_times_dw(struct dword *st, struct dword *x, struct dword *y) {
   if (!dw_times_dw_weak_precond_check(x, y)) {
      return DW_WEAK_INPUT_REJECTED;
   }
   dw_times_dw_kernel(st, x, y);
   if (!isfinite_dword(st)) {
      return DW_POST_CHECK_REJECTED;
   }
   return DW_OK;
}

enum dw_status dw_times_dw_strong(struct dword *st, struct dword *x,
                               struct dword *y) {
   if (!dw_times_dw_strong_precond_check(x, y)) {
      return DW_STRONG_INPUT_REJECTED;
   }
   dw_times_dw_kernel(st, x, y);
   return DW_OK;
}
