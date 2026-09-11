#include "dw_arith.h"
#include "fp_utils.h"

enum dw_status dw_times_dw(struct dword *st, struct dword *x, struct dword *y) {
   struct dword result;
   if (!dw_times_dw_weak_precond_check(x, y)) {
      return DW_WEAK_INPUT_REJECTED;
   }
   dw_times_dw_kernel(&result, x, y);
   if (!isfinite_dword(&result)) {
      return DW_POST_CHECK_REJECTED;
   }
   *st = result;
   return DW_OK;
}

enum dw_status dw_times_dw_strong(struct dword *st, struct dword *x,
                               struct dword *y) {
   struct dword result;
   if (!dw_times_dw_strong_precond_check(x, y)) {
      return DW_STRONG_INPUT_REJECTED;
   }
   dw_times_dw_kernel(&result, x, y);
   *st = result;
   return DW_OK;
}
