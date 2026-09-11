#include "dw_arith.h"
#include "fp_utils.h"

enum dw_status dw_times_fp(struct dword *st, struct dword *x, double y) {
   struct dword result;
   if (!dw_times_fp_weak_precond_check(x, y)) {
      return DW_WEAK_INPUT_REJECTED;
   }
   dw_times_fp_kernel(&result, x, y);
   if (!isfinite_dword(&result)) {
      return DW_POST_CHECK_REJECTED;
   }
   st->s = result.s;
   st->t = result.t;
   return DW_OK;
}

enum dw_status dw_times_fp_strong(struct dword *st, struct dword *x, double y) {
   struct dword result;
   if (!dw_times_fp_strong_precond_check(x, y)) {
      return DW_STRONG_INPUT_REJECTED;
   }
   dw_times_fp_kernel(&result, x, y);
   st->s = result.s;
   st->t = result.t;
   return DW_OK;
}
