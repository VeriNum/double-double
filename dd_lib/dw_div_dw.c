#include "dw_arith.h"
#include "fp_utils.h"

enum dw_status dw_div_dw(struct dword *z, struct dword *x, struct dword *y) {
   struct dword result;
   if (!dw_div_dw_weak_precond_check(x, y)) {
      return DW_WEAK_INPUT_REJECTED;
   }
   dw_div_dw_kernel(&result, x, y);
   if (!isfinite_dword(&result)) {
      return DW_POST_CHECK_REJECTED;
   }
   z->s = result.s;
   z->t = result.t;
   return DW_OK;
}

enum dw_status dw_div_dw_strong(struct dword *z, struct dword *x,
                             struct dword *y) {
   struct dword result;
   if (!dw_div_dw_strong_precond_check(x, y)) {
      return DW_STRONG_INPUT_REJECTED;
   }
   dw_div_dw_kernel(&result, x, y);
   z->s = result.s;
   z->t = result.t;
   return DW_OK;
}
