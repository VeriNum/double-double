#include "dw_arith.h"
#include "fp_utils.h"

/* Default interface: check the mathematical input condition, run the kernel,
   then reject a nonfinite result. */
enum dw_status dw_plus_fp(struct dword *st, struct dword *x, double y) {
   struct dword result;
   if (!dw_plus_fp_weak_precond_check(x, y)) {
      return DW_WEAK_INPUT_REJECTED;
   }
   dw_plus_fp_kernel(&result, x, y);
   if (!isfinite_dword(&result)) {
      return DW_POST_CHECK_REJECTED;
   }
   st->s = result.s;
   st->t = result.t;
   return DW_OK;
}

/* Strong interface: the input check proves output finiteness in advance. */
enum dw_status dw_plus_fp_strong(struct dword *st, struct dword *x, double y) {
   struct dword result;
   if (!dw_plus_fp_strong_precond_check(x, y)) {
      return DW_STRONG_INPUT_REJECTED;
   }
   dw_plus_fp_kernel(&result, x, y);
   st->s = result.s;
   st->t = result.t;
   return DW_OK;
}
