#include "dw_arith.h"
#include "fp_utils.h"

enum dw_status dw_div_fp(struct dword *z, struct dword *x, double y) {
   struct dword result;
   if (!dw_div_fp_weak_check(x, y)) {
      return DW_WEAK_INPUT_REJECTED;
   }
   dw_div_fp_kernel(&result, x, y);
   if (!isfinite_dword(&result)) {
      return DW_POST_CHECK_REJECTED;
   }
   *z = result;
   return DW_OK;
}

enum dw_status dw_div_fp_strong(struct dword *z, struct dword *x, double y) {
   struct dword result;
   if (!dw_div_fp_strong_check(x, y)) {
      return DW_STRONG_INPUT_REJECTED;
   }
   dw_div_fp_kernel(&result, x, y);
   *z = result;
   return DW_OK;
}
