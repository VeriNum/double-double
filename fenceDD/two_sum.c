#include "dw_arith.h"
#include "fp_utils.h"

enum dw_status two_sum(struct dword *st, double a, double b) {
   if (!isfinite_double(a)) {
      return DW_WEAK_INPUT_REJECTED;
   }
   if (!isfinite_double(b)) {
      return DW_WEAK_INPUT_REJECTED;
   }
   two_sum_kernel(st, a, b);
   if (!isfinite_dword(st)) {
      return DW_POST_CHECK_REJECTED;
   }
   return DW_OK;
}
