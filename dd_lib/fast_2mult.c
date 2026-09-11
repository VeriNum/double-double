#include "dw_arith.h"
#include "fp_utils.h"

enum dw_status fast_2mult(struct dword *st, double a, double b) {
   if (!fast2_mult_exact_check(a,b)) {
      return DW_WEAK_INPUT_REJECTED;
   }
   fast_2mult_kernel(st, a, b);
   return DW_OK;
}
