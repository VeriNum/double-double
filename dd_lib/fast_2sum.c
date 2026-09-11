#include "dw_arith.h"
#include "fp_utils.h"

enum dw_status fast_2sum(struct dword *st, double a, double b) {
   struct dword result;
   if (!fast2_sum_magnitude_order_check(a,b)) {
      return DW_WEAK_INPUT_REJECTED;
   }
   fast_2sum_kernel(&result, a, b);
   st->s = result.s;
   st->t = result.t;
   return DW_OK;
}
