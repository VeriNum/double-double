#include <stdlib.h>
#include "dw_arith.h"
#include "fp_utils.h"

void fast_2sum(struct dword *st, double a, double b) {
   if (!fast2_sum_magnitude_order_check(a,b)) {
      exit(EXIT_FAILURE);
   }
   fast_2sum_kernel(st, a, b);
}
