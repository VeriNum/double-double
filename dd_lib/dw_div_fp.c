#include <stdlib.h>
#include "dw_arith.h"
#include "fp_utils.h"

void dw_div_fp(struct dword *z, struct dword *x, double y) {
   if (!dw_div_fp_weak_check(x, y)) {
      exit(EXIT_FAILURE);
   }
   dw_div_fp_kernel(z, x, y);
   if (!isfinite_dword(z)) {
      exit(EXIT_FAILURE);
   }
}

void dw_div_fp_strong(struct dword *z, struct dword *x, double y) {
   if (!dw_div_fp_strong_check(x, y)) {
      exit(EXIT_FAILURE);
   }
   dw_div_fp_kernel(z, x, y);
}
