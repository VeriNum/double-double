#include <stdlib.h>
#include "dw_arith.h"
#include "fp_utils.h"

void dw_div_dw(struct dword *z, struct dword *x, struct dword *y) {
   if (!dw_div_dw_weak_precond_check(x, y)) {
      exit(EXIT_FAILURE);
   }
   dw_div_dw_kernel(z, x, y);
   if (!isfinite_dword(z)) {
      exit(EXIT_FAILURE);
   }
}

void dw_div_dw_strong(struct dword *z, struct dword *x, struct dword *y) {
   if (!dw_div_dw_strong_precond_check(x, y)) {
      exit(EXIT_FAILURE);
   }
   dw_div_dw_kernel(z, x, y);
}
