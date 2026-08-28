#include <stdlib.h>
#include "dw_arith.h"
#include "fp_utils.h"

void dw_div_dw(struct dword *z, struct dword *x, struct dword *y) {
   if (!dw_div_dw_input_check(x, y)) {
      exit(EXIT_FAILURE);
   }
   dw_div_dw_kernel(z, x, y);
   if (!dword_finite_check(z)) {
      exit(EXIT_FAILURE);
   }
}

void dw_div_dw_strong(struct dword *z, struct dword *x, struct dword *y) {
   if (!dw_div_dw_check(x, y)) {
      exit(EXIT_FAILURE);
   }
   dw_div_dw_kernel(z, x, y);
}
