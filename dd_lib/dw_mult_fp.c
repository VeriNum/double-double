#include <stdlib.h>
#include "dw_arith.h"
#include "fp_utils.h"

void dw_mult_fp(struct dword *st, struct dword *x, double y) {
   if (!dw_mult_fp_input_check(x, y)) {
      exit(EXIT_FAILURE);
   }
   dw_mult_fp_kernel(st, x, y);
   if (!dword_finite_check(st)) {
      exit(EXIT_FAILURE);
   }
}

void dw_mult_fp_strong(struct dword *st, struct dword *x, double y) {
   if (!dw_mult_fp_check(x, y)) {
      exit(EXIT_FAILURE);
   }
   dw_mult_fp_kernel(st, x, y);
}
