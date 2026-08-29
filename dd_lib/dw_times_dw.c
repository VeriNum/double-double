#include <stdlib.h>
#include "dw_arith.h"
#include "fp_utils.h"

void dw_times_dw(struct dword *st, struct dword *x, struct dword *y) {
   if (!dw_times_dw_weak_precond_check(x, y)) {
      exit(EXIT_FAILURE);
   }
   dw_times_dw_kernel(st, x, y);
   if (!dword_finite_check(st)) {
      exit(EXIT_FAILURE);
   }
}

void dw_times_dw_strong(struct dword *st, struct dword *x, struct dword *y) {
   if (!dw_times_dw_strong_precond_check(x, y)) {
      exit(EXIT_FAILURE);
   }
   dw_times_dw_kernel(st, x, y);
}
