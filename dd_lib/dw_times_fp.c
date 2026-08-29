#include <stdlib.h>
#include "dw_arith.h"
#include "fp_utils.h"

void dw_times_fp(struct dword *st, struct dword *x, double y) {
   if (!dw_times_fp_weak_precond_check(x, y)) {
      exit(EXIT_FAILURE);
   }
   dw_times_fp_kernel(st, x, y);
   if (!isfinite_dword(st)) {
      exit(EXIT_FAILURE);
   }
}

void dw_times_fp_strong(struct dword *st, struct dword *x, double y) {
   if (!dw_times_fp_strong_precond_check(x, y)) {
      exit(EXIT_FAILURE);
   }
   dw_times_fp_kernel(st, x, y);
}
