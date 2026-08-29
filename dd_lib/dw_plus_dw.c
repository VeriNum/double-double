#include <stdlib.h>
#include "dw_arith.h"
#include "fp_utils.h"

/* Default interface: check the mathematical input condition, run the kernel,
   then reject a nonfinite result. */
void dw_plus_dw(struct dword *st, struct dword *x, struct dword *y) {
   if (!dw_plus_dw_weak_precond_check(x, y)) {
      exit(EXIT_FAILURE);
   }
   dw_plus_dw_kernel(st, x, y);
   if (!isfinite_dword(st)) {
      exit(EXIT_FAILURE);
   }
}

/* Strong interface: the input check proves output finiteness in advance. */
void dw_plus_dw_strong(struct dword *st, struct dword *x, struct dword *y) {
   if (!dw_plus_dw_strong_precond_check(x, y)) {
      exit(EXIT_FAILURE);
   }
   dw_plus_dw_kernel(st, x, y);
}
