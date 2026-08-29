#include <stdlib.h>
#include "dw_arith.h"
#include "fp_utils.h"

/* Default interface: check the mathematical input condition, run the kernel,
   then reject a nonfinite result. */
void dw_plus_fp(struct dword *st, struct dword *x, double y) {
   if (!dw_plus_fp_weak_precond_check(x, y)) {
      exit(EXIT_FAILURE);
   }
   dw_plus_fp_kernel(st, x, y);
   if (!dword_finite_check(st)) {
      exit(EXIT_FAILURE);
   }
}

/* Strong interface: the input check proves output finiteness in advance. */
void dw_plus_fp_strong(struct dword *st, struct dword *x, double y) {
   if (!dw_plus_fp_strong_precond_check(x, y)) {
      exit(EXIT_FAILURE);
   }
   dw_plus_fp_kernel(st, x, y);
}
