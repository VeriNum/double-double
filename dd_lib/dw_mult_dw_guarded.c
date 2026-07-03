#include <stdlib.h>
#include "dw_arith.h"
#include "fp_utils.h"

void dw_mult_dw12_guarded(struct dword *st, struct dword *x, struct dword *y) {
   if (!dw_mult_dw_check(x, y)) {
      exit(EXIT_FAILURE);
   }
   dw_mult_dw12(st, x, y);
}
