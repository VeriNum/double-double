#include <stdlib.h>
#include "dw_arith.h"
#include "fp_utils.h"

void dw_mult_fp9_guarded(struct dword *st, struct dword *x, double y) {
   if (!dw_mult_fp_check(x, y)) {
      exit(EXIT_FAILURE);
   }
   dw_mult_fp9(st, x, y);
}
