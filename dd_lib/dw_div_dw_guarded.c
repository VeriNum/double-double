#include <stdlib.h>
#include "dw_arith.h"
#include "fp_utils.h"

void dw_div_dw18_guarded(struct dword *st, struct dword *x, struct dword *y) {
   if (!dw_div_dw_check(x, y)) {
      exit(EXIT_FAILURE);
   }
   dw_div_dw18(st, x, y);
}
