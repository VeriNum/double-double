#include <stdlib.h>
#include "dw_arith.h"
#include "fp_utils.h"

void dw_plus_dw2_guarded(struct dword *st, struct dword *x, struct dword *y) {
   if (!dw_plus_dw_check(x, y)) {
      exit(EXIT_FAILURE);
   }
   dw_plus_dw2(st, x, y);
}
