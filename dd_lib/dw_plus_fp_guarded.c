#include <stdlib.h>
#include "dw_arith.h"
#include "fp_utils.h"

void dw_plus_fp_guarded(struct dword *st, struct dword *x, double y) {
   if (!dw_plus_fp_check(x, y)) {
      exit(EXIT_FAILURE);
   }
   dw_plus_fp(st, x, y);
}
