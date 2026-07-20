#include <stdlib.h>
#include "dw_arith.h"
#include "fp_utils.h"

void dw_div_fp15_guarded(struct dword *z, struct dword *x, double y) {
   if (!dw_div_fp_check(x, y)) {
      exit(EXIT_FAILURE);
   }
   dw_div_fp15(z, x, y);
}
