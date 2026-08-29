#include <stdlib.h>
#include "dw_arith.h"
#include "fp_utils.h"

void fast_2mult_guarded(struct dword *st, double a, double b) {
   if (!fast2_mult_exact_check(a,b)) {
      exit(EXIT_FAILURE);
   }
   fast_2mult(st, a, b);
}
