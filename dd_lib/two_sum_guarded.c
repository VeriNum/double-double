#include <stdlib.h>
#include "dw_arith.h"
#include "fp_utils.h"

void two_sum_guarded(struct dword *st, double a, double b) {
   if (!two_sum_check(a,b)) {
      exit(EXIT_FAILURE);
   }
   two_sum(st, a, b);
}
