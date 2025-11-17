#include <math.h>
#include <stdlib.h> // Required for exit()
#include "dw_arith.h"
#include "fp_utils.h"

void fast_2mult(struct dword *st, double a, double b) {
   if (!isnormal_mul_double(a,b)) {
      exit(EXIT_FAILURE);
   }
   st->s  = a * b;
   st->t  = fma(a,b,-st->s);
}

