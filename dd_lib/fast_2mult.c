#include <math.h>
#include <stdlib.h> // Required for exit()
#include "dw_arith.h"
#include "fp_utils.h"

void fast_2mult(struct dword *st, double a, double b) {
   st->s  = a * b;
   if (!isfinite_double(st->s) || !isnormal_double(st->s)) {
      exit(EXIT_FAILURE);
   }
   st->t  = fma(a,b,-st->s);
}

