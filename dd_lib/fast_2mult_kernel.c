#include <math.h>
#include "dw_arith.h"

void fast_2mult_kernel(struct dword *st, double a, double b) {
   st->s  = a * b;
   st->t  = fma(a,b,-st->s);
}
