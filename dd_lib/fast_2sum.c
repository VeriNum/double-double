#include <math.h>
#include "dw_arith.h"

void fast_2sum(struct dword *st, double a, double b) {
   double z;
   st->s  = a + b;
   z      = st->s - a;
   st->t  = b + z;
}
