#include <math.h>
#include "dw_arith.h"

void two_sum(struct dword *st, double a, double b) {
   double ap; double bp; double da; double db;
   st->s  = a + b;
   ap     = st->s - b;
   bp     = st->s - ap;
   da     = a - ap;
   db     = b - bp;
   st->t  = da + db;
}
