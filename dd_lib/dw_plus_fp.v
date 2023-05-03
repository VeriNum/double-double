#include <math.h>
#include "dw_arith.h"

void dw_plus_fp(struct dword *st,struct dword *x, double y) {
   double v; struct dword sh;
   two_sum(&sh,x->s,y);
   v      = x->t + sh.t;
   fast_2sum(st,sh.s,v);
}
