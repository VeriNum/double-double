#include <math.h>
#include "dw_arith.h"

void dw_plus_sfp(struct dword *st,struct dword *x, float y) {
   double v; struct dword sh;
   two_sum(&sh,x->s,y);
   v      = x->t + sh.t;
   fast_2sum(st,sh.s,v);
}
