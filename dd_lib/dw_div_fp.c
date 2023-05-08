#include <math.h>
#include "dw_arith.h"

void dw_div_fp15(struct dword *z, struct dword *x, double y) {
   double th; struct dword p; double dh; double dt; double d; double tl;
   th = x->s/y;
   fast_2mult(&p,th,y);
   dh = x->s - p.s; 
   dt = dh - p.t;
   d = dt + x->t;
   tl = d/y;
   fast_2sum(z,th,tl);
}

