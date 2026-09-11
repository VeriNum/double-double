#include <math.h>
#include "dw_arith.h"

void dw_div_dw_kernel(struct dword *z, struct dword *x, struct dword *y) {
   double th; double rh; double rl;
   struct dword e; struct dword delta; struct dword m;
   th     = 1.0/y->s;
   rh     = fma(-y->s,th,1.0);
   rl     = -(y->t * th);
   fast_2sum_kernel(&e,rh,rl);
   dw_times_fp_kernel(&delta,&e,th);
   dw_plus_fp_kernel(&m,&delta,th);
   dw_times_dw_kernel(z,x,&m);
}
