#include <math.h>
#include "dw_arith.h"

void dw_div_dw18(struct dword *z, struct dword *x, struct dword *y) {
   double th; double rh; double rl;
   struct dword e; struct dword delta; struct dword m;
   th     = 1.0/y->s;
   rh     = fma(-y->s,th,1.0);      /* rh = 1 - yh*th (exact) */
   rl     = -(y->t * th);
   fast_2sum(&e,rh,rl);
   dw_mult_fp9(&delta,&e,th);
   dw_plus_fp_kernel(&m,&delta,th);
   dw_mult_dw12(z,x,&m);
}
