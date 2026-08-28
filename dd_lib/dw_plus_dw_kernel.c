#include <math.h>
#include "dw_arith.h"

void dw_plus_dw_kernel(struct dword *st, struct dword *x, struct dword *y) {
  double c; double w;
  struct dword sh; struct dword th; struct dword vh;
  two_sum(&sh,x->s,y->s);
  two_sum(&th,x->t,y->t);
  c       = sh.t + th.s;
  fast_2sum(&vh,sh.s,c);
  w       = th.t + vh.t;
  fast_2sum(st,vh.s,w);
}
