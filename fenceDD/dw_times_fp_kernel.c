#include <math.h>
#include "dw_arith.h"

void dw_times_fp_kernel(struct dword *zh, struct dword *x, double y) {
   double c3; struct dword ch;
   fast_2mult_kernel(&ch,x->s,y);
   c3     = fma(x->t,y,ch.t);
   fast_2sum_kernel(zh,ch.s,c3);
}
