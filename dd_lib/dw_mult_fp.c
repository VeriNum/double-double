#include <math.h>
#include "dw_arith.h"

void dw_mult_fp9(struct dword *zh, struct dword *x, double y) {
   double c3; struct dword ch;
   fast_2mult(&ch,x->s,y);
   c3     = fma(x->t,y,ch.t); 
   fast_2sum(zh,ch.s,c3);
}

