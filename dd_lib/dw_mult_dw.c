#include <math.h>
#include "dw_arith.h"

void dw_mult_dw12(struct dword *zh, struct dword *x, struct dword *y) {
   double t0; double t1; double c2; double c3; 
   struct dword ch;
   fast_2mult(&ch,x->s,y->s);
   t0     = x->t * y->t;
   t1	  = fma(x->s,y->t,t0);
   c2     = fma(x->t,y->s,t1);
   c3     = ch.t + c2; 
   fast_2sum(zh,ch.s,c3);
}

