#include <math.h>
#include "DWArith.h"

void SDWPFP(dword *st, dword *x, float y) {
   double v; dword sh;
   TwoSum(&sh,x->s,y);
   v      = x->t + sh.t;
   Fast2Sum(st,sh.s,v);
}
