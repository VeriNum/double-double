#include <math.h>
#include "DWArith.h"

void SDWPFP(dword *st, dword *x, float y) {
   double v;
   st     = TwoSum(x.s,y);
   v      = x.t + st.t;
   st     = Fast2Sum(st.s, v);
}
