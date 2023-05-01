#include <math.h>
#include "DWArith.h"

void TwoSum(dword *st, double a, double b) {
   double ap; double bp; double da; double db;
   st->s  = a + b;
   ap     = st->s - b;
   bp     = st->s - ap;
   da     = a - ap;
   db     = b - bp;
   st->t  = da + db;
}
