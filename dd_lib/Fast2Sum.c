#include <math.h>
#include "DWArith.h"

void Fast2Sum(dword *st, double a, double b) {
   double z;
   st->s  = a + b;
   z      = st->s - a;
   st->t  = b + z;
}
