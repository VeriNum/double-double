#include <math.h>
#include "DWArith.h"

void Fast2Mult(dword *st, double a, double b) {
   st->s  = a * b;
   st->t  = fma(a,b,-st->s);
}

