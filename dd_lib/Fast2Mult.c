#include <math.h>
#include "Fast2Mult.h"

void Fast2Mult(struct dd_struct *st, double a, double b) {
   st->s  = a * b;
   st->t  = fma(a,b,-st->s);
}

