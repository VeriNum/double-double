// dd_lib/fp_utils.c
#include <stdint.h>
#include "include/fp_utils.h"
#include <math.h> // for fabs  
#include <float.h>  // for DBL_MIN



int isfinite_double(double x) {
    /* For finite x, x - x == 0
       For +inf/-inf, x - x is NaN
       For NaN, x - x is NaN
       Comparison with 0.0 is false for NaN. */
    return (x - x) == 0.0;
}

int isnormal_mul_double(double x, double y) {
    double z = x * y;
    // 2 ^ (emin + 2 * p - 1)
    double thresh = DBL_MIN * ldexp(1.0, 53); 
    int fin = isfinite_double(z);
    // checking if result z is zero is not sufficient
    int zx = x == 0.0 && isfinite_double(y);
    int zy = y == 0.0 && isfinite_double(x);
    int lb = (zx || zy) || thresh <= fabs(z); 
    return fin && lb;  
}