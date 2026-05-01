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

int fast2_mult_check(double x, double y) {
    double z = x * y;
    // 2 ^ (emin + 2 * p - 1)
    double thresh = DBL_MIN * ldexp(1.0, 53); 
    int fin = isfinite_double(z);
    // checking if result z is zero is not sufficient
    // if z is zero we can't prove the 
    // real product is zero
    int zx = x == 0.0 && isfinite_double(y);
    int zy = y == 0.0 && isfinite_double(x);
    // checking if result z ge thresh is not sufficient
    // if z is ge thresh we can't to prove the 
    // real product is ge thresh; also requires finite
    return fin && ((zx || zy) || thresh < fabs(z)); 
}

int fast2_sum_check(double a, double b) {
    double s = a + b;
    int fin = isfinite_double(s);
    /* short-circuit: fabs called only when fin=true, i.e. a and b are finite */
    return fin && (fabs(b) <= fabs(a));
}

int two_sum_check(double a, double b) {
    int fin_sum  = isfinite_double(a + b);
    int fin_diff = isfinite_double(a - b);
    /* short-circuit: fabs called only when both fin checks pass */
    /* pred(2^1024) = DBL_MAX; strict inequality excludes ±DBL_MAX */
    return fin_sum && fin_diff && (fabs(b) < DBL_MAX);
}

int fast2_mult_check2(double x, double y, double z) {
    // 2 ^ (emin + 2 * p - 1)
    double thresh = DBL_MIN * ldexp(1.0, 53); 
    // checking if result z is zero is not sufficient
    // if z is zero we can't prove the 
    // real product is zero
    int zx = x == 0.0 && isfinite_double(y);
    int zy = y == 0.0 && isfinite_double(x);
    // checking if result z ge thresh is not sufficient
    // if z is ge thresh we can't to prove the 
    // real product is ge thresh
    // accuracy bound also requires finite
    int fin = isfinite_double(x * y + z);
    return fin && ((zx || zy) || thresh < fabs(x * y)); 
}
