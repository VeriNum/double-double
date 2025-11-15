// dd_lib/fp_utils.c
#include <stdint.h>
#include "include/fp_utils.h"

int isfinite_double(double x) {
    /* For finite x, x - x == 0
       For +inf/-inf, x - x is NaN
       For NaN, x - x is NaN
       Comparison with 0.0 is false for NaN. */
    return (x - x) == 0.0;
}

int issubnormal_double(double x) {
    union { double d; uint64_t u; } v;
    v.d = x;

    uint64_t ax = v.u & 0x7fffffffffffffffULL;
    uint64_t exponent = ax >> 52;
    uint64_t fraction = ax & 0x000fffffffffffffULL;

    return (exponent == 0 && fraction != 0);
}