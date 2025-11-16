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

int isnormal_double(double x) {
    union { double d; uint64_t u; } v;
    v.d = x;

    // Clear the sign bit.
    uint64_t ax = v.u & 0x7fffffffffffffffULL;

    // Extract the 11-bit exponent.
    uint64_t exponent = (ax >> 52) & 0x7ffULL;

    // Normal iff 0 < exponent < 0x7ff.
    return (exponent != 0 && exponent != 0x7ffULL);
}
