// dd_lib/fp_utils.c
#include <stdint.h>
#include "include/dw_arith.h"
#include "include/fp_utils.h"
#include <math.h> // for fabs, ldexp
#include <float.h>  // for DBL_MIN, DBL_MAX

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

int dw_plus_dw_check(struct dword *x, struct dword *y) {
    /* Verifies DWPlusDW_cond: each component is finite, both pairs satisfy the
       double-word relation (high part is the IEEE-754 RN sum of the components),
       and the high parts are bounded by Omega/4 = 2^1022.
       The DW relation (x->s + x->t == x->s) is well-defined as a comparison
       only when both operands are finite — hence the short-circuit ordering. */
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_yh = isfinite_double(y->s);
    int fin_yl = isfinite_double(y->t);
    int dwx = fin_xh && fin_xl && (x->s + x->t == x->s);
    int dwy = fin_yh && fin_yl && (y->s + y->t == y->s);
    double q_omega = ldexp(1.0, 1022);  /* Omega/4 for IEEE-754 double */
    int xh_bnd = fabs(x->s) <= q_omega;
    int yh_bnd = fabs(y->s) <= q_omega;
    return dwx && dwy && xh_bnd && yh_bnd;
}

int dw_mult_fp_check(struct dword *x, double y) {
    /* Verifies DWTimesFP_cond: xh, xl, y finite; (x->s, x->t) is a double-word;
       |x->s|, |y| <= Omega/4; |x->s * y| <= Omega/4 (the *product* bound, which
       bounds the high part of the result and leaves margin for the final
       Fast2Sum — bounding the factors alone does not bound the product);
       Fast2Mult(x->s, y) is safe (finite + the underflow disjunction shared
       with fast2_mult_check).  The DW prop alone does not pin down finiteness
       of x->t in R (FT2R sends NaN/Inf to 0), so fin_xl is asserted, even
       though x->s + x->t == x->s implies it under IEEE comparison semantics. */
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_y  = isfinite_double(y);
    int dwx    = fin_xh && fin_xl && (x->s + x->t == x->s);
    double q_omega = ldexp(1.0, 1022);  /* Omega/4 for IEEE-754 double */
    int xh_bnd = fabs(x->s) <= q_omega;
    int y_bnd  = fabs(y)    <= q_omega;
    /* Fast2Mult(x->s, y) safety — mirror fast2_mult_check */
    double z = x->s * y;
    double thresh = DBL_MIN * ldexp(1.0, 53);  /* 2^(emin + 2*p - 1) */
    int fin_z = isfinite_double(z);
    int z_bnd = fabs(z) <= q_omega;  /* |round(x->s * y)| <= Omega/4 */
    int zxh = x->s == 0.0 && fin_y;
    int zy  = y    == 0.0 && fin_xh;
    int mult_safe = fin_z && ((zxh || zy) || thresh < fabs(z));
    return dwx && fin_y && xh_bnd && y_bnd && z_bnd && mult_safe;
}

int dw_plus_fp_check(struct dword *x, double y) {
    /* Verifies DWPlusFP_cond: xh, xl, y are finite, (x->s, x->t) is a
       double-word, and |x->s|, |y| <= Omega/4 = 2^1022.  The DW prop alone
       does not pin down finiteness of x->t in R (FT2R sends NaN/Inf to 0),
       so fin_xl is asserted, even though x->s + x->t == x->s implies it
       under IEEE comparison semantics. */
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_y  = isfinite_double(y);
    int dwx = fin_xh && fin_xl && (x->s + x->t == x->s);
    double q_omega = ldexp(1.0, 1022);  /* Omega/4 for IEEE-754 double */
    int xh_bnd = fabs(x->s) <= q_omega;
    int y_bnd  = fabs(y)    <= q_omega;
    return dwx && fin_y && xh_bnd && y_bnd;
}
