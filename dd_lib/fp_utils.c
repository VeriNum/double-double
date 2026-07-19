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
       Comparison with 0.0 is false for NaN.

       IMPORTANT: this idiom is only correct under strict IEEE-754 semantics.
       This file MUST be compiled WITHOUT -ffast-math / -ffinite-math-only.
       Those flags let the compiler assume no NaNs/infinities exist, so it
       constant-folds (x - x) to 0.0 and this function collapses to
       `return 1;`, silently breaking every finiteness check that depends on
       it. The verification proofs likewise assume strict IEEE semantics. */
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

int fast2_mult_acc_check(double x, double y) {
    /* "Accurate-only" guard for Fast2Mult: it certifies just enough for the
       accuracy bound |err| <= 1/2 ulp(x*y), which holds in every regime, so
       it only tests overflow-safety (finiteness of the rounded product) and
       omits fast2_mult_check's underflow zero/threshold test.  It does NOT
       certify the error-free / double-word property (mul + err == x*y); use
       fast2_mult_check for that.  Discharges DDModels.Fast2Mult_cond_acc. */
    return isfinite_double(x * y);
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
    /* Verifies DWTimesFP_cond: x->t, y finite; (x->s, x->t) is a double-word;
       Fast2Mult(x->s, y) is safe (round(x->s * y) finite AND the underflow
       disjunction below); and the real product |FT2R x->s * FT2R y| <= Omega/2
       = 2^(femax-1) = 2^1023.  The DW prop alone does not pin down finiteness of
       x->t in R (FT2R sends NaN/Inf to 0), so fin_xl is asserted, even though
       x->s + x->t == x->s implies it under IEEE comparison semantics. */
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_y  = isfinite_double(y);
    int dwx    = fin_xh && fin_xl && (x->s + x->t == x->s);
    double z = x->s * y;
    double thresh = DBL_MIN * ldexp(1.0, 53);  /* 2^(emin + 2*p - 1) */
    double q_prod = ldexp(1.0, 1023);          /* Omega/2 = 2^(femax-1) */
    /* Product magnitude bound, replacing the old per-factor bounds.  This single
       STRICT check on the rounded product z = RN(x->s * y) does double duty:

         (1) it establishes the cond's real-product bound |FT2R x->s * FT2R y|
             <= Omega/2, and
         (2) it forces z to be finite (a NaN compares unordered -> false;
             +Inf < 2^1023 -> false), giving Fast2Mult's round(x->s*y)-finite
             requirement and making fabs(z) below an honest magnitude.

       SUBTLETY: the cond bounds the EXACT real product, but this check inspects
       only the ROUNDED product z = RN(x->s*y).  Soundness relies on the
       implication running one way only:

         |RN(x->s*y)| < 2^1023  =>  |x->s*y| < 2^1023 <= Omega/2   (not the converse)

       proven in Coq as no_overflow_real_from_round_mul (float_verif_lemmas.v).
       The STRICT `<` is essential: 2^1023 is a representable power of two and RN
       is monotone/idempotent on it, so a real product >= 2^1023 rounds to
       >= 2^1023; contrapositively a rounded product strictly below 2^1023 forces
       the exact product strictly below it.  A non-strict `<=` would be UNSOUND
       (a real product just above 2^1023 can round down to exactly 2^1023).  The
       check may REJECT the measure-zero boundary |x->s*y| = 2^1023 (a harmless
       false negative) but never ACCEPTS an input violating the cond.

       Unlike the old factor bounds |x->s|,|y| <= 2^511, this product form is
       maximally general: it accepts any factor split (e.g. a large x->s times a
       small y) whose product is in range. */
    int prod_bnd = fabs(z) < q_prod;
    /* Fast2Mult(x->s, y) underflow disjunction, mirror fast2_mult_check.  Encodes
       the cond's real-product disjunct (FT2R x->s * FT2R y = 0  \/
       2^(emin+2*p-1) <= |FT2R x->s * FT2R y|).  Same rounded-vs-exact
       one-directional argument as above: thresh < |RN(x->s*y)| => thresh <
       |x->s*y| (no_underflow_real_from_round_mul).  Overflow can no longer make
       fabs(z) spuriously large, because prod_bnd already forces z finite. */
    int zxh = x->s == 0.0 && fin_y;
    int zy  = y    == 0.0 && fin_xh;
    int mult_safe = (zxh || zy) || thresh < fabs(z);
    return dwx && fin_y && prod_bnd && mult_safe;
}

int dw_mult_dw_check(struct dword *x, struct dword *y) {
    /* Verifies DWTimesDW_cond: x->t, y->t finite; (x->s, x->t) and (y->s, y->t)
       are each a double-word; Fast2Mult(x->s, y->s) is safe (round(x->s * y->s)
       finite AND the underflow disjunction below); and the real product
       |FT2R x->s * FT2R y->s| <= Omega/2 = 2^(femax-1) = 2^1023.

       This is dw_mult_fp_check with the scalar y promoted to a second
       double-word (y->s, y->t): the product bound and mult-safe disjunction now
       range over y->s (the high part), and finiteness of both y-components plus
       the y double-word relation are asserted, exactly as dw_plus_dw_check does
       for its second operand.  The DW prop alone does not pin down finiteness of
       x->t / y->t in R (FT2R sends NaN/Inf to 0), so fin_xl / fin_yl are
       asserted, even though s + t == s implies each under IEEE comparison
       semantics.  All soundness subtleties of the strict rounded-product bound
       (one-directional implication; overflow precluded because prod_bnd forces z
       finite) are identical to dw_mult_fp_check above — see that comment. */
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_yh = isfinite_double(y->s);
    int fin_yl = isfinite_double(y->t);
    int dwx    = fin_xh && fin_xl && (x->s + x->t == x->s);
    int dwy    = fin_yh && fin_yl && (y->s + y->t == y->s);
    double z = x->s * y->s;
    double thresh = DBL_MIN * ldexp(1.0, 53);  /* 2^(emin + 2*p - 1) */
    double q_prod = ldexp(1.0, 1023);          /* Omega/2 = 2^(femax-1) */
    /* Strict product magnitude bound (replaces the old per-factor 2^511 bounds):
       |RN(x->s*y->s)| < 2^1023 gives both the cond's real-product bound
       |FT2R x->s * FT2R y->s| <= Omega/2 AND finiteness of z. */
    int prod_bnd = fabs(z) < q_prod;
    /* Fast2Mult(x->s, y->s) underflow disjunction, mirror fast2_mult_check.
       Encodes the cond's real-product disjunct (FT2R x->s * FT2R y->s = 0  \/
       2^(emin+2*p-1) <= |FT2R x->s * FT2R y->s|). */
    int zxh = x->s == 0.0 && fin_yh;
    int zyh = y->s == 0.0 && fin_xh;
    int mult_safe = (zxh || zyh) || thresh < fabs(z);
    return dwx && dwy && prod_bnd && mult_safe;
}

int dw_div_fp_check(struct dword *x, double y) {
    /* Verifies DWDivFP_cond (DDModels.v): xh, xl, y finite; (x->s, x->t) a
       double-word; |x->s| within the window [2^(emin+2p), Omega/4]; and the
       quotient |x->s / y| within the window [2^(emin+2p-1), Omega/4].

       The two quotient bounds are tested on the ROUNDED quotient q = RN(x->s / y);
       the rounded->exact transfer is the division analog of dw_mult_fp_check's
       product-magnitude argument, proven one-directional in Coq
       (no_overflow_real_from_round_div / no_underflow_real_from_round_div).  As
       with prod_bnd there, the STRICT `<` on q's upper bound does double duty: it
       establishes the cond's real-quotient upper bound |x->s/y| <= Omega/4 AND
       forces q finite (a NaN abs compares unordered -> false; +Inf -> false),
       which in turn forces the divisor y != 0 in R.  The lower bound q_qlo < |q|
       is likewise strict, giving 2^(emin+2p-1) <= |x->s/y| (and again y != 0).

       The |x->s| window is a pair of direct comparisons on x->s (no rounding),
       exactly like dw_plus_fp_check's xh_bnd; the extra lower bound is the
       product-node underflow guard 2^(emin+2p) <= |x->s| from DWDivFP_cond.

       The DW prop alone does not pin down finiteness of x->t in R (FT2R sends
       NaN/Inf to 0), so fin_xl is asserted, even though x->s + x->t == x->s
       implies it under IEEE comparison semantics. */
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_y  = isfinite_double(y);
    int dwx = fin_xh && fin_xl && (x->s + x->t == x->s);

    double q_omega = ldexp(1.0, 1022);   /* Omega/4 = 2^(femax-2) = 2^1022 */
    double q_plo   = ldexp(1.0, -968);   /* 2^(emin+2*p)   product-node lower bound */
    double q_qlo   = ldexp(1.0, -969);   /* 2^(emin+2*p-1) quotient lower bound */

    /* |x->s| window: 2^(emin+2p) <= |x->s| <= Omega/4 */
    int xh_hi = fabs(x->s) <= q_omega;
    int xh_lo = q_plo <= fabs(x->s);

    /* quotient window on the rounded quotient q = RN(x->s / y) */
    double q = x->s / y;
    int qt_hi = fabs(q) < q_omega;   /* STRICT: |x->s/y| <= Omega/4; also forces q finite */
    int qt_lo = q_qlo < fabs(q);     /* STRICT: 2^(emin+2p-1) <= |x->s/y|; forces y != 0 */

    return dwx && fin_y && xh_hi && xh_lo && qt_hi && qt_lo;
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
