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
    /* Verifies DWTimesFP_cond: xh, xl, y finite; (x->s, x->t) is a double-word;
       |x->s|, |y| <= 2^(femax/2 - 1) = 2^511 (the *factor* / square-root-scale
       bound, NOT Omega/4 — because multiplication squares magnitudes, the cond
       bounds the factors at 2^511 so that |x->s * y| <= 2^(femax-2) = Omega/4
       follows); Fast2Mult(x->s, y) is safe via the underflow disjunction shared
       with fast2_mult_check.  From the 2^511 factor bounds, both finiteness of
       round(x->s * y) and |round(x->s * y)| <= Omega/4 are DERIVED in the
       accuracy proofs (no_overflow_mult_is_finite + round monotonicity), so no
       explicit fin_z / z_bnd checks are needed here.  The DW prop alone does not
       pin down finiteness of x->t in R (FT2R sends NaN/Inf to 0), so fin_xl is
       asserted, even though x->s + x->t == x->s implies it under IEEE comparison
       semantics. */
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_y  = isfinite_double(y);
    int dwx    = fin_xh && fin_xl && (x->s + x->t == x->s);
    double q_sqrt = ldexp(1.0, 511);  /* 2^(femax/2 - 1), the factor bound */
    int xh_bnd = fabs(x->s) <= q_sqrt;
    int y_bnd  = fabs(y)    <= q_sqrt;
    /* Fast2Mult(x->s, y) safety — underflow disjunction, mirror fast2_mult_check.
       This encodes the cond's real-product disjunct
       (FT2R x->s * FT2R y = 0  \/  2^(emin + 2*p - 1) <= |FT2R x->s * FT2R y|),
       which the factor bounds alone do not give.

       SUBTLETY: the cond bounds the EXACT real product |FT2R xh * FT2R y|, but
       this check can only inspect the ROUNDED product z = RN(xh*y).  These
       differ by rounding error, so the check does NOT check the same quantity
       the cond asserts.  It is nonetheless sound because the implication runs
       in the conservative direction only:

         thresh < |RN(xh*y)|  =>  thresh < |xh*y|      (never the converse)

       proven in Coq as no_underflow_real_from_round_mul (float_verif_lemmas.v).
       That direction is valid because thresh = 2^(emin+2p-1) is a power of two,
       hence exactly representable, and RN is monotone and idempotent on it: an
       exact product at or below thresh would round to <= thresh, so a rounded
       product strictly above thresh forces the exact product strictly above it
       too.  The check may therefore REJECT boundary inputs that actually satisfy
       the cond (harmless false negatives), but it can never ACCEPT one that
       violates it (no false positives) — exactly what a guard needs.

       The other way FT2R could misrepresent z is overflow (FT2R sends Inf->0):
       if xh*y overflowed, fabs(z)=Inf would pass the threshold spuriously.  That
       is precluded here by the factor bounds xh_bnd/y_bnd (|xh|,|y| <= 2^511 =>
       |xh*y| <= 2^1022, finite), so z is genuinely finite and fabs(z) is an
       honest magnitude.  The underflow guard's soundness is thus COUPLED to the
       factor bounds above; they are not independent conjuncts.

       ALTERNATIVE (not taken): per-component lower bounds |xh|,|y| >= 2^k with
       k = ceil((emin+2p-1)/2) = -484 would imply this disjunct (2^k * 2^k >=
       thresh) while never forming the product in C — two exact comparisons
       against representable powers of two, no rounded-product bridge and no
       overflow coupling.  Rejected because it is strictly STRONGER: it excludes
       valid mixed-magnitude inputs (e.g. a small-normal xh times a large y whose
       product still clears thresh).  We keep the product form to leave the
       precondition maximally general. */
    double z = x->s * y;
    double thresh = DBL_MIN * ldexp(1.0, 53);  /* 2^(emin + 2*p - 1) */
    int zxh = x->s == 0.0 && fin_y;
    int zy  = y    == 0.0 && fin_xh;
    int mult_safe = (zxh || zy) || thresh < fabs(z);
    return dwx && fin_y && xh_bnd && y_bnd && mult_safe;
}

int dw_mult_dw_check(struct dword *x, struct dword *y) {
    /* Verifies DWTimesDW_cond: xh, xl, yh, yl finite; (x->s, x->t) and
       (y->s, y->t) are each a double-word; |x->s|, |y->s| <= 2^(femax/2 - 1) =
       2^511 (the *factor* / square-root-scale bound, NOT Omega/4 — because
       multiplication squares magnitudes, the cond bounds the factors at 2^511
       so that |x->s * y->s| <= 2^(femax-2) = Omega/4 follows); Fast2Mult(x->s,
       y->s) is safe via the underflow disjunction shared with fast2_mult_check.

       This is dw_mult_fp_check with the scalar y promoted to a second
       double-word (y->s, y->t): the factor bound and mult-safe disjunction now
       range over y->s (the high part), and finiteness of both y-components plus
       the y double-word relation are asserted, exactly as dw_plus_dw_check does
       for its second operand.  The DW prop alone does not pin down finiteness of
       x->t / y->t in R (FT2R sends NaN/Inf to 0), so fin_xl / fin_yl are
       asserted, even though s + t == s implies each under IEEE comparison
       semantics.  All the soundness subtleties of the rounded-product underflow
       guard (conservative one-directional implication; overflow precluded by the
       factor bounds) are identical to dw_mult_fp_check above — see that comment. */
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_yh = isfinite_double(y->s);
    int fin_yl = isfinite_double(y->t);
    int dwx    = fin_xh && fin_xl && (x->s + x->t == x->s);
    int dwy    = fin_yh && fin_yl && (y->s + y->t == y->s);
    double q_sqrt = ldexp(1.0, 511);  /* 2^(femax/2 - 1), the factor bound */
    int xh_bnd = fabs(x->s) <= q_sqrt;
    int yh_bnd = fabs(y->s) <= q_sqrt;
    /* Fast2Mult(x->s, y->s) safety — underflow disjunction, mirror
       fast2_mult_check.  Encodes the cond's real-product disjunct
       (FT2R x->s * FT2R y->s = 0  \/  2^(emin+2*p-1) <= |FT2R x->s * FT2R y->s|). */
    double z = x->s * y->s;
    double thresh = DBL_MIN * ldexp(1.0, 53);  /* 2^(emin + 2*p - 1) */
    int zxh = x->s == 0.0 && fin_yh;
    int zyh = y->s == 0.0 && fin_xh;
    int mult_safe = (zxh || zyh) || thresh < fabs(z);
    return dwx && dwy && xh_bnd && yh_bnd && mult_safe;
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
