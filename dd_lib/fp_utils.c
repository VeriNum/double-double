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

int fast2_mult_exact_check(double x, double y) {
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

int fast2_mult_product_finite_check(double x, double y) {
    /* This Fast2Mult guard checks that the rounded product is finite.  That is
       exactly what the bound |err| <= 1/2 ulp(x*y) needs in every regime, so the
       check omits fast2_mult_exact_check's underflow zero/threshold test.  It does
       NOT certify that mul + err == x*y or that the result is a valid double
       word; use fast2_mult_exact_check for those guarantees. */
    return isfinite_double(x * y);
}

int fast2_sum_magnitude_order_check(double a, double b) {
    /* short-circuit: fabs called only when fin=true, i.e. a and b are finite */
    return isfinite_double(a + b) && (fabs(b) <= fabs(a));
}

int two_sum_exact_check(double a, double b) {
    /* short-circuit: fabs called only when both fin checks pass */
    /* pred(2^1024) = DBL_MAX; strict inequality excludes ±DBL_MAX */
    return isfinite_double(a + b)
        && isfinite_double(a - b)
        && (fabs(b) < DBL_MAX);
}

int dw_plus_dw_strong_precond_check(const struct dword *x, const struct dword *y) {
    /* Verifies DWPlusDW_strong_precond: each component is finite, both pairs satisfy the
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

int dw_plus_dw_weak_precond_check(const struct dword *x, const struct dword *y) {
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_yh = isfinite_double(y->s);
    int fin_yl = isfinite_double(y->t);
    int dwx = fin_xh && fin_xl && (x->s + x->t == x->s);
    int dwy = fin_yh && fin_yl && (y->s + y->t == y->s);
    return dwx && dwy;
}

int dw_times_fp_strong_precond_check(const struct dword *x, double y) {
    /* Verifies DWTimesFP_strong_precond: x->t, y finite; (x->s, x->t) is a double-word;
       round(x->s * y) finite; and the real product |FT2R x->s * FT2R y| <=
       Omega/2 = 2^(femax-1) = 2^1023.  The DW prop alone does not pin down
       finiteness of x->t in R (FT2R sends NaN/Inf to 0), so fin_xl is asserted,
       even though x->s + x->t == x->s implies it under IEEE comparison
       semantics.

       NOT CHECKED, deliberately: Fast2Mult's underflow disjunction
         FT2R x->s * FT2R y = 0  \/  2^(emin+2*p-1) <= |FT2R x->s * FT2R y|
       (the `mult_safe` test this function used to carry, and which
       fast2_mult_exact_check still does).  That disjunct buys the
       PURE relative bound 2u^2 by excluding the Fast2Mult underflow gap, at the
       cost of aborting on any input whose leading product lands in it -- ordinary
       tiny-operand inputs.  The contract exported by dw_times_fp_strong is
       instead the whole-range MIXED bound

         |(zh+zl) - (x->s + x->t)*y| <= 2u^2 |(x->s + x->t)*y| + 2.51*eta

       (DWTimesFP_mixed_acc.DWTimesFP_guarantee_from_strong_precond),
       which holds in EVERY regime given
       only the double-word relation and finiteness of the computed pair.  The
       three conjuncts below are exactly what is needed to establish that
       finiteness
       (DWTimesFP_relative_acc.DWTimesFP_finite_post_cond_from_strong_precond), so the gap is accepted
       rather than fatal.  Output double-word closure likewise survives
       as part of the same mixed guarantee. */
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_y  = isfinite_double(y);
    int dwx    = fin_xh && fin_xl && (x->s + x->t == x->s);
    double z = x->s * y;
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
    return dwx && fin_y && prod_bnd;
}

int dw_times_fp_weak_precond_check(const struct dword *x, double y) {
    return dw_plus_fp_weak_precond_check(x, y);
}

int dw_times_dw_strong_precond_check(const struct dword *x, const struct dword *y) {
    /* Verifies DWTimesDW_strong_precond: x->t, y->t finite; (x->s, x->t) and
       (y->s, y->t) are each a double-word; round(x->s * y->s) finite; and the
       real product |FT2R x->s * FT2R y->s| <= Omega/2 = 2^(femax-1) = 2^1023.

       This is dw_times_fp_strong_precond_check with the scalar y promoted to a second
       double-word (y->s, y->t): the product bound now ranges over y->s (the high
       part), and finiteness of both y-components plus the y double-word relation
       are asserted, exactly as dw_plus_dw_strong_precond_check does for its second operand.
       The DW prop alone does not pin down finiteness of x->t / y->t in R (FT2R
       sends NaN/Inf to 0), so fin_xl / fin_yl are asserted, even though
       s + t == s implies each under IEEE comparison semantics.

       NOT CHECKED, deliberately: Fast2Mult's underflow disjunction
         FT2R x->s * FT2R y->s = 0  \/  2^(emin+2*p-1) <= |FT2R x->s * FT2R y->s|
       (the `mult_safe` test this function used to carry, and which
       fast2_mult_exact_check still does).  That disjunct buys the PURE relative bound
       4u^2 by excluding the Fast2Mult underflow gap, at the cost of aborting on
       any input whose leading product lands in it -- ordinary tiny-operand
       inputs.  The contract exported by dw_times_dw_strong is instead the
       whole-range MIXED bound

         |(zh+zl) - (x->s+x->t)*(y->s+y->t)|
             <= 4u^2 |(x->s+x->t)*(y->s+y->t)| + 2.5*eta

       (DWTimesDW_mixed_acc.DWTimesDW_guarantee_from_strong_precond),
       which holds in EVERY regime given
       only the two double-word relations and finiteness of the computed pair.
       The four conjuncts below are exactly what is needed to establish that
       finiteness
       (DWTimesDW_relative_acc.DWTimesDW_finite_post_cond_from_strong_precond), so the gap is accepted
       rather than fatal.  Output double-word closure likewise survives
       as part of the same mixed guarantee: closure needs only that the
       closing Fast2Sum preserves its sum, which holds both above the threshold
       (via the ordering |cl3| <= |ch|) and inside the gap (where failure of that
       ordering forces the exact sum onto the FLT/FIX lattice at emin, making
       Fast2Sum exact anyway).

       All soundness subtleties of the strict rounded-product bound
       (one-directional implication; overflow precluded because prod_bnd forces z
       finite) are identical to dw_times_fp_strong_precond_check above -- see that comment. */
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_yh = isfinite_double(y->s);
    int fin_yl = isfinite_double(y->t);
    int dwx    = fin_xh && fin_xl && (x->s + x->t == x->s);
    int dwy    = fin_yh && fin_yl && (y->s + y->t == y->s);
    double z = x->s * y->s;
    double q_prod = ldexp(1.0, 1023);          /* Omega/2 = 2^(femax-1) */
    /* Strict product magnitude bound (replaces the old per-factor 2^511 bounds):
       |RN(x->s*y->s)| < 2^1023 gives both the cond's real-product bound
       |FT2R x->s * FT2R y->s| <= Omega/2 AND finiteness of z. */
    int prod_bnd = fabs(z) < q_prod;
    return dwx && dwy && prod_bnd;
}

int dw_times_dw_weak_precond_check(const struct dword *x, const struct dword *y) {
    return dw_plus_dw_weak_precond_check(x, y);
}

int dw_div_fp_strong_check(const struct dword *x, double y) {
    if (!dw_div_fp_weak_check(x, y))
        return 0;

    double q_omega = ldexp(1.0, 1022);
    if (!(fabs(x->s) <= q_omega) || y == 0.0)
        return 0;

    double q = x->s / y;
    return fabs(q) < q_omega;
}

int dw_div_fp_weak_check(const struct dword *x, double y) {
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_y = isfinite_double(y);
    int dwx = fin_xh && fin_xl && (x->s + x->t == x->s);
    double q_plo = ldexp(1.0, -968);
    int xh_lo = (x->s == 0.0) || q_plo <= fabs(x->s);
    return dwx && fin_y && xh_lo;
}

int dw_plus_fp_strong_precond_check(const struct dword *x, double y) {
    /* Verifies DWPlusFP_strong_precond: xh, xl, y are finite, (x->s, x->t) is a
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

int dw_plus_fp_weak_precond_check(const struct dword *x, double y) {
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_y  = isfinite_double(y);
    int dwx = fin_xh && fin_xl && (x->s + x->t == x->s);
    return dwx && fin_y;
}

int isfinite_dword(const struct dword *x) {
    return isfinite_double(x->s) && isfinite_double(x->t);
}

int dw_div_dw_strong_precond_check(const struct dword *x, const struct dword *y) {
    /* Verifies DWDivDW_strong_precond (DDConds.v), the guard for the
       reciprocal-bootstrap double-word division kernel.  Nine conjuncts,
       five clauses: x->s, x->t, y->s, y->t finite; (x->s, x->t) and
       (y->s, y->t) double-words; |y->s| <= 2^(femax-p-5);
       2^(emin+2p) <= |y->s|; and |x->s/y->s| <= Omega/4.

       The quotient CEILING is the same construction as dw_div_fp_strong_check's: it is
       tested on the ROUNDED quotient q = RN(x->s / y->s), and the rounded->exact
       transfer is one-directional in Coq (BDIV_abs_le_bpow).  The STRICT `<` on
       qt_hi does double duty, giving the cond's real-quotient upper bound AND
       forcing q finite.  A non-strict `<=` would be UNSOUND, since RN is monotone
       and idempotent on the representable power of two 2^1022.

       Three clauses this check does NOT have, each because it would make the
       guard stronger than the condition it discharges:

       - No test on a rounded reciprocal 1.0/y->s.  The cond's conjunct 7 is
         stated directly as |y->s| <= 2^(femax-p-5); its reciprocal form
         2^(emin+2p+2) <= |1/y->s| is a statement about the EXACT reciprocal,
         so for y->s != 0 it is *equivalent* to |y->s| <= 2^(femax-p-5) = 2^966
         -- a direct, non-strict comparison on the input with no rounding and no
         transfer lemma.  (y->s != 0 comes from yh_lo below; at y->s == 0 the Coq
         model has 1/0 = 0, so the conjunct is false there and yh_lo is what rules
         that out.)  Testing q_qlo < fabs(1.0/y->s) instead would be strictly
         stronger AND would need an extra finiteness clause, since a strict lower
         bound on a rounded value does not force it finite (2^(emin+2p-1) < inf).

       - No `fabs(x->s) <= q_omega` clause.  The cond bounds no node by |x->s|:
         x->s only ever enters the algorithm multiplied by m ~ 1/y->s, so the
         quotient ceiling already covers every node it reaches.

       - No quotient FLOOR `q_qlo < fabs(q)`.  That was DWDivDW_relative_precond's conjunct 8,
         which DWDivDW_strong_precond drops; it bought the sharper 2*eta closing floor
         (and with it the pure 13.9u^2 relative bound), at the cost of rejecting
         every quotient below 2^-969.  The exported guarantee here is the
         whole-range mixed bound 9.8u^2|Q| + 2.5*eta plus double-word closure,
         which needs no such floor.

       The DW prop alone does not pin down finiteness of x->t / y->t in R (FT2R
       sends NaN/Inf to 0), so fin_xl and fin_yl are asserted, even though
       x->s + x->t == x->s implies them under IEEE comparison semantics. */
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_yh = isfinite_double(y->s);
    int fin_yl = isfinite_double(y->t);
    int dwx = fin_xh && fin_xl && (x->s + x->t == x->s);
    int dwy = fin_yh && fin_yl && (y->s + y->t == y->s);

    double q_omega = ldexp(1.0, 1022);   /* Omega/4 = 2^(femax-2) = 2^1022 */
    double q_yhi   = ldexp(1.0, 966);    /* 2^(femax-p-5) divisor upper bound */
    double q_ylo   = ldexp(1.0, -968);   /* 2^(emin+2*p)   divisor lower bound */

    /* |y->s| window: 2^(emin+2p) <= |y->s| <= 2^966.  Both sides are direct
       non-strict comparisons on the input -- the cond states conjunct 7 on
       |y->s| rather than on 1/y->s, so there is no rounded->exact transfer
       here.  yh_lo also forces y->s != 0.

       The upper exponent IS the exported u^2 coefficient: conjunct 7 says
       eta*|y->s| <= u^2/4, which is what pays for the reciprocal
       reconstruction's own underflow floor when the closing multiply by X
       scales it up.  Loosening 966 by k binades multiplies that charge by 2^k
       and takes the exported constant from 9.8 back toward 12.33 -- see the
       DWDivDW_relative_precond doc comment in DDModels.v. */
    int yh_hi = fabs(y->s) <= q_yhi;
    int yh_lo = q_ylo <= fabs(y->s);

    /* yh_lo implies y->s != 0.  Reject the remaining clauses before division,
       so an invalid divisor cannot raise a floating-point exception merely by
       being checked. */
    int ready = dwx && dwy && yh_hi && yh_lo;
    if (!ready) return 0;

    /* quotient ceiling on the rounded quotient q = RN(x->s / y->s) */
    double q = x->s / y->s;
    int qt_hi = fabs(q) < q_omega;   /* STRICT: |x->s/y->s| <= Omega/4; also forces q finite */
    return qt_hi;
}

int dw_div_dw_weak_precond_check(const struct dword *x, const struct dword *y) {
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_yh = isfinite_double(y->s);
    int fin_yl = isfinite_double(y->t);
    int dwx = fin_xh && fin_xl && (x->s + x->t == x->s);
    int dwy = fin_yh && fin_yl && (y->s + y->t == y->s);
    double q_yhi = ldexp(1.0, 966);
    double q_ylo = ldexp(1.0, -968);
    int yh_hi = fabs(y->s) <= q_yhi;
    int yh_lo = q_ylo <= fabs(y->s);
    return dwx && dwy && yh_hi && yh_lo;
}
