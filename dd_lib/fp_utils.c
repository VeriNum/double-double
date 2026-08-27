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
    /* This Fast2Mult guard checks that the rounded product is finite.  That is
       exactly what the bound |err| <= 1/2 ulp(x*y) needs in every regime, so the
       check omits fast2_mult_check's underflow zero/threshold test.  It does
       NOT certify that mul + err == x*y or that the result is a valid double
       word; use fast2_mult_check for those guarantees.
       Discharges DDConds.Fast2Mult_acc_only_cond. */
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

int dw_plus_dw_check(struct dword *x, struct dword *y) {
    /* Verifies DWPlusDW_safe_input_cond: each component is finite, both pairs satisfy the
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
    /* Verifies DWTimesFP_mixed_error_input_cond: x->t, y finite; (x->s, x->t) is a double-word;
       round(x->s * y) finite; and the real product |FT2R x->s * FT2R y| <=
       Omega/2 = 2^(femax-1) = 2^1023.  The DW prop alone does not pin down
       finiteness of x->t in R (FT2R sends NaN/Inf to 0), so fin_xl is asserted,
       even though x->s + x->t == x->s implies it under IEEE comparison
       semantics.

       NOT CHECKED, deliberately: Fast2Mult's underflow disjunction
         FT2R x->s * FT2R y = 0  \/  2^(emin+2*p-1) <= |FT2R x->s * FT2R y|
       (the `mult_safe` test this function used to carry, and which
       fast2_mult_check still does).  That disjunct buys the
       PURE relative bound 2u^2 by excluding the Fast2Mult underflow gap, at the
       cost of aborting on any input whose leading product lands in it -- ordinary
       tiny-operand inputs.  The contract exported by dw_mult_fp9_guarded is
       instead the whole-range MIXED bound

         |(zh+zl) - (x->s + x->t)*y| <= 2u^2 |(x->s + x->t)*y| + 2.51*eta

       (DWMulFP_mixed_acc.DWTimesFP_mixed_guarantee_from_safe_input_cond),
       which holds in EVERY regime given
       only the double-word relation and finiteness of the computed pair.  The
       three conjuncts below are exactly what is needed to establish that
       finiteness
       (DWMulFP_relative_acc.DWTimesFP3_finite_from_safe_input_cond), so the gap is accepted
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

int dw_mult_dw_check(struct dword *x, struct dword *y) {
    /* Verifies DWTimesDW_mixed_error_input_cond: x->t, y->t finite; (x->s, x->t) and
       (y->s, y->t) are each a double-word; round(x->s * y->s) finite; and the
       real product |FT2R x->s * FT2R y->s| <= Omega/2 = 2^(femax-1) = 2^1023.

       This is dw_mult_fp_check with the scalar y promoted to a second
       double-word (y->s, y->t): the product bound now ranges over y->s (the high
       part), and finiteness of both y-components plus the y double-word relation
       are asserted, exactly as dw_plus_dw_check does for its second operand.
       The DW prop alone does not pin down finiteness of x->t / y->t in R (FT2R
       sends NaN/Inf to 0), so fin_xl / fin_yl are asserted, even though
       s + t == s implies each under IEEE comparison semantics.

       NOT CHECKED, deliberately: Fast2Mult's underflow disjunction
         FT2R x->s * FT2R y->s = 0  \/  2^(emin+2*p-1) <= |FT2R x->s * FT2R y->s|
       (the `mult_safe` test this function used to carry, and which
       fast2_mult_check still does).  That disjunct buys the PURE relative bound
       4u^2 by excluding the Fast2Mult underflow gap, at the cost of aborting on
       any input whose leading product lands in it -- ordinary tiny-operand
       inputs.  The contract exported by dw_mult_dw12_guarded is instead the
       whole-range MIXED bound

         |(zh+zl) - (x->s+x->t)*(y->s+y->t)|
             <= 4u^2 |(x->s+x->t)*(y->s+y->t)| + 2.5*eta

       (DWMulDW_mixed_acc.DWTimesDW_mixed_guarantee_from_safe_input_cond),
       which holds in EVERY regime given
       only the two double-word relations and finiteness of the computed pair.
       The four conjuncts below are exactly what is needed to establish that
       finiteness
       (DWMulDW_relative_acc.DWTimesDW3_finite_from_safe_input_cond), so the gap is accepted
       rather than fatal.  Output double-word closure likewise survives
       as part of the same mixed guarantee: closure needs only that the
       closing Fast2Sum preserves its sum, which holds both above the threshold
       (via the ordering |cl3| <= |ch|) and inside the gap (where failure of that
       ordering forces the exact sum onto the FLT/FIX lattice at emin, making
       Fast2Sum exact anyway).

       All soundness subtleties of the strict rounded-product bound
       (one-directional implication; overflow precluded because prod_bnd forces z
       finite) are identical to dw_mult_fp_check above -- see that comment. */
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

int dw_div_fp_check(struct dword *x, double y) {
    /* Verifies DWDivFP_mixed_safe_input_cond (DDConds.v): xh, xl, y finite; (x->s, x->t) a
       double-word; RN(x->s / y) finite; |x->s| in [2^(emin+2p), Omega/4]; and
       |x->s / y| <= Omega/4.  There is NO quotient lower bound.

       HISTORY, and why the floor is gone.  This test carried a quotient floor
       through two rounds of relaxation:

         2^(emin+2p-1) = 2^-969   the floor of an earlier, quotient-window
                                  formulation of the relative tier;
         2^(emin+p-1)  = 2^-1022  the floor of the internal
                                  DWDivFP_normal_quotient_input_cond in
                                  DWDivFP_relative_acc.v, which is what Layer 1's
                                  FLX->FLT bridge for the leading quotient
                                  node needs;
         (none)                   DWDivFP_mixed_safe_input_cond, this guard.

       The last step is not a bridge relaxation but a separate proof: below
       2^(emin+p-1) the leading node RN(x->s/y) is subnormal and Layer 1 does
       not apply at all, so that region gets its own argument
       (DWDivFP_subnormal.v, DWDivFP3_subnormal_leg).  It works because the
       whole computation there sits on the 2^emin lattice -- the correction
       lands within half an ulp of the exact one and the closing Fast2Sum is
       exact -- and it yields the SAME contract, with the SAME constant:

         |(zh+zl) - (x->s + x->t)/y| <= 3u^2 |(x->s + x->t)/y| + 2^emin

       (DWDivFP_mixed_acc.DWDivFP_mixed_guarantee_from_safe_input_cond), which
       bundles the accuracy bound and output double-word closure; finiteness of
       the computed pair is established while deriving the mixed condition.

       The PURE relative bound 3u^2 is a separate, NORMAL-RANGE tier
       (DWDivFP_relative_acc.DWDivFP_relative_accuracy); its condition constrains the
       computed nodes, not just the inputs, so no runtime input check
       discharges it.
       So the guard now admits EVERY quotient magnitude the format can
       represent, and the exported postcondition did not weaken.

       WHAT REPLACES THE FLOOR.  The cond's fifth conjunct is now
       `is_finite (BDIV x->s y)` -- the division analogue of Fast2Mult_acc_only_cond,
       which is likewise just `is_finite (BMULT a b)`.  It is established here by
       qt_hi alone: a STRICT comparison against a finite constant rejects NaN
       (unordered) and +Inf, so it forces RN(x->s/y) finite, which in turn forces
       y != 0 in R (BDIV_denom_ne0).  That is exactly what the old floor was
       secretly providing, at the cost of also rejecting tiny quotients.

       The STRICT `<` in qt_hi remains load-bearing and must not become `<=`:
       2^1022 is a representable power of two on which RN is monotone and
       idempotent, so a real quotient at or beyond it rounds to at or beyond it.
       The check may reject the measure-zero boundary |x->s/y| = 2^1022 (a
       harmless false negative) but never accepts an input violating the cond.

       CLAUSE 8 STAYS.  The |x->s| lower bound 2^(emin+2p) is NOT removable, and
       is a different bound on a different node: it is what makes the division
       residual (x->s + x->t) - th*y representable to relative accuracy u, hence
       what makes DWDivFP3 a double-word algorithm rather than a single-word
       one.  Concretely, x->s = 7*eta with y = 3*eta is a valid double word whose
       quotient 7/3 is perfectly normal, and on which the algorithm returns
       z->t = 0 with relative error u/2 -- violating 3u^2|Q| + c*eta for every
       constant c.  In this branch it also forces |y| > 2^(p+1), without which
       the closing division node has no bound at all.

       The DW prop alone does not pin down finiteness of x->t in R (FT2R sends
       NaN/Inf to 0), so fin_xl is asserted, even though x->s + x->t == x->s
       implies it under IEEE comparison semantics. */
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_y  = isfinite_double(y);
    int dwx = fin_xh && fin_xl && (x->s + x->t == x->s);

    double q_omega = ldexp(1.0, 1022);   /* Omega/4 = 2^(femax-2) = 2^1022 */
    double q_plo   = ldexp(1.0, -968);   /* 2^(emin+2*p)  product-node lower bound */

    /* |x->s| window: 2^(emin+2p) <= |x->s| <= Omega/4 */
    int xh_hi = fabs(x->s) <= q_omega;
    int xh_lo = q_plo <= fabs(x->s);

    /* Quotient CEILING only, on the rounded quotient q = RN(x->s / y).  There
       is deliberately no quotient floor: see the comment block above. */
    double q = x->s / y;
    int qt_hi = fabs(q) < q_omega;   /* STRICT: |x->s/y| <= Omega/4; also forces q finite */

    return dwx && fin_y && xh_hi && xh_lo && qt_hi;
}

int dw_plus_fp_check(struct dword *x, double y) {
    /* Verifies DWPlusFP_safe_input_cond: xh, xl, y are finite, (x->s, x->t) is a
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

int dw_div_dw_check(struct dword *x, struct dword *y) {
    /* Verifies DWDivDW_mixed_safe_input_cond (DDConds.v), the guard for the
       reciprocal-bootstrap double-word division dw_div_dw18.  Nine conjuncts,
       five clauses: x->s, x->t, y->s, y->t finite; (x->s, x->t) and
       (y->s, y->t) double-words; |y->s| <= 2^(femax-p-5);
       2^(emin+2p) <= |y->s|; and |x->s/y->s| <= Omega/4.

       The quotient CEILING is the same construction as dw_div_fp_check's: it is
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

       - No quotient FLOOR `q_qlo < fabs(q)`.  That was DWDivDW_relative_error_input_cond's conjunct 8,
         which DWDivDW_mixed_safe_input_cond drops; it bought the sharper 2*eta closing floor
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
       DWDivDW_relative_error_input_cond doc comment in DDModels.v. */
    int yh_hi = fabs(y->s) <= q_yhi;
    int yh_lo = q_ylo <= fabs(y->s);

    /* quotient ceiling on the rounded quotient q = RN(x->s / y->s) */
    double q = x->s / y->s;
    int qt_hi = fabs(q) < q_omega;   /* STRICT: |x->s/y->s| <= Omega/4; also forces q finite */

    return dwx && dwy && yh_hi && yh_lo && qt_hi;
}
