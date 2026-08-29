/* dw_arith_guarded_inline.h
 *
 * Header-inline distribution of the checked double-word operations.  The
 * addition defaults check their mathematical inputs and reject nonfinite
 * outputs; strong and guarded interfaces use sufficient input checks.  The
 * bodies mirror fp_utils.c and the public wrapper sources.
 *
 * All EFTs retain their guarded variants.  DW + FP additionally exposes the
 * default input-check/kernel/output-check interface and a strong-input
 * interface.  The Tier B Fast2Mult wrapper
 * (fast_2mult_acc_guarded) whose contract contains only a bound on the returned
 * error component.  It uses the cheaper fast2_mult_product_finite_check and does NOT prove
 * exact reconstruction or that the output is a valid double word.  Use
 * fast_2mult_guarded for those stronger guarantees.
 *
 * Pulls in dw_arith_inline.h for the internal kernels the wrappers delegate to.
 */
#ifndef DWARITH_GUARDED_INLINE_DOT_H
#define DWARITH_GUARDED_INLINE_DOT_H

#include <stdlib.h>   /* exit */
#include <math.h>     /* fabs, ldexp */
#include <float.h>    /* DBL_MIN, DBL_MAX */
#include "dw_arith_inline.h"

/* ---- checks (from fp_utils.c) -------------------------------------------- */

static inline int isfinite_double(double x) { return (x - x) == 0.0; }

static inline int dword_finite_check(struct dword *x) {
    int fin_s = isfinite_double(x->s);
    int fin_t = isfinite_double(x->t);
    if (!fin_s) return 0;
    if (!fin_t) return 0;
    return 1;
}

static inline int two_sum_exact_check(double a, double b) {
    int fin_sum  = isfinite_double(a + b);
    int fin_diff = isfinite_double(a - b);
    return fin_sum && fin_diff && (fabs(b) < DBL_MAX);
}

static inline int fast2_sum_magnitude_order_check(double a, double b) {
    double s = a + b;
    int fin = isfinite_double(s);
    return fin && (fabs(b) <= fabs(a));
}

static inline int fast2_mult_exact_check(double x, double y) {
    double z = x * y;
    double thresh = DBL_MIN * ldexp(1.0, 53);   /* 2^(emin + 2p - 1) */
    int fin = isfinite_double(z);
    int zx = x == 0.0 && isfinite_double(y);
    int zy = y == 0.0 && isfinite_double(x);
    return fin && ((zx || zy) || thresh < fabs(z));
}

static inline int fast2_mult_product_finite_check(double x, double y) {
    return isfinite_double(x * y);   /* Tier B proves only the error bound. */
}

static inline int dw_plus_fp_strong_precond_check(struct dword *x, double y) {
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_y  = isfinite_double(y);
    int dwx = fin_xh && fin_xl && (x->s + x->t == x->s);
    double q_omega = ldexp(1.0, 1022);          /* Omega/4 */
    int xh_bnd = fabs(x->s) <= q_omega;
    int y_bnd  = fabs(y)    <= q_omega;
    return dwx && fin_y && xh_bnd && y_bnd;
}

static inline int dw_plus_fp_weak_precond_check(struct dword *x, double y) {
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_y  = isfinite_double(y);
    int dwx = fin_xh && fin_xl && (x->s + x->t == x->s);
    return dwx && fin_y;
}

static inline int dw_plus_dw_strong_precond_check(struct dword *x, struct dword *y) {
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_yh = isfinite_double(y->s);
    int fin_yl = isfinite_double(y->t);
    int dwx = fin_xh && fin_xl && (x->s + x->t == x->s);
    int dwy = fin_yh && fin_yl && (y->s + y->t == y->s);
    double q_omega = ldexp(1.0, 1022);
    int xh_bnd = fabs(x->s) <= q_omega;
    int yh_bnd = fabs(y->s) <= q_omega;
    return dwx && dwy && xh_bnd && yh_bnd;
}

static inline int dw_plus_dw_weak_precond_check(struct dword *x, struct dword *y) {
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_yh = isfinite_double(y->s);
    int fin_yl = isfinite_double(y->t);
    int dwx = fin_xh && fin_xl && (x->s + x->t == x->s);
    int dwy = fin_yh && fin_yl && (y->s + y->t == y->s);
    return dwx && dwy;
}

/* DWTimesFP_strong_precond: no underflow disjunction -- the exported contract is the
   whole-range mixed bound 2u^2|P| + 2.51*eta, not the pure 2u^2 relative bound,
   so the Fast2Mult underflow gap is accepted.  See dd_lib/fp_utils.c. */
static inline int dw_mult_fp_strong_precond_check(struct dword *x, double y) {
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_y  = isfinite_double(y);
    int dwx    = fin_xh && fin_xl && (x->s + x->t == x->s);
    double z = x->s * y;
    double q_prod = ldexp(1.0, 1023);           /* Omega/2 */
    int prod_bnd = fabs(z) < q_prod;
    return dwx && fin_y && prod_bnd;
}

static inline int dw_mult_fp_weak_precond_check(struct dword *x, double y) {
    return dw_plus_fp_weak_precond_check(x, y);
}

/* DWTimesDW_strong_precond: no underflow disjunction -- the exported contract is the
   whole-range mixed bound 4u^2|P| + 2.5*eta, not the pure 8u^2 relative bound,
   so the Fast2Mult underflow gap is accepted.  See dd_lib/fp_utils.c. */
static inline int dw_mult_dw_strong_precond_check(struct dword *x, struct dword *y) {
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_yh = isfinite_double(y->s);
    int fin_yl = isfinite_double(y->t);
    int dwx    = fin_xh && fin_xl && (x->s + x->t == x->s);
    int dwy    = fin_yh && fin_yl && (y->s + y->t == y->s);
    double z = x->s * y->s;
    double q_prod = ldexp(1.0, 1023);           /* Omega/2 */
    int prod_bnd = fabs(z) < q_prod;
    return dwx && dwy && prod_bnd;
}

static inline int dw_mult_dw_weak_precond_check(struct dword *x, struct dword *y) {
    return dw_plus_dw_weak_precond_check(x, y);
}

/* Discharges DWDivFP_strong_precond.  NO quotient floor: qt_hi alone gives both the
   quotient ceiling and finiteness of RN(x->s/y) (hence y != 0), which is the
   cond's fifth conjunct.  The xh floor admits exact zero separately. */
static inline int dw_div_fp_strong_precond_check(struct dword *x, double y) {
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_y  = isfinite_double(y);
    int dwx = fin_xh && fin_xl && (x->s + x->t == x->s);
    double q_omega = ldexp(1.0, 1022);           /* Omega/4 = 2^(femax-2) */
    double q_plo   = ldexp(1.0, -968);           /* 2^(emin+2p), product node */
    int xh_hi = fabs(x->s) <= q_omega;
    int xh_lo = (x->s == 0.0) || q_plo <= fabs(x->s);
    double q = x->s / y;
    int qt_hi = fabs(q) < q_omega;   /* STRICT: also forces q finite, hence y != 0 */
    return dwx && fin_y && xh_hi && xh_lo && qt_hi;
}

static inline int dw_div_fp_weak_precond_check(struct dword *x, double y) {
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_y = isfinite_double(y);
    int dwx = fin_xh && fin_xl && (x->s + x->t == x->s);
    double q_plo = ldexp(1.0, -968);
    int xh_lo = (x->s == 0.0) || q_plo <= fabs(x->s);
    return dwx && fin_y && xh_lo;
}

static inline int dw_div_dw_strong_precond_check(struct dword *x, struct dword *y) {
    int fin_xh = isfinite_double(x->s);
    int fin_xl = isfinite_double(x->t);
    int fin_yh = isfinite_double(y->s);
    int fin_yl = isfinite_double(y->t);
    int dwx = fin_xh && fin_xl && (x->s + x->t == x->s);
    int dwy = fin_yh && fin_yl && (y->s + y->t == y->s);
    double q_omega = ldexp(1.0, 1022);           /* Omega/4 = 2^(femax-2) */
    double q_yhi   = ldexp(1.0, 966);            /* 2^(femax-p-5) */
    double q_ylo   = ldexp(1.0, -968);           /* 2^(emin+2p) */
    /* Divisor window |y->s| in [2^(emin+2p), 2^(femax-p-5)]; the upper side is
       conjunct 7 stated directly on |y->s| (equivalently
       2^(emin+2p+2) <= |1/y->s|), and it implies |y->s| <= Omega/4.  yh_lo
       forces y->s != 0.  The upper exponent IS the exported u^2 coefficient
       9.8 -- loosening it by k binades costs a factor 2^k on the reciprocal
       floor's charge.  No |x->s| bound and no quotient FLOOR: see
       dd_lib/fp_utils.c, this mirrors DWDivDW_strong_precond. */
    int yh_hi = fabs(y->s) <= q_yhi;
    int yh_lo = q_ylo <= fabs(y->s);
    double q = x->s / y->s;
    int qt_hi = fabs(q) < q_omega;   /* STRICT: also forces q finite */
    return dwx && dwy && yh_hi && yh_lo && qt_hi;
}


static inline int dw_div_dw_weak_precond_check(struct dword *x, struct dword *y) {
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

/* ---- guarded wrappers (from dd_lib *_guarded.c) -------------------------- */

static inline void two_sum_guarded(struct dword *st, double a, double b) {
    if (!two_sum_exact_check(a, b)) exit(EXIT_FAILURE);
    two_sum(st, a, b);
}
static inline void fast_2sum_guarded(struct dword *st, double a, double b) {
    if (!fast2_sum_magnitude_order_check(a, b)) exit(EXIT_FAILURE);
    fast_2sum(st, a, b);
}
static inline void fast_2mult_guarded(struct dword *st, double a, double b) {
    if (!fast2_mult_exact_check(a, b)) exit(EXIT_FAILURE);
    fast_2mult(st, a, b);
}
static inline void fast_2mult_acc_guarded(struct dword *st, double a, double b) {
    if (!fast2_mult_product_finite_check(a, b)) exit(EXIT_FAILURE);
    fast_2mult(st, a, b);
}
static inline void dw_plus_fp(struct dword *st, struct dword *x, double y) {
    if (!dw_plus_fp_weak_precond_check(x, y)) exit(EXIT_FAILURE);
    dw_plus_fp_kernel(st, x, y);
    if (!dword_finite_check(st)) exit(EXIT_FAILURE);
}
static inline void dw_plus_fp_strong(struct dword *st, struct dword *x, double y) {
    if (!dw_plus_fp_strong_precond_check(x, y)) exit(EXIT_FAILURE);
    dw_plus_fp_kernel(st, x, y);
}
static inline void dw_plus_dw(struct dword *st, struct dword *x, struct dword *y) {
    if (!dw_plus_dw_weak_precond_check(x, y)) exit(EXIT_FAILURE);
    dw_plus_dw_kernel(st, x, y);
    if (!dword_finite_check(st)) exit(EXIT_FAILURE);
}
static inline void dw_plus_dw_strong(struct dword *st, struct dword *x, struct dword *y) {
    if (!dw_plus_dw_strong_precond_check(x, y)) exit(EXIT_FAILURE);
    dw_plus_dw_kernel(st, x, y);
}
static inline void dw_mult_fp(struct dword *st, struct dword *x, double y) {
    if (!dw_mult_fp_weak_precond_check(x, y)) exit(EXIT_FAILURE);
    dw_mult_fp_kernel(st, x, y);
    if (!dword_finite_check(st)) exit(EXIT_FAILURE);
}
static inline void dw_mult_fp_strong(struct dword *st, struct dword *x, double y) {
    if (!dw_mult_fp_strong_precond_check(x, y)) exit(EXIT_FAILURE);
    dw_mult_fp_kernel(st, x, y);
}
static inline void dw_mult_dw(struct dword *st, struct dword *x, struct dword *y) {
    if (!dw_mult_dw_weak_precond_check(x, y)) exit(EXIT_FAILURE);
    dw_mult_dw_kernel(st, x, y);
    if (!dword_finite_check(st)) exit(EXIT_FAILURE);
}
static inline void dw_mult_dw_strong(struct dword *st, struct dword *x, struct dword *y) {
    if (!dw_mult_dw_strong_precond_check(x, y)) exit(EXIT_FAILURE);
    dw_mult_dw_kernel(st, x, y);
}
static inline void dw_div_fp(struct dword *z, struct dword *x, double y) {
    if (!dw_div_fp_weak_precond_check(x, y)) exit(EXIT_FAILURE);
    dw_div_fp_kernel(z, x, y);
    if (!dword_finite_check(z)) exit(EXIT_FAILURE);
}
static inline void dw_div_fp_strong(struct dword *z, struct dword *x, double y) {
    if (!dw_div_fp_strong_precond_check(x, y)) exit(EXIT_FAILURE);
    dw_div_fp_kernel(z, x, y);
}
static inline void dw_div_dw(struct dword *st, struct dword *x, struct dword *y) {
    if (!dw_div_dw_weak_precond_check(x, y)) exit(EXIT_FAILURE);
    dw_div_dw_kernel(st, x, y);
    if (!dword_finite_check(st)) exit(EXIT_FAILURE);
}
static inline void dw_div_dw_strong(struct dword *st, struct dword *x, struct dword *y) {
    if (!dw_div_dw_strong_precond_check(x, y)) exit(EXIT_FAILURE);
    dw_div_dw_kernel(st, x, y);
}

#endif /* DWARITH_GUARDED_INLINE_DOT_H */
