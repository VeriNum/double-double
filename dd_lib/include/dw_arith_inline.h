/* dw_arith_inline.h
 *
 * Header-inline distribution of the double-word primitives, mirroring QD's
 * approach (kernels defined `inline` in a header) so consumers inline them at
 * -O2 WITHOUT needing -flto / whole-program optimization.
 *
 * The function BODIES here are copied verbatim from the corresponding dd_lib
 * source files, so the algorithm is identical to the verified/linked library: same
 * Coq/VST-proven arithmetic, bit-for-bit identical outputs. What differs is only
 * the compilation/packaging:
 *
 *   - dd_lib .c + dw_arith.h   : out-of-line functions, compiled by CompCert
 *                                (ccomp). The proof-carrying, end-to-end-verified
 *                                artifact. Callers pay a function-call + struct
 *                                store per op unless they enable -flto.
 *   - dw_arith_inline.h (this) : same source, but the CONSUMER'S compiler
 *                                (gcc/clang) inlines and codegens it. Matches QD's
 *                                speed with no special flags. Note: the resulting
 *                                machine code is produced by the consumer's
 *                                compiler, not CompCert -- the same trust posture
 *                                you already accept when you build the library
 *                                with -flto. The C-level correctness proof still
 *                                applies; the CompCert-compiled-this-exact-object
 *                                guarantee does not.
 *
 * Use exactly ONE of the two headers in a translation unit, not both.
 */
#ifndef DWARITH_INLINE_DOT_H
#define DWARITH_INLINE_DOT_H

#include <math.h>   /* fma */

struct dword { double s; double t; };

static inline void two_sum(struct dword *st, double a, double b) {
   double ap; double bp; double da; double db;
   st->s  = a + b;
   ap     = st->s - b;
   bp     = st->s - ap;
   da     = a - ap;
   db     = b - bp;
   st->t  = da + db;
}

static inline void fast_2sum(struct dword *st, double a, double b) {
   double z;
   st->s  = a + b;
   z      = st->s - a;
   st->t  = b - z;
}

static inline void fast_2mult(struct dword *st, double a, double b) {
   st->s  = a * b;
   st->t  = fma(a, b, -st->s);
}

static inline void dw_plus_fp_kernel(struct dword *st, struct dword *x, double y) {
   double v; struct dword sh;
   two_sum(&sh, x->s, y);
   v      = x->t + sh.t;
   fast_2sum(st, sh.s, v);
}

static inline void dw_plus_dw_kernel(struct dword *st, struct dword *x, struct dword *y) {
   double c; double w;
   struct dword sh; struct dword th; struct dword vh;
   two_sum(&sh, x->s, y->s);
   two_sum(&th, x->t, y->t);
   c      = sh.t + th.s;
   fast_2sum(&vh, sh.s, c);
   w      = th.t + vh.t;
   fast_2sum(st, vh.s, w);
}

static inline void dw_mult_fp9(struct dword *zh, struct dword *x, double y) {
   double c3; struct dword ch;
   fast_2mult(&ch, x->s, y);
   c3     = fma(x->t, y, ch.t);
   fast_2sum(zh, ch.s, c3);
}

static inline void dw_mult_dw12(struct dword *zh, struct dword *x, struct dword *y) {
   double t0; double t1; double c2; double c3;
   struct dword ch;
   fast_2mult(&ch, x->s, y->s);
   t0     = x->t * y->t;
   t1     = fma(x->s, y->t, t0);
   c2     = fma(x->t, y->s, t1);
   c3     = ch.t + c2;
   fast_2sum(zh, ch.s, c3);
}

static inline void dw_div_fp15(struct dword *z, struct dword *x, double y) {
   double th; struct dword p; double dh; double dt; double d; double tl;
   th = x->s / y;
   fast_2mult(&p, th, y);
   dh = x->s - p.s;
   dt = dh - p.t;
   d = dt + x->t;
   tl = d / y;
   fast_2sum(z, th, tl);
}

static inline void dw_div_dw18(struct dword *z, struct dword *x, struct dword *y) {
   double th; double rh; double rl;
   struct dword e; struct dword delta; struct dword m;
   th     = 1.0 / y->s;
   rh     = fma(-y->s, th, 1.0);      /* rh = 1 - yh*th (exact) */
   rl     = -(y->t * th);
   fast_2sum(&e, rh, rl);
   dw_mult_fp9(&delta, &e, th);
   dw_plus_fp_kernel(&m, &delta, th);
   dw_mult_dw12(z, x, &m);
}

#endif /* DWARITH_INLINE_DOT_H */
