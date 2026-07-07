/* dw_arith.h
 *
 * Copright (C) 2023 Ariel Kellison
 *
 * Double-double precision floating point arithmetic.
 *
 */

#ifndef DWARITH_DOT_H
#define DWARITH_DOT_H

struct dword {
 double s; 
 double t;
};

void fast_2mult(struct dword *st, double a, double b);

void fast_2mult_guarded(struct dword *st, double a, double b);

void fast_2mult_acc_guarded(struct dword *st, double a, double b);

void two_sum(struct dword *st, double a, double b);

void two_sum_guarded(struct dword *st, double a, double b);

void fast_2sum(struct dword *st, double a, double b);

void fast_2sum_guarded(struct dword *st, double a, double b);

void dw_plus_fp(struct dword *st, struct dword *x, double a);

void dw_plus_fp_guarded(struct dword *st, struct dword *x, double y);

void dw_plus_dw2(struct dword *st, struct dword *x, struct dword *y);

void dw_plus_dw2_guarded(struct dword *st, struct dword *x, struct dword *y);

void dw_mult_fp9(struct dword *st, struct dword *x, double y);

void dw_mult_fp9_guarded(struct dword *st, struct dword *x, double y);

void dw_mult_dw12(struct dword *st, struct dword *x, struct dword *y);

void dw_mult_dw12_guarded(struct dword *st, struct dword *x, struct dword *y);

void dw_div_fp15(struct dword *st, struct dword *x, double y);

void dw_div_dw18(struct dword *st, struct dword *x, struct dword *y);

#endif /* DWARITH_DOT_H */
