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

void fast_2mult_kernel(struct dword *st, double a, double b);

void fast_2mult(struct dword *st, double a, double b);

void two_sum(struct dword *st, double a, double b);

void fast_2sum_kernel(struct dword *st, double a, double b);

void fast_2sum(struct dword *st, double a, double b);

void dw_plus_fp_kernel(struct dword *st, struct dword *x, double y);

void dw_plus_fp(struct dword *st, struct dword *x, double y);

void dw_plus_fp_strong(struct dword *st, struct dword *x, double y);

void dw_plus_dw_kernel(struct dword *st, struct dword *x, struct dword *y);

void dw_plus_dw(struct dword *st, struct dword *x, struct dword *y);

void dw_plus_dw_strong(struct dword *st, struct dword *x, struct dword *y);

void dw_times_fp_kernel(struct dword *st, struct dword *x, double y);

void dw_times_fp(struct dword *st, struct dword *x, double y);

void dw_times_fp_strong(struct dword *st, struct dword *x, double y);

void dw_times_dw_kernel(struct dword *st, struct dword *x, struct dword *y);

void dw_times_dw(struct dword *st, struct dword *x, struct dword *y);

void dw_times_dw_strong(struct dword *st, struct dword *x, struct dword *y);

void dw_div_fp_kernel(struct dword *st, struct dword *x, double y);

void dw_div_fp(struct dword *st, struct dword *x, double y);

void dw_div_fp_strong(struct dword *st, struct dword *x, double y);

void dw_div_dw_kernel(struct dword *st, struct dword *x, struct dword *y);

void dw_div_dw(struct dword *st, struct dword *x, struct dword *y);

void dw_div_dw_strong(struct dword *st, struct dword *x, struct dword *y);

#endif /* DWARITH_DOT_H */
