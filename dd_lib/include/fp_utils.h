// dd_lib/include/fp_utils.h
#ifndef FP_UTILS_H
#define FP_UTILS_H

#include "dw_arith.h"

int isfinite_double(double x);

int dword_finite_check(struct dword *x);

int fast2_sum_magnitude_order_check(double a, double b);

int two_sum_exact_check(double a, double b);

int fast2_mult_exact_check(double x, double y);

int fast2_mult_product_finite_check(double x, double y);

int dw_plus_dw_strong_precond_check(struct dword *x, struct dword *y);

int dw_plus_dw_weak_precond_check(struct dword *x, struct dword *y);

int dw_plus_fp_strong_precond_check(struct dword *x, double y);

int dw_plus_fp_weak_precond_check(struct dword *x, double y);

int dw_div_fp_strong_precond_check(struct dword *x, double y);

int dw_div_fp_weak_precond_check(struct dword *x, double y);

int dw_mult_fp_strong_precond_check(struct dword *x, double y);

int dw_mult_fp_weak_precond_check(struct dword *x, double y);

int dw_mult_dw_strong_precond_check(struct dword *x, struct dword *y);

int dw_mult_dw_weak_precond_check(struct dword *x, struct dword *y);

int dw_div_dw_strong_precond_check(struct dword *x, struct dword *y);

int dw_div_dw_weak_precond_check(struct dword *x, struct dword *y);

#endif
