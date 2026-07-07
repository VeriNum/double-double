// dd_lib/include/fp_utils.h
#ifndef FP_UTILS_H
#define FP_UTILS_H

#include "dw_arith.h"

int isfinite_double(double x);

int fast2_sum_check(double a, double b);

int two_sum_check(double a, double b);

int fast2_mult_check(double x, double y);

int fast2_mult_acc_check(double x, double y);

int fast2_mult_check2(double x, double y, double z);

int dw_plus_dw_check(struct dword *x, struct dword *y);

int dw_plus_fp_check(struct dword *x, double y);

int dw_mult_fp_check(struct dword *x, double y);

int dw_mult_dw_check(struct dword *x, struct dword *y);

#endif