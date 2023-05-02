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

void two_sum(struct dword *st, double a, double b);

void fast_2sum(struct dword *st, double a, double b);

void dw_plus_sfp(struct dword *st, struct dword *x, float a);

#endif /* DWARITH_DOT_H */
