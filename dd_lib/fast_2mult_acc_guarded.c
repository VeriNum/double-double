#include <stdlib.h>
#include "dw_arith.h"
#include "fp_utils.h"

/* "Accurate-only" guarded Fast2Mult wrapper (Tier B).  It guards fast_2mult
   with the cheaper fast2_mult_acc_check (finiteness only, no underflow
   zero/threshold test).  Its verified postcondition carries only the accuracy
   bound |st->t| <= 1/2 ulp(a*b); it does NOT assert the error-free / double-word
   property.  Use fast_2mult_guarded for the full accurate+correct guarantee. */
void fast_2mult_acc_guarded(struct dword *st, double a, double b) {
   if (!fast2_mult_acc_check(a,b)) {
      exit(EXIT_FAILURE);
   }
   fast_2mult(st, a, b);
}
