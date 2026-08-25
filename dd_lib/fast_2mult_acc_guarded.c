#include <stdlib.h>
#include "dw_arith.h"
#include "fp_utils.h"

/* This Tier B Fast2Mult wrapper exposes only a bound on the returned error
   component.  It guards fast_2mult with the cheaper fast2_mult_acc_check, which
   tests that the rounded product is finite but does not perform the underflow
   zero/threshold test.  Its verified postcondition carries only
   |st->t| <= 1/2 ulp(a*b); it does NOT assert exact reconstruction or that the
   output is a valid double word.  Use fast_2mult_guarded for those stronger
   guarantees. */
void fast_2mult_acc_guarded(struct dword *st, double a, double b) {
   if (!fast2_mult_acc_check(a,b)) {
      exit(EXIT_FAILURE);
   }
   fast_2mult(st, a, b);
}
