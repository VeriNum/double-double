/* dd_ops.c
 *
 * Aggregation translation unit for VSU verification.
 *
 * This file exists solely to compile the double-word *operations* and their
 * guarded wrappers into a single Clight program (verif_objs/dd_ops.v) so that
 * all intra-module calls (guarded -> unguarded, composite -> leaf) are resolved
 * within one CompSpecs.  The runtime checks live in fp_utils.c (a separate TU);
 * the guarded wrappers here call them as externals, discharged at VSU link time.
 *
 * The included headers carry include guards, so the repeated header includes in
 * the aggregated .c files are harmless.  Each .c is included exactly once.
 */

#include "two_sum.c"
#include "two_sum_guarded.c"
#include "fast_2sum.c"
#include "fast_2sum_guarded.c"
#include "fast_2mult.c"
#include "fast_2mult_guarded.c"
#include "fast_2mult_acc_guarded.c"

#include "dw_plus_fp.c"
#include "dw_plus_fp_guarded.c"

#include "dw_plus_dw.c"
#include "dw_plus_dw_guarded.c"

#include "dw_mult_fp.c"
#include "dw_mult_fp_guarded.c"

#include "dw_mult_dw.c"
#include "dw_mult_dw_guarded.c"

#include "dw_div_dw.c"
