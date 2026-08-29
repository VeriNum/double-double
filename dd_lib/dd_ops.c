/* dd_ops.c
 *
 * Aggregation translation unit for VSU verification.
 *
 * This file exists solely to compile the double-word operations and their
 * public wrappers into a single Clight program (verif_objs/dd_ops.v) so that
 * all intra-module calls (wrapper -> kernel, composite -> leaf) are resolved
 * within one CompSpecs.  The runtime checks live in fp_utils.c (a separate TU);
 * the public wrappers call them as externals, discharged at VSU link time.
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

#include "dw_plus_fp_kernel.c"
#include "dw_plus_fp.c"

#include "dw_plus_dw_kernel.c"
#include "dw_plus_dw.c"

#include "dw_times_fp_kernel.c"
#include "dw_times_fp.c"

#include "dw_times_dw_kernel.c"
#include "dw_times_dw.c"

#include "dw_div_dw_kernel.c"
#include "dw_div_dw.c"

#include "dw_div_fp_kernel.c"
#include "dw_div_fp.c"
