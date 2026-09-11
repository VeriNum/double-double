# A Guide to the Rocq Layer of FenceDD

FenceDD is a verified library for double-word arithmetic over IEEE 754 floating-point formats. This guide summarizes the main definitions and theorems in the Rocq development and maps the numbered results in the accompanying paper to their formal counterparts.

For the C implementation, runtime interfaces, and usage instructions, see the documentation in [`fenceDD`](fenceDD/).

## Contents

- [Common definitions](#common-definitions)
- [Functional models](#functional-models)
- [Definitions used by numerical theorems](#definitions-used-by-numerical-theorems)
- [Numerical Results](#numerical-results)
  - [Error-free transformations](#error-free-transformations)
  - [Double Word Operations](#double-word-operations)
    - [Double-word plus a floating-point number: `DWPlusFP`](#double-word-plus-a-floating-point-number-dwplusfp)
    - [Double-word plus a double-word number: `DWPlusDW`](#double-word-plus-a-double-word-number-dwplusdw)
    - [Double-word times a floating-point number: `DWTimesFP`](#double-word-times-a-floating-point-number-dwtimesfp)
    - [Double-word times a double-word number: `DWTimesDW`](#double-word-times-a-double-word-number-dwtimesdw)
    - [Double-word divided by a floating-point number: `DWDivFP`](#double-word-divided-by-a-floating-point-number-dwdivfp)
    - [Double-word divided by a double-word number: `DWDivDW`](#double-word-divided-by-a-double-word-number-dwdivdw)
- [C implementations](#c-implementations)
- [Verified weak and strong wrappers](#verified-weak-and-strong-wrappers)

## Common definitions

| Concept | Rocq definition | Paper definition |
|---|---|---|
| Round to nearest, ties to even | `rounded` ([`common/common.v`](common/common.v#L10)) and the VCFloat operations `BPLUS`, `BMULT`, `BDIV`, and `BFMA` | `RN`, Section 3.1 |
| Precision and range parameters | `fprec t`, `bpow radix2 (-fprec t)`, and `bpow radix2 common.emin` | `p`, `u=2^-p`, and `eta=2^emin`, Section 3.1 |
| Finite returned pair | `is_finite_p` ([`common/common.v`](common/common.v#L18)) | `Fin(zh,zl)`, Definition 3.5 for DWDivFP and Theorem 3.9 for the remaining operations |
| Double word | `double_word_prop xh xl` ([`DDModels.v`](DDModels.v#L62)) | `xh = RN(xh+xl)`, Definition 2.1 |
| Error-free transformation | Exact reconstruction together with `double_word_prop` | Definition 3.1 |

## Functional models

| Algorithm | Rocq definition | Paper definition |
|---|---|---|
| TwoSum | `TwoSumF` ([source](DDModels.v#L14)) | Joldes et al., Algorithm 1; Figure 8a |
| Fast2Sum | `Fast2Sum` ([source](DDModels.v#L29)) | Joldes et al., Algorithm 2; Figure 8b |
| Fast2Mult | `Fast2Mult` ([source](DDModels.v#L44)) | Joldes et al., Algorithm 3; Figure 8c |
| Addition of a double word and floating-point value | `DWPlusFP` ([source](DDModels.v#L74)) | Joldes et al., Algorithm 4; Table 1 and Theorem 3.9 |
| Addition of two double words | `DWPlusDW` ([source](DDModels.v#L80)) | Joldes et al., Algorithm 6; Table 1 and Theorem 3.9 |
| Multiplication of a double word and floating-point value | `DWTimesFP` ([source](DDModels.v#L89)) | Joldes et al., Algorithm 9; Table 1 and Theorem 3.9 |
| Multiplication of two double words | `DWTimesDW` ([source](DDModels.v#L95)) | Joldes et al., Algorithm 12; Table 1 and Theorem 3.9 |
| Division of a double word by a floating-point value | `DWDivFP` ([source](DDModels.v#L104)) | Joldes et al., Algorithm 15; Figure 9 and Theorem 3.7 |
| Division of two double words | `DWDivDW` ([source](DDModels.v#L114)) | Joldes et al., Algorithm 18; Table 1 and Theorem 3.9 |

## Definitions used by numerical theorems

This table lists the named predicates that occur in the statements of
accuracy and correctness results.

| Name | Description | Rocq definition | Paper reference |
|---|---|---|---|
| Fast2Sum exact hypothesis | The rounded sum is finite and the operands are ordered | `Fast2Sum_exact_cond` ([definition](DDConds.v#L34)) | Theorem 3.2(2) |
| Fast2Mult exact hypothesis | The rounded leading product is finite and the exact product is zero or lies above a threshold | `Fast2Mult_exact_cond` ([definition](DDConds.v#L54)) | Theorem 3.4, exact case |
| DWPlusFP weak theorem hypothesis | The input pair is a double word and the returned pair is finite | `DWPlusFP_weak_pre_and_finite_post_cond` ([definition](DDConds.v#L125)) | Theorem 3.9, finite-result alternative |
| DWPlusFP strong theorem hypothesis | The operands are finite, the input pair is a double word, and the high component and floating-point operand are bounded by `Omega/4` | `DWPlusFP_strong_precond` ([definition](DDConds.v#L108)) | Theorem 3.9, Table 2 |
| DWPlusDW weak theorem hypothesis | Both input pairs are double words and the returned pair is finite | `DWPlusDW_weak_pre_and_finite_post_cond` ([definition](DDConds.v#L89)) | Theorem 3.9, finite-result alternative |
| DWPlusDW strong theorem hypothesis | The operands are finite, both input pairs are double words, and both leading components are bounded by `Omega/4` | `DWPlusDW_strong_precond` ([definition](DDConds.v#L69)) | Theorem 3.9, Table 2 |
| DWTimesFP weak theorem hypothesis | The input pair is a double word and the returned pair is finite | `DWTimesFP_weak_pre_and_finite_post_cond` ([definition](DDConds.v#L169)) | Theorem 3.9, finite-result alternative |
| DWTimesFP strong theorem hypothesis | The low component is finite, the input pair is a double word, the rounded leading product is finite, and the exact leading product is bounded by `Omega/2` | `DWTimesFP_strong_precond` ([definition](DDConds.v#L155)) | Theorem 3.9, Table 2 |
| DWTimesDW weak theorem hypothesis | Both input pairs are double words and the returned pair is finite | `DWTimesDW_weak_pre_and_finite_post_cond` ([definition](DDConds.v#L240)) | Theorem 3.9, finite-result alternative |
| DWTimesDW strong theorem hypothesis | The low components are finite, both input pairs are double words, the rounded leading product is finite, and the exact leading product is bounded by `Omega/2` | `DWTimesDW_strong_precond` ([definition](DDConds.v#L210)) | Theorem 3.9, Table 2 |
| DWDivFP weak theorem hypothesis | The dividend is a double word, its leading component is zero or above the required lower bound, and the returned pair is finite | `DWDivFP_weak_pre_and_finite_post_cond` ([definition](DDConds.v#L308)) | Definition 3.5, weak input and finite-result definitions |
| DWDivFP strong theorem hypothesis | The operands and leading quotient are finite, the dividend is a double word, and input and quotient bounds provide overflow and residual-accuracy headroom | `DWDivFP_strong_precond` ([definition](DDConds.v#L285)) | Definition 3.5, strong input definition |
| DWDivFP normal-range hypothesis | The leading quotient is normal, and the correction is zero or its quotient by the divisor is normal | `DWDivFP_relative_regime_cond` ([definition](DDConds.v#L321)) | Theorem 3.7, relative error case |
| DWDivFP strong pure-relative hypothesis | The strong input hypothesis and the normal-range hypothesis both hold | `DWDivFP_relative_precond` ([definition](DDConds.v#L336)) | Definition 3.5 and Theorem 3.7, relative error case |
| DWDivDW weak theorem hypothesis | Both inputs are double words, the leading divisor lies in the required magnitude window, and the returned pair is finite | `DWDivDW_weak_pre_and_finite_post_cond` ([definition](DDConds.v#L390)) | Theorem 3.9, finite-result alternative |
| DWDivDW strong theorem hypothesis | All components are finite, both inputs are double words, the leading divisor lies in the required magnitude window, and the leading quotient has overflow headroom | `DWDivDW_strong_precond` ([definition](DDConds.v#L367)) | Theorem 3.9, Table 2 |

## Numerical Results

### Error-free transformations

| Model | Description | Rocq theorem | Paper theorem |
|---|---|---|---|
| `TwoSumF` | If both returned components are finite, `t = a + b - s` and `(s,t)` is a double word | `TwoSumF_correct` and `TwoSum_is_DW` ([exact sum](accuracy_proofs/basic_blocks/TwoSum_acc_helpers.v#L1108), [double-word result](accuracy_proofs/basic_blocks/TwoSum_acc_helpers.v#L1165)) | Theorem 3.2(1) |
| `Fast2Sum` | If `RN(a+b)` is finite and either `ulp(b) <= ulp(a)` or `a = 0`, then `t = a + b - s` | `FastTwoSum_correct_from_exact_cond` ([source](accuracy_proofs/basic_blocks/Fast2Sum_acc_helpers.v#L122)) | Theorem 3.2(2) |
| `Fast2Sum` | If `RN(a+b)` is finite and `abs(b) <= abs(a)`, then `abs(t) <= ulp(a+b)/2`, `s+t = a+b`, and `(s,t)` is a double word | `Fast2Sum_exact_guarantee_from_magnitude_order` ([source](accuracy_proofs/basic_blocks/Fast2Sum_acc.v#L70)) | Theorem 3.2(2) |
| `Fast2Sum` | If `(s,t)` is finite and `abs(a+b) <= 2^(emin+p)`, then `s+t = a+b`; this equality also establishes that `(s,t)` is a double word | `Fast2Sum_sum_exact_of_sum_small` and `Fast2Sum_double_word_of_sum` ([exact sum](accuracy_proofs/basic_blocks/Fast2Sum_acc_helpers.v#L497), [double-word result](accuracy_proofs/basic_blocks/Fast2Sum_acc_helpers.v#L563)) | Theorem 3.3 |
| `Fast2Mult` | If `p >= 3` and `(ch,cl)` is finite, then `abs((ch+cl)-a*b) <= eta/2` | `Fast2Mult_sum_error_floor` ([source](accuracy_proofs/basic_blocks/Fast2Mult_acc.v#L120)) | Theorem 3.4 |
| `Fast2Mult` | If `RN(a*b)` is finite and either `a*b = 0` or `abs(a*b) >= 2^(emin+2p-1)`, then `abs(cl) <= ulp(a*b)/2`, `ch+cl = a*b`, and `(ch,cl)` is a double word | `Fast2Mult_accuracy_from_exact_cond` and `Fast2Mult_correct_from_exact_cond` ([accuracy](accuracy_proofs/basic_blocks/Fast2Mult_acc.v#L219), [exact reconstruction](accuracy_proofs/basic_blocks/Fast2Mult_acc.v#L233)) | Theorem 3.4, exact case |

### Double Word Operations

Every theorem listed below proves a combined accuracy and double-word result.

#### Double-word plus a floating-point number: `DWPlusFP`

| Description | Rocq theorem | Paper theorem |
|---|---|---|
| Accuracy and double-word result from the weak input hypothesis and result finiteness | `DWPlusFP_relative_guarantee_from_weak_pre_and_finite_post_cond` ([theorem](accuracy_proofs/dw_opps/DWPlusFP_relative_acc.v#L151)) | Theorem 3.9, finite-result alternative |
| Accuracy and double-word result from the strong input hypothesis | `DWPlusFP_relative_guarantee_from_strong_precond` ([theorem](accuracy_proofs/dw_opps/DWPlusFP_relative_acc.v#L181)) | Theorem 3.9, Table 2 |

#### Double-word plus a double-word number: `DWPlusDW`

| Description | Rocq theorem | Paper theorem |
|---|---|---|
| Accuracy and double-word result from the weak input hypothesis and result finiteness | `DWPlusDW_relative_guarantee_from_weak_pre_and_finite_post_cond` ([theorem](accuracy_proofs/dw_opps/DWPlusDW_relative_acc.v#L272)) | Theorem 3.9, finite-result alternative |
| Accuracy and double-word result from the strong input hypothesis | `DWPlusDW_relative_guarantee_from_strong_precond` ([theorem](accuracy_proofs/dw_opps/DWPlusDW_relative_acc.v#L302)) | Theorem 3.9, Table 2 |

#### Double-word times a floating-point number: `DWTimesFP`

| Description | Rocq theorem | Paper theorem |
|---|---|---|
| Accuracy and double-word result from the weak input hypothesis and result finiteness | `DWTimesFP_guarantee_from_weak_pre_and_finite_post_cond` ([theorem](accuracy_proofs/dw_opps/DWTimesFP_mixed_acc.v#L502)) | Theorem 3.9, finite-result alternative |
| Accuracy and double-word result from the strong input hypothesis | `DWTimesFP_guarantee_from_strong_precond` ([theorem](accuracy_proofs/dw_opps/DWTimesFP_mixed_acc.v#L520)) | Theorem 3.9, Table 2 |

#### Double-word times a double-word number: `DWTimesDW`

| Description | Rocq theorem | Paper theorem |
|---|---|---|
| Accuracy and double-word result from the weak input hypothesis and result finiteness | `DWTimesDW_guarantee_from_weak_pre_and_finite_post_cond` ([theorem](accuracy_proofs/dw_opps/DWTimesDW_mixed_acc.v#L2638)) | Theorem 3.9, finite-result alternative |
| Accuracy and double-word result from the strong input hypothesis | `DWTimesDW_guarantee_from_strong_precond` ([theorem](accuracy_proofs/dw_opps/DWTimesDW_mixed_acc.v#L2668)) | Theorem 3.9, Table 2 |

#### Double-word divided by a floating-point number: `DWDivFP`

| Description | Rocq theorem | Paper theorem |
|---|---|---|
| Accuracy and double-word result from the weak input hypothesis and result finiteness | `DWDivFP_guarantee_from_weak_pre_and_finite_post_cond` ([theorem](accuracy_proofs/dw_opps/DWDivFP_mixed_acc.v#L276)) | Theorem 3.7 and Corollary 3.8, finite-result alternative |
| Accuracy and double-word result from the strong input hypothesis | `DWDivFP_guarantee_from_strong_precond` ([theorem](accuracy_proofs/dw_opps/DWDivFP_mixed_acc.v#L290)) | Theorem 3.7 and Corollary 3.8, strong-input alternative |

#### Double-word divided by a double-word number: `DWDivDW`

| Description | Rocq theorem | Paper theorem |
|---|---|---|
| Accuracy and double-word result from the weak input hypothesis and result finiteness | `DWDivDW_guarantee_from_weak_pre_and_finite_post_cond` ([theorem](accuracy_proofs/dw_opps/DWDivDW_mixed_acc.v#L79)) | Theorem 3.9, finite-result alternative |
| Accuracy and double-word result from the strong input hypothesis | `DWDivDW_guarantee_from_strong_precond` ([theorem](accuracy_proofs/dw_opps/DWDivDW_mixed_acc.v#L104)) | Theorem 3.9, Table 2 |


## C implementations

| Transformation | Kernel implementation | Public wrapper | Runtime check implementation |
|---|---|---|---|
| TwoSum | `two_sum` ([source](fenceDD/two_sum.c#L4)) | Same function | None |
| Fast2Sum | `fast_2sum_kernel` ([source](fenceDD/fast_2sum_kernel.c#L4)) | `fast_2sum` ([source](fenceDD/fast_2sum.c#L5)) | `fast2_sum_magnitude_order_check` ([source](fenceDD/fp_utils.c#L48)) |
| Fast2Mult exact | `fast_2mult_kernel` ([source](fenceDD/fast_2mult_kernel.c#L4)) | `fast_2mult` ([source](fenceDD/fast_2mult.c#L5)) | `fast2_mult_exact_check` ([source](fenceDD/fp_utils.c#L23)) |

| Operation | Kernel implementation | Default (weak) and alternative (strong) wrappers | Weak and strong runtime checks |
|---|---|---|---|
| DWPlusFP | `dw_plus_fp_kernel` ([source](fenceDD/dw_plus_fp_kernel.c#L6)) | `dw_plus_fp` ([source](fenceDD/dw_plus_fp.c#L7)), `dw_plus_fp_strong` ([source](fenceDD/dw_plus_fp.c#L18)) | [`dw_plus_fp_weak_precond_check`](fenceDD/fp_utils.c#L247), [`dw_plus_fp_strong_precond_check`](fenceDD/fp_utils.c#L231) |
| DWPlusDW | `dw_plus_dw_kernel` ([source](fenceDD/dw_plus_dw_kernel.c#L4)) | `dw_plus_dw` ([source](fenceDD/dw_plus_dw.c#L7)), `dw_plus_dw_strong` ([source](fenceDD/dw_plus_dw.c#L18)) | [`dw_plus_dw_weak_precond_check`](fenceDD/fp_utils.c#L71), [`dw_plus_dw_strong_precond_check`](fenceDD/fp_utils.c#L53) |
| DWTimesFP | `dw_times_fp_kernel` ([source](fenceDD/dw_times_fp_kernel.c#L4)) | `dw_times_fp` ([source](fenceDD/dw_times_fp.c#L5)), `dw_times_fp_strong` ([source](fenceDD/dw_times_fp.c#L15)) | [`dw_times_fp_weak_precond_check`](fenceDD/fp_utils.c#L145), [`dw_times_fp_strong_precond_check`](fenceDD/fp_utils.c#L81) |
| DWTimesDW | `dw_times_dw_kernel` ([source](fenceDD/dw_times_dw_kernel.c#L4)) | `dw_times_dw` ([source](fenceDD/dw_times_dw.c#L5)), `dw_times_dw_strong` ([source](fenceDD/dw_times_dw.c#L15)) | [`dw_times_dw_weak_precond_check`](fenceDD/fp_utils.c#L205), [`dw_times_dw_strong_precond_check`](fenceDD/fp_utils.c#L149) |
| DWDivFP | `dw_div_fp_kernel` ([source](fenceDD/dw_div_fp_kernel.c#L4)) | `dw_div_fp` ([source](fenceDD/dw_div_fp.c#L5)), `dw_div_fp_strong` ([source](fenceDD/dw_div_fp.c#L15)) | [`dw_div_fp_weak_check`](fenceDD/fp_utils.c#L221), [`dw_div_fp_strong_check`](fenceDD/fp_utils.c#L209) |
| DWDivDW | `dw_div_dw_kernel` ([source](fenceDD/dw_div_dw_kernel.c#L4)) | `dw_div_dw` ([source](fenceDD/dw_div_dw.c#L5)), `dw_div_dw_strong` ([source](fenceDD/dw_div_dw.c#L15)) | [`dw_div_dw_weak_precond_check`](fenceDD/fp_utils.c#L338), [`dw_div_dw_strong_precond_check`](fenceDD/fp_utils.c#L259) |

Every default wrapper calls `isfinite_dword` after the arithmetic kernel
([source](fenceDD/fp_utils.c#L255)). Every alternative wrapper obtains result
finiteness from the strong input condition.

## Verified weak and strong wrappers

All six kernels have an unconditional refinement proof identifying their C
result with the corresponding functional model. Each public wrapper has an
empty numerical precondition: a failed check exits, while normal return
provides the listed numerical guarantee.

Theorem 2.2 is the normal-return contract for both DWDivFP wrappers. Theorem
4.1 is the soundness theorem for the two DWDivFP runtime checks. The VST items
below are the formal counterparts of these numbered statements and of the
library-wide wrapper claims summarized in Table 1.

The default wrappers run `isfinite_dword` after the kernel; its VST interface
is `isfinite_dword_spec` and its proof is `body_isfinite_dword`
([spec](verif_proofs/fp_utils_specs.v#L93),
[proof](verif_proofs/verif_fp_utils_dw_plus_fp_interface_checks.v#L95)). Thus
their proof path is:

```text
weak check -> kernel refinement -> result-finiteness check
           -> *_guarantee_from_weak_pre_and_finite_post_cond
           -> weak wrapper contract
```

The alternative wrappers use:

```text
strong check -> *_strong_precond -> kernel refinement
             -> *_guarantee_from_strong_precond
             -> strong wrapper contract
```

The body proofs are assembled into the library VSUs by
[`Ops_VSU.v`](verif_proofs/vsu/Ops_VSU.v) and
[`Checks_VSU.v`](verif_proofs/vsu/Checks_VSU.v).

### Error-free transformations

The transformation interfaces do not use the weak and strong wrapper split.

| Transformation | Kernel spec / proof | Public wrapper spec / proof | Runtime check spec / proof |
|---|---|---|---|
| TwoSum | `two_sum_spec` / `body_two_sum` ([spec](verif_proofs/DDOpsASI.v#L43), [proof](verif_proofs/verif_dd_ops_basic.v#L21)) | Same function and proof | None |
| Fast2Sum | `fast_2sum_kernel_spec` / `body_fast_2sum_kernel` ([spec](verif_proofs/DDOpsASI.v#L51), [proof](verif_proofs/verif_dd_ops_basic.v#L29)) | `fast_2sum_spec` / `body_fast_2sum` ([spec](verif_proofs/DDOpsASI.v#L208), [proof](verif_proofs/verif_dd_ops_basic.v#L45)) | `fast2_sum_magnitude_order_check_spec` / `body_fast2_sum_magnitude_order_check` ([spec](verif_proofs/fp_utils_specs.v#L73), [proof](verif_proofs/verif_fp_utils_fast2_sum_magnitude_order_check.v#L11)) |
| Fast2Mult exact | `fast_2mult_kernel_spec` / `body_fast_2mult_kernel` ([spec](verif_proofs/DDOpsASI.v#L59), [proof](verif_proofs/verif_dd_ops_basic.v#L37)) | `fast_2mult_spec` / `body_fast_2mult` ([spec](verif_proofs/DDOpsASI.v#L220), [proof](verif_proofs/verif_dd_ops_basic.v#L76)) | `fast2_mult_exact_check_spec` / `body_fast2_mult_exact_check` ([spec](verif_proofs/fp_utils_specs.v#L34), [proof](verif_proofs/verif_fp_utils_fast2_mult_exact_check.v#L10)) |

### Double-word operations

| Operation | Kernel spec / refinement proof | Default (weak) checker and wrapper | Alternative (strong) checker and wrapper |
|---|---|---|---|
| DWPlusFP | `dw_plus_fp_kernel_spec` / `body_dw_plus_fp_kernel` ([spec](verif_proofs/DDOpsASI.v#L71), [proof](verif_proofs/verif_dd_ops_plus.v#L29)) | Check: `dw_plus_fp_weak_precond_check_spec` / `body_dw_plus_fp_weak_precond_check` ([spec](verif_proofs/fp_utils_specs.v#L106), [proof](verif_proofs/verif_fp_utils_dw_plus_fp_interface_checks.v#L7)); wrapper: `dw_plus_fp_spec` / `body_dw_plus_fp` ([spec](verif_proofs/DDOpsASI.v#L86), [proof](verif_proofs/verif_dd_ops_plus.v#L75)) | Check: `dw_plus_fp_strong_precond_check_spec` / `body_dw_plus_fp_strong_precond_check` ([spec](verif_proofs/fp_utils_specs.v#L157), [proof](verif_proofs/verif_fp_utils_dw_plus_fp_strong_precond_check.v#L15)); wrapper: `dw_plus_fp_strong_spec` / `body_dw_plus_fp_strong` ([spec](verif_proofs/DDOpsASI.v#L101), [proof](verif_proofs/verif_dd_ops_plus.v#L124)) |
| DWPlusDW | `dw_plus_dw_kernel_spec` / `body_dw_plus_dw_kernel` ([spec](verif_proofs/DDOpsASI.v#L116), [proof](verif_proofs/verif_dd_ops_plus.v#L47)) | Check: `dw_plus_dw_weak_precond_check_spec` / `body_dw_plus_dw_weak_precond_check` ([spec](verif_proofs/fp_utils_specs.v#L139), [proof](verif_proofs/verif_fp_utils_dw_plus_dw_strong_precond_check.v#L301)); wrapper: `dw_plus_dw_spec` / `body_dw_plus_dw` ([spec](verif_proofs/DDOpsASI.v#L245), [proof](verif_proofs/verif_dd_ops_plus.v#L153)) | Check: `dw_plus_dw_strong_precond_check_spec` / `body_dw_plus_dw_strong_precond_check` ([spec](verif_proofs/fp_utils_specs.v#L121), [proof](verif_proofs/verif_fp_utils_dw_plus_dw_strong_precond_check.v#L15)); wrapper: `dw_plus_dw_strong_spec` / `body_dw_plus_dw_strong` ([spec](verif_proofs/DDOpsASI.v#L265), [proof](verif_proofs/verif_dd_ops_plus.v#L210)) |
| DWTimesFP | `dw_times_fp_kernel_spec` / `body_dw_times_fp_kernel` ([spec](verif_proofs/DDOpsASI.v#L135), [proof](verif_proofs/verif_dd_ops_times.v#L22)) | Check: `dw_times_fp_weak_precond_check_spec` / `body_dw_times_fp_weak_precond_check` ([spec](verif_proofs/fp_utils_specs.v#L236), [proof](verif_proofs/verif_fp_utils_dw_times_fp_strong_precond_check.v#L182)); wrapper: `dw_times_fp_spec` / `body_dw_times_fp` ([spec](verif_proofs/DDOpsASI.v#L285), [proof](verif_proofs/verif_dd_ops_times.v#L62)) | Check: `dw_times_fp_strong_precond_check_spec` / `body_dw_times_fp_strong_precond_check` ([spec](verif_proofs/fp_utils_specs.v#L220), [proof](verif_proofs/verif_fp_utils_dw_times_fp_strong_precond_check.v#L30)); wrapper: `dw_times_fp_strong_spec` / `body_dw_times_fp_strong` ([spec](verif_proofs/DDOpsASI.v#L301), [proof](verif_proofs/verif_dd_ops_times.v#L113)) |
| DWTimesDW | `dw_times_dw_kernel_spec` / `body_dw_times_dw_kernel` ([spec](verif_proofs/DDOpsASI.v#L150), [proof](verif_proofs/verif_dd_ops_times.v#L36)) | Check: `dw_times_dw_weak_precond_check_spec` / `body_dw_times_dw_weak_precond_check` ([spec](verif_proofs/fp_utils_specs.v#L268), [proof](verif_proofs/verif_fp_utils_dw_times_dw_strong_precond_check.v#L238)); wrapper: `dw_times_dw_spec` / `body_dw_times_dw` ([spec](verif_proofs/DDOpsASI.v#L317), [proof](verif_proofs/verif_dd_ops_times.v#L142)) | Check: `dw_times_dw_strong_precond_check_spec` / `body_dw_times_dw_strong_precond_check` ([spec](verif_proofs/fp_utils_specs.v#L250), [proof](verif_proofs/verif_fp_utils_dw_times_dw_strong_precond_check.v#L22)); wrapper: `dw_times_dw_strong_spec` / `body_dw_times_dw_strong` ([spec](verif_proofs/DDOpsASI.v#L337), [proof](verif_proofs/verif_dd_ops_times.v#L198)) |
| DWDivFP | `dw_div_fp_kernel_spec` / `body_dw_div_fp_kernel` ([spec](verif_proofs/DDOpsASI.v#L188), [proof](verif_proofs/verif_dd_ops_div.v#L78)) | Check: `dw_div_fp_weak_check_spec` / `body_dw_div_fp_weak_check` ([spec](verif_proofs/fp_utils_specs.v#L197), [proof](verif_proofs/verif_fp_utils_dw_div_fp_strong_check.v#L130)); wrapper: `dw_div_fp_spec` / `body_dw_div_fp` ([spec](verif_proofs/DDOpsASI.v#L357), [proof](verif_proofs/verif_dd_ops_div.v#L110)) | Check: `dw_div_fp_strong_check_spec` / `body_dw_div_fp_strong_check` ([spec](verif_proofs/fp_utils_specs.v#L181), [proof](verif_proofs/verif_fp_utils_dw_div_fp_strong_check.v#L11)); wrapper: `dw_div_fp_strong_spec` / `body_dw_div_fp_strong` ([spec](verif_proofs/DDOpsASI.v#L373), [proof](verif_proofs/verif_dd_ops_div.v#L162)) |
| DWDivDW | `dw_div_dw_kernel_spec` / `body_dw_div_dw_kernel` ([spec](verif_proofs/DDOpsASI.v#L169), [proof](verif_proofs/verif_dd_ops_div.v#L31)) | Check: `dw_div_dw_weak_precond_check_spec` / `body_dw_div_dw_weak_precond_check` ([spec](verif_proofs/fp_utils_specs.v#L303), [proof](verif_proofs/verif_fp_utils_dw_div_dw_strong_precond_check.v#L327)); wrapper: `dw_div_dw_spec` / `body_dw_div_dw` ([spec](verif_proofs/DDOpsASI.v#L389), [proof](verif_proofs/verif_dd_ops_div.v#L191)) | Check: `dw_div_dw_strong_precond_check_spec` / `body_dw_div_dw_strong_precond_check` ([spec](verif_proofs/fp_utils_specs.v#L285), [proof](verif_proofs/verif_fp_utils_dw_div_dw_strong_precond_check.v#L52)); wrapper: `dw_div_dw_strong_spec` / `body_dw_div_dw_strong` ([spec](verif_proofs/DDOpsASI.v#L408), [proof](verif_proofs/verif_dd_ops_div.v#L246)) |
