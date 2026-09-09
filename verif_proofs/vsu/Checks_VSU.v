(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* The checks VSU packages the runtime checks in [fp_utils.c].  It imports
   fabs and ldexp and exports the checks consumed by the operations VSU. *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Require Import DDModels.
Require Import DD.verif_proofs.verif_objs.fp_utils.
Require Import DD.verif_proofs.fp_utils_specs.
Require Import DD.verif_proofs.verif_fp_utils_common.
Require Import DD.verif_proofs.verif_fp_utils_isfinite_double.
Require Import DD.verif_proofs.verif_fp_utils_two_sum_exact_check.
Require Import DD.verif_proofs.verif_fp_utils_fast2_sum_magnitude_order_check.
Require Import DD.verif_proofs.verif_fp_utils_fast2_mult_exact_check.
Require Import DD.verif_proofs.verif_fp_utils_fast2_mult_product_finite_check.
Require Import DD.verif_proofs.verif_fp_utils_dw_plus_dw_strong_precond_check.
Require Import DD.verif_proofs.verif_fp_utils_dw_times_dw_strong_precond_check.
Require Import DD.verif_proofs.verif_fp_utils_dw_plus_fp_strong_precond_check.
Require Import DD.verif_proofs.verif_fp_utils_dw_plus_fp_interface_checks.
Require Import DD.verif_proofs.verif_fp_utils_dw_times_fp_strong_precond_check.
Require Import DD.verif_proofs.verif_fp_utils_dw_div_fp_strong_check.
Require Import DD.verif_proofs.verif_fp_utils_dw_div_dw_strong_precond_check.
Require Import DD.verif_proofs.vsu.VSU_tactics.

Definition ChecksVSU: @VSU NullExtension.Espec
        nil Checks_Imports ltac:(QPprog prog) Checks_Exports emp.
Proof.
  mkVSU prog Checks_Internal.
  1:{ solve_SF_dd body_isfinite_double. }
  1:{ solve_SF_dd body_fast2_mult_exact_check. }
  1:{ solve_SF_dd body_fast2_mult_product_finite_check. }
  1:{ solve_SF_dd body_fast2_sum_magnitude_order_check. }
  1:{ solve_SF_dd body_two_sum_exact_check. }
  1:{ solve_SF_dd body_dw_plus_dw_strong_precond_check. }
  1:{ solve_SF_dd body_dw_plus_dw_weak_precond_check. }
  1:{ solve_SF_dd body_dw_times_fp_strong_precond_check. }
  1:{ solve_SF_dd body_dw_times_fp_weak_precond_check. }
  1:{ solve_SF_dd body_dw_times_dw_strong_precond_check. }
  1:{ solve_SF_dd body_dw_times_dw_weak_precond_check. }
  1:{ solve_SF_dd body_dw_plus_fp_strong_precond_check. }
  1:{ solve_SF_dd body_dw_plus_fp_weak_precond_check. }
  1:{ solve_SF_dd body_isfinite_dword. }
  1:{ solve_SF_dd body_dw_div_fp_strong_check. }
  1:{ solve_SF_dd body_dw_div_fp_weak_check. }
  1:{ solve_SF_dd body_dw_div_dw_strong_precond_check. }
  1:{ solve_SF_dd body_dw_div_dw_weak_precond_check. }
Qed.
