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
Require Import DD.verif_proofs.verif_fp_utils_two_sum_check.
Require Import DD.verif_proofs.verif_fp_utils_fast2_sum_check.
Require Import DD.verif_proofs.verif_fp_utils_fast2_mult_check.
Require Import DD.verif_proofs.verif_fp_utils_fast2_mult_acc_check.
Require Import DD.verif_proofs.verif_fp_utils_dw_plus_dw_check.
Require Import DD.verif_proofs.verif_fp_utils_dw_mult_dw_check.
Require Import DD.verif_proofs.verif_fp_utils_dw_plus_fp_check.
Require Import DD.verif_proofs.verif_fp_utils_dw_plus_fp_interface_checks.
Require Import DD.verif_proofs.verif_fp_utils_dw_mult_fp_check.
Require Import DD.verif_proofs.verif_fp_utils_dw_div_fp_check.
Require Import DD.verif_proofs.verif_fp_utils_dw_div_dw_check.
Require Import DD.verif_proofs.vsu.VSU_tactics.

Definition ChecksVSU: @VSU NullExtension.Espec
        nil Checks_Imports ltac:(QPprog prog) Checks_Exports emp.
Proof.
  mkVSU prog Checks_Internal.
  1:{ solve_SF_dd body_isfinite_double. }
  1:{ solve_SF_dd body_fast2_mult_check. }
  1:{ solve_SF_dd body_fast2_mult_acc_check. }
  1:{ solve_SF_dd body_fast2_sum_check. }
  1:{ solve_SF_dd body_two_sum_check. }
  1:{ solve_SF_dd body_dw_plus_dw_check. }
  1:{ solve_SF_dd body_dw_plus_dw_input_check. }
  1:{ solve_SF_dd body_dw_mult_fp_check. }
  1:{ solve_SF_dd body_dw_mult_dw_check. }
  1:{ solve_SF_dd body_dw_plus_fp_check. }
  1:{ solve_SF_dd body_dw_plus_fp_input_check. }
  1:{ solve_SF_dd body_dword_finite_check. }
  1:{ solve_SF_dd body_dw_div_fp_check. }
  1:{ solve_SF_dd body_dw_div_dw_check. }
Qed.
