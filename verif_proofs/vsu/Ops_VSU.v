(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* The operations VSU packages the kernels and public wrappers in [dd_ops.c].
   The checks are discharged by linking with [ChecksVSU]; fma and exit remain
   imports of the linked VSU. *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Require Import DDModels.
Require Import DD.verif_proofs.verif_objs.dd_ops.
Require Import DD.verif_proofs.DDOpsASI.
Require Import DD.verif_proofs.verif_dd_ops_common.
Require Import DD.verif_proofs.verif_dd_ops_basic.
Require Import DD.verif_proofs.verif_dd_ops_plus.
Require Import DD.verif_proofs.verif_dd_ops_mult.
Require Import DD.verif_proofs.verif_dd_ops_div.
Require Import DD.verif_proofs.vsu.VSU_tactics.

Definition OpsVSU: @VSU NullExtension.Espec
        nil Ops_Imports ltac:(QPprog prog) Ops_Exports emp.
Proof.
  mkVSU prog Ops_Internal.
  (* Discharge each internal function's SF obligation by focusing the first
     remaining goal.  Sequential 1:{ } focusing avoids a `;`-composition
     interaction that causes solve_SF_internal's evars to elaborate incorrectly. *)
  1:{ solve_SF_dd body_two_sum. }
  1:{ solve_SF_dd body_fast_2sum. }
  1:{ solve_SF_dd body_fast_2mult. }
  1:{ solve_SF_dd body_dw_plus_fp_kernel. }
  1:{ solve_SF_dd body_dw_plus_fp. }
  1:{ solve_SF_dd body_dw_plus_fp_strong. }
  1:{ solve_SF_dd body_dw_plus_dw_kernel. }
  1:{ solve_SF_dd body_dw_plus_dw. }
  1:{ solve_SF_dd body_dw_plus_dw_strong. }
  1:{ solve_SF_dd body_dw_mult_fp_kernel. }
  1:{ solve_SF_dd body_two_sum_guarded. }
  1:{ solve_SF_dd body_fast_2sum_guarded. }
  1:{ solve_SF_dd body_fast_2mult_guarded. }
  1:{ solve_SF_dd body_fast_2mult_acc_guarded. }
  1:{ solve_SF_dd body_dw_mult_fp. }
  1:{ solve_SF_dd body_dw_mult_fp_strong. }
  1:{ solve_SF_dd body_dw_mult_dw_kernel. }
  1:{ solve_SF_dd body_dw_mult_dw. }
  1:{ solve_SF_dd body_dw_mult_dw_strong. }
  1:{ solve_SF_dd body_dw_div_dw18. }
  1:{ solve_SF_dd body_dw_div_dw18_guarded. }
  1:{ solve_SF_dd body_dw_div_fp15. }
  1:{ solve_SF_dd body_dw_div_fp15_guarded. }
Qed.
