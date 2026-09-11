(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

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
Require Import DD.verif_proofs.verif_dd_ops_times.
Require Import DD.verif_proofs.verif_dd_ops_div.
Require Import DD.verif_proofs.vsu.VSU_tactics.

Definition OpsVSU: @VSU NullExtension.Espec
        nil Ops_Imports ltac:(QPprog prog) Ops_Exports emp.
Proof.
  mkVSU prog Ops_Internal.

  1:{ solve_SF_dd body_two_sum. }
  1:{ solve_SF_dd body_fast_2sum_kernel. }
  1:{ solve_SF_dd body_fast_2mult_kernel. }
  1:{ solve_SF_dd body_dw_plus_fp_kernel. }
  1:{ solve_SF_dd body_dw_plus_fp. }
  1:{ solve_SF_dd body_dw_plus_fp_strong. }
  1:{ solve_SF_dd body_dw_plus_dw_kernel. }
  1:{ solve_SF_dd body_dw_plus_dw. }
  1:{ solve_SF_dd body_dw_plus_dw_strong. }
  1:{ solve_SF_dd body_dw_times_fp_kernel. }
  1:{ solve_SF_dd body_fast_2sum. }
  1:{ solve_SF_dd body_fast_2mult. }
  1:{ solve_SF_dd body_dw_times_fp. }
  1:{ solve_SF_dd body_dw_times_fp_strong. }
  1:{ solve_SF_dd body_dw_times_dw_kernel. }
  1:{ solve_SF_dd body_dw_times_dw. }
  1:{ solve_SF_dd body_dw_times_dw_strong. }
  1:{ solve_SF_dd body_dw_div_dw_kernel. }
  1:{ solve_SF_dd body_dw_div_dw. }
  1:{ solve_SF_dd body_dw_div_dw_strong. }
  1:{ solve_SF_dd body_dw_div_fp_kernel. }
  1:{ solve_SF_dd body_dw_div_fp. }
  1:{ solve_SF_dd body_dw_div_fp_strong. }
Qed.
