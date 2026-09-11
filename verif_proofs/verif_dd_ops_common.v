(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import VST.floyd.proofauto.
Require Import DD.verif_proofs.DDOpsASI.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

#[export] Instance change_composite_env_checks_ops :
  change_composite_env fp_utils_specs.CompSpecs DDOpsASI.CompSpecs.
Proof.
  make_cs_preserve fp_utils_specs.CompSpecs DDOpsASI.CompSpecs.
Qed.

#[export] Instance change_composite_env_ops_checks :
  change_composite_env DDOpsASI.CompSpecs fp_utils_specs.CompSpecs.
Proof.
  make_cs_preserve DDOpsASI.CompSpecs fp_utils_specs.CompSpecs.
Qed.

Definition Gprog : funspecs := Ops_Imports ++ Ops_Internal.
