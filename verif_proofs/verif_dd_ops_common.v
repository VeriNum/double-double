(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Shared proof environment for the body proofs of dd_ops.c.  As in LAProof's
   densemat_lemmas.v, every body proof module imports this single definition of
   Gprog so that all semax_body theorems use exactly the VSU's specification
   environment. *)

Require Import VST.floyd.proofauto.
Require Import DD.verif_proofs.DDOpsASI.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

(* The checker specs are defined under the [fp_utils] translation unit's
   composite environment and reused by the [dd_ops] translation unit.  Both
   environments contain the same [struct dword]; these instances let VST move
   spatial assertions across that module boundary. *)
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
