(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Shared proof environment for the body proofs of dd_ops.c.  As in LAProof's
   densemat_lemmas.v, every body-proof module imports this single definition of
   Gprog so that all semax_body theorems use exactly the VSU's specification
   environment. *)

Require Import VST.floyd.proofauto.
Require Import DD.verif_proofs.DDOpsASI.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition Gprog : funspecs := Ops_Imports ++ Ops_Internal.
