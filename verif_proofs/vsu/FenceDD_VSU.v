(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* The linked double-word library VSU.  linkVSUs merges the operation and check
   translation units and discharges their internal calls.  The only remaining
   imports are the libm functions fma, fabs, and ldexp. *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.

Require Import DD.verif_proofs.vsu.Ops_VSU.
Require Import DD.verif_proofs.vsu.Checks_VSU.

Definition FenceDDVSU := ltac:(linkVSUs OpsVSU ChecksVSU).
