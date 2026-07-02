(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* The linked double-word library VSU.  linkVSUs merges the ops and checks
   translation units, discharging the guarded -> check calls (the one genuine
   cross-module boundary).  The result exports the six guarded wrappers; its
   only remaining imports are the libc/libm externals fma, exit, fabs, ldexp. *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.

Require Import DD.verif_proofs.vsu.Ops_VSU.
Require Import DD.verif_proofs.vsu.Checks_VSU.

Definition DDLibVSU := ltac:(linkVSUs OpsVSU ChecksVSU).
