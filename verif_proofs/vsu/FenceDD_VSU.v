(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.

Require Import DD.verif_proofs.vsu.Ops_VSU.
Require Import DD.verif_proofs.vsu.Checks_VSU.

Definition FenceDDVSU := ltac:(linkVSUs OpsVSU ChecksVSU).
