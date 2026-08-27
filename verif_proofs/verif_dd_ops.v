(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Compatibility aggregator for the body proofs of dd_ops.c.  New code should
   import the family modules directly; this module preserves the former
   single import interface. *)

Require Export DD.verif_proofs.verif_dd_ops_common.
Require Export DD.verif_proofs.verif_dd_ops_basic.
Require Export DD.verif_proofs.verif_dd_ops_plus.
Require Export DD.verif_proofs.verif_dd_ops_mult.
Require Export DD.verif_proofs.verif_dd_ops_div.
