(* Copyright 2025 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Quarantine for unused helpers that were defined alongside the TwoSum
   accuracy proofs but turned out to have no callers. Kept here so they
   remain discoverable without polluting the main proof path. *)

Require Import vcfloat.VCFloat.
From Stdlib Require Import ZArith.
Require Import float_acc_lems op_defs dd_tactics.
Require Import DDModels common.
From Flocq Require Import Core.
Require Import mathcomp.ssreflect.ssreflect.

Set Bullet Behavior "Strict Subproofs".

Section TwoSumWIP.

Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).

(* Discharges generic_format goals about FT2R values and 0. Unused. *)
Ltac basic_round :=
  try (rewrite -B2R_float_of_ftype; apply Binary.generic_format_B2R);
  try apply generic_format_0
.

(* Variant of Flocq's pred_plus_ulp identity. Unused. *)
Lemma pred_plus_ulp_2:
  forall (beta : radix) (fexp : Z -> Z),
  Valid_exp fexp ->
  forall x : R,
  0 < x ->
  generic_format beta fexp x -> pred beta fexp x = x - Ulp.ulp beta fexp (pred beta fexp x).
Proof.
  intros; pose proof pred_plus_ulp beta fexp x H0 H1; nra.
Qed.

(* Replaces FLT_exp with FLX_exp inside a round expression. Unused. *)
Ltac FLT_replace :=
  match goal with |- context[round ?A (FLT_exp ?B ?C) ?D ?E] =>
  replace (round A (FLT_exp B C) D E) with (round A (FLX_exp C) D E)
  end .

End TwoSumWIP.
