(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Final accuracy results for the TwoSum algorithm in the FLT format.
   Helper lemmas live in TwoSum_acc_helpers.v. *)

Require Import vcfloat.VCFloat.
From Stdlib Require Import ZArith.
Require Import float_acc_lems op_defs dd_tactics.
Require Import DDConds common.
Require Export TwoSum_acc_helpers.
From Flocq Require Import Core.
Require Import mathcomp.ssreflect.ssreflect.

Set Bullet Behavior "Strict Subproofs".

Section TwoSumAcc.

Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation BPLUS  := (@FPCore.BPLUS  NANS t STD).
Notation ulp    := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))).

Variables (a b : ftype t).
Hypothesis (FIN : is_finite_p (TwoSumF a b)).

Theorem TwoSum_accuracy :
    Rabs (FT2R (TwoSumF_err a b))  <= /2 * ulp (FT2R a + FT2R b).
Proof.
have FINs : is_finite (BPLUS a b) = true := proj1 FIN.
rewrite TwoSumF_correct; auto. unfold TwoSumF_sum. simpl.
rewrite Rabs_minus_sym.
pose proof error_le_half_ulp
  Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) choice (FT2R a + FT2R b) as HE.
BPLUS_correct t a b.
rewrite !B2R_float_of_ftype; auto.
Qed.

End TwoSumAcc.

Section TwoSumCondAcc.

Context {NANS: Nans} {t : type} {STD: is_standard t}.

Variables (a b : ftype t).

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))).

Definition TwoSum_exact_guarantee : Prop :=
  Rabs (FT2R (TwoSumF_err a b)) <= /2 * ulp (FT2R a + FT2R b) /\
  FT2R (TwoSumF_sum a b) + FT2R (TwoSumF_err a b) =
    FT2R a + FT2R b /\
  double_word_prop (TwoSumF_sum a b) (TwoSumF_err a b).

Corollary TwoSum_accuracy_from_exact_cond :
  TwoSum_exact_cond a b ->
  Rabs (FT2R (TwoSumF_err a b)) <= /2 * ulp (FT2R a + FT2R b).
Proof.
  intros [Hfin_plus [Hfin_minus HbFmax]].
  apply TwoSum_accuracy.
  split; [exact Hfin_plus | apply is_finite_TwoSum; assumption].
Qed.

Theorem TwoSum_exact_guarantee_from_cond :
  TwoSum_exact_cond a b ->
  TwoSum_exact_guarantee.
Proof.
intros Hcond.
have Hacc := TwoSum_accuracy_from_exact_cond Hcond.
destruct Hcond as [Hfin_plus [Hfin_minus HbFmax]].
have Hfin : is_finite_p (TwoSumF a b).
{ split; [exact Hfin_plus |].
  apply is_finite_TwoSum; assumption. }
have Hcorrect := TwoSumF_correct a b Hfin.
have Hdw := TwoSum_is_DW a b Hfin.
unfold TwoSum_exact_guarantee.
split; [exact Hacc |].
split; [lra | exact Hdw].
Qed.

End TwoSumCondAcc.
