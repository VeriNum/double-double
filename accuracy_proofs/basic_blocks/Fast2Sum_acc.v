(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Final accuracy results for the Fast2Sum algorithm in the FLT format.
   Helper lemmas live in Fast2Sum_acc_helpers.v. *)

Require Import vcfloat.VCFloat.
From Stdlib Require Import ZArith.
Require Import float_acc_lems op_defs dd_tactics.
Require Import DDConds common.
Require Export Fast2Sum_acc_helpers.
From Flocq Require Import Core.
Require Import mathcomp.ssreflect.ssreflect.

Set Bullet Behavior "Strict Subproofs".

Section FastTwoSumAcc.

Context {NANS: Nans} {t : type} {STD: is_standard t}.

Variables (a b : ftype t).
Hypothesis (Hfin_plus : is_finite (BPLUS a b) = true).
Hypothesis Hle : Rabs (FT2R b) <= Rabs (FT2R a).

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))).
Notation u   := (bpow Zaux.radix2 (- fprec t)).

Theorem FastTwoSum_accuracy:
    Rabs (FT2R (Fast2Sum_err a b))  <= /2 * ulp (FT2R a + FT2R b).
Proof.
rewrite FastTwoSum_correct; auto. unfold Fast2Sum_sum. simpl.
rewrite Rabs_minus_sym.
pose proof error_le_half_ulp
  Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) choice (FT2R a + FT2R b) as HE.
have FINs : is_finite (BPLUS a b) = true := Hfin_plus.
BPLUS_correct t a b.
by rewrite !B2R_float_of_ftype.
Qed.

End FastTwoSumAcc.

Section FastTwoSumCondAcc.

Context {NANS: Nans} {t : type} {STD: is_standard t}.

Variables (a b : ftype t).

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))).

Definition Fast2Sum_exact_guarantee : Prop :=
  Rabs (FT2R (Fast2Sum_err a b)) <= /2 * ulp (FT2R a + FT2R b) /\
  FT2R (Fast2Sum_sum a b) + FT2R (Fast2Sum_err a b) =
    FT2R a + FT2R b /\
  double_word_prop (Fast2Sum_sum a b) (Fast2Sum_err a b).

(* Accuracy of the Fast2Sum error term, from the Dekker condition |b| <= |a|.
   (Fast2Sum_exact_cond was generalized to an ulp/a=0 disjunction; this accuracy
   bound is stated directly from |b| <= |a|, which is the case the bound is
   used for.  The disjunction's other legs give correctness via the paper's
   cexp / Fast2Sum0f lemmas, handled at the DWPlusDW use sites.) *)
Corollary FastTwoSum_accuracy_from_magnitude_order :
  is_finite (BPLUS a b) = true ->
  Rabs (FT2R b) <= Rabs (FT2R a) ->
  Rabs (FT2R (Fast2Sum_err a b)) <= /2 * ulp (FT2R a + FT2R b).
Proof.
  intros Hfin_plus Hle.
  apply FastTwoSum_accuracy; assumption.
Qed.

Theorem Fast2Sum_exact_guarantee_from_magnitude_order :
  is_finite (BPLUS a b) = true ->
  Rabs (FT2R b) <= Rabs (FT2R a) ->
  Fast2Sum_exact_guarantee.
Proof.
intros Hfin Hle.
have Hacc := FastTwoSum_accuracy_from_magnitude_order Hfin Hle.
have Hcorrect := FastTwoSum_correct a b Hfin Hle.
have Hdw := Fast2Sum_is_DW a b Hfin Hle.
unfold Fast2Sum_exact_guarantee.
split; [exact Hacc |].
split; [lra | exact Hdw].
Qed.

End FastTwoSumCondAcc.
