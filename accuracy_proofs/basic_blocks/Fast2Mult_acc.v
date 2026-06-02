(* Copyright 2025 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Final accuracy results for the Fast2Mult algorithm in the FLT format.
   Helper lemmas live in Fast2Mult_acc_helpers.v. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs common dd_tactics.
Require Import DDModels.
Require Export Fast2Mult_acc_helpers.
From Flocq Require Import Pff2Flocq Core.
Require Import mathcomp.ssreflect.ssreflect.

Set Bullet Behavior "Strict Subproofs".

Section TwoMultAcc.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (@common.emin t).
Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))).
Notation u   := (bpow Zaux.radix2 (- fprec t)).

Variables (a b : ftype t).

Hypothesis (Fast2Mult_overflow_condition : is_finite (BMULT a b) = true).
Hypothesis (Fast2Mult_underflow_condition : (FT2R a * FT2R b) <> 0 ->
  bpow Zaux.radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R a * FT2R b)).

Theorem Fast2Mult_accuracy_norm:
    Rabs (FT2R (Fast2Mult_err a b))  <= /2 * ulp (FT2R a * FT2R b).
Proof.
  have FIN: (is_finite_p (Fast2Mult a b)) by apply Fast2Mult_finite_if_BMULT_finite.
  intros; rewrite Fast2MultModel_correct; auto. unfold Fast2Mult_mul. simpl.
  rewrite Rabs_minus_sym.
  pose proof error_le_half_ulp
    Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) choice (FT2R a * FT2R b) as HE.
  destruct FIN as (FINs & FINd); simpl in FINs.
  BMULT_correct t a b.
  by rewrite !B2R_float_of_ftype.
Qed.

End TwoMultAcc.

Section TwoMultCheckImplies.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))).

Variables (a b : ftype t).

(* Fast2Mult_cond is the single pre-condition shared with the verif spec
   (MulResultIsSafeForFast2Mult is definitionally Fast2Mult_cond at Tdouble). *)
Corollary Fast2Mult_accuracy_from_safety :
  Fast2Mult_cond a b ->
  Rabs (FT2R (Fast2Mult_err a b)) <= /2 * ulp (FT2R a * FT2R b).
Proof.
  intros [Hfin Huf].
  apply Fast2Mult_accuracy_norm; auto.
  intros Hne.
  destruct Huf as [H | H].
  - exfalso; apply Hne; exact H.
  - exact H.
Qed.

End TwoMultCheckImplies.
