(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Relative error and output validity results for [DWPlusFP].

    The operation has no separate mixed error tier: under the mathematical
    input condition and finiteness of the computed pair, its relative error is
    at most [2u^2] over the whole range.  A condition on the inputs proves
    result finiteness and reaches the same guarantee as a corollary. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common.
Require Import DWPlus DDConds DWord_defs TwoSum_acc Fast2Sum_acc.
Require Import DWPlusFP_relative_acc_helpers.
Require Import DD.accuracy_proofs.dw_opps.DWPlus_finite.
From Flocq Require Import Pff2Flocq Core.

Require Import mathcomp.ssreflect.ssreflect.

(* for choice functions : choice = fun x0 : Z => negb (Z.even x0) *)
Set Bullet Behavior "Strict Subproofs".

Section FiniteAccuracyDWPlusFP.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Variables (xh xl y : ftype t).
Let zh := (FT2R (fst (DWPlusFP xh xl y))).
Let zl := (FT2R (snd (DWPlusFP xh xl y))).
Let xr := (FT2R xh + FT2R xl).
Let yr := (FT2R y).
Let sl := snd (TwoSumF xh y).
Let v  := BPLUS xl sl.

(* start section hyps *)
Hypothesis DWx : double_word xh xl.
Hypothesis FIN : is_finite_p (DWPlusFP xh xl y). 
Hypothesis Hp3 : (3 <= fprec t)%Z.
(* end section hyps *)

Notation u   := (bpow Zaux.radix2 (- fprec t)).
Definition relative_error_DWPlusFP := Rabs (((zh + zl) - (xr  + yr)) / (xr  + yr)).

Theorem DWPlusFP_relative_accuracy_core :
  relative_error_DWPlusFP <= 2 * u ^ 2.
Proof.
have Hf : generic_format radix2 (FLX_exp (fprec t)) (FT2R y).
{ apply ( @generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t)).
  rewrite -!B2R_float_of_ftype. 
  apply (Binary.generic_format_B2R). }  
destruct ( @DWPlusFP_correct (fprec t) (fprec_gt_one t) choice eq_refl 
  Hp3 (FT2R xh) (FT2R xl) (FT2R y) Hf) => // .
apply dw_word_DWdouble => //.
apply Rle_trans with (relative_errorDWFP (fprec t) choice (FT2R xh) (FT2R xl) (FT2R y)) => //.
apply Req_le.
rewrite /relative_error_DWPlusFP/relative_errorDWFP. 
pose proof DWPlusFP_eq xh  xl y FIN.
 rewrite /F2Rp/DWPlus.DWPlusFP in H1.
repeat f_equal.
all: by rewrite H1.
Qed.

Theorem DWPlusFP_multiplicative_accuracy_core :
  exists del, (zh + zl) = (xr + yr) * (1 + del) /\
    Rabs del <= 2 * u ^ 2.
Proof.
have Hf : generic_format radix2 (FLX_exp (fprec t)) (FT2R y).
-
apply ( @generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t)). 
rewrite -!B2R_float_of_ftype. 
eapply Binary.generic_format_B2R. 
-  
destruct ( @DWPlusFP_correct (fprec t) (fprec_gt_one t) choice eq_refl 
  Hp3 (FT2R xh) (FT2R xl) (FT2R y) Hf) => // .
apply dw_word_DWdouble => //.
destruct (Req_dec (xr + yr) 0) as [Hx0|Hx0].
+ 
exists 0; rewrite Hx0; split; [field_simplify; 
now rewrite DWPlusFP_0 | now rewrite Rabs_R0; nra]. 
+
exists (((zh + zl) - (xr  + yr)) / (xr  + yr)); split. 
* 
now field_simplify.
*
apply DWPlusFP_relative_accuracy_core.
Qed.

End FiniteAccuracyDWPlusFP.

(** Absolute form of the sharp paper multiplicative theorem. *)
Lemma DWPlusFP_error_paper_tight {NANS : Nans} {t : type}
    {STD : is_standard t} (ah al b : ftype t) :
  (3 <= fprec t)%Z -> double_word_prop ah al ->
  is_finite_p (DWPlusFP ah al b) ->
  Rabs ((FT2R (fst (DWPlusFP ah al b)) +
         FT2R (snd (DWPlusFP ah al b))) -
        (FT2R ah + FT2R al + FT2R b))
    <= 2 * bpow radix2 (-fprec t)^2 *
         Rabs (FT2R ah + FT2R al + FT2R b).
Proof.
move => Hp3 DWa FIN.
have H := @DWPlusFP_multiplicative_accuracy_core
  NANS t STD ah al b DWa FIN Hp3.
destruct H as [del [Heq Hdel]].
cbv zeta in Heq.
set q := (FT2R ah + FT2R al + FT2R b)%R.
set u := bpow radix2 (-fprec t).
fold q in Heq. fold u in Hdel.
change (Rabs ((FT2R (fst (DWPlusFP ah al b)) +
  FT2R (snd (DWPlusFP ah al b))) - q) <= 2 * u^2 * Rabs q).
rewrite Heq.
replace (q * (1 + del) - q)%R with (q * del)%R by ring.
rewrite Rabs_mult.
have Hmul := Rmult_le_compat_l (Rabs q) _ _ (Rabs_pos q) Hdel.
eapply Rle_trans; [exact Hmul |]. right; ring.
Qed.

Section RelativeInterfaceDWPlusFP.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Definition DWPlusFP_relative_guarantee (xh xl y : ftype t) : Prop :=
  let '(zh, zl) := DWPlusFP xh xl y in
  Rabs
    ((FT2R zh + FT2R zl - (FT2R xh + FT2R xl + FT2R y)) /
       (FT2R xh + FT2R xl + FT2R y))
    <= 2 * bpow Zaux.radix2 (- fprec t) ^ 2 /\
  double_word_prop zh zl.

Theorem DWPlusFP_relative_accuracy_from_weak_pre_and_finite_post_cond
    (xh xl y : ftype t) :
  (3 <= fprec t)%Z ->
  DWPlusFP_weak_pre_and_finite_post_cond xh xl y ->
  relative_error_DWPlusFP xh xl y <=
    2 * bpow Zaux.radix2 (- fprec t) ^ 2.
Proof.
intros Hp3 [Hdw Hfin].
exact (DWPlusFP_relative_accuracy_core xh xl y Hdw Hfin Hp3).
Qed.

Theorem DWPlusFP_double_word_from_weak_pre_and_finite_post_cond
    (xh xl y : ftype t) :
  (3 <= fprec t)%Z ->
  DWPlusFP_weak_pre_and_finite_post_cond xh xl y ->
  double_word_prop (fst (DWPlusFP xh xl y))
                   (snd (DWPlusFP xh xl y)).
Proof.
intros Hp3 [Hdw Hfin].
exact (DWPlusFP_relative_acc_helpers.DWPlusFP_double_word
         xh xl y Hdw Hfin Hp3).
Qed.

Theorem DWPlusFP_relative_guarantee_from_weak_pre_and_finite_post_cond
    (xh xl y : ftype t) :
  (3 <= fprec t)%Z ->
  DWPlusFP_weak_pre_and_finite_post_cond xh xl y ->
  DWPlusFP_relative_guarantee xh xl y.
Proof.
intros Hp3 Hcond.
have Hacc := DWPlusFP_relative_accuracy_from_weak_pre_and_finite_post_cond xh xl y Hp3 Hcond.
have Hdw := DWPlusFP_double_word_from_weak_pre_and_finite_post_cond xh xl y Hp3 Hcond.
unfold relative_error_DWPlusFP in Hacc.
unfold DWPlusFP_relative_guarantee.
revert Hacc Hdw.
destruct (DWPlusFP xh xl y) as [zh zl].
cbn [fst snd]. intros Hacc Hdw. exact (conj Hacc Hdw).
Qed.

Lemma DWPlusFP_weak_pre_and_finite_post_cond_of_strong_precond (xh xl y : ftype t) :
  DWPlusFP_strong_precond xh xl y ->
  DWPlusFP_weak_pre_and_finite_post_cond xh xl y.
Proof.
intros Hsafe.
have Hfin : is_finite_p (DWPlusFP xh xl y) :=
  DWPlusFP_finite_post_cond_from_strong_precond xh xl y Hsafe.
specialize (Hfin NANS STD).
destruct Hsafe as (_ & _ & _ & Hdw & _ & _).
unfold DWPlusFP_weak_pre_and_finite_post_cond, DWPlusFP_weak_precond,
       DWPlusFP_finite_post_cond.
exact (conj Hdw Hfin).
Qed.

Theorem DWPlusFP_relative_guarantee_from_strong_precond
    (xh xl y : ftype t) :
  (3 <= fprec t)%Z ->
  DWPlusFP_strong_precond xh xl y ->
  DWPlusFP_relative_guarantee xh xl y.
Proof.
intros Hp3 Hsafe.
apply DWPlusFP_relative_guarantee_from_weak_pre_and_finite_post_cond; [exact Hp3 |].
exact (DWPlusFP_weak_pre_and_finite_post_cond_of_strong_precond xh xl y Hsafe).
Qed.

End RelativeInterfaceDWPlusFP.
