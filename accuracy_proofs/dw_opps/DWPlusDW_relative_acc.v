(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Relative error and output validity results for [DWPlusDW].

    The operation has no separate mixed error tier: under two input
    double-word properties and finiteness of the computed pair, its relative
    error is at most [3u^2/(1-4u)] over the whole range.  The condition on
    inputs proves result finiteness and reaches the same guarantee as a
    corollary. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common.
Require Import TwoSum_acc Fast2Sum_acc.
Require Import DWPlus DDConds DWord_defs DWPlusDW_relative_acc_helpers.
Require Import DD.accuracy_proofs.dw_opps.DWPlus_finite.
From Flocq Require Import Pff2Flocq Core.
Require Import mathcomp.ssreflect.ssreflect.
Set Bullet Behavior "Strict Subproofs".

Section AccuracyDWPlusDW.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Notation u := (bpow Zaux.radix2 (- fprec t)).
Notation p := (fprec t).

Variables (xh xl yh yl : ftype t).

Let ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))).
Let emin :=  ( @common.emin t).

Let xhr := (FT2R xh).
Let xlr := (FT2R xl).
Let yhr := (FT2R yh).
Let ylr := (FT2R yl).

(* connect paper proofs to local defs *)
Local Definition DWPlusDW_FLX :=
  F2Sum.Fast2Sum p choice
           (fst
              (F2Sum.Fast2Sum p choice (TwoSum_sum p choice xhr yhr)
                 (round radix2 (FLX_exp p) (Znearest choice)
                    (TwoSum_err p choice xhr yhr + TwoSum_sum p choice xlr ylr))))
           (round radix2 (FLX_exp p) (Znearest choice)
              (TwoSum_err p choice xlr ylr +
               snd
                 (F2Sum.Fast2Sum p choice (TwoSum_sum p choice xhr yhr)
                    (round radix2 (FLX_exp p) (Znearest choice)
                       (TwoSum_err p choice xhr yhr + TwoSum_sum p choice xlr ylr)))))
.


Hypothesis Hcond: DWPlusDW_weak_pre_and_finite_post_cond xh xl yh yl.
Hypothesis Hp3 : (3 <= fprec t)%Z.

Let FIN : is_finite_p (DWPlusDW xh xl yh yl) :=
  (proj2 Hcond).

Ltac prove_finite :=
  move : FIN;
  rewrite /is_finite_p/DWPlusDW;
  rewrite /Fast2Sum/TwoSumF/snd/fst;
  move => [] ; repeat subexpr_finite => //
.

Let f0 := BPLUS xh yh.
Let x  := TwoSumF_err xl yl.
Let x1 := TwoSumF_err xh yh.
Let y1 := BPLUS xl yl.
Let f1 := BPLUS x1 y1.
Let y  := snd (Fast2Sum f0 f1).

Local Fact FIN1 : is_finite_p (Fast2Sum f0 f1).
Proof. prove_finite. Qed.

Local Fact FIN2 : is_finite_p (TwoSumF xh yh).
Proof. prove_finite. Qed.

Local Fact FIN3 : is_finite (BPLUS x1 y1) = true.
Proof. prove_finite. Qed.

Local Fact FIN4 : is_finite_p (TwoSumF xl yl).
Proof. prove_finite. Qed.

Local Fact FIN5 : is_finite (BPLUS x y) = true.
Proof. prove_finite. Qed.

(* the result of the FLT format algorithm and the FLX format algorithm are
  equal, regardless of underflow. *)
Local Lemma DWPlusDWEq_FLT :
  DWPlusDW_FLX = F2Rp (DWPlusDW xh xl yh yl).
Proof.
pose proof FIN1 as fin1.
pose proof FIN2 as fin2.
pose proof FIN3 as fin3.
pose proof FIN4 as fin4.
pose proof FIN5 as fin5.
move: FIN.
rewrite /DWPlusDW/is_finite_p/DWPlusDW_FLX.
move => [].
replace (TwoSumF xh yh) with (BPLUS xh yh, TwoSumF_err xh yh) => //.
replace (TwoSumF xl yl) with (BPLUS xl yl, TwoSumF_err xl yl) => //.
replace (Fast2Sum f0 f1) with
  (fst (Fast2Sum f0 f1), y) => //.
set (f3 := (BPLUS (TwoSumF_err xl yl) y)) => //.
pose proof FastTwoSumEq_FLT (fst (Fast2Sum f0 f1)) f3 as H1.
move: H1.
replace (Fast2Sum (fst (Fast2Sum f0 f1)) f3) with
  (fst (Fast2Sum (fst (Fast2Sum f0 f1)) f3),
   snd (Fast2Sum (fst (Fast2Sum f0 f1)) f3)) => //.
match goal with |-context [F2Sum.Fast2Sum _ _ ?a ?b] =>
  set (A := a); set (B := b)
end.
replace (F2Sum.Fast2Sum p choice A B) with
  (fst (F2Sum.Fast2Sum p choice A B),
   snd (F2Sum.Fast2Sum p choice A B)) => //.
rewrite /F2Rp.
move => H1 HFIN1 HFIN2.
rewrite -H1 => //. clear H1. subst A B.
match goal with |-context [F2Sum.Fast2Sum _ _ ?a ?b] =>
  set (A := a); set (B := b)
end.
replace (F2Sum.Fast2Sum p choice A B) with
  (fst (F2Sum.Fast2Sum p choice A B),
   snd (F2Sum.Fast2Sum p choice A B)) => //.
rewrite /F2Sum.Fast2Sum/F2SumFLX.Fast2Sum/fst/snd.
replace (Fast2Sum f0 f1) with
  (fst (Fast2Sum f0 f1), snd (Fast2Sum f0 f1)) => //.
have Hf0 : TwoSum_sum p choice xhr yhr = FT2R f0.
- subst f0. rewrite /TwoSum_sum.
  rewrite TwoSumEq_FLT /F2Rp/snd => //.
- have Hx1 : TwoSum_err p choice xhr yhr = FT2R x1.
  + subst x1. rewrite /TwoSum_err/TwoSumF_err.
    rewrite TwoSumEq_FLT /F2Rp/snd => //.
  + have Hy1 : TwoSum_sum p choice xlr ylr = FT2R y1.
    * subst y1. rewrite /TwoSum_sum.
      rewrite TwoSumEq_FLT /F2Rp/snd => //.
    * have Hf1 : round radix2 (FLX_exp p) (Znearest choice)
                   (TwoSum_err p choice xhr yhr +
                    TwoSum_sum p choice xlr ylr) = FT2R f1.
      -- subst f1.
         BPLUS_correct t x1 y1.
         rewrite -rnd_plus_FLT_FLX_eq.
         ++ f_equal. f_equal => //.
         ++ apply generic_format_FLT_FT2R.
         ++ apply generic_format_FLT_FT2R.
      -- have Heq1 : FT2R (fst (Fast2Sum f0 f1)) =
                       (fst (F2Sum.Fast2Sum p choice (FT2R f0) (FT2R f1))).
         ++ by rewrite (FastTwoSumEq_FLT f0 f1 fin1).
         ++ have HA : A = FT2R (fst (Fast2Sum f0 f1)).
            ** subst A.
               rewrite Heq1 /F2Sum.Fast2Sum/F2SumFLX.Fast2Sum/fst.
               f_equal. f_equal => //.
            ** have Hx : TwoSum_err p choice xlr ylr = FT2R x.
               { subst x. rewrite /TwoSum_err/TwoSumF_err.
                 rewrite TwoSumEq_FLT /F2Rp/snd => //. }
               have Heq2 : FT2R (snd (Fast2Sum f0 f1)) =
                             (snd (F2Sum.Fast2Sum p choice (FT2R f0) (FT2R f1))).
               --- by rewrite (FastTwoSumEq_FLT f0 f1 fin1).
               --- have Hy : snd (F2Sum.Fast2Sum p choice (TwoSum_sum p choice xhr yhr)
                               (round radix2 (FLX_exp p) (Znearest choice)
                               (TwoSum_err p choice xhr yhr + TwoSum_sum p choice xlr ylr))) = FT2R y.
                   +++ subst y.
                       rewrite Heq2.
                       rewrite /F2Sum.Fast2Sum/F2SumFLX.Fast2Sum/snd.
                       repeat f_equal => //.
                   +++ have HB : B = FT2R f3.
                       *** subst B f3.
                           replace (TwoSumF_err xl yl) with x => //.
                           BPLUS_correct t x y.
                           rewrite -rnd_plus_FLT_FLX_eq.
                           ---- f_equal. f_equal => //.
                           ---- apply generic_format_FLT_FT2R.
                           ---- apply generic_format_FLT_FT2R.
                       *** repeat f_equal => //.
Qed.


Let zh := (FT2R (fst (DWPlusDW xh xl yh yl))).
Let zl := (FT2R (snd (DWPlusDW xh xl yh yl))).

Definition relative_error_DWPlusDW :=
  Rabs ((zh + zl - (xhr + xlr + yhr + ylr)) / (xhr + xlr + yhr + ylr)).

Local Lemma relative_errorDWDW_eq :
  relative_errorDWDW p choice xhr xlr yhr ylr = relative_error_DWPlusDW.
Proof.
rewrite /relative_errorDWDW/relative_error_DWPlusDW.
f_equal. f_equal; try nra. f_equal; try nra.
unfold zh, zl.
fold DWPlusDW_FLX.
rewrite DWPlusDWEq_FLT => //.
Qed.

Theorem DWPlusDW_relative_accuracy_from_weak_pre_and_finite_post_cond :
  relative_error_DWPlusDW <= (3 * u^2) / (1 - 4 * u).
Proof.
have [DWx DWy] := proj1 Hcond.
have HDWx : DWPlus.double_word p choice xhr xlr by apply (dw_word_DWdouble xh xl xh DWx).
have HDWy : DWPlus.double_word p choice yhr ylr by apply (dw_word_DWdouble yh yl yh DWy).
pose proof @DWPlusDW_relerr_bound (fprec t)
  (fprec_gt_one t) choice eq_refl Hp3 xhr xlr yhr ylr
  HDWx HDWy.
move: H. by rewrite relative_errorDWDW_eq.
Qed.

End AccuracyDWPlusDW.

Section RelativeGuaranteeDWPlusDW.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Definition DWPlusDW_relative_guarantee
    (xh xl yh yl : ftype t) : Prop :=
  let '(zh, zl) := DWPlusDW xh xl yh yl in
  Rabs
    ((FT2R zh + FT2R zl -
        (FT2R xh + FT2R xl + FT2R yh + FT2R yl)) /
       (FT2R xh + FT2R xl + FT2R yh + FT2R yl))
    <= (3 * bpow Zaux.radix2 (- fprec t) ^ 2) /
         (1 - 4 * bpow Zaux.radix2 (- fprec t)) /\
  double_word_prop zh zl.

Theorem DWPlusDW_double_word_from_weak_pre_and_finite_post_cond
    (xh xl yh yl : ftype t) :
  (3 <= fprec t)%Z ->
  DWPlusDW_weak_pre_and_finite_post_cond xh xl yh yl ->
  double_word_prop (fst (DWPlusDW xh xl yh yl))
                   (snd (DWPlusDW xh xl yh yl)).
Proof.
intros Hp3 [[DWx DWy] Hfin].
unfold DWPlusDW_finite_post_cond in Hfin.
set sh := TwoSumF_sum xh yh.
set c := BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl).
set vh := Fast2Sum_sum sh c.
set vl := Fast2Sum_err sh c.
set w := BPLUS (TwoSumF_err xl yl) vl.
Ltac finite_from_result H :=
  move: H;
  rewrite /is_finite_p /DWPlusDW /Fast2Sum /TwoSumF /snd /fst;
  move=>[]; repeat subexpr_finite=> //.
have Fsh : is_finite sh = true by unfold sh; finite_from_result Hfin.
have Fsl : is_finite (TwoSumF_err xh yh) = true by finite_from_result Hfin.
have Fth : is_finite (TwoSumF_sum xl yl) = true by finite_from_result Hfin.
have Ftl : is_finite (TwoSumF_err xl yl) = true by finite_from_result Hfin.
have Fc : is_finite c = true by unfold c; finite_from_result Hfin.
have Fvh : is_finite vh = true by unfold vh, sh, c; finite_from_result Hfin.
have Fz : is_finite (BMINUS (BPLUS sh c) sh) = true
  by unfold sh, c; finite_from_result Hfin.
have Fvl : is_finite vl = true by unfold vl, sh, c; finite_from_result Hfin.
have Fw : is_finite w = true
  by unfold w, vl, sh, c; finite_from_result Hfin.
have Fzh : is_finite (BPLUS vh w) = true
  by unfold vh, w, vl, sh, c; finite_from_result Hfin.
have Horder :=
  @DWPlusDW_vh_w_disjunction_core
    NANS t STD xh xl yh yl DWx DWy Hp3
    Fsh Fsl Fth Ftl Fc Fvh Fz Fvl Fw.
have Hexact : Fast2Sum_exact_cond vh w := conj Fzh Horder.
change (double_word_prop (Fast2Sum_sum vh w) (Fast2Sum_err vh w)).
have Hsum := FastTwoSum_correct_from_exact_cond vh w Hexact.
unfold double_word_prop, rounded.
rewrite Hsum.
replace
  (FT2R (Fast2Sum_sum vh w) +
     (FT2R vh + FT2R w - FT2R (Fast2Sum_sum vh w)))
  with (FT2R vh + FT2R w) by ring.
symmetry.
exact (BPLUS_round_correct t vh w Fzh).
Qed.

Theorem DWPlusDW_relative_guarantee_from_weak_pre_and_finite_post_cond
    (xh xl yh yl : ftype t) :
  (3 <= fprec t)%Z ->
  DWPlusDW_weak_pre_and_finite_post_cond xh xl yh yl ->
  DWPlusDW_relative_guarantee xh xl yh yl.
Proof.
intros Hp3 Hcond.
have Hacc := @DWPlusDW_relative_accuracy_from_weak_pre_and_finite_post_cond
               NANS t STD xh xl yh yl Hcond Hp3.
have Hdw := DWPlusDW_double_word_from_weak_pre_and_finite_post_cond xh xl yh yl Hp3 Hcond.
unfold relative_error_DWPlusDW in Hacc.
unfold DWPlusDW_relative_guarantee.
revert Hacc Hdw.
destruct (DWPlusDW xh xl yh yl) as [zh zl].
cbn [fst snd]. intros Hacc Hdw. exact (conj Hacc Hdw).
Qed.

Lemma DWPlusDW_weak_pre_and_finite_post_cond_of_strong_precond
    (xh xl yh yl : ftype t) :
  DWPlusDW_strong_precond xh xl yh yl ->
  DWPlusDW_weak_pre_and_finite_post_cond xh xl yh yl.
Proof.
intros Hsafe.
have Hfin := DWPlusDW_finite_post_cond_from_strong_precond xh xl yh yl Hsafe.
specialize (Hfin NANS STD).
destruct Hsafe as (_ & _ & _ & _ & Hdx & Hdy & _ & _).
unfold DWPlusDW_weak_pre_and_finite_post_cond, DWPlusDW_weak_precond, DWPlusDW_finite_post_cond.
exact (conj (conj Hdx Hdy) Hfin).
Qed.

Theorem DWPlusDW_relative_guarantee_from_strong_precond
    (xh xl yh yl : ftype t) :
  (3 <= fprec t)%Z ->
  DWPlusDW_strong_precond xh xl yh yl ->
  DWPlusDW_relative_guarantee xh xl yh yl.
Proof.
intros Hp3 Hsafe.
apply DWPlusDW_relative_guarantee_from_weak_pre_and_finite_post_cond; [exact Hp3|].
exact (DWPlusDW_weak_pre_and_finite_post_cond_of_strong_precond xh xl yh yl Hsafe).
Qed.

End RelativeGuaranteeDWPlusDW.
