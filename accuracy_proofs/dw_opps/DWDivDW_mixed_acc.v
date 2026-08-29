(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Public whole range mixed error and output validity API for [DWDivDW].

    The shared reciprocal analysis and normal range relative theorem are in
    [DWDivDW_relative_acc]. *)

Require Import vcfloat.VCFloat.
Require Import common op_defs DDConds DWord_defs.
Require Import DWMulDW_mixed_acc DWDivDW_relative_acc.
From Flocq Require Import Core.
Require Import mathcomp.ssreflect.ssreflect.

Set Bullet Behavior "Strict Subproofs".

Section MixedGuaranteeDWDivDW.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Variables (xh xl yh yl : ftype t).
Notation u := (bpow radix2 (-fprec t)).
Let X := FT2R xh + FT2R xl.
Let Q := X / (FT2R yh + FT2R yl).
Let zr := FT2R (fst (DWDivDW xh xl yh yl)) +
          FT2R (snd (DWDivDW xh xl yh yl)).

(** Compact error name used by the VST funspec. *)
Definition absolute_error_DWDivDW : R := Rabs (zr - Q).

(** The whole range mixed error bound and output validity, destructuring the
    result once to keep the VST funspec small. *)
Definition DWDivDW_guarantee : Prop :=
  let (zh, zl) := DWDivDW xh xl yh yl in
  (Rabs (FT2R zh + FT2R zl - Q) <=
     98/10*u^2*Rabs Q + 5/2*bpow radix2 (@common.emin t))%R /\
  double_word_prop zh zl.

Theorem DWDivDW_accuracy_from_weak_pre_and_finite_post_cond :
  (14 <= fprec t)%Z ->
  DWDivDW_weak_pre_and_finite_post_cond xh xl yh yl ->
  absolute_error_DWDivDW <=
    98/10*u^2*Rabs Q + 5/2*bpow radix2 (@common.emin t).
Proof.
move => Hp14 Hcond.
unfold absolute_error_DWDivDW.
exact (DWDivDW_error_mixed_arms_acc xh xl yh yl Hp14 Hcond).
Qed.

Theorem DWDivDW_double_word_from_weak_pre_and_finite_post_cond :
  (14 <= fprec t)%Z ->
  DWDivDW_weak_pre_and_finite_post_cond xh xl yh yl ->
  double_word_prop (fst (DWDivDW xh xl yh yl))
                   (snd (DWDivDW xh xl yh yl)).
Proof.
move => Hp14 Hcond.
have COND := DWDivDW_internal_precond_of_weak_pre_and_finite_post_cond xh xl yh yl Hcond.
have FIN : is_finite_p (DWDivDW xh xl yh yl) := proj2 Hcond.
specialize (FIN STD).
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
set rl := BOPP (BMULT yl th).
set e := Fast2Sum rh rl.
set d := DWTimesFP (fst e) (snd e) th.
set m := DWPlusFP (fst d) (snd d) th.
set mh := fst m; set ml := snd m.
have FINmul : is_finite_p (DWTimesDW xh xl mh ml).
{ fold th rh rl e d m mh ml in FIN. exact FIN. }
have Hrec := DWDivDW_reciprocal_relative_from_cond
  xh xl yh yl Hp14 COND.
specialize (Hrec NANS STD).
fold th rh rl e d m in Hrec.
destruct Hrec as [_ [_ [_ [DWm _]]]].
fold m mh ml in DWm.
move: (COND) => [_ [_ [_ [_ [DWx _]]]]].
exact (DWMulDW_mixed_acc.DWTimesDW_double_word_from_weak_pre_and_finite_post_cond xh xl mh ml
  ltac:(lia) (conj (conj DWx DWm) FINmul)).
Qed.

Theorem DWDivDW_guarantee_from_weak_pre_and_finite_post_cond :
  (14 <= fprec t)%Z ->
  DWDivDW_weak_pre_and_finite_post_cond xh xl yh yl ->
  DWDivDW_guarantee.
Proof.
move => Hp14 Hcond.
have Hacc := DWDivDW_accuracy_from_weak_pre_and_finite_post_cond Hp14 Hcond.
have Hdw := DWDivDW_double_word_from_weak_pre_and_finite_post_cond Hp14 Hcond.
unfold absolute_error_DWDivDW in Hacc.
unfold DWDivDW_guarantee.
revert Hacc Hdw.
destruct (DWDivDW xh xl yh yl) as [zh zl].
cbn [fst snd]. intros Hacc Hdw. exact (conj Hacc Hdw).
Qed.

Lemma DWDivDW_weak_precond_of_strong_precond :
  DDConds.DWDivDW_strong_precond xh xl yh yl ->
  DWDivDW_weak_precond xh xl yh yl.
Proof.
move => Hsafe.
destruct Hsafe as (_ & _ & _ & _ & Hdx & Hdy & Hyhi & Hylo & _).
unfold DWDivDW_weak_precond.
exact (conj Hdx (conj Hdy (conj Hyhi Hylo))).
Qed.

Theorem DWDivDW_guarantee_from_strong_precond :
  (14 <= fprec t)%Z ->
  DDConds.DWDivDW_strong_precond xh xl yh yl ->
  DWDivDW_guarantee.
Proof.
move => Hp14 Hsafe.
apply DWDivDW_guarantee_from_weak_pre_and_finite_post_cond; [exact Hp14 |].
split.
- exact (DWDivDW_weak_precond_of_strong_precond Hsafe).
- unfold DWDivDW_finite_post_cond.
  exact (DWDivDW_finite_from_cond xh xl yh yl Hp14 Hsafe).
Qed.

End MixedGuaranteeDWDivDW.
