(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Mixed accuracy and output-validity results for [DWDivFP]. *)

Require Import vcfloat.VCFloat.
Require Import common float_acc_lems op_defs DDModels DDConds DWord_defs.
Require Import DD.accuracy_proofs.dw_opps.DWDivFP_relative_acc.
Require Import DD.accuracy_proofs.dw_opps.DWDivFP_subnormal.
Require Import DD.accuracy_proofs.dw_opps.DWDivFP_finite.
From Flocq Require Import Pff2Flocq Core.
Require Import mathcomp.ssreflect.ssreflect.

Set Bullet Behavior "Strict Subproofs".

Section MixedAccuracyDWDivFP.
Context {NANS : Nans} {t : type} {STD : is_standard t}.

Notation emin := (@common.emin t).
Notation u := (bpow radix2 (-fprec t)).

Definition DWDivFP_guarantee (xh xl y : ftype t) : Prop :=
  let '(zh, zl) := DWDivFP xh xl y in
  Rabs (FT2R zh + FT2R zl - (FT2R xh + FT2R xl) / FT2R y)
    <= 3 * u^2 * Rabs ((FT2R xh + FT2R xl) / FT2R y) +
       bpow radix2 emin /\
  double_word_prop zh zl.

Local Lemma zero_div (a b : ftype t) :
  is_finite a = true -> is_finite b = true -> FT2R b <> 0 -> FT2R a = 0 ->
  is_finite (BDIV a b) = true /\ FT2R (BDIV a b) = 0.
Proof.
intros Hfa Hfb Hb Ha.
have Hf : is_finite (BDIV a b) = true.
{ apply no_overflow_div_is_finite; [exact Hfa | exact Hb |].
  rewrite Ha /Rdiv Rmult_0_l /rounded round_0 Rabs_R0.
  apply bpow_gt_0. }
split; [exact Hf |].
rewrite -(BDIV_round_correct t a b Hb Hf) Ha /Rdiv Rmult_0_l round_0 //.
Qed.

Local Lemma zero_mult (a b : ftype t) :
  is_finite a = true -> is_finite b = true -> FT2R a = 0 ->
  is_finite (BMULT a b) = true /\ FT2R (BMULT a b) = 0.
Proof.
intros Hfa Hfb Ha.
have Hf : is_finite (BMULT a b) = true.
{ apply no_overflow_mult_is_finite; [exact Hfa | exact Hfb |].
  rewrite Ha Rmult_0_l /rounded round_0 Rabs_R0. apply bpow_gt_0. }
split; [exact Hf |].
rewrite -(BMULT_round_correct t a b Hf) Ha Rmult_0_l round_0 //.
Qed.

Local Lemma zero_fma (a b c : ftype t) :
  is_finite a = true -> is_finite b = true -> is_finite c = true ->
  FT2R a = 0 -> FT2R c = 0 ->
  is_finite (BFMA a b c) = true /\ FT2R (BFMA a b c) = 0.
Proof.
intros Hfa Hfb Hfc Ha Hc.
have Hf : is_finite (BFMA a b c) = true.
{ apply no_overflow_fma_is_finite; [exact Hfa | exact Hfb | exact Hfc |].
  rewrite Ha Hc Rmult_0_l Rplus_0_l /rounded round_0 Rabs_R0.
  apply bpow_gt_0. }
split; [exact Hf |].
rewrite -(BFMA_round_correct t a b c Hf) Ha Hc Rmult_0_l Rplus_0_l round_0 //.
Qed.

Local Lemma zero_minus (a b : ftype t) :
  is_finite a = true -> is_finite b = true -> FT2R a = 0 -> FT2R b = 0 ->
  is_finite (BMINUS a b) = true /\ FT2R (BMINUS a b) = 0.
Proof.
intros Hfa Hfb Ha Hb.
have Hf : is_finite (BMINUS a b) = true.
{ apply no_overflow_minus_is_finite; [exact Hfa | exact Hfb |].
  unfold Bminus_no_overflow, rounded. rewrite Ha Hb.
  replace (0 - 0)%R with 0 by ring. rewrite round_0 Rabs_R0.
  apply bpow_gt_0. }
split; [exact Hf |].
rewrite -(BMINUS_round_correct t a b Hf) Ha Hb.
replace (0 - 0)%R with 0 by ring. rewrite round_0 //.
Qed.

Local Lemma zero_plus (a b : ftype t) :
  is_finite a = true -> is_finite b = true -> FT2R a = 0 -> FT2R b = 0 ->
  is_finite (BPLUS a b) = true /\ FT2R (BPLUS a b) = 0.
Proof.
intros Hfa Hfb Ha Hb.
have Hf : is_finite (BPLUS a b) = true.
{ apply no_overflow_sum_is_finite; [exact Hfa | exact Hfb |].
  unfold Bplus_no_overflow, rounded. rewrite Ha Hb.
  replace (0 + 0)%R with 0 by ring. rewrite round_0 Rabs_R0.
  apply bpow_gt_0. }
split; [exact Hf |].
rewrite -(BPLUS_round_correct t a b Hf) Ha Hb.
replace (0 + 0)%R with 0 by ring. rewrite round_0 //.
Qed.

Local Lemma DWDivFP_zero_finite_and_guarantee (xh xl y : ftype t) :
  is_finite xh = true -> is_finite xl = true -> is_finite y = true ->
  double_word_prop xh xl -> is_finite (BDIV xh y) = true ->
  FT2R xh = 0 ->
  is_finite_p (DWDivFP xh xl y) /\ DWDivFP_guarantee xh xl y.
Proof.
intros Hfxh Hfxl Hfy Hdw Hfq Hxh0.
have Hxl0 := double_word_0 xh xl Hdw Hxh0.
specialize (Hxl0 STD).
have Hy0 := DWDivFP_denom_nonzero_from_finite xh y Hfy Hfq.
have [Hfth Hth0] := zero_div xh y Hfxh Hfy Hy0 Hxh0.
have [Hfpih Hpih0] := zero_mult (BDIV xh y) y Hfth Hfy Hth0.
have Hfopp : is_finite (BOPP (BMULT (BDIV xh y) y)) = true
  by (apply (proj2 (BOPP_is_finite t _)); exact Hfpih).
have Hopp0 : FT2R (BOPP (BMULT (BDIV xh y) y)) = 0.
{ rewrite -(BOPP_binary t _ (or_introl Hfopp)) Hpih0 Ropp_0 //. }
have [Hfpil Hpil0] := zero_fma (BDIV xh y) y
  (BOPP (BMULT (BDIV xh y) y)) Hfth Hfy Hfopp Hth0 Hopp0.
have [Hfdh Hdh0] := zero_minus xh (BMULT (BDIV xh y) y)
  Hfxh Hfpih Hxh0 Hpih0.
have [Hfdt Hdt0] := zero_minus
  (BMINUS xh (BMULT (BDIV xh y) y))
  (Fast2Mult_err (BDIV xh y) y) Hfdh Hfpil Hdh0 Hpil0.
have [Hfd Hd0] := zero_plus
  (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
          (Fast2Mult_err (BDIV xh y) y)) xl Hfdt Hfxl Hdt0 Hxl0.
have [Hftl Htl0] := zero_div
  (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                 (Fast2Mult_err (BDIV xh y) y)) xl) y Hfd Hfy Hy0 Hd0.
have [Hfzh Hzh0] := zero_plus (BDIV xh y)
  (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                       (Fast2Mult_err (BDIV xh y) y)) xl) y)
  Hfth Hftl Hth0 Htl0.
have [Hfz Hz0] := zero_minus
  (BPLUS (BDIV xh y)
    (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                         (Fast2Mult_err (BDIV xh y) y)) xl) y))
  (BDIV xh y) Hfzh Hfth Hzh0 Hth0.
have [Hfzl Hzl0] := zero_minus
  (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                       (Fast2Mult_err (BDIV xh y) y)) xl) y)
  (BMINUS (BPLUS (BDIV xh y)
    (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                         (Fast2Mult_err (BDIV xh y) y)) xl) y))
    (BDIV xh y)) Hftl Hfz Htl0 Hz0.
split.
- unfold DWDivFP, Fast2Mult_err, Fast2Mult, Fast2Sum. cbn [fst snd].
  exact (conj Hfzh Hfzl).
- unfold DWDivFP_guarantee, DWDivFP, Fast2Mult_err, Fast2Mult, Fast2Sum.
  cbn [fst snd]. split.
  + rewrite Hzh0 Hzl0 Hxh0 Hxl0 Rplus_0_l /Rdiv Rmult_0_l
            Rminus_diag Rabs_R0.
    replace (3 * bpow radix2 (- fprec t) ^ 2 * 0 + bpow radix2 emin)
      with (bpow radix2 emin) by ring.
    apply Rlt_le, bpow_gt_0.
  + unfold double_word_prop. rewrite Hzh0 Hzl0 Rplus_0_l /rounded round_0 //.
Qed.

Local Lemma DWDivFP_finite_post_cond_from_strong_precond
    (xh xl y : ftype t) :
  DWDivFP_strong_precond xh xl y ->
  is_finite_p (DWDivFP xh xl y).
Proof.
intros Hsafe.
destruct Hsafe as
  (Hfxh & Hfxl & Hfy & Hdwp & Hfth & Hxhb & Hqub & [Hxh0 | Hxhlb]).
- exact (proj1 (DWDivFP_zero_finite_and_guarantee
    xh xl y Hfxh Hfxl Hfy Hdwp Hfth Hxh0)).
- have Hsafe : DWDivFP_strong_precond xh xl y.
  { repeat split; try assumption. right; exact Hxhlb. }
  have Hxhne : FT2R xh <> 0.
  { intro Hxh0. move: Hxhlb. rewrite Hxh0 Rabs_R0.
    intros Hbad. exact (Rlt_not_le _ _
      (bpow_gt_0 radix2 (emin + 2 * fprec t)) Hbad). }
  destruct (Rle_or_lt (bpow radix2 (emin + fprec t - 1))
                      (Rabs (FT2R xh / FT2R y))) as [Hn | Hs].
  + exact (DWDivFP_finite_post_cond_normal xh xl y Hsafe Hxhne Hn).
  + exact (DWDivFP_finite_post_cond_subnormal xh xl y Hsafe Hxhne Hs).
Qed.

Lemma DWDivFP_weak_pre_and_finite_post_cond_of_strong_precond (xh xl y : ftype t) :
  DWDivFP_strong_precond xh xl y ->
  DWDivFP_weak_pre_and_finite_post_cond xh xl y.
Proof.
intros Hsafe.
have Hfin := DWDivFP_finite_post_cond_from_strong_precond xh xl y Hsafe.
destruct Hsafe as (_ & _ & _ & Hdw & _ & _ & _ & Hxh).
unfold DWDivFP_weak_pre_and_finite_post_cond, DWDivFP_weak_precond,
       DWDivFP_finite_post_cond.
exact (conj (conj Hdw Hxh) Hfin).
Qed.

Local Lemma DWDivFP_zero_from_weak_pre_and_finite_post_cond (xh xl y : ftype t) :
  DWDivFP_weak_pre_and_finite_post_cond xh xl y ->
  FT2R xh = 0 ->
  is_finite_p (DWDivFP xh xl y) /\ DWDivFP_guarantee xh xl y.
Proof.
intros Hcond Hxh0.
have Hresult : DWDivFP_finite_post_cond xh xl y := proj2 Hcond.
have [Hfxh [Hfxl Hfy]] :=
  DWDivFP_inputs_finite_of_finite_post_cond xh xl y Hresult.
have FIN : is_finite_p (DWDivFP xh xl y) := Hresult.
specialize (FIN STD).
have Hfth : is_finite (BDIV xh y) = true := FINth xh xl y FIN.
have Hdw : double_word_prop xh xl := proj1 (proj1 Hcond).
exact (DWDivFP_zero_finite_and_guarantee
  xh xl y Hfxh Hfxl Hfy Hdw Hfth Hxh0).
Qed.

(** Whole range mixed accuracy from the mathematical input assumptions and an
    a posteriori finiteness check on the result. *)
Theorem DWDivFP_accuracy_from_weak_pre_and_finite_post_cond (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_weak_pre_and_finite_post_cond xh xl y ->
  Rabs (FT2R (fst (DWDivFP xh xl y)) + FT2R (snd (DWDivFP xh xl y))
        - (FT2R xh + FT2R xl) / FT2R y)
    <= 3 * u^2 * Rabs ((FT2R xh + FT2R xl) / FT2R y) +
       bpow radix2 emin.
Proof.
move => Hp4 Hcond.
have Hrange := proj2 (proj1 Hcond).
destruct Hrange as [Hxh0 | Hxhlb].
- have HG := proj2 (DWDivFP_zero_from_weak_pre_and_finite_post_cond xh xl y Hcond Hxh0).
  unfold DWDivFP_guarantee in HG.
  revert HG. destruct (DWDivFP xh xl y) as [zh zl].
  cbn [fst snd]. tauto.
- have Hxhne : FT2R xh <> 0.
  { intro Hxh0. move: Hxhlb. rewrite Hxh0 Rabs_R0.
    intros Hbad. exact (Rlt_not_le _ _
      (bpow_gt_0 radix2 (emin + 2 * fprec t)) Hbad). }
  have INTERNAL :=
    DWDivFP_internal_precond_of_weak_pre_and_finite_post_cond xh xl y Hcond Hxhne.
have FIN : is_finite_p (DWDivFP xh xl y) := proj2 Hcond.
specialize (FIN STD).
move: (INTERNAL) => [Hfxh [Hfxl [Hfy [Hdwp [Hfth Hfloor]]]]].
have Hyne := DWDivFP_denom_nonzero_from_finite xh y Hfy Hfth.
destruct (Rle_or_lt (bpow radix2 (emin + fprec t - 1))
                    (Rabs (FT2R xh / FT2R y))) as [Hn | Hs].
+ exact (DWDivFP_error_mixed_acc xh xl y Hp4 INTERNAL FIN Hn).
+ exact (proj1 (DWDivFP_subnormal_accuracy_and_double_word
    xh xl y Hp4 FIN Hyne Hdwp Hfloor Hs)).
Qed.

Theorem DWDivFP_double_word_from_weak_pre_and_finite_post_cond (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_weak_pre_and_finite_post_cond xh xl y ->
  double_word_prop (fst (DWDivFP xh xl y))
                   (snd (DWDivFP xh xl y)).
Proof.
move => Hp4 Hcond.
have Hrange := proj2 (proj1 Hcond).
destruct Hrange as [Hxh0 | Hxhlb].
- have HG := proj2 (DWDivFP_zero_from_weak_pre_and_finite_post_cond xh xl y Hcond Hxh0).
  unfold DWDivFP_guarantee in HG.
  revert HG. destruct (DWDivFP xh xl y) as [zh zl].
  cbn [fst snd]. tauto.
- have Hxhne : FT2R xh <> 0.
  { intro Hxh0. move: Hxhlb. rewrite Hxh0 Rabs_R0.
    intros Hbad. exact (Rlt_not_le _ _
      (bpow_gt_0 radix2 (emin + 2 * fprec t)) Hbad). }
  have INTERNAL :=
    DWDivFP_internal_precond_of_weak_pre_and_finite_post_cond xh xl y Hcond Hxhne.
have FIN : is_finite_p (DWDivFP xh xl y) := proj2 Hcond.
specialize (FIN STD).
move: (INTERNAL) => [Hfxh [Hfxl [Hfy [Hdwp [Hfth Hfloor]]]]].
have Hyne := DWDivFP_denom_nonzero_from_finite xh y Hfy Hfth.
destruct (Rle_or_lt (bpow radix2 (emin + fprec t - 1))
                    (Rabs (FT2R xh / FT2R y))) as [Hn | Hs].
+ exact (DWDivFP_double_word_from_internal_normal_quotient
    xh xl y Hp4 INTERNAL FIN Hn).
+ exact (proj2 (DWDivFP_subnormal_accuracy_and_double_word
    xh xl y Hp4 FIN Hyne Hdwp Hfloor Hs)).
Qed.

Theorem DWDivFP_guarantee_from_weak_pre_and_finite_post_cond (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_weak_pre_and_finite_post_cond xh xl y ->
  DWDivFP_guarantee xh xl y.
Proof.
move => Hp4 Hcond.
have Hacc := DWDivFP_accuracy_from_weak_pre_and_finite_post_cond xh xl y Hp4 Hcond.
have Hdw := DWDivFP_double_word_from_weak_pre_and_finite_post_cond xh xl y Hp4 Hcond.
unfold DWDivFP_guarantee.
revert Hacc Hdw.
destruct (DWDivFP xh xl y) as [zh zl].
cbn [fst snd]. intros Hacc Hdw. exact (conj Hacc Hdw).
Qed.

Theorem DWDivFP_guarantee_from_strong_precond
    (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_strong_precond xh xl y ->
  DWDivFP_guarantee xh xl y.
Proof.
move => Hp4 Hsafe.
apply DWDivFP_guarantee_from_weak_pre_and_finite_post_cond; [exact Hp4 |].
exact (DWDivFP_weak_pre_and_finite_post_cond_of_strong_precond xh xl y Hsafe).
Qed.

End MixedAccuracyDWDivFP.
