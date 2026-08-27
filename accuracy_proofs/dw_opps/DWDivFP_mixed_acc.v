(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Public whole-range mixed-accuracy interface for [DWDivFP3].

    The normal-range proof is supplied by [DWDivFP_acc]; the subnormal proof
    leg is supplied by [DWDivFP_subnormal].  This file exposes only the public
    condition ladder and the combined accuracy/closure guarantee. *)

Require Import vcfloat.VCFloat.
Require Import common DDConds.
Require Import DD.accuracy_proofs.dw_opps.DWDivFP_acc.
Require Import DD.accuracy_proofs.dw_opps.DWDivFP_subnormal.
From Flocq Require Import Pff2Flocq Core.
Require Import mathcomp.ssreflect.ssreflect.

Set Bullet Behavior "Strict Subproofs".

Section MixedAccuracyDWDivFP.
Context {NANS : Nans} {t : type} {STD : is_standard t}.

Notation emin := (@common.emin t).
Notation u := (bpow radix2 (-fprec t)).

Definition DWDivFP_mixed_guarantee (xh xl y : ftype t) : Prop :=
  let '(zh, zl) := DWDivFP3 xh xl y in
  Rabs (FT2R zh + FT2R zl - (FT2R xh + FT2R xl) / FT2R y)
    <= 3 * u^2 * Rabs ((FT2R xh + FT2R xl) / FT2R y) +
       bpow radix2 emin /\
  double_word_prop zh zl.

Local Lemma DWDivFP_normal_quotient_input_cond_of_mixed_safe_input_cond
    (xh xl y : ftype t) :
  DWDivFP_mixed_safe_input_cond xh xl y ->
  bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xh / FT2R y) ->
  DWDivFP_normal_quotient_input_cond xh xl y.
Proof.
intros (Hfxh & Hfxl & Hfy & Hdwp & Hfth & Hxhb & Hqub & Hxhlb) Hnorm.
repeat split; try assumption.
Qed.

Local Lemma DWDivFP_result_finite_from_safe_input_cond
    (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_mixed_safe_input_cond xh xl y ->
  is_finite_p (DWDivFP3 xh xl y).
Proof.
intros Hp4 Hsafe.
destruct (Rle_or_lt (bpow radix2 (emin + fprec t - 1))
                    (Rabs (FT2R xh / FT2R y))) as [Hn | Hs].
- have Hnormal :=
    DWDivFP_normal_quotient_input_cond_of_mixed_safe_input_cond
      xh xl y Hsafe Hn.
  split.
  + exact (DWDivFP3_fst_finite_acc xh xl y Hp4 Hnormal).
  + exact (DWDivFP3_snd_finite_acc xh xl y Hp4 Hnormal).
- exact (proj2 (proj2 (DWDivFP3_subnormal_leg xh xl y Hp4 Hsafe Hs))).
Qed.

Lemma DWDivFP_mixed_cond_of_safe_input_cond (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_mixed_safe_input_cond xh xl y ->
  DWDivFP_mixed_cond xh xl y.
Proof.
intros Hp4 Hsafe.
have Hfin := DWDivFP_result_finite_from_safe_input_cond xh xl y Hp4 Hsafe.
destruct Hsafe as (_ & _ & _ & Hdw & _ & _ & _ & Hxh).
unfold DWDivFP_mixed_cond, DWDivFP_mixed_input_cond,
       DWDivFP_result_finite.
exact (conj (conj Hdw Hxh) Hfin).
Qed.

(** Whole-range mixed accuracy from the mathematical input assumptions and an
    a-posteriori finiteness check on the result. *)
Theorem DWDivFP_mixed_accuracy_from_cond (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_mixed_cond xh xl y ->
  Rabs (FT2R (fst (DWDivFP3 xh xl y)) + FT2R (snd (DWDivFP3 xh xl y))
        - (FT2R xh + FT2R xl) / FT2R y)
    <= 3 * u^2 * Rabs ((FT2R xh + FT2R xl) / FT2R y) +
       bpow radix2 emin.
Proof.
move => Hp4 Hcond.
have INTERNAL := DWDivFP_internal_input_cond_of_mixed_cond xh xl y Hcond.
have FIN : is_finite_p (DWDivFP3 xh xl y) := proj2 Hcond.
specialize (FIN STD).
move: (INTERNAL) => [Hfxh [Hfxl [Hfy [Hdwp [Hfth Hxhlb]]]]].
have Hyne := DWDivFP_denom_nonzero_from_finite xh y Hfy Hfth.
destruct (Rle_or_lt (bpow radix2 (emin + fprec t - 1))
                    (Rabs (FT2R xh / FT2R y))) as [Hn | Hs].
- exact (DWDivFP3_error_mixed_acc xh xl y Hp4 INTERNAL FIN Hn).
- exact (proj1 (DWDivFP3_subnormal_accuracy_and_double_word
    xh xl y Hp4 FIN Hyne Hdwp Hxhlb Hs)).
Qed.

Theorem DWDivFP_double_word_from_cond (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_mixed_cond xh xl y ->
  double_word_prop (fst (DWDivFP3 xh xl y))
                   (snd (DWDivFP3 xh xl y)).
Proof.
move => Hp4 Hcond.
have INTERNAL := DWDivFP_internal_input_cond_of_mixed_cond xh xl y Hcond.
have FIN : is_finite_p (DWDivFP3 xh xl y) := proj2 Hcond.
specialize (FIN STD).
move: (INTERNAL) => [Hfxh [Hfxl [Hfy [Hdwp [Hfth Hxhlb]]]]].
have Hyne := DWDivFP_denom_nonzero_from_finite xh y Hfy Hfth.
destruct (Rle_or_lt (bpow radix2 (emin + fprec t - 1))
                    (Rabs (FT2R xh / FT2R y))) as [Hn | Hs].
- exact (DWDivFP_double_word_from_internal_normal_quotient
    xh xl y Hp4 INTERNAL FIN Hn).
- exact (proj2 (DWDivFP3_subnormal_accuracy_and_double_word
    xh xl y Hp4 FIN Hyne Hdwp Hxhlb Hs)).
Qed.

Theorem DWDivFP_mixed_guarantee_from_cond (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_mixed_cond xh xl y ->
  DWDivFP_mixed_guarantee xh xl y.
Proof.
move => Hp4 Hcond.
have Hacc := DWDivFP_mixed_accuracy_from_cond xh xl y Hp4 Hcond.
have Hdw := DWDivFP_double_word_from_cond xh xl y Hp4 Hcond.
unfold DWDivFP_mixed_guarantee.
revert Hacc Hdw.
destruct (DWDivFP3 xh xl y) as [zh zl].
cbn [fst snd]. intros Hacc Hdw. exact (conj Hacc Hdw).
Qed.

Theorem DWDivFP_mixed_guarantee_from_safe_input_cond
    (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_mixed_safe_input_cond xh xl y ->
  DWDivFP_mixed_guarantee xh xl y.
Proof.
move => Hp4 Hsafe.
apply DWDivFP_mixed_guarantee_from_cond; [exact Hp4 |].
exact (DWDivFP_mixed_cond_of_safe_input_cond xh xl y Hp4 Hsafe).
Qed.

End MixedAccuracyDWDivFP.
