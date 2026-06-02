(* Copyright 2025 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Helper lemmas for the accuracy and correctness proofs of the
   Fast2Mult algorithm in the FLT format.

   Layout:
     1. Finiteness (TwoMultFinite section)
     2. Correctness & double-word property (TwoMultCorrect section)

   The two sections are kept separate because they take different
   hypothesis blocks. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs common dd_tactics.
Require Import DDModels.
From Flocq Require Import Pff2Flocq Core.

Require Import mathcomp.ssreflect.ssreflect.

Set Bullet Behavior "Strict Subproofs".

(* ===================================================================== *)
(* 1. Finiteness                                                           *)
(* ===================================================================== *)

Section TwoMultFinite.
Context {NANS: Nans} {t : type} {STD: is_standard t}.
Notation emin := (@common.emin t).

Variables (a b : ftype t).

Hypothesis Fast2Mult_underflow_condition :
FT2R a * FT2R b <> 0 -> bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R a * FT2R b).

Lemma Fast2Mult_underflow_condition_imples:
  FT2R a * FT2R b <> 0 ->
  bpow radix2 (SpecFloat.emin (fprec t) (femax t) + fprec t - 1) <= Rabs (FT2R a * FT2R b).
Proof.
  move => H0.
  eapply Rle_trans; [ | apply Fast2Mult_underflow_condition] => //.
  apply bpow_le. cbv [emin SpecFloat.emin].
  pose proof femax_lb t; pose proof fprec_gt_1 t; lia.
Qed.

Lemma Fast2Mult_finite_if_BMULT_finite:
  is_finite (BMULT a b) = true -> is_finite_p (Fast2Mult a b).
Proof.
  move => Hfin.
  rewrite /is_finite_p/Fast2Mult/fst/snd; split; auto.
  set (res :=
  Binary.B2R _ _ (float_of_ftype a) * Binary.B2R _ _ (float_of_ftype b) +
  Binary.B2R _ _ (float_of_ftype (BOPP (BMULT a b))) ).
  assert ((Rabs (round radix2 (FLT_exp emin (fprec t))
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) res)) <
  (bpow radix2 (femax t))).
  subst res.
  rewrite !B2R_float_of_ftype.
  rewrite -BOPP_binary; [ | right; auto].
  rewrite Rplus_opp -BMULT_round_correct => //.
  destruct (Req_dec (Rabs (FT2R a * FT2R b)) 0) as [H0 | H0].
  -
  apply Rabs_eq_R0 in H0. rewrite H0 round_0 Rminus_diag round_0 Rabs_R0.
  apply bpow_gt_0.
  -
  eapply Rle_lt_trans.
  rewrite <- round_NE_abs; FLT_basics.
  rewrite round_generic.
  rewrite Rabs_minus_sym.
  apply error_le_ulp_round; FLT_basics.
  rewrite Rabs_minus_sym.
  apply generic_format_abs.
  apply Mult_error.mult_error_FLT; FLT_basics; auto.
  rewrite <- ulp_abs.
  eapply Rle_lt_trans.
  apply Rabs_pos_lt in H0. rewrite Rabs_Rabsolu in H0; auto.
  apply ulp_le_id.
  rewrite round_FLT_FLX. rewrite -round_NE_abs. apply gt_0_round_gt_0_FLX; FLT_basics; auto.
  apply Fast2Mult_underflow_condition_imples.
  apply Rabs_lt_pos; auto.
  rewrite -round_NE_abs.
  apply generic_format_round; FLT_basics.
  eapply is_finite_BMULT_no_overflow; auto.
  -
  destruct (BMULT_finite_e _ _ _ Hfin) as [Hfa  Hfb].
  destruct (BOPP_is_finite t (BMULT a b)) as [_ Hfo].
  specialize (Hfo Hfin).
  rewrite !is_finite_Binary in Hfa Hfb Hfo.
  pose proof (Binary.Bfma_correct  (fprec t) (femax t)
  (fprec_gt_0 t) (fprec_lt_femax t)
  (fma_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE
  (float_of_ftype a) (float_of_ftype b)
  (float_of_ftype (BOPP (BMULT a b))) Hfa Hfb Hfo).
  apply Rlt_bool_true in H.
  cbv zeta in H0.
  fold res in H0.
  rewrite H in H0.
  destruct H0 as [_ [Hfin2 _]].
  rewrite is_finite_Binary /BFMA float_of_ftype_of_float; auto.
Qed.

End TwoMultFinite.

(* ===================================================================== *)
(* 2. Correctness & double-word property                                   *)
(* ===================================================================== *)

Section TwoMultCorrect.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (@common.emin t).

Variables (a b : ftype t).

Hypothesis (Fast2Mult_overflow_condition : is_finite (BMULT a b) = true).
Hypothesis (Fast2Mult_underflow_condition : (FT2R a * FT2R b) <> 0 ->
  bpow Zaux.radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R a * FT2R b)).

Lemma Fast2MultModel_correct:
  FT2R (Fast2Mult_err a b) =  FT2R a * FT2R b - FT2R (Fast2Mult_mul a b).
Proof.
  have FIN: (is_finite_p (Fast2Mult a b)) by apply Fast2Mult_finite_if_BMULT_finite.
  set (m := BMULT a b).
  set (p := BFMA a b (BOPP m)).
  destruct FIN as (FINm & FINp).
  unfold Fast2Mult_mul, Fast2Mult_err, fst, snd in *; simpl in *.
  fold m in FINp. fold m.
  BFMA_correct t a b (BOPP m).
  unfold m.
  rewrite -!B2R_float_of_ftype.
  rewrite /BOPP float_of_ftype_of_float.
  rewrite Binary.B2R_Bopp !B2R_float_of_ftype.
  rewrite round_generic => //.
  set (x1:= FT2R a * FT2R b).
  set (x2:= FT2R (BMULT a b)).
  replace (x1 + - x2) with ( - (x2 - x1)) by nra.
  apply Generic_fmt.generic_format_opp.
  subst x1 x2.
  BMULT_correct t a b; rewrite !B2R_float_of_ftype.
  apply (Mult_error.mult_error_FLT (Zaux.radix2) emin (fprec t)
    (Generic_fmt.Znearest choice) (FT2R a) (FT2R b)) => //;
  apply generic_format_FLT_FT2R.
Qed.


Lemma TwoMult_is_DW:
  double_word (Fast2Mult_mul a b) (Fast2Mult_err a b).
Proof.
  have FIN: (is_finite_p (Fast2Mult a b)) by apply Fast2Mult_finite_if_BMULT_finite.
  rewrite /double_word Fast2MultModel_correct // /TwoSumF_sum /= /common.rounded.
  destruct FIN as (FINm & FINp).
  unfold Fast2Mult_mul, Fast2Mult_err, Fast2Mult, fst, snd in *.
    BMULT_correct t a b.
  by rewrite -!B2R_float_of_ftype.
Qed.

End TwoMultCorrect.
