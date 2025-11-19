
(* verif_float_lemmas.v: helpers lemmas for compcert floats*)
(* Copyright 2025 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.FPCompCert.

From Flocq Require Import Pff2Flocq Core.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Require Import float_acc_lems real_extras.
Require Import Coq.Logic.Decidable.

Lemma Float_cmp_Ceq_zero_finite:
  forall a,
    Float.cmp Ceq a (Float.of_bits (Int64.repr 0)) = true ->
    is_finite (ftype_of_float a) = true.
Proof.
    intros; destruct a; simpl in *; auto;
    destruct s; 
    cbv [Float.of_bits Bits.b64_of_bits Bits.binary_float_of_bits Float.cmp] in H;
    simpl in H; auto. 
Qed.

Lemma Float_cmp_Ceq_zero_mul_FT2R:
  forall x y,
    Float.cmp Ceq (Float.mul x y) (Float.of_bits (Int64.repr 0)) = true -> 
    FT2R (ftype_of_float (Float.mul x y)) = 0%R.
Proof.
    intros. apply Rcompare_Eq_inv. 
    pose proof Float_cmp_Ceq_zero_finite (Float.mul x y) H. 
    cbv [Float.cmp cmp_of_comparison Float.compare Float.of_bits] in H.
    rewrite Binary.Bcompare_correct in H; simpl in H; auto.
    rewrite FT2R_ftype_of_float; simpl.
    cbv [fprec]. simpl.
    destruct (Rcompare _ _); auto; discriminate.
Qed.

Lemma Float_cmp_Ceq_zero_mul_FT2R_l:
  forall x y,
  Float.cmp Ceq x (Float.of_bits (Int64.repr 0)) = true -> 
  (FT2R (ftype_of_float x) * y)%R = 0.
Proof.
  intros.
    pose proof Float_cmp_Ceq_zero_finite x H. 
  cbv [Float.cmp cmp_of_comparison Float.compare Float.of_bits] in H.
  rewrite Binary.Bcompare_correct in H; simpl in H; auto.
  rewrite FT2R_ftype_of_float; simpl.
  cbv [fprec]. simpl.
  rewrite <- (Rmult_0_l y); f_equal.
  destruct x; simpl; auto.
  apply Rcompare_Eq_inv.
  destruct (Rcompare _ _); auto; try discriminate.
Qed.

Lemma Float_cmp_Ceq_zero_mul_FT2R_r:
  forall x y,
  Float.cmp Ceq y (Float.of_bits (Int64.repr 0)) = true -> 
  ( x * FT2R (ftype_of_float y))%R = 0.
Proof.
  intros.
  pose proof Float_cmp_Ceq_zero_finite y H. 
  cbv [Float.cmp cmp_of_comparison Float.compare Float.of_bits] in H.
  rewrite Binary.Bcompare_correct in H; simpl in H; auto.
  rewrite FT2R_ftype_of_float; simpl.
  cbv [fprec]. simpl.
  rewrite <- (Rmult_0_r x); f_equal.
  destruct y; simpl; auto.
  apply Rcompare_Eq_inv.
  destruct (Rcompare _ _); auto; try discriminate.
Qed.

Lemma Float_cmp_Ceq_eqb : 
forall x y,
 Float.cmp Ceq x y = false -> 
 eqb (Float.cmp Ceq x y) true = false.
Proof.
  intros. destruct ((Float.cmp Ceq x y)); auto.
Qed.

Notation emin := (SpecFloat.emin (fprec Tdouble) (femax Tdouble)).
Notation fexp :=
  (SpecFloat.fexp (fprec Tdouble) (femax Tdouble)).

Lemma no_underflow_real_from_round_mul :
  forall (x y: ftype Tdouble),
  bpow Zaux.radix2 (emin + 2 * fprec Tdouble - 1) < 
    Rabs ((round radix2  fexp ZnearestE) (FT2R x * FT2R y))->
  Rlt_bool (bpow Zaux.radix2 (emin + 2 * fprec Tdouble - 1))   
    (Rabs (FT2R x * FT2R y)%R) = true.
Proof.
  intros x y H.
  set (bexp := (bpow Zaux.radix2 (emin + 2 * fprec Tdouble - 1))) in *.
  set (rnd_mult := round radix2 fexp ZnearestE (FT2R x * FT2R y)) in *.
  destruct (Rlt_dec bexp (Rabs (FT2R x * FT2R y)%R)) 
    as [Hlt | Hle]; auto. 
  apply Rlt_bool_true; nra.
  exfalso; apply Rnot_lt_le in Hle.
  apply (round_le radix2 fexp (Znearest common.choice)) in Hle.
  rewrite round_NE_abs in Hle; [ |   ].
  replace (round _ _ _ bexp) with bexp in Hle.
  unfold rnd_mult in H; nra.
  rewrite round_generic; auto. 
  apply valid_rnd_N.
  apply generic_format_bpow; cbv; exact finish_compute_le.
  apply FLT_exp_valid.
  cbv; auto.
Qed.

Lemma Float_cmp_Cle_mul : 
forall x y A B (Hfin1: is_finite (ftype_of_float (Float.mul x y)) = true)
  (Hfin2: is_finite B = true) (Heq: A = FT2R B),
  Vint (if Rlt_bool A (Rabs ((round radix2 fexp ZnearestE) 
    (FT2R (ftype_of_float x) * FT2R (ftype_of_float y)))) then Int.one else Int.zero) =
  bool2val (Float.cmp Clt (float_of_ftype B) (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (Float.mul x y))).
Proof.
  intros.
  cbv [Float.cmp cmp_of_comparison Float.compare Float.of_bits bool2val].
  rewrite Binary.Bcompare_correct; simpl; auto.
  rewrite Float_mul_rewrite. rewrite Binary.B2R_Babs. 
  rewrite <- (FT2R_ftype_of_float (x * y)%F64); simpl.
  change (Binary.Bmult _ _ _ _ _ _ _ _) with (BMULT (ftype_of_float x) (ftype_of_float y)).
  rewrite <- BMULT_round_correct; auto.
  set (fabs:= (Rabs (round _ _ _ _ ))).
  pose proof Rcompare_Lt_inv (Binary.B2R 53 1024 B) fabs.
  pose proof Rcompare_Lt (Binary.B2R 53 1024 B) fabs.
  pose proof Rlt_bool_true (Binary.B2R 53 1024 B) fabs.
  pose proof Rlt_bool_to_Rlt (Binary.B2R 53 1024 B) fabs.
  replace (Binary.B2R 53 1024 B) with A in *.
  destruct Rcompare; destruct Rlt_bool; simpl; auto;
  try assert (Eq = Lt) by (apply H0; apply H2; auto); try discriminate;
  try assert (Gt = Lt) by (apply H0; apply H2; auto); try discriminate;
  try assert (false = true) by (apply H1; apply H; auto); try discriminate.
  rewrite Binary.is_finite_Babs; auto.
Qed.   