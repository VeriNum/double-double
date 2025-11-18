
(* verif_float_lemmas.v: helpers lemmas for compcert floats*)
(* Copyright 2025 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.FPCompCert.

From Flocq Require Import Pff2Flocq Core.
Require Import Coq.Reals.Reals.
Require Import float_acc_lems.

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