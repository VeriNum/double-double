
(* verif_float_lemmas.v: helpers lemmas for compcert floats*)
(* Copyright 2025 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.FPCompCert.
Require Import vcfloat.VCFloat.

From Flocq Require Import Pff2Flocq Core.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import micromega.Lra.

Require Import float_acc_lems real_extras.
From Stdlib Require Import Logic.Decidable.

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

Lemma is_finite_Float_add_l : forall (a b : Floats.float),
  Binary.is_finite (fprec Tdouble) (femax Tdouble) (Float.add a b) = true ->
  Binary.is_finite (fprec Tdouble) (femax Tdouble) a = true.
Proof.
  intros a b H.
  destruct a; simpl in *; auto;
  ( cbv [Float.add Floats.Float.add Binary.Bplus Binary.B2BSN
           BinarySingleNaN.Bplus Binary.BSN2B] in H;
    destruct b; simpl in H; try discriminate;
    destruct s, s0; simpl in H; try discriminate).
Qed.

Lemma is_finite_Float_add_r : forall (a b : Floats.float),
  Binary.is_finite (fprec Tdouble) (femax Tdouble) (Float.add a b) = true ->
  Binary.is_finite (fprec Tdouble) (femax Tdouble) b = true.
Proof.
  intros a b H.
  destruct b; simpl in *; auto;
  ( cbv [Float.add Floats.Float.add Binary.Bplus Binary.B2BSN
           BinarySingleNaN.Bplus Binary.BSN2B] in H;
    destruct a; simpl in H; try discriminate;
    destruct s0; simpl in H; try discriminate;
    destruct s; simpl in H; try discriminate).
Qed.

(* dbl_max_val is the IEEE 754 double with bit pattern 0x7FEFFFFFFFFFFFFF,
   which equals DBL_MAX = pred(2^1024) = (2^53-1)*2^971. *)
Definition dbl_max_val :=
  Float.of_bits (Int64.repr 9218868437227405311).

Lemma dbl_max_val_finite :
  is_finite (ftype_of_float dbl_max_val) = true.
Proof.
  cbv [dbl_max_val is_finite Binary.is_finite Float.of_bits
       Bits.b64_of_bits Bits.binary_float_of_bits ftype_of_float]; auto.
Qed.

Lemma dbl_max_val_FT2R :
  FT2R (ftype_of_float dbl_max_val) =
  Ulp.pred Zaux.radix2 fexp (bpow Zaux.radix2 (femax Tdouble)).
Proof.
  assert (Hlhs : FT2R (ftype_of_float dbl_max_val) =
                 bpow Zaux.radix2 1024 - bpow Zaux.radix2 971).
  { assert (Haux : Bits.binary_float_of_bits_aux 52 11
                     (Int64.unsigned (Int64.repr 9218868437227405311)) =
                   Binary.F754_finite false 9007199254740991%positive 971).
    { vm_compute. reflexivity. }
    rewrite FT2R_ftype_of_float.
    cbv [dbl_max_val Float.of_bits Bits.b64_of_bits Bits.binary_float_of_bits].
    rewrite Binary.B2R_FF2B, Haux.
    cbv [Binary.FF2R cond_Zopp F2R Fnum Fexp].
    replace (bpow radix2 971) with (bpow Zaux.radix2 971) by reflexivity.
    replace (bpow Zaux.radix2 1024) with (bpow Zaux.radix2 53 * bpow Zaux.radix2 971)
      by (rewrite <- bpow_plus; reflexivity).
    rewrite <- (IZR_Zpower Zaux.radix2 53 ltac:(lia)).
    replace (Zpower (Zaux.radix2 : Z) 53) with (9007199254740991 + 1)%Z
      by (vm_compute; reflexivity).
    rewrite plus_IZR; ring. }
  assert (Hrhs : Ulp.pred Zaux.radix2 fexp (bpow Zaux.radix2 (femax Tdouble)) =
                 bpow Zaux.radix2 1024 - bpow Zaux.radix2 971).
  { change (femax Tdouble) with 1024%Z.
    rewrite Ulp.pred_bpow.
    cbv [fexp SpecFloat.fexp SpecFloat.emin fprec femax]; simpl. reflexivity. }
  lra.
Qed.

(* Float.cmp Cle (fabs b) (fabs a) = true → Rabs (FT2R b) ≤ Rabs (FT2R a) *)
Lemma Float_cmp_Cle_abs :
  forall (a b : ftype Tdouble),
  is_finite a = true ->
  is_finite b = true ->
  Float.cmp Cle
    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype b))
    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype a)) = true ->
  Rabs (FT2R b) <= Rabs (FT2R a).
Proof.
  intros a b Ha Hb H.
  cbv [Float.cmp cmp_of_comparison Float.compare] in H.
  assert (Hfa : Binary.is_finite 53 1024
    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype a)) = true).
  { rewrite Binary.is_finite_Babs; rewrite <- is_finite_Binary; exact Ha. }
  assert (Hfb : Binary.is_finite 53 1024
    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype b)) = true).
  { rewrite Binary.is_finite_Babs; rewrite <- is_finite_Binary; exact Hb. }
  rewrite Binary.Bcompare_correct in H; [| exact Hfb | exact Hfa].
  rewrite !Binary.B2R_Babs, !B2R_float_of_ftype in H.
  destruct (Rcompare (Rabs (FT2R b)) (Rabs (FT2R a))) eqn:Hcmp;
    simpl in H; try discriminate.
  - apply Req_le; apply Rcompare_Eq_inv; exact Hcmp.
  - apply Rlt_le; apply Rcompare_Lt_inv; exact Hcmp.
Qed.

(* Float.cmp Clt (fabs b) DBL_MAX = true → Rabs (FT2R b) < pred radix2 fexp Omega *)
Lemma Float_cmp_Clt_dbl_max :
  forall (b : ftype Tdouble),
  is_finite b = true ->
  Float.cmp Clt
    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype b))
    dbl_max_val = true ->
  Rabs (FT2R b) < Ulp.pred Zaux.radix2 fexp (bpow Zaux.radix2 (femax Tdouble)).
Proof.
  intros b Hb H.
  cbv [Float.cmp cmp_of_comparison Float.compare] in H.
  assert (Hfb : Binary.is_finite 53 1024
    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype b)) = true).
  { rewrite Binary.is_finite_Babs; rewrite <- is_finite_Binary; exact Hb. }
  assert (Hfd : Binary.is_finite (fprec Tdouble) (femax Tdouble) dbl_max_val = true).
  { cbv [dbl_max_val Binary.is_finite Float.of_bits Bits.b64_of_bits fprec femax
         Bits.binary_float_of_bits]; auto. }
  rewrite Binary.Bcompare_correct in H; [| exact Hfb | exact Hfd].
  rewrite Binary.B2R_Babs, B2R_float_of_ftype in H.
  assert (Heq : FT2R (ftype_of_float dbl_max_val) = Binary.B2R 53 1024 dbl_max_val).
  { rewrite FT2R_ftype_of_float; cbv [fprec femax]; reflexivity. }
  pose proof dbl_max_val_FT2R as Hft2r.
  destruct (Rcompare (Rabs (FT2R b)) (Binary.B2R 53 1024 dbl_max_val)) eqn:Hcmp;
    simpl in H; try discriminate.
  apply Rlt_le_trans with (Binary.B2R 53 1024 dbl_max_val).
  - apply Rcompare_Lt_inv; exact Hcmp.
  - lra.
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