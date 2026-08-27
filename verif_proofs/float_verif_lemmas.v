
(* float_verif_lemmas.v: Helper lemmas connecting CompCert floating-point
   operations and comparisons with VCFloat/Flocq real semantics.
   Includes finiteness, rounding bound, and concrete IEEE-754 threshold
   results used by the VST verification proofs. *)
   (* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.FPCompCert.
Require Import vcfloat.VCFloat.

From Flocq Require Import Pff2Flocq Core.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import micromega.Lra.

Require Import float_acc_lems real_extras common.
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

(* Upper bound mirror of no_underflow_real_from_round_mul: a STRICT rounded product
   bound transfers to the exact product.  |RN(x*y)| < 2^1023 forces |x*y| < 2^1023
   = /2 * Omega.  Sound only for the strict inequality: 2^1023 is a representable
   power of two and RN is monotone/idempotent on it, so |x*y| >= 2^1023 would give
   |RN(x*y)| >= 2^1023.  Used to lift the C guard `fabs(x->s*y) < ldexp(1.0,1023)`
   into the cond's product magnitude bound Rabs (FT2R xh * FT2R y) <= /2 * Omega. *)
Lemma no_overflow_real_from_round_mul :
  forall (x y: ftype Tdouble),
  Rabs ((round radix2 fexp ZnearestE) (FT2R x * FT2R y)) <
    bpow Zaux.radix2 1023 ->
  Rabs (FT2R x * FT2R y) <= /2 * bpow Zaux.radix2 (femax Tdouble).
Proof.
  intros x y H.
  set (B := bpow Zaux.radix2 1023) in *.
  set (rnd_mult := round radix2 fexp ZnearestE (FT2R x * FT2R y)) in *.
  assert (HB : /2 * bpow Zaux.radix2 (femax Tdouble) = B).
  { unfold B. change (femax Tdouble) with 1024%Z.
    replace 1024%Z with (1 + 1023)%Z by lia.
    rewrite bpow_plus. simpl. lra. }
  rewrite HB.
  destruct (Rle_dec (Rabs (FT2R x * FT2R y)) B) as [Hle | Hgt]; auto.
  exfalso. apply Rnot_le_lt in Hgt.
  apply Rlt_le in Hgt.
  apply (round_le radix2 fexp (Znearest common.choice)) in Hgt.
  rewrite round_NE_abs in Hgt; [ | apply FLT_exp_valid; cbv; auto].
  replace (round radix2 fexp (Znearest common.choice) B) with B in Hgt.
  2:{ rewrite round_generic; auto.
      apply valid_rnd_N.
      apply generic_format_bpow; cbv; exact finish_compute_le. }
  unfold rnd_mult in H. unfold B in H, Hgt. lra.
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

(* q_omega_val: IEEE-754 double for 2^1022 = Omega/4 in Tdouble.
   Mirrors ldexp_val's construction: scale 1.0 (bit pattern 0x3FF0000000000000)
   by 2^1022 via Bldexp. Used by Float_cmp_Cle_bpow1022 to lift the C runtime
   check `fabs(a) <= ldexp(1.0, 1022)` into the abstract bound
   Rabs (FT2R a) <= /4 * Omega. *)
Definition q_omega_val :=
  Binary.Bldexp (fprec Tdouble) 1024 (fprec_gt_0 Tdouble)
    (fprec_lt_femax Tdouble) BinarySingleNaN.mode_NE
    (Float.of_bits (Int64.repr 4607182418800017408)) 1022.

Lemma q_omega_val_finite : is_finite (ftype_of_float q_omega_val) = true.
Proof.
  cbv [q_omega_val Binary.is_finite Float.of_bits
       Bits.b64_of_bits Binary.Bldexp Binary.lift Binary.Bmult]; auto.
Qed.

Lemma q_omega_val_FT2R :
  FT2R (ftype_of_float q_omega_val) = bpow Zaux.radix2 1022.
Proof.
  cbv [q_omega_val ftype_of_float Float.of_bits
       Bits.b64_of_bits Binary.Bldexp]; simpl.
  cbv [Binary.lift Binary.Bmult]; simpl.
  cbv [BinarySingleNaN.binary_round_correct BinarySingleNaN.Bmult_correct_aux];
    simpl.
  cbv [FT2R]; simpl.
  cbv [F2R]; simpl.
  nra.
Qed.

(* Float.cmp Cle (fabs b) q_omega_val = true → Rabs (FT2R b) <= /4 * Omega *)
Lemma Float_cmp_Cle_bpow1022 :
  forall (b : ftype Tdouble),
  is_finite b = true ->
  Float.cmp Cle
    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype b))
    q_omega_val = true ->
  Rabs (FT2R b) <= /4 * bpow Zaux.radix2 (femax Tdouble).
Proof.
  intros b Hb H.
  cbv [Float.cmp cmp_of_comparison Float.compare] in H.
  assert (Hfb : Binary.is_finite 53 1024
    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype b)) = true).
  { rewrite Binary.is_finite_Babs; rewrite <- is_finite_Binary; exact Hb. }
  assert (Hfq : Binary.is_finite (fprec Tdouble) (femax Tdouble) q_omega_val = true).
  { generalize q_omega_val_finite. rewrite is_finite_Binary, float_of_ftype_of_float;
    cbv [fprec femax]; auto. }
  rewrite Binary.Bcompare_correct in H; [| exact Hfb | exact Hfq].
  rewrite Binary.B2R_Babs, B2R_float_of_ftype in H.
  assert (Heq : FT2R (ftype_of_float q_omega_val) = Binary.B2R 53 1024 q_omega_val).
  { rewrite FT2R_ftype_of_float; cbv [fprec femax]; reflexivity. }
  pose proof q_omega_val_FT2R as Hft2r.
  assert (Hqval : Binary.B2R 53 1024 q_omega_val = bpow Zaux.radix2 1022) by lra.
  assert (Hqomega : bpow Zaux.radix2 1022 = /4 * bpow Zaux.radix2 (femax Tdouble)).
  { change (femax Tdouble) with 1024%Z.
    replace 1024%Z with (2 + 1022)%Z by lia.
    rewrite bpow_plus. simpl. lra. }
  destruct (Rcompare (Rabs (FT2R b)) (Binary.B2R 53 1024 q_omega_val)) eqn:Hcmp;
    simpl in H; try discriminate.
  - apply Req_le.
    apply Rcompare_Eq_inv in Hcmp. lra.
  - apply Rlt_le.
    apply Rcompare_Lt_inv in Hcmp. lra.
Qed.

(* q_sqrt_val: IEEE-754 double for 2^(femax/2 - 1) = 2^511 in Tdouble, the
   *factor* (square root scale) bound used by DWTimesFP_relative_error_input_cond / DWTimesDW_exact_leading_product_input_cond.
   Same construction as q_omega_val but scaling 1.0 by 2^511 instead of 2^1022.
   Used by Float_cmp_Cle_bpow511 to lift the C runtime check
   `fabs(a) <= ldexp(1.0, 511)` into the abstract bound
   Rabs (FT2R a) <= bpow radix2 (femax/2 - 1). *)
Definition q_sqrt_val :=
  Binary.Bldexp (fprec Tdouble) 1024 (fprec_gt_0 Tdouble)
    (fprec_lt_femax Tdouble) BinarySingleNaN.mode_NE
    (Float.of_bits (Int64.repr 4607182418800017408)) 511.

Lemma q_sqrt_val_finite : is_finite (ftype_of_float q_sqrt_val) = true.
Proof.
  cbv [q_sqrt_val Binary.is_finite Float.of_bits
       Bits.b64_of_bits Binary.Bldexp Binary.lift Binary.Bmult]; auto.
Qed.

Lemma q_sqrt_val_FT2R :
  FT2R (ftype_of_float q_sqrt_val) = bpow Zaux.radix2 511.
Proof.
  cbv [q_sqrt_val ftype_of_float Float.of_bits
       Bits.b64_of_bits Binary.Bldexp]; simpl.
  cbv [Binary.lift Binary.Bmult]; simpl.
  cbv [BinarySingleNaN.binary_round_correct BinarySingleNaN.Bmult_correct_aux];
    simpl.
  cbv [FT2R]; simpl.
  cbv [F2R]; simpl.
  nra.
Qed.

(* Float.cmp Cle (fabs b) q_sqrt_val = true → Rabs (FT2R b) <= 2^(femax/2 - 1).
   The factor bound analog of Float_cmp_Cle_bpow1022 (no /4 factor: the bound
   is bpow (femax/2 - 1) itself, matching DWTimesFP_relative_error_input_cond directly). *)
Lemma Float_cmp_Cle_bpow511 :
  forall (b : ftype Tdouble),
  is_finite b = true ->
  Float.cmp Cle
    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype b))
    q_sqrt_val = true ->
  Rabs (FT2R b) <= bpow Zaux.radix2 (femax Tdouble / 2 - 1).
Proof.
  intros b Hb H.
  cbv [Float.cmp cmp_of_comparison Float.compare] in H.
  assert (Hfb : Binary.is_finite 53 1024
    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype b)) = true).
  { rewrite Binary.is_finite_Babs; rewrite <- is_finite_Binary; exact Hb. }
  assert (Hfq : Binary.is_finite (fprec Tdouble) (femax Tdouble) q_sqrt_val = true).
  { generalize q_sqrt_val_finite. rewrite is_finite_Binary, float_of_ftype_of_float;
    cbv [fprec femax]; auto. }
  rewrite Binary.Bcompare_correct in H; [| exact Hfb | exact Hfq].
  rewrite Binary.B2R_Babs, B2R_float_of_ftype in H.
  pose proof q_sqrt_val_FT2R as Hft2r.
  assert (Hqval : Binary.B2R 53 1024 q_sqrt_val = bpow Zaux.radix2 511).
  { rewrite <- Hft2r, FT2R_ftype_of_float; cbv [fprec femax]; reflexivity. }
  assert (Hfe : (femax Tdouble / 2 - 1)%Z = 511%Z) by (cbv [femax Tdouble]; reflexivity).
  rewrite Hfe.
  destruct (Rcompare (Rabs (FT2R b)) (Binary.B2R 53 1024 q_sqrt_val)) eqn:Hcmp;
    simpl in H; try discriminate.
  - apply Req_le. apply Rcompare_Eq_inv in Hcmp. lra.
  - apply Rlt_le. apply Rcompare_Lt_inv in Hcmp. lra.
Qed.

(* q_prod_val: IEEE-754 double for 2^1023 = Omega/2 = 2^(femax-1) in Tdouble, the
   *product* magnitude bound used by DWTimesFP_relative_error_input_cond / DWTimesDW_exact_leading_product_input_cond.  Same
   construction as q_omega_val / q_sqrt_val but scaling 1.0 by 2^1023.  Used by
   Float_cmp_Clt_bpow1023 to lift the C runtime check `fabs(z) < ldexp(1.0, 1023)`
   into the abstract bound Rabs (FT2R z) < bpow radix2 1023 together with
   is_finite z. *)
Definition q_prod_val :=
  Binary.Bldexp (fprec Tdouble) 1024 (fprec_gt_0 Tdouble)
    (fprec_lt_femax Tdouble) BinarySingleNaN.mode_NE
    (Float.of_bits (Int64.repr 4607182418800017408)) 1023.

Lemma q_prod_val_finite : is_finite (ftype_of_float q_prod_val) = true.
Proof.
  cbv [q_prod_val Binary.is_finite Float.of_bits
       Bits.b64_of_bits Binary.Bldexp Binary.lift Binary.Bmult]; auto.
Qed.

Lemma q_prod_val_FT2R :
  FT2R (ftype_of_float q_prod_val) = bpow Zaux.radix2 1023.
Proof.
  cbv [q_prod_val ftype_of_float Float.of_bits
       Bits.b64_of_bits Binary.Bldexp]; simpl.
  cbv [Binary.lift Binary.Bmult]; simpl.
  cbv [BinarySingleNaN.binary_round_correct BinarySingleNaN.Bmult_correct_aux];
    simpl.
  cbv [FT2R]; simpl.
  cbv [F2R]; simpl.
  nra.
Qed.

(* Float.cmp Clt (fabs b) q_prod_val = true → is_finite b = true ∧
   Rabs (FT2R b) < 2^1023.  Unlike the Cle_bpow* lemmas, finiteness is DERIVED
   (not assumed): a strict `<` against the finite q_prod_val can only hold when b
   is finite (a NaN abs compares unordered → false; +Inf → Gt → false).  This is
   what makes the single prod_bnd check discharge both Fast2Mult's finiteness
   requirement and the product magnitude bound. *)
Lemma Float_cmp_Clt_bpow1023 :
  forall (b : ftype Tdouble),
  Float.cmp Clt
    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype b))
    q_prod_val = true ->
  is_finite b = true /\ Rabs (FT2R b) < bpow Zaux.radix2 1023.
Proof.
  intros b H.
  assert (Hfin : is_finite b = true).
  { rewrite is_finite_Binary.
    cbv [Float.cmp cmp_of_comparison Float.compare] in H.
    destruct (float_of_ftype b) eqn:E; simpl in H |- *; auto;
      cbv [Binary.Babs Binary.Bsign] in H; simpl in H; try discriminate. }
  split; [exact Hfin|].
  cbv [Float.cmp cmp_of_comparison Float.compare] in H.
  assert (Hfb : Binary.is_finite 53 1024
    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype b)) = true).
  { rewrite Binary.is_finite_Babs; rewrite <- is_finite_Binary; exact Hfin. }
  assert (Hfq : Binary.is_finite (fprec Tdouble) (femax Tdouble) q_prod_val = true).
  { generalize q_prod_val_finite. rewrite is_finite_Binary, float_of_ftype_of_float;
    cbv [fprec femax]; auto. }
  rewrite Binary.Bcompare_correct in H; [| exact Hfb | exact Hfq].
  rewrite Binary.B2R_Babs, B2R_float_of_ftype in H.
  pose proof q_prod_val_FT2R as Hft2r.
  assert (Hqval : Binary.B2R 53 1024 q_prod_val = bpow Zaux.radix2 1023).
  { rewrite <- Hft2r, FT2R_ftype_of_float; cbv [fprec femax]; reflexivity. }
  destruct (Rcompare (Rabs (FT2R b)) (Binary.B2R 53 1024 q_prod_val)) eqn:Hcmp;
    simpl in H; try discriminate.
  apply Rcompare_Lt_inv in Hcmp. lra.
Qed.

(* Packaging lemma for the guard: the single strict product check
   `fabs(x->s * y) < ldexp(1.0, 1023)` establishes BOTH the Fast2Mult finiteness
   requirement (is_finite (BMULT a b)) and the cond's product magnitude bound
   (Rabs (FT2R a * FT2R b) <= /2 * Omega).  Combines Float_cmp_Clt_bpow1023 (which
   also derives z finite) with no_overflow_real_from_round_mul.  It derives
   both facts directly from the product bound. *)
Lemma prod_bnd_facts :
  forall (a b : ftype Tdouble),
  Float.cmp Clt
    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble))
       (Float.mul (float_of_ftype a) (float_of_ftype b)))
    q_prod_val = true ->
  is_finite (BMULT a b) = true /\
  Rabs (FT2R a * FT2R b) <= /2 * bpow Zaux.radix2 (femax Tdouble).
Proof.
  intros a b H.
  assert (Hbm : ftype_of_float (Float.mul (float_of_ftype a) (float_of_ftype b))
                = BMULT a b).
  { reflexivity. }
  destruct (Float_cmp_Clt_bpow1023 (BMULT a b)) as [Hfin Hlt].
  { rewrite <- Hbm. rewrite float_of_ftype_of_float. exact H. }
  split; [exact Hfin|].
  rewrite <- (BMULT_round_correct Tdouble a b Hfin) in Hlt.
  apply no_overflow_real_from_round_mul; exact Hlt.
Qed.

(* Float.cmp Ceq (Float.add a b) a = true → FT2R a = round(FT2R a + FT2R b),
   i.e., (a, b) satisfies the double-word relation in IEEE-754 RN.
   The C test `(a + b) == a` lifts to double_word_prop. *)
Lemma Float_add_eq_dw : forall (a b : ftype Tdouble),
  is_finite a = true ->
  is_finite b = true ->
  Float.cmp Ceq (Float.add (float_of_ftype a) (float_of_ftype b))
                (float_of_ftype a) = true ->
  FT2R a = rounded Tdouble (FT2R a + FT2R b).
Proof.
  intros a b Ha Hb Hcmp.
  set (sum := Float.add (float_of_ftype a) (float_of_ftype b)) in *.
  rewrite is_finite_Binary in Ha, Hb.
  (* Derive finiteness of sum from Hcmp: Ceq with finite a forces sum to be
     finite (otherwise Bcompare returns Gt/Lt for Inf, or None for NaN). *)
  assert (Hfin_sum : Binary.is_finite 53 1024 sum = true).
  { destruct sum; auto; cbv [Float.cmp cmp_of_comparison Float.compare] in Hcmp;
    destruct (float_of_ftype a); simpl in Hcmp; try discriminate;
    destruct s; simpl in Hcmp; try discriminate;
    destruct s0; simpl in Hcmp; discriminate. }
  (* Now Bcompare yields B2R sum = B2R a. *)
  cbv [Float.cmp cmp_of_comparison Float.compare] in Hcmp.
  rewrite Binary.Bcompare_correct in Hcmp; [| exact Hfin_sum | exact Ha].
  destruct (Rcompare (Binary.B2R 53 1024 sum)
                     (Binary.B2R 53 1024 (float_of_ftype a))) eqn:Hcmpeq;
    simpl in Hcmp; try discriminate.
  apply Rcompare_Eq_inv in Hcmpeq.
  (* Hcmpeq : Binary.B2R 53 1024 sum = Binary.B2R 53 1024 (float_of_ftype a) *)
  (* For Tdouble standard: Binary.B2R 53 1024 = FT2R definitionally. *)
  change (Binary.B2R 53 1024 (float_of_ftype a)) with (FT2R a) in Hcmpeq.
  (* sum = Float.add (float_of_ftype a) (float_of_ftype b) = BPLUS a b *)
  unfold sum in Hcmpeq.
  rewrite Float_add_rewrite in Hcmpeq.
  change (Binary.B2R 53 1024
            (@BPLUS _ Tdouble _ (float_of_ftype a) (float_of_ftype b)))
    with (FT2R (BPLUS a b)) in Hcmpeq.
  (* Hcmpeq : FT2R (BPLUS a b) = FT2R a *)
  assert (Hfin_BPLUS : is_finite (BPLUS a b) = true).
  { rewrite is_finite_Binary. change (BPLUS a b) with sum. exact Hfin_sum. }
  pose proof (BPLUS_round_correct Tdouble a b Hfin_BPLUS) as Hbplus.
  simpl in Hbplus.
  (* Hbplus : round (FT2R a + FT2R b) = FT2R (BPLUS a b) *)
  unfold rounded.
  transitivity (FT2R (BPLUS a b)); [exact (eq_sym Hcmpeq)|].
  symmetry. etransitivity; [|exact Hbplus]. reflexivity.
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

(* ==================================================================== *)
(*  Division guard helpers (dw_div_fp_check / DWDivFP_mixed_safe_input_cond)  *)
(* ==================================================================== *)

(* Generic rounded->exact magnitude transfer.  RN is monotone and idempotent on
   a format value bpow k, so:
     - a STRICT rounded bound below bpow k forces the exact value <= bpow k, and
     - a STRICT rounded bound above bpow k forces the exact value > bpow k.
   These are the division check analogs of no_overflow/underflow_real_from_round_mul,
   stated for an arbitrary real r (instantiated at r = FT2R xh / FT2R y via
   BDIV_round_correct in body_dw_div_fp_check). *)
Lemma round_abs_le_bpow (r : R) (k : Z) :
  generic_format radix2 fexp (bpow Zaux.radix2 k) ->
  Rabs (round radix2 fexp ZnearestE r) < bpow Zaux.radix2 k ->
  Rabs r <= bpow Zaux.radix2 k.
Proof.
  intros Hfmt H.
  destruct (Rle_dec (Rabs r) (bpow Zaux.radix2 k)) as [Hle | Hgt]; auto.
  exfalso. apply Rnot_le_lt in Hgt. apply Rlt_le in Hgt.
  apply (round_le radix2 fexp (Znearest common.choice)) in Hgt.
  rewrite round_NE_abs in Hgt; [ | apply FLT_exp_valid; cbv; auto].
  replace (round radix2 fexp (Znearest common.choice) (bpow Zaux.radix2 k))
    with (bpow Zaux.radix2 k) in Hgt.
  2:{ rewrite round_generic; auto. apply valid_rnd_N. }
  lra.
Qed.

Lemma round_abs_gt_bpow (r : R) (k : Z) :
  generic_format radix2 fexp (bpow Zaux.radix2 k) ->
  bpow Zaux.radix2 k < Rabs (round radix2 fexp ZnearestE r) ->
  bpow Zaux.radix2 k < Rabs r.
Proof.
  intros Hfmt H.
  destruct (Rlt_dec (bpow Zaux.radix2 k) (Rabs r)) as [Hlt | Hle]; auto.
  exfalso. apply Rnot_lt_le in Hle.
  apply (round_le radix2 fexp (Znearest common.choice)) in Hle.
  rewrite round_NE_abs in Hle; [ | apply FLT_exp_valid; cbv; auto].
  replace (round radix2 fexp (Znearest common.choice) (bpow Zaux.radix2 k))
    with (bpow Zaux.radix2 k) in Hle.
  2:{ rewrite round_generic; auto. apply valid_rnd_N. }
  lra.
Qed.

(* is_finite (BDIV a b) with b finite forces the divisor's real value nonzero:
   a finite b with FT2R b = 0 is the zero float, and a/0 = +/-Inf (or NaN) is
   not finite.  Lets the quotient checks invoke BDIV_round_correct. *)
Lemma BDIV_denom_ne0 : forall (a b : ftype Tdouble),
  is_finite b = true ->
  is_finite (BDIV a b) = true ->
  FT2R b <> 0%R.
Proof.
  intros a b Hb Hfin Hb0.
  rewrite <- B2R_float_of_ftype in Hb0.
  rewrite is_finite_Binary in Hb, Hfin.
  unfold BDIV, BINOP in Hfin.
  rewrite float_of_ftype_of_float in Hfin.
  destruct (float_of_ftype b) eqn:E; simpl in Hb; try discriminate.
  - (* B754_zero: a / 0 is Inf/NaN, not finite -> Hfin false *)
    destruct (float_of_ftype a); simpl in Hfin; try discriminate.
  - (* B754_finite: B2R is a nonzero F2R, contradicting Hb0 *)
    revert Hb0. cbn [Binary.B2R]. apply F2R_neq_0. destruct s; simpl; lia.
Qed.

(* BDIV packaging of the rounded->exact transfer: from a magnitude bound on
   the FLOAT quotient FT2R (BDIV a b) (with b's real value nonzero and BDIV finite)
   to the corresponding bound on the EXACT real quotient FT2R a / FT2R b.  Combines
   BDIV_round_correct (FT2R (BDIV a b) = RN(FT2R a / FT2R b)) with round_abs_*_bpow,
   exactly as prod_bnd_facts does for multiplication. *)
Lemma BDIV_abs_le_bpow : forall (a b : ftype Tdouble) (k : Z),
  FT2R b <> 0%R -> is_finite (BDIV a b) = true ->
  generic_format radix2 fexp (bpow Zaux.radix2 k) ->
  Rabs (FT2R (BDIV a b)) < bpow Zaux.radix2 k ->
  Rabs (FT2R a / FT2R b) <= bpow Zaux.radix2 k.
Proof.
  intros a b k Hne Hfin Hfmt H.
  rewrite <- (BDIV_round_correct Tdouble a b Hne Hfin) in H.
  apply round_abs_le_bpow; assumption.
Qed.

Lemma BDIV_abs_gt_bpow : forall (a b : ftype Tdouble) (k : Z),
  FT2R b <> 0%R -> is_finite (BDIV a b) = true ->
  generic_format radix2 fexp (bpow Zaux.radix2 k) ->
  bpow Zaux.radix2 k < Rabs (FT2R (BDIV a b)) ->
  bpow Zaux.radix2 k < Rabs (FT2R a / FT2R b).
Proof.
  intros a b k Hne Hfin Hfmt H.
  rewrite <- (BDIV_round_correct Tdouble a b Hne Hfin) in H.
  apply round_abs_gt_bpow; assumption.
Qed.

(* Normal powers of two used by the division guards.
   [q_lo968_val = 2^-968] is the DW/FP product floor and the DW/DW divisor
   floor.  [q_lo969_val = 2^-969] is used to derive the DW/DW divisor ceiling.
   Their normal representation supports the strict transfer from rounded to exact
   in [BDIV_abs_gt_bpow]. *)
Definition q_lo968_val :=
  Binary.Bldexp (fprec Tdouble) 1024 (fprec_gt_0 Tdouble)
    (fprec_lt_femax Tdouble) BinarySingleNaN.mode_NE
    (Float.of_bits (Int64.repr 4607182418800017408)) (-968).

Definition q_lo969_val :=
  Binary.Bldexp (fprec Tdouble) 1024 (fprec_gt_0 Tdouble)
    (fprec_lt_femax Tdouble) BinarySingleNaN.mode_NE
    (Float.of_bits (Int64.repr 4607182418800017408)) (-969).

Lemma q_lo968_val_finite : is_finite (ftype_of_float q_lo968_val) = true.
Proof.
  cbv [q_lo968_val Binary.is_finite Float.of_bits
       Bits.b64_of_bits Binary.Bldexp Binary.lift Binary.Bmult]; auto.
Qed.

Lemma q_lo969_val_finite : is_finite (ftype_of_float q_lo969_val) = true.
Proof.
  cbv [q_lo969_val Binary.is_finite Float.of_bits
       Bits.b64_of_bits Binary.Bldexp Binary.lift Binary.Bmult]; auto.
Qed.

Lemma q_lo968_val_FT2R :
  FT2R (ftype_of_float q_lo968_val) = bpow Zaux.radix2 (-968).
Proof.
  cbv [q_lo968_val ftype_of_float Float.of_bits
       Bits.b64_of_bits Binary.Bldexp]; simpl.
  cbv [Binary.lift Binary.Bmult]; simpl.
  cbv [BinarySingleNaN.binary_round_correct BinarySingleNaN.Bmult_correct_aux];
    simpl.
  cbv [FT2R]; simpl.
  cbv [F2R]; simpl.
  nra.
Qed.

Lemma q_lo969_val_FT2R :
  FT2R (ftype_of_float q_lo969_val) = bpow Zaux.radix2 (-969).
Proof.
  cbv [q_lo969_val ftype_of_float Float.of_bits
       Bits.b64_of_bits Binary.Bldexp]; simpl.
  cbv [Binary.lift Binary.Bmult]; simpl.
  cbv [BinarySingleNaN.binary_round_correct BinarySingleNaN.Bmult_correct_aux];
    simpl.
  cbv [FT2R]; simpl.
  cbv [F2R]; simpl.
  nra.
Qed.

(* Generic magnitude comparisons against a concrete finite float constant v
   whose real value is C.  Cle_lo / Clt_lo lift `v (<=|<) fabs b` into the
   corresponding real lower bound on |FT2R b|; Clt_hi lifts `fabs b < v` into
   finiteness of b AND the strict upper bound |FT2R b| < C (deriving finiteness
   the same way as Float_cmp_Clt_bpow1023). *)
Lemma Float_cmp_Cle_lo :
  forall (v : Floats.float) (b : ftype Tdouble) (C : R),
  is_finite b = true ->
  is_finite (ftype_of_float v) = true ->
  FT2R (ftype_of_float v) = C ->
  Float.cmp Cle v
    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype b)) = true ->
  C <= Rabs (FT2R b).
Proof.
  intros v b C Hb Hv HC H.
  cbv [Float.cmp cmp_of_comparison Float.compare] in H.
  assert (Hfb : Binary.is_finite 53 1024
    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype b)) = true).
  { rewrite Binary.is_finite_Babs; rewrite <- is_finite_Binary; exact Hb. }
  assert (Hfv : Binary.is_finite 53 1024 v = true).
  { generalize Hv. rewrite is_finite_Binary, float_of_ftype_of_float;
    cbv [fprec femax]; auto. }
  rewrite Binary.Bcompare_correct in H; [| exact Hfv | exact Hfb].
  rewrite Binary.B2R_Babs, B2R_float_of_ftype in H.
  assert (Hvr : Binary.B2R 53 1024 v = C).
  { rewrite <- HC, FT2R_ftype_of_float; cbv [fprec femax]; reflexivity. }
  rewrite Hvr in H.
  destruct (Rcompare C (Rabs (FT2R b))) eqn:Hcmp; simpl in H; try discriminate.
  - apply Req_le. apply Rcompare_Eq_inv in Hcmp; lra.
  - apply Rlt_le. apply Rcompare_Lt_inv in Hcmp; lra.
Qed.

Lemma Float_cmp_Clt_lo :
  forall (v : Floats.float) (b : ftype Tdouble) (C : R),
  is_finite b = true ->
  is_finite (ftype_of_float v) = true ->
  FT2R (ftype_of_float v) = C ->
  Float.cmp Clt v
    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype b)) = true ->
  C < Rabs (FT2R b).
Proof.
  intros v b C Hb Hv HC H.
  cbv [Float.cmp cmp_of_comparison Float.compare] in H.
  assert (Hfb : Binary.is_finite 53 1024
    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype b)) = true).
  { rewrite Binary.is_finite_Babs; rewrite <- is_finite_Binary; exact Hb. }
  assert (Hfv : Binary.is_finite 53 1024 v = true).
  { generalize Hv. rewrite is_finite_Binary, float_of_ftype_of_float;
    cbv [fprec femax]; auto. }
  rewrite Binary.Bcompare_correct in H; [| exact Hfv | exact Hfb].
  rewrite Binary.B2R_Babs, B2R_float_of_ftype in H.
  assert (Hvr : Binary.B2R 53 1024 v = C).
  { rewrite <- HC, FT2R_ftype_of_float; cbv [fprec femax]; reflexivity. }
  rewrite Hvr in H.
  destruct (Rcompare C (Rabs (FT2R b))) eqn:Hcmp; simpl in H; try discriminate.
  apply Rcompare_Lt_inv in Hcmp; exact Hcmp.
Qed.

(* Strict upper quotient bound against q_omega_val (2^1022 = Omega/4): the
   analog of Float_cmp_Clt_bpow1023 for Clt and bpow1022, deriving finiteness of the
   (rounded) quotient AND the strict magnitude bound.  Specialized (not generic
   in v) because the finiteness derivation needs q_omega_val concrete so that
   Bcompare against an infinity/NaN left operand reduces. *)
Lemma Float_cmp_Clt_bpow1022 :
  forall (b : ftype Tdouble),
  Float.cmp Clt
    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype b))
    q_omega_val = true ->
  is_finite b = true /\ Rabs (FT2R b) < bpow Zaux.radix2 1022.
Proof.
  intros b H.
  assert (Hfin : is_finite b = true).
  { rewrite is_finite_Binary.
    cbv [Float.cmp cmp_of_comparison Float.compare] in H.
    destruct (float_of_ftype b) eqn:E; simpl in H |- *; auto;
      cbv [Binary.Babs Binary.Bsign] in H; simpl in H; try discriminate. }
  split; [exact Hfin|].
  cbv [Float.cmp cmp_of_comparison Float.compare] in H.
  assert (Hfb : Binary.is_finite 53 1024
    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype b)) = true).
  { rewrite Binary.is_finite_Babs; rewrite <- is_finite_Binary; exact Hfin. }
  assert (Hfq : Binary.is_finite (fprec Tdouble) (femax Tdouble) q_omega_val = true).
  { generalize q_omega_val_finite. rewrite is_finite_Binary, float_of_ftype_of_float;
    cbv [fprec femax]; auto. }
  rewrite Binary.Bcompare_correct in H; [| exact Hfb | exact Hfq].
  rewrite Binary.B2R_Babs, B2R_float_of_ftype in H.
  pose proof q_omega_val_FT2R as Hft2r.
  assert (Hqval : Binary.B2R 53 1024 q_omega_val = bpow Zaux.radix2 1022).
  { rewrite <- Hft2r, FT2R_ftype_of_float; cbv [fprec femax]; reflexivity. }
  destruct (Rcompare (Rabs (FT2R b)) (Binary.B2R 53 1024 q_omega_val)) eqn:Hcmp;
    simpl in H; try discriminate.
  apply Rcompare_Lt_inv in Hcmp. lra.
Qed.
(* ==================================================================== *)
(*  Double word division check helpers (dw_div_dw_check / DWDivDW_mixed_safe_input_cond) *)
(* ==================================================================== *)

(* [q_hi966_val] represents [2^966 = 2^(femax-p-5)], the upper divisor bound
   in [DWDivDW_mixed_safe_input_cond].  This bound is equivalent to
   [eta*|yh| <= u^2/4], which pays for the reciprocal reconstruction floor.
   The guard compares [|y->s|] directly with this value. *)
Definition q_hi966_val :=
  Binary.Bldexp (fprec Tdouble) 1024 (fprec_gt_0 Tdouble)
    (fprec_lt_femax Tdouble) BinarySingleNaN.mode_NE
    (Float.of_bits (Int64.repr 4607182418800017408)) 966.

Lemma q_hi966_val_finite : is_finite (ftype_of_float q_hi966_val) = true.
Proof.
  cbv [q_hi966_val Binary.is_finite Float.of_bits
       Bits.b64_of_bits Binary.Bldexp Binary.lift Binary.Bmult]; auto.
Qed.

Lemma q_hi966_val_FT2R :
  FT2R (ftype_of_float q_hi966_val) = bpow Zaux.radix2 966.
Proof.
  cbv [q_hi966_val ftype_of_float Float.of_bits
       Bits.b64_of_bits Binary.Bldexp]; simpl.
  cbv [Binary.lift Binary.Bmult]; simpl.
  cbv [BinarySingleNaN.binary_round_correct BinarySingleNaN.Bmult_correct_aux];
    simpl.
  cbv [FT2R]; simpl.
  cbv [F2R]; simpl.
  nra.
Qed.

(* Upper bound mirror of Float_cmp_Cle_lo: lifts the C test `fabs b <= v` into
   the real bound Rabs (FT2R b) <= C.  Generic in the constant float v (unlike
   Float_cmp_Cle_bpow1022, which is specialized to q_omega_val and concludes in
   the /4*Omega form), so the same lemma serves both the 2^966 bound on |yh| and
   the 2^(femax-2) bounds that DWDivDW_mixed_safe_input_cond states as bpow (femax t - 2). *)
Lemma Float_cmp_Cle_hi :
  forall (v : Floats.float) (b : ftype Tdouble) (C : R),
  is_finite b = true ->
  is_finite (ftype_of_float v) = true ->
  FT2R (ftype_of_float v) = C ->
  Float.cmp Cle
    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype b))
    v = true ->
  Rabs (FT2R b) <= C.
Proof.
  intros v b C Hb Hv HC H.
  cbv [Float.cmp cmp_of_comparison Float.compare] in H.
  assert (Hfb : Binary.is_finite 53 1024
    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype b)) = true).
  { rewrite Binary.is_finite_Babs; rewrite <- is_finite_Binary; exact Hb. }
  assert (Hfv : Binary.is_finite 53 1024 v = true).
  { generalize Hv. rewrite is_finite_Binary, float_of_ftype_of_float;
    cbv [fprec femax]; auto. }
  rewrite Binary.Bcompare_correct in H; [| exact Hfb | exact Hfv].
  rewrite Binary.B2R_Babs, B2R_float_of_ftype in H.
  assert (Hvr : Binary.B2R 53 1024 v = C).
  { rewrite <- HC, FT2R_ftype_of_float; cbv [fprec femax]; reflexivity. }
  rewrite Hvr in H.
  destruct (Rcompare (Rabs (FT2R b)) C) eqn:Hcmp; simpl in H; try discriminate.
  - apply Req_le. apply Rcompare_Eq_inv in Hcmp; lra.
  - apply Rlt_le. apply Rcompare_Lt_inv in Hcmp; lra.
Qed.

(* An upper bound on |r| is a lower bound on |1/r|, for r <> 0.  This is what
   makes the check's direct nonstrict test on |y->s| discharge the DW/DW
   reciprocal conjunct exactly (no rounding, no strictness slop).  The r <> 0
   side condition is essential and not cosmetic: at r = 0 the Coq convention
   1/0 = 0 makes the conclusion false while the hypothesis Rabs 0 <= C holds.
   In the check it is supplied by the separate yh_lo clause
   (2^(emin+2p) <= |y->s|), not by this bound. *)
Lemma recip_lower_from_upper : forall (r C : R),
  0 < C -> r <> 0%R -> Rabs r <= C -> / C <= Rabs (1 / r).
Proof.
  intros r C HC Hr H.
  assert (Hra : 0 < Rabs r) by (apply Rabs_pos_lt; exact Hr).
  replace (1 / r)%R with (/ r)%R by (unfold Rdiv; ring).
  rewrite Rabs_Rinv by exact Hr.
  apply Rinv_le_contravar; [exact Hra | exact H].
Qed.

(* Instance of recip_lower_from_upper expressed with bpow, which is the form the DW/DW
   reciprocal conjunct used to be stated in: a nonstrict upper bound |r| <= 2^k on the
   divisor is exactly the lower bound 2^(-k) <= |1/r| on the reciprocal.  At
   k = -(emin + 2p - 1) = 969 for Tdouble this is what yh_hi discharges. *)
Lemma recip_lower_from_bpow_upper : forall (r : R) (k : Z),
  r <> 0%R ->
  Rabs r <= bpow Zaux.radix2 k ->
  bpow Zaux.radix2 (- k) <= Rabs (1 / r).
Proof.
  intros r k Hr H.
  rewrite bpow_opp.
  apply recip_lower_from_upper; [apply bpow_gt_0 | exact Hr | exact H].
Qed.
