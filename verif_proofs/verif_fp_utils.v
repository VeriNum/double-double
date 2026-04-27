(* Copyright 2025 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* verif_fp_utils.v *)
Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Require Import float_acc_lems common real_extras.
From Flocq Require Import Pff2Flocq Core.

Require Import fp_utils fp_utils_specs.
Require Import float_verif_lemmas.

#[export] Instance CompSpecs : 
  compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

(* ldexp_val  defines the IEEE-754 float for ldexp(1.0, 53) = 2^53.
   It mirrors the C expression `ldexp(1.0, 53)` used in fast2_mult_check
   and fast2_mult_check2 to build the underflow threshold.
   Bit pattern 4607182418800017408 = 0x3FF0000000000000 is the encoding
   of 1.0 as a 64-bit double; Bldexp then scales it by 2^53. *)
Definition ldexp_val :=
  Binary.Bldexp (fprec Tdouble) 1024 (fprec_gt_0 Tdouble)
    (fprec_lt_femax Tdouble) BinarySingleNaN.mode_NE
    (Float.of_bits (Int64.repr 4607182418800017408)) 53.

(* thresh_val defines the IEEE-754 float for DBL_MIN * ldexp(1.0, 53) = 2^(-969).
   Bit pattern 4503599627370496 = 0x0010000000000000 is the encoding of
   DBL_MIN (smallest normal double, 2^(-1022)).  The product 2^(-1022) * 2^53
   equals 2^(-969) = bpow 2 (emin + 2*p - 1), the Fast2Mult underflow bound
   from Fast2Mult_cond.  Defining it here avoids repeating the verbose
   IEEE-754 expression in every LOCAL clause and proof obligation. *)
Definition thresh_val :=
  Float.mul (Float.of_bits (Int64.repr 4503599627370496)) ldexp_val.

(* thresh_val is a finite (non-NaN, non-infinite) double; proved by
   computational reduction of the concrete bit patterns. *)
Lemma thresh_val_finite : is_finite (ftype_of_float thresh_val) = true.
Proof.
  cbv [thresh_val ldexp_val Binary.is_finite Float.mul Float.of_bits
       Bits.b64_of_bits Binary.Bldexp Binary.lift Binary.Bmult]; auto.
Qed.

(* The real value of thresh_val equals the Fast2Mult underflow bound
   bpow 2 (emin + 2*p - 1).  This links the concrete C constant to the
   abstract bound in Fast2Mult_cond, allowing Float_cmp_Cle_mul to fire. *)
Lemma thresh_val_FT2R :
  FT2R (ftype_of_float thresh_val) =
  bpow Zaux.radix2 (SpecFloat.emin (fprec Tdouble) (femax Tdouble) + 2 * fprec Tdouble - 1).
Proof.
  (* Unfold in stages: a single large cbv leaves a goal nra cannot close. *)
  cbv [thresh_val ldexp_val ftype_of_float Float.mul Float.of_bits
       Bits.b64_of_bits Binary.Bldexp]; simpl.
  cbv [Binary.lift Binary.Bmult]; simpl.
  cbv [BinarySingleNaN.binary_round_correct BinarySingleNaN.Bmult_correct_aux]; simpl.
  cbv [FT2R]; simpl.
  cbv [F2R]; simpl.
  nra.
Qed.

Definition tbool (b : bool) : int :=
  if b then Int.one else Int.zero.

(* Collect the function-API specs together into Gprog: list funspec *)
Definition Gprog : funspecs := MathASI ++ [ isfinite_double_spec; fast2_mult_check_spec; fast2_mult_check2_spec].

(* isfinite_double(x) returns 1 iff x is finite.
   The C implementation uses the trick (x - x) == 0.0: finite values give 0,
   while infinities and NaNs give NaN, for which the == comparison is false.
   The proof strategy: use is_finite x as the witness bool, then for the
   finite case (B754_finite) show that x - x rounds to 0 and Rcompare gives Eq. *)
Lemma body_isfinite_double: semax_body Vprog Gprog f_isfinite_double isfinite_double_spec.
Proof.
  start_function.
  forward.
  Exists (is_finite x).
  entailer!.
  remember (is_finite x) as B.
  destruct x; simpl;  auto.
  1,2,3 : subst; destruct s; simpl; auto.
  cbv [Float.cmp cmp_of_comparison Float.compare Float.sub Float.of_bits].
  rewrite Binary.Bcompare_correct; simpl; auto.
  remember (Rcompare _ _) as X.
  assert (Eq = X).
  -
  subst X.
  pose proof BMINUS_zero Tdouble
      (Binary.B754_finite 53 1024 s m e e0) as H.
      rewrite <- B2R_float_of_ftype in H.
  unfold BMINUS in H. simpl in H.
  specialize (H eq_refl).
  change (fprec Tdouble) with 53%Z in *.
  cbv [fprec_gt_0 fprec_lt_femax] in H.
  cbv [binop_nan single_double single_double_ex eq_rect_r] in H;
  simpl in H.
  rewrite H; clear H.
  rewrite <-B2R_float_of_ftype.
  symmetry;  apply Rcompare_Eq; auto.
  -
  subst; rewrite <-H; auto.
  - (* x - x is finite: Bminus_no_overflow holds because the real difference is 0 *)
  pose proof (no_overflow_minus_is_finite Tdouble
  (Binary.B754_finite 53 1024 s m e e0)
  (Binary.B754_finite 53 1024 s m e e0)) as H.
  rewrite is_finite_Binary in H; simpl in H.
  cbv [fprec_gt_0 fprec_lt_femax] in H.
  cbv [binop_nan single_double single_double_ex eq_rect_r] in H;
  simpl in H. apply H; auto.
  unfold Bminus_no_overflow; rewrite Rminus_diag, round_0, Rabs_R0.
  apply bpow_gt_0.
  apply valid_rnd_N.
Qed.

(* The function satisfies its API spec (with a semax-body proof) *)
Lemma body_fast2_mult_check: semax_body Vprog Gprog f_fast2_mult_check fast2_mult_check_spec.
Proof.
  start_function.
  forward.
  forward_call.
  forward.
  forward_call.
  Intros vret_fin.
  rename H into Hfin_spec.

  set (px := is_finite y = true /\
    Float.cmp Ceq x (Float.of_bits (Int64.repr 0)) = true).
  set (py := is_finite x = true /\
    Float.cmp Ceq y (Float.of_bits (Int64.repr 0)) = true).

  set (Post_if :=
    EX b_zx: bool,
    PROP (b_zx = true -> px)
    LOCAL ( temp _fin (Vint (if vret_fin then Int.one else Int.zero));
            temp _thresh (Vfloat thresh_val);
            temp _t'1 (Vfloat ldexp_val);
            temp _t'3 (Vint (if b_zx then Int.one else Int.zero));
            temp _z (Vfloat (Float.mul x y));
            temp _x (Vfloat x);
            temp _y (Vfloat y))
    SEP ()).
  forward_if Post_if.

  - (* x == 0.0 = true: call isfinite(y), Exists (is_finite y) *)
    forward_call.
    Intros vret.
    forward.
    unfold Post_if; Exists vret; entailer!.
    split.
    + intro Hvret; unfold px; split; [apply (proj1 H0); exact Hvret | assumption].
    + destruct vret; simpl; auto.

  - (* x == 0.0 = false: return false, vacuously true *)
    forward.
    unfold Post_if; entailer!.
    Exists false.
    entailer!.

  - unfold Post_if; clear Post_if.
    Intros b_zx.
    rename H into H_b_zx.
    forward.
    set (Post_if2 :=
      EX b_zy: bool,
      PROP (b_zy = true -> py)
      LOCAL ( temp _zx (Vint (if b_zx then Int.one else Int.zero));
              temp _fin (Vint (if vret_fin then Int.one else Int.zero));
              temp _thresh (Vfloat thresh_val);
              temp _t'1 (Vfloat ldexp_val);
              temp _t'5 (Vint (if b_zy then Int.one else Int.zero));
              temp _z (Vfloat (Float.mul x y));
              temp _x (Vfloat x);
              temp _y (Vfloat y))
      SEP ()).
    forward_if Post_if2.

    + (* y == 0.0 = true *)
      forward_call.
      Intros vret_xfin.
      forward.
      unfold Post_if2; clear Post_if2; Exists vret_xfin; entailer!.
      split.
      * intro Hvret_xfin; unfold py; split; [apply (proj1 H0); exact Hvret_xfin | assumption].
      * destruct vret_xfin; simpl; auto.

    + (* y == 0.0 = false *)
      forward.
      unfold Post_if2; clear Post_if2; entailer!.
      Exists false.
      entailer!.

    + unfold Post_if2; clear Post_if2.
      Intros b_zy.
      rename H into H_b_zy.
      forward.
      set (Post_t7 :=
        EX b_lb: bool,
        PROP (b_lb = true -> vret_fin = true /\ (px \/ py \/
          Rlt_bool (bpow radix2 (emin + 2 * fprec Tdouble - 1))
            (Rabs (round radix2 (FLT_exp emin (fprec Tdouble))
              ZnearestE (FT2R x * FT2R y))) = true))
        LOCAL ( temp _zx (Vint (if b_zx then Int.one else Int.zero));
                temp _zy (Vint (if b_zy then Int.one else Int.zero));
                temp _fin (Vint (if vret_fin then Int.one else Int.zero));
                temp _thresh (Vfloat thresh_val);
                temp _t'1 (Vfloat ldexp_val);
                temp _t'7 (Vint (if b_lb then Int.one else Int.zero));
                temp _z (Vfloat (Float.mul x y));
                temp _x (Vfloat x);
                temp _y (Vfloat y))
        SEP ()).
      forward_if Post_t7.

      * (* fin = true *)
        set (Post_xy :=
          EX b_xy: bool,
          PROP (b_xy = true -> px \/ py)
          LOCAL ( temp _zx (Vint (if b_zx then Int.one else Int.zero));
                  temp _zy (Vint (if b_zy then Int.one else Int.zero));
                  temp _fin (Vint (if vret_fin then Int.one else Int.zero));
                  temp _thresh (Vfloat thresh_val);
                  temp _t'1 (Vfloat ldexp_val);
                  temp _t'8 (Vint (if b_xy then Int.one else Int.zero));
                  temp _z (Vfloat (Float.mul x y));
                  temp _x (Vfloat x);
                  temp _y (Vfloat y))
          SEP ()).
        forward_if Post_xy.

        ** (* b_zx = true *)
           forward.
           unfold Post_xy; clear Post_xy; Exists true; entailer!.
           left; apply H_b_zx.
           destruct b_zx; [reflexivity | simpl in H0; contradiction].

        ** (* b_zx = false *)
           forward.
           unfold Post_xy; clear Post_xy; Exists (orb b_zx b_zy); entailer!.
           match goal with |- ?A /\ ?B => refine (conj _ _) end.
           { intro Htrue.
             destruct (orb_prop _ _ Htrue) as [Hzx | Hzy].
             - left; apply H_b_zx; exact Hzx.
             - right; apply H_b_zy; exact Hzy. }
           { assert (b_zx = false) as Hbzx_false.
             { destruct b_zx; [exfalso; discriminate H0 | reflexivity]. }
             subst b_zx; simpl; destruct b_zy; reflexivity. }

        ** unfold Post_xy; clear Post_xy.
           Intros b_xy.
           rename H into H_b_xy.
           forward_if.

           (* b_xy = true: short-circuit, return fin = true *)
           forward.
           unfold Post_t7; clear Post_t7; entailer!.
           set (uf := Rlt_bool (bpow radix2 (emin + 2 * fprec Tdouble - 1))
             (Rabs (round radix2 (FLT_exp emin (fprec Tdouble))
               ZnearestE (FT2R x * FT2R y)))).
           Exists (andb vret_fin (orb b_xy uf)).
           entailer!.
           match goal with |- ?A /\ ?B =>
             assert (b_xy = true) as Hbxy_eq by (destruct b_xy; auto; simpl in H; contradiction);
             assert (vret_fin = true) as Hvf_eq by (destruct vret_fin; auto; simpl in H_b_xy; contradiction);
             subst b_xy vret_fin;
             split
           end.
           { intro Htrue.
             destruct (andb_prop _ _ Htrue) as [Hvf Hxy_uf].
             split; [exact Hvf |].
             destruct (orb_prop _ _ Hxy_uf) as [Hxy | Huf].
             { destruct (H0 Hxy) as [Hpx | Hpy].
               { left; exact Hpx. }
               { right; left; exact Hpy. } }
             { right; right; exact Huf. } }
           { simpl; reflexivity. }

           (* b_xy = false: check threshold *)
           forward_call.
           forward.
           forward.
           unfold Post_t7; clear Post_t7; entailer!.
           set (uf := Rlt_bool (bpow radix2 (emin + 2 * fprec Tdouble - 1))
             (Rabs (round radix2 (FLT_exp emin (fprec Tdouble))
               ZnearestE (FT2R x * FT2R y)))).
           Exists uf.
           entailer!.
           assert (vret_fin = true) as Hvf_eq by
             (destruct vret_fin; auto; simpl in H_b_xy; contradiction).
           assert (is_finite (ftype_of_float (Float.mul x y)) = true) as Hfin_mul by
             (rewrite is_finite_Binary; rewrite float_of_ftype_of_float;
              apply Hfin_spec; exact Hvf_eq).
           pose proof Float_cmp_Cle_mul x y (bpow radix2 (emin + 2 * fprec Tdouble - 1))
             (ftype_of_float thresh_val) Hfin_mul thresh_val_finite (eq_sym thresh_val_FT2R) as Hcmp.
           simpl in Hcmp; rewrite <- Hcmp; clear Hcmp.
           match goal with |- ?A /\ ?B => refine (conj _ _) end.
           { (* PROP: uf = true -> vret_fin = true /\ ... *)
             intro Htrue.
             destruct uf eqn:Huf_eq.
             - split; [exact Hvf_eq | right; right; reflexivity].
             - discriminate Htrue. }
           { (* Vint equality *)
             unfold uf; reflexivity. }

      * (* fin = false *)
        forward.
        unfold Post_t7; clear Post_t7; entailer!.
        Exists false.
        entailer!.

      * unfold Post_t7; clear Post_t7.
        Intros b_lb.
        rename H into H_lb.
        forward.
        Exists b_lb.
        entailer!.
        destruct (H_lb eq_refl) as [Hvf Hdisj].
        unfold MulResultIsSafeForFast2Mult, DDModels.Fast2Mult_cond.
        split.
        { apply Hfin_spec; exact Hvf. }
        { destruct Hdisj as [Hpx | [Hpy | Hpuf]].
          - left.
            pose proof Float_cmp_Ceq_zero_mul_FT2R_l as Hr; simpl in Hr.
            apply Hr; exact (proj2 Hpx).
          - left.
            pose proof Float_cmp_Ceq_zero_mul_FT2R_r as Hr; simpl in Hr.
            apply Hr; exact (proj2 Hpy).
          - right; apply Rlt_le, Rlt_bool_to_Rlt, no_underflow_real_from_round_mul.
            apply Rlt_bool_to_Rlt; exact Hpuf. }
Qed.

(* The function satisfies its API spec (with a semax-body proof) *)
Lemma body_fast2_mult_check2: semax_body Vprog Gprog f_fast2_mult_check2 fast2_mult_check2_spec.
Proof.
  start_function.
  forward_call.
  forward.

  set (px := is_finite y = true /\
    Float.cmp Ceq x (Float.of_bits (Int64.repr 0)) = true).
  set (py := is_finite x = true /\
    Float.cmp Ceq y (Float.of_bits (Int64.repr 0)) = true).

  set (Post_if :=
    EX b_zx: bool,
    PROP (b_zx = true -> px)
    LOCAL ( temp _thresh (Vfloat thresh_val);
            temp _t'1 (Vfloat ldexp_val);
            temp _t'2 (Vint (if b_zx then Int.one else Int.zero));
            temp _z (Vfloat z);
            temp _x (Vfloat x);
            temp _y (Vfloat y))
    SEP ()).
  forward_if Post_if.

  - (* x == 0.0 = true *)
    forward_call.
    Intros vret.
    rename H into H_cmp_x.
    rename H0 into Hisfinite_y.
    forward.
    unfold Post_if; Exists vret; entailer!.
    split.
    + intro Hvret; unfold px; split; [apply (proj1 Hisfinite_y); exact Hvret | assumption].
    + destruct vret; simpl; auto.

  - (* x == 0.0 = false *)
    forward.
    unfold Post_if; entailer!.
    Exists false.
    entailer!.

  - unfold Post_if; clear Post_if.
    Intros b_zx.
    rename H into H_b_zx.
    forward.
    set (Post_if2 :=
      EX b_zy: bool,
      PROP (b_zy = true -> py)
      LOCAL ( temp _zx (Vint (if b_zx then Int.one else Int.zero));
              temp _thresh (Vfloat thresh_val);
              temp _t'1 (Vfloat ldexp_val);
              temp _t'4 (Vint (if b_zy then Int.one else Int.zero));
              temp _z (Vfloat z);
              temp _x (Vfloat x);
              temp _y (Vfloat y))
      SEP ()).
    forward_if Post_if2.

    + (* y == 0.0 = true *)
      forward_call.
      Intros vret_xfin.
      rename H into H_cmp_y.
      rename H0 into Hisfinite_x.
      forward.
      unfold Post_if2; clear Post_if2; Exists vret_xfin; entailer!.
      split.
      * intro Hvret_xfin; unfold py; split; [apply (proj1 Hisfinite_x); exact Hvret_xfin | assumption].
      * destruct vret_xfin; simpl; auto.

    + (* y == 0.0 = false *)
      forward.
      unfold Post_if2; clear Post_if2; entailer!.
      Exists false.
      entailer!.

    + unfold Post_if2; clear Post_if2.
      Intros b_zy.
      rename H into H_b_zy.
      forward.
      forward_call.
      Intros vret.
      rename H into Hfin_spec.
      (* Hfin_spec : vret = true <-> is_finite (BFMA x y z) = true *)
      set (Post_t7 :=
        EX b_lb: bool,
        PROP (b_lb = true -> vret = true /\ (px \/ py \/
          Rlt_bool (bpow radix2 (emin + 2 * fprec Tdouble - 1))
            (Rabs (round radix2 (FLT_exp emin (fprec Tdouble))
              ZnearestE (FT2R x * FT2R y))) = true))
        LOCAL ( temp _zx (Vint (if b_zx then Int.one else Int.zero));
                temp _zy (Vint (if b_zy then Int.one else Int.zero));
                temp _fin (Vint (if vret then Int.one else Int.zero));
                temp _thresh (Vfloat thresh_val);
                temp _t'1 (Vfloat ldexp_val);
                temp _t'7 (Vint (if b_lb then Int.one else Int.zero));
                temp _z (Vfloat z);
                temp _x (Vfloat x);
                temp _y (Vfloat y))
        SEP ()).
      forward_if Post_t7.

      * (* fin = true *)
        set (Post_xy :=
          EX b_xy: bool,
          PROP (b_xy = true -> px \/ py)
          LOCAL ( temp _zx (Vint (if b_zx then Int.one else Int.zero));
                  temp _zy (Vint (if b_zy then Int.one else Int.zero));
                  temp _fin (Vint (if vret then Int.one else Int.zero));
                  temp _thresh (Vfloat thresh_val);
                  temp _t'1 (Vfloat ldexp_val);
                  temp _t'8 (Vint (if b_xy then Int.one else Int.zero));
                  temp _z (Vfloat z);
                  temp _x (Vfloat x);
                  temp _y (Vfloat y))
          SEP ()).
        forward_if Post_xy.

        ** (* b_zx = true *)
           forward.
           unfold Post_xy; clear Post_xy; Exists true; entailer!.
           left; apply H_b_zx.
           destruct b_zx; [reflexivity | simpl in H0; contradiction].

        ** (* b_zx = false *)
           forward.
           unfold Post_xy; clear Post_xy; Exists (orb b_zx b_zy); entailer!.
           match goal with |- ?A /\ ?B => refine (conj _ _) end.
           { intro Htrue.
             destruct (orb_prop _ _ Htrue) as [Hzx | Hzy].
             - left; apply H_b_zx; exact Hzx.
             - right; apply H_b_zy; exact Hzy. }
           { assert (b_zx = false) as Hbzx_false.
             { destruct b_zx; [exfalso; discriminate H0 | reflexivity]. }
             subst b_zx; simpl; destruct b_zy; reflexivity. }

        ** unfold Post_xy; clear Post_xy.
           Intros b_xy.
           rename H into H_b_xy.
           forward_if.

           (* b_xy = true *)
           forward.
           unfold Post_t7; clear Post_t7; entailer!.
           set (uf := Rlt_bool (bpow radix2 (emin + 2 * fprec Tdouble - 1))
             (Rabs (round radix2 (FLT_exp emin (fprec Tdouble))
               ZnearestE (FT2R x * FT2R y)))).
           Exists (andb vret (orb b_xy uf)).
           entailer!.
           assert (b_xy = true) as Hbxy_eq by (destruct b_xy; auto; simpl in H; contradiction).
           assert (vret = true) as Hvf_eq2 by (destruct vret; auto; simpl in H_b_xy; contradiction).
           subst b_xy vret.
           split; [| simpl; reflexivity].
           intro Htrue.
           destruct (andb_prop _ _ Htrue) as [Hvf Hxy_uf].
           split; [exact Hvf |].
           destruct (orb_prop _ _ Hxy_uf) as [Hxy | Huf].
           { destruct (H0 Hxy) as [Hpx | Hpy].
             { left; exact Hpx. }
             { right; left; exact Hpy. } }
           { right; right; exact Huf. }

           (* b_xy = false: check threshold *)
           forward_call.
           forward.
           forward.
           unfold Post_t7; clear Post_t7; entailer!.
           set (uf := Rlt_bool (bpow radix2 (emin + 2 * fprec Tdouble - 1))
             (Rabs (round radix2 (FLT_exp emin (fprec Tdouble))
               ZnearestE (FT2R x * FT2R y)))).
           Exists uf.
           entailer!.
           assert (vret = true) as Hvf_eq by
             (destruct vret; auto; simpl in H_b_xy; contradiction).
           assert (is_finite (ftype_of_float (Float.mul x y)) = true) as Hfin_mul.
           { rewrite is_finite_Binary, float_of_ftype_of_float.
             apply (is_finite_Float_add_l (Float.mul x y) z).
             pose proof proj1 Hfin_spec Hvf_eq as Hadd_fin.
             rewrite is_finite_Binary in Hadd_fin.
             exact Hadd_fin. }
           pose proof Float_cmp_Cle_mul x y (bpow radix2 (emin + 2 * fprec Tdouble - 1))
             (ftype_of_float thresh_val) Hfin_mul thresh_val_finite (eq_sym thresh_val_FT2R) as Hcmp.
           simpl in Hcmp; rewrite <- Hcmp; clear Hcmp.
           match goal with |- ?A /\ ?B => refine (conj _ _) end.
           { intro Htrue.
             destruct uf eqn:Huf_eq.
             - split; [exact Hvf_eq | right; right; reflexivity].
             - discriminate Htrue. }
           { unfold uf; reflexivity. }

      * (* fin = false *)
        forward.
        unfold Post_t7; clear Post_t7; entailer!.
        Exists false.
        entailer!.

      * unfold Post_t7; clear Post_t7.
        Intros b_lb.
        rename H into H_lb.
        forward.
        Exists b_lb.
        entailer!.
        destruct (H_lb eq_refl) as [Hvf Hdisj].
        unfold MulResultIsSafeForFast2Mult2, DDModels.Fast2Mult_cond2.
        split.
        { apply (proj1 Hfin_spec); exact Hvf. }
        { destruct Hdisj as [Hpx | [Hpy | Hpuf]].
          + left.
            pose proof Float_cmp_Ceq_zero_mul_FT2R_l as Hr; simpl in Hr.
            apply Hr; exact (proj2 Hpx).
          + left.
            pose proof Float_cmp_Ceq_zero_mul_FT2R_r as Hr; simpl in Hr.
            apply Hr; exact (proj2 Hpy).
          + right; apply Rlt_le, Rlt_bool_to_Rlt, no_underflow_real_from_round_mul.
            apply Rlt_bool_to_Rlt; exact Hpuf. }
Qed.

