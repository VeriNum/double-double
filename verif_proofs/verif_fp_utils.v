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
Definition Gprog : funspecs := MathASI ++
  [ isfinite_double_spec; fast2_mult_check_spec; fast2_mult_check2_spec;
    two_sum_check_spec; fast2_sum_check_spec ].

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

(* fast2_mult_check(x, y) returns 1 only if Fast2Mult_cond x y holds, i.e.,
   x*y is finite and either the real product is zero or it is at least
   bpow 2 (emin + 2*p - 1) (the Fast2Mult underflow safety threshold).

   Proof structure: three intermediate PROP invariants, each carrying only
   the forward direction (b = true -> P) since the spec postcondition needs
   only that implication.
     Post_if  : captures C variable `zx = (x == 0.0) && isfinite(y)`.
     Post_if2 : captures C variable `zy = (y == 0.0) && isfinite(x)`.
     Post_t7  : captures the final return value after the threshold check.
   At the join point Post_t7 discharges MulResultIsSafeForFast2Mult using
   Hfin_spec (finiteness of x*y), Float_cmp_Ceq_zero_mul_FT2R_{l,r} (zero
   product from the C zero-checks), and no_underflow_real_from_round_mul
   (above-threshold product from the fabs comparison). *)
Lemma body_fast2_mult_check: semax_body Vprog Gprog f_fast2_mult_check fast2_mult_check_spec.
Proof.
  start_function.
  (* z = x * y;  thresh = DBL_MIN * ldexp(1.0,53);  fin = isfinite_double(z) *)
  forward.
  forward_call.
  forward.
  forward_call.
  Intros vret_fin.
  (* Hfin_spec : vret_fin = true <-> is_finite (BMULT x y) = true *)
  rename H into Hfin_spec.

  (* px / py: the zero-product witnesses carried through the boolean short-circuits.
     px asserts x == 0.0 (and y is finite); py asserts y == 0.0 (and x is finite).
     Either witness allows us to conclude FT2R x * FT2R y = 0 at the join point. *)
  set (px := is_finite y = true /\
    Float.cmp Ceq x (Float.of_bits (Int64.repr 0)) = true).
  set (py := is_finite x = true /\
    Float.cmp Ceq y (Float.of_bits (Int64.repr 0)) = true).

  (* Post_if: join point after `zx = (x == 0.0) && isfinite(y)`.
     b_zx = true implies the real product is zero because x is zero. *)
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

  - (* x == 0.0 = true: call isfinite(y) and witness b_zx with its return value. *)
    forward_call.
    Intros vret.
    forward.
    unfold Post_if; Exists vret; entailer!.
    split.
    + (* PROP forward direction: H0 is the isfinite spec iff; assumption is the branch cond. *)
      intro Hvret; unfold px; split; [apply (proj1 H0); exact Hvret | assumption].
    + destruct vret; simpl; auto.

  - (* x == 0.0 = false: short-circuit gives 0; PROP is vacuously satisfied. *)
    forward.
    unfold Post_if; entailer!.
    Exists false.
    entailer!.

  - (* After the zx branch: collect b_zx and move to the zy check. *)
    unfold Post_if; clear Post_if.
    Intros b_zx.
    rename H into H_b_zx.
    forward.
    (* Post_if2: join point after `zy = (y == 0.0) && isfinite(x)`. *)
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

    + (* y == 0.0 = true: call isfinite(x) and witness b_zy with its return value. *)
      forward_call.
      Intros vret_xfin.
      forward.
      unfold Post_if2; clear Post_if2; Exists vret_xfin; entailer!.
      split.
      * intro Hvret_xfin; unfold py; split; [apply (proj1 H0); exact Hvret_xfin | assumption].
      * destruct vret_xfin; simpl; auto.

    + (* y == 0.0 = false: short-circuit gives 0. *)
      forward.
      unfold Post_if2; clear Post_if2; entailer!.
      Exists false.
      entailer!.

    + (* After the zy branch: proceed to the threshold comparison. *)
      unfold Post_if2; clear Post_if2.
      Intros b_zy.
      rename H into H_b_zy.
      forward.
      (* Post_t7: join point after `return fin && ((zx || zy) || thresh < fabs(z))`.
         b_lb = true implies (1) x*y is finite and (2) the real product is either
         zero (via px or py) or above the underflow threshold (via uf). *)
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

      * (* fin = true: evaluate the zx || zy short-circuit. *)
        (* Post_xy: join point for `zx || zy`. *)
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

        ** (* b_zx = true: zx || zy is true; witness Post_xy with true. *)
           forward.
           unfold Post_xy; clear Post_xy; Exists true; entailer!.
           left; apply H_b_zx.
           destruct b_zx; [reflexivity | simpl in H0; contradiction].

        ** (* b_zx = false: evaluate zy; witness with b_zx || b_zy. *)
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

        ** (* After zx || zy: check thresh < fabs(z). *)
           unfold Post_xy; clear Post_xy.
           Intros b_xy.
           rename H into H_b_xy.
           forward_if.

           (* b_xy = true: zero product confirmed; no threshold check needed. *)
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

           (* b_xy = false: call fabs, compare against thresh.
              Float_cmp_Cle_mul connects the C float comparison thresh < fabs(z)
              to Rlt_bool on the rounded real product. *)
           forward_call.
           forward.
           forward.
           unfold Post_t7; clear Post_t7; entailer!.
           set (uf := Rlt_bool (bpow radix2 (emin + 2 * fprec Tdouble - 1))
             (Rabs (round radix2 (FLT_exp emin (fprec Tdouble))
               ZnearestE (FT2R x * FT2R y)))).
           Exists uf.
           entailer!.
           (* Derive is_finite (x*y) from fin = true (vret_fin = true) via Hfin_spec. *)
           assert (vret_fin = true) as Hvf_eq by
             (destruct vret_fin; auto; simpl in H_b_xy; contradiction).
           assert (is_finite (ftype_of_float (Float.mul x y)) = true) as Hfin_mul by
             (rewrite is_finite_Binary; rewrite float_of_ftype_of_float;
              apply Hfin_spec; exact Hvf_eq).
           pose proof Float_cmp_Cle_mul x y (bpow radix2 (emin + 2 * fprec Tdouble - 1))
             (ftype_of_float thresh_val) Hfin_mul thresh_val_finite (eq_sym thresh_val_FT2R) as Hcmp.
           simpl in Hcmp; rewrite <- Hcmp; clear Hcmp.
           match goal with |- ?A /\ ?B => refine (conj _ _) end.
           { intro Htrue.
             destruct uf eqn:Huf_eq.
             - split; [exact Hvf_eq | right; right; reflexivity].
             - discriminate Htrue. }
           { unfold uf; reflexivity. }

      * (* fin = false: return value is 0; PROP is vacuously satisfied. *)
        forward.
        unfold Post_t7; clear Post_t7; entailer!.
        Exists false.
        entailer!.

      * (* Join: discharge MulResultIsSafeForFast2Mult from Post_t7.
           b_lb = true gives finiteness and the disjunction of safety witnesses.
           - px: Float_cmp_Ceq_zero_mul_FT2R_l gives FT2R x * FT2R y = 0.
           - py: Float_cmp_Ceq_zero_mul_FT2R_r gives FT2R x * FT2R y = 0.
           - uf: no_underflow_real_from_round_mul gives the Rabs lower bound. *)
        unfold Post_t7; clear Post_t7.
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

(* fast2_mult_check2(x, y, z) returns 1 only if Fast2Mult_cond2 x y z holds,
   i.e., x*y + z (as compiled by CompCert) is finite and either the real
   product x*y is zero or it is at least bpow 2 (emin + 2*p - 1).

   Key difference from fast2_mult_check: the finiteness check calls
   isfinite_double(fma(x,y,z)).  CompCert lowers fma(x,y,z) to two sequential
   IEEE operations (Float.mul followed by Float.add), not a fused FMA.
   Fast2Mult_cond2 therefore uses BPLUS (BMULT x y) z, not BFMA x y z.
   To derive is_finite (x*y) from is_finite (x*y + z), the proof uses
   is_finite_Float_add_l (finiteness of a sum implies finiteness of the left
   addend).

   The invariant structure mirrors fast2_mult_check; see that proof for the
   detailed explanation of Post_if, Post_if2, Post_xy, and Post_t7. *)
Lemma body_fast2_mult_check2: semax_body Vprog Gprog f_fast2_mult_check2 fast2_mult_check2_spec.
Proof.
  start_function.
  (* thresh = DBL_MIN * ldexp(1.0,53) *)
  forward_call.
  forward.

  set (px := is_finite y = true /\
    Float.cmp Ceq x (Float.of_bits (Int64.repr 0)) = true).
  set (py := is_finite x = true /\
    Float.cmp Ceq y (Float.of_bits (Int64.repr 0)) = true).

  (* Post_if: join point after `zx = (x == 0.0) && isfinite(y)`. *)
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

  - (* x == 0.0 = true: call isfinite(y); witness b_zx with its return value. *)
    forward_call.
    Intros vret.
    rename H into H_cmp_x.
    rename H0 into Hisfinite_y.
    forward.
    unfold Post_if; Exists vret; entailer!.
    split.
    + intro Hvret; unfold px; split; [apply (proj1 Hisfinite_y); exact Hvret | assumption].
    + destruct vret; simpl; auto.

  - (* x == 0.0 = false: short-circuit gives 0. *)
    forward.
    unfold Post_if; entailer!.
    Exists false.
    entailer!.

  - (* After zx branch: collect b_zx and proceed to the zy check. *)
    unfold Post_if; clear Post_if.
    Intros b_zx.
    rename H into H_b_zx.
    forward.
    (* Post_if2: join point after `zy = (y == 0.0) && isfinite(x)`. *)
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

    + (* y == 0.0 = true: call isfinite(x); witness b_zy with its return value. *)
      forward_call.
      Intros vret_xfin.
      rename H into H_cmp_y.
      rename H0 into Hisfinite_x.
      forward.
      unfold Post_if2; clear Post_if2; Exists vret_xfin; entailer!.
      split.
      * intro Hvret_xfin; unfold py; split; [apply (proj1 Hisfinite_x); exact Hvret_xfin | assumption].
      * destruct vret_xfin; simpl; auto.

    + (* y == 0.0 = false: short-circuit gives 0. *)
      forward.
      unfold Post_if2; clear Post_if2; entailer!.
      Exists false.
      entailer!.

    + (* After zy branch: call isfinite(fma(x,y,z)), then check threshold. *)
      unfold Post_if2; clear Post_if2.
      Intros b_zy.
      rename H into H_b_zy.
      forward.
      forward_call.
      Intros vret.
      (* Hfin_spec : vret = true <-> is_finite (BPLUS (BMULT x y) z) = true
         (fma compiled by CompCert as two sequential IEEE ops: mul then add). *)
      rename H into Hfin_spec.
      (* Post_t7: captures the return value of the entire boolean expression. *)
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

      * (* fin = true: evaluate zx || zy. *)
        (* Post_xy: join point for `zx || zy`. *)
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

        ** (* b_zx = true: witness Post_xy with true. *)
           forward.
           unfold Post_xy; clear Post_xy; Exists true; entailer!.
           left; apply H_b_zx.
           destruct b_zx; [reflexivity | simpl in H0; contradiction].

        ** (* b_zx = false: witness with b_zx || b_zy. *)
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

        ** (* After zx || zy: check thresh < fabs(x*y). *)
           unfold Post_xy; clear Post_xy.
           Intros b_xy.
           rename H into H_b_xy.
           forward_if.

           (* b_xy = true: zero product confirmed; no threshold check needed. *)
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

           (* b_xy = false: call fabs, compare against thresh.
              is_finite_Float_add_l extracts is_finite (x*y) from
              is_finite (x*y + z), needed by Float_cmp_Cle_mul. *)
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
           (* Extract is_finite (x*y) from is_finite (x*y + z) via Hfin_spec. *)
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

      * (* fin = false: return value is 0. *)
        forward.
        unfold Post_t7; clear Post_t7; entailer!.
        Exists false.
        entailer!.

      * (* Join: discharge MulResultIsSafeForFast2Mult2 from Post_t7.
           proj1 Hfin_spec converts vret = true to is_finite (BPLUS (BMULT x y) z) = true. *)
        unfold Post_t7; clear Post_t7.
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

(* fast2_sum_check(x,y) returns 1 only if Fast2Sum_cond x y holds:
   (a+b) is finite (derived by isfinite_double(s)), and |b| ≤ |a| (by fabs comparison).
   Because the C uses short-circuit &&, fabs is called only when fin=true,
   so is_finite x and is_finite y can be derived from is_finite (BPLUS x y)
   via is_finite_Float_add_l / is_finite_Float_add_r. *)
Lemma body_fast2_sum_check: semax_body Vprog Gprog f_fast2_sum_check fast2_sum_check_spec.
Proof.
  start_function.
  forward. (* s = x + y *)
  forward_call. (* fin = isfinite_double(s): Scall + Sset _fin handled together *)
  Intros vret_fin.
  rename H into Hfin_spec.
  set (Post_ret :=
    EX b_r : bool,
    PROP(b_r = true -> SumResultIsSafeForFast2Sum x y)
    LOCAL(temp _t'2 (Vint (if b_r then Int.one else Int.zero));
          temp _a (Vfloat (float_of_ftype x));
          temp _b (Vfloat (float_of_ftype y)))
    SEP()).
  forward_if Post_ret.
  - (* fin ≠ 0: vret_fin = true, so BPLUS x y is finite *)
    assert (vret_fin = true) as Hvf.
    { destruct vret_fin; auto; simpl in H; rep_lia. }
    assert (is_finite (BPLUS x y) = true) as Hfin_sum.
    { apply (proj1 Hfin_spec); exact Hvf. }
    rewrite is_finite_Binary in Hfin_sum.
    assert (is_finite x = true) as Hx_fin.
    { rewrite is_finite_Binary.
      apply is_finite_Float_add_l with (b := float_of_ftype y).
      exact Hfin_sum. }
    assert (is_finite y = true) as Hy_fin.
    { rewrite is_finite_Binary.
      apply is_finite_Float_add_r with (a := float_of_ftype x).
      exact Hfin_sum. }
    forward_call (y). (* t'3 = fabs(b) *)
    forward_call (x). (* t'4 = fabs(a) *)
    forward. (* t'2 = (bool)(t'3 <= t'4) *)
    unfold Post_ret; clear Post_ret.
    Exists (Float.cmp Cle
      (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype y))
      (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype x))).
    entailer!.
    split.
    + intro Hcmp_true.
      unfold SumResultIsSafeForFast2Sum, DDModels.Fast2Sum_cond.
      split.
      { rewrite is_finite_Binary; exact Hfin_sum. }
      { apply Float_cmp_Cle_abs; [exact Hx_fin | exact Hy_fin | exact Hcmp_true]. }
    + change (femax Tdouble) with 1024%Z;
      change (float_of_ftype y) with y;
      change (float_of_ftype x) with x;
      generalize (Float.cmp Cle
        (Binary.Babs (fprec Tdouble) 1024
          (abs_nan (fprec Tdouble) 1024 (fprec_gt_one Tdouble)) y)
        (Binary.Babs (fprec Tdouble) 1024
          (abs_nan (fprec Tdouble) 1024 (fprec_gt_one Tdouble)) x)).
      intro b_cmp; destruct b_cmp; reflexivity.
  - (* fin = 0: t'2 = 0 *)
    forward. (* t'2 = 0 *)
    unfold Post_ret; clear Post_ret; Exists false; entailer!.
  - (* join: return t'2 *)
    unfold Post_ret; clear Post_ret.
    Intros b_r.
    rename H into H_r.
    forward. (* return t'2 *)
    Exists b_r; entailer!.
Qed.

(* two_sum_check(x,y) returns 1 only if TwoSum_cond x y holds:
   (x+y) finite, (x-y) finite, and |y| < pred(2^1024) = DBL_MAX.
   Short-circuit && ensures fabs(b) is called only after both fin checks pass,
   at which point is_finite y follows from is_finite (BPLUS x y). *)
Lemma body_two_sum_check: semax_body Vprog Gprog f_two_sum_check two_sum_check_spec.
Proof.
  start_function.
  forward_call. (* fin_sum = isfinite_double(x+y) *)
  Intros vret_sum.
  rename H into Hfin_sum_spec.
  forward_call. (* fin_diff = isfinite_double(x-y) *)
  Intros vret_diff.
  rename H into Hfin_diff_spec.
  (* first short-circuit: if fin_sum then t'3 = (bool)fin_diff else t'3 = 0 *)
  set (Post_if :=
    EX b_fd : bool,
    PROP(b_fd = true -> is_finite (BPLUS x y) = true /\
                        is_finite (BMINUS x y) = true)
    LOCAL(temp _fin_sum (Vint (if vret_sum then Int.one else Int.zero));
          temp _fin_diff (Vint (if vret_diff then Int.one else Int.zero));
          temp _t'3 (Vint (if b_fd then Int.one else Int.zero));
          temp _a (Vfloat (float_of_ftype x));
          temp _b (Vfloat (float_of_ftype y)))
    SEP()).
  forward_if Post_if.
  - (* fin_sum ≠ 0: vret_sum = true *)
    assert (vret_sum = true) as Hvs.
    { destruct vret_sum; auto; simpl in H; rep_lia. }
    forward.
    unfold Post_if; Exists vret_diff; entailer!.
    split.
    + intro Hvd.
      split.
      { apply (proj1 Hfin_sum_spec); auto. }
      { apply (proj1 Hfin_diff_spec); auto. }
    + destruct vret_diff; simpl; auto.
  - (* fin_sum = 0: t'3 = 0 *)
    forward.
    unfold Post_if; Exists false; entailer!.
  - (* after first short-circuit: check |b| < DBL_MAX *)
    unfold Post_if; clear Post_if.
    Intros b_fd.
    rename H into H_b_fd.
    set (Post_final :=
      EX b_fin : bool,
      PROP(b_fin = true -> SumResultIsSafeForTwoSum x y)
      LOCAL(temp _t'4 (Vint (if b_fin then Int.one else Int.zero));
            temp _a (Vfloat (float_of_ftype x));
            temp _b (Vfloat (float_of_ftype y)))
      SEP()).
    forward_if Post_final.
    + (* t'3 ≠ 0: b_fd = true, so both fin checks pass *)
      assert (b_fd = true) as Hbfd_eq.
      { destruct b_fd; auto; simpl in H; rep_lia. }
      destruct (H_b_fd Hbfd_eq) as [Hfin_plus Hfin_minus].
      assert (is_finite y = true) as Hy_fin.
      { rewrite is_finite_Binary.
        apply is_finite_Float_add_r with (a := float_of_ftype x).
        rewrite is_finite_Binary in Hfin_plus; exact Hfin_plus. }
      forward_call (y). (* t'5 = fabs(b) *)
      forward. (* t'4 = (bool)(t'5 < DBL_MAX) *)
      unfold Post_final; clear Post_final.
      Exists (Float.cmp Clt
        (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype y))
        dbl_max_val).
      entailer!.
      split.
      { intro Hcmp_true.
        unfold SumResultIsSafeForTwoSum, DDModels.TwoSum_cond.
        split; [exact Hfin_plus | split; [exact Hfin_minus |]].
        apply Float_cmp_Clt_dbl_max; [exact Hy_fin | exact Hcmp_true]. }
      { change (femax Tdouble) with 1024%Z;
        change (float_of_ftype y) with y;
        unfold dbl_max_val;
        generalize (Float.cmp Clt
          (Binary.Babs (fprec Tdouble) 1024
            (abs_nan (fprec Tdouble) 1024 (fprec_gt_one Tdouble)) y)
          (Float.of_bits (Int64.repr 9218868437227405311))).
        intro b_cmp; destruct b_cmp; reflexivity. }
    + (* t'3 = 0: t'4 = 0 *)
      forward. (* t'4 = 0 *)
      unfold Post_final; clear Post_final; Exists false; entailer!.
    + (* join: return t'4 *)
      unfold Post_final; clear Post_final.
      Intros b_fin.
      rename H into H_fin.
      forward. (* return t'4 *)
      Exists b_fin; entailer!.
Qed.

