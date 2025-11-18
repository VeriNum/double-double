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

Definition tbool (b : bool) : int :=
  if b then Int.one else Int.zero.

(* Collect the function-API specs together into Gprog: list funspec *)
Definition Gprog : funspecs := MathASI ++ [ isfinite_double_spec; isnormal_mul_double_spec].

(* The function satisfies its API spec (with a semax-body proof) *)
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
- 
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
Lemma body_isnormal_mul_double: semax_body Vprog Gprog f_isnormal_mul_double isnormal_mul_double_spec.
Proof.
start_function.
forward.
forward_call.
forward.
forward_call.
Intros vret_fin.

set (px := is_finite y = true /\
Float.cmp Ceq x (Float.of_bits (Int64.repr 0)) = true).
set (py := is_finite x = true /\
Float.cmp Ceq y (Float.of_bits (Int64.repr 0)) = true).

set (Post_if := 
EX b_fin b_zx: bool,  
    PROP ( b_fin = true <-> is_finite (BMULT x y) = true;
           b_zx = true <-> px)
    LOCAL ( temp _fin (Vint (if b_fin then Int.one else Int.zero)); 
            temp _thresh (Vfloat
              (Float.mul (Float.of_bits (Int64.repr 4503599627370496))
              (Binary.Bldexp (fprec Tdouble) 1024 (fprec_gt_0 Tdouble)
              (fprec_lt_femax Tdouble) BinarySingleNaN.mode_NE
              (Float.of_bits (Int64.repr 4607182418800017408)) 53))); 
            temp _t'1 (Vfloat 
              (Binary.Bldexp (fprec Tdouble) 1024 (fprec_gt_0 Tdouble)
              (fprec_lt_femax Tdouble) BinarySingleNaN.mode_NE
              (Float.of_bits (Int64.repr 4607182418800017408)) 53));
            temp _t'3 (Vint (if b_zx then Int.one else Int.zero));
            temp _z (Vfloat (Float.mul x y)); 
            temp _x (Vfloat x); 
            temp _y (Vfloat y)) 
    SEP ()).
forward_if Post_if.

-
forward_call.
Intros vret.
forward.
unfold Post_if; entailer!.
set (b_zx:= eqb (is_finite y) true).
Exists vret_fin b_zx.
entailer!; repeat split; intros; auto.
subst b_zx.
destruct H1, vret. 
specialize (H1 eq_refl). 
rewrite H1; simpl; auto.
destruct (is_finite y); simpl; auto.
subst b_zx.
destruct H2 as [H2 _]; rewrite H2. 
simpl; auto.
subst b_zx. 
destruct vret, H1.
specialize (H1 eq_refl); rewrite H1. simpl; auto. 
destruct (is_finite y).
specialize (H2 eq_refl); discriminate.
simpl; auto. 

-
forward.
unfold Post_if; entailer!.
set (b_zx:= eqb (Float.cmp Ceq x (Float.of_bits (Int64.repr 0))) true).
Exists vret_fin b_zx.
entailer!; repeat split; intros; auto.
subst b_zx.
exfalso.
apply eqb_prop in H1; 
rewrite H1 in H0; discriminate.
subst b_zx.
apply eqb_prop in H1; auto.
subst b_zx. 
exfalso.
destruct H1 as [_ H1].
rewrite H1 in H0; discriminate.
subst b_zx. 
destruct (Float.cmp Ceq x (Float.of_bits (Int64.repr 0))).
discriminate.
simpl; auto.

-
unfold Post_if; clear Post_if.
Intros b_fin b_zx.
forward.
set (Post_if := 
EX b_zy: bool,
    PROP (  b_zy = true <-> py)
    LOCAL ( temp _zx (Vint (if b_zx then Int.one else Int.zero));
            temp _fin  (Vint (if b_fin then Int.one else Int.zero));
            temp _thresh (Vfloat
              (Float.mul (Float.of_bits (Int64.repr 4503599627370496))
              (Binary.Bldexp (fprec Tdouble) 1024 (fprec_gt_0 Tdouble)
              (fprec_lt_femax Tdouble) BinarySingleNaN.mode_NE
              (Float.of_bits (Int64.repr 4607182418800017408)) 53))); 
            temp _t'1 (Vfloat 
              (Binary.Bldexp (fprec Tdouble) 1024 (fprec_gt_0 Tdouble)
              (fprec_lt_femax Tdouble) BinarySingleNaN.mode_NE
              (Float.of_bits (Int64.repr 4607182418800017408)) 53));
            temp _t'3 (Vint (if b_zx then Int.one else Int.zero));
            temp _t'5 (Vint (if b_zy then Int.one else Int.zero));
            temp _z (Vfloat (Float.mul x y)); 
            temp _x (Vfloat x); 
            temp _y (Vfloat y)) 
    SEP ()).
forward_if Post_if.

+
forward_call.
Intros vret_xfin.
forward.
unfold Post_if; clear Post_if; entailer!.
set (b_zy := (eqb (is_finite x) true)).
Exists b_zy. 
entailer!.
subst b_zy.
repeat split; auto.
apply eqb_prop; auto.
intros [ A _].
rewrite A; simpl; auto.
destruct vret_xfin; auto.
destruct (is_finite x); simpl; auto;
exfalso; destruct H3 as [H3 _].
specialize (H3 eq_refl); auto.
destruct (is_finite x); simpl; auto;
exfalso; destruct H3 as [_ H3].
specialize (H3 eq_refl); auto.

+
forward.
unfold Post_if; clear Post_if; entailer!.
set (b_zy := 
  (eqb (Float.cmp Ceq y (Float.of_bits (Int64.repr 0))) true)).
Exists b_zy. 
entailer!.
subst b_zy py.
repeat split; auto.
apply eqb_prop; auto.
exfalso.
apply eqb_prop in H3; 
rewrite H3 in H2; discriminate.
apply eqb_prop in H3; 
rewrite H3 in H2; discriminate.
intros [ _ A ].
rewrite A; simpl; auto.
destruct 
(Float.cmp Ceq y (Float.of_bits (Int64.repr 0)));
simpl; auto; discriminate.

+
unfold Post_if; clear Post_if.
Intros b_zy.
forward.
set (puf := ((FT2R x * FT2R y)%R = 0%R \/
    (bpow Zaux.radix2 (emin + 2 * fprec Tdouble - 1) <= 
    Rabs (FT2R x * FT2R y))%R)).
set (Post_if := 
EX b_lb: bool,
    PROP (  b_lb = true <-> py /\ px /\ puf)
    LOCAL ( temp _zx (Vint (if b_zx then Int.one else Int.zero));
            temp _fin  (Vint (if b_fin then Int.one else Int.zero));
            temp _thresh (Vfloat
              (Float.mul (Float.of_bits (Int64.repr 4503599627370496))
              (Binary.Bldexp (fprec Tdouble) 1024 (fprec_gt_0 Tdouble)
              (fprec_lt_femax Tdouble) BinarySingleNaN.mode_NE
              (Float.of_bits (Int64.repr 4607182418800017408)) 53))); 
            temp _t'1 (Vfloat 
              (Binary.Bldexp (fprec Tdouble) 1024 (fprec_gt_0 Tdouble)
              (fprec_lt_femax Tdouble) BinarySingleNaN.mode_NE
              (Float.of_bits (Int64.repr 4607182418800017408)) 53));
            temp _t'3 (Vint (if b_zx then Int.one else Int.zero));
            temp _t'5 (Vint (if b_zy then Int.one else Int.zero));            temp _z (Vfloat (Float.mul x y)); 
            temp _x (Vfloat x); 
            temp _y (Vfloat y))
    SEP ()).
forward_if Post_if.

*
forward.
unfold Post_if; entailer!; clear Post_if.
Exists (b_zx && b_zy)%bool.
entailer!.
destruct b_fin, b_nrm; simpl; auto.
exfalso. admit.

+
forward.
unfold Post2.
Exists (b_fin && b_nrm)%bool. 
entailer!.
destruct b_fin; try discriminate.
rewrite andb_false_l; auto.

+ 
unfold Post2.
Intros vret.
forward.
Exists (b_fin && b_nrm)%bool.
entailer!.
split; intros; destruct b_fin;
destruct b_nrm; simpl in *; try discriminate; auto.

*
admit.
*
apply H1.
destruct H2 as [ _ H2 ]; apply H2.
*
apply H0.
destruct H2 as [ H2 _ ]; apply H2.
*
apply H0. 
destruct H2 as [ H2 _ ]; apply H2.
Admitted.
