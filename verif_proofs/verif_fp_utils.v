(* Copyright 2025 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* verif_fp_utils.v *)
Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.
Require Import VST.floyd.library.

Require Import Interval.Tactic.
Require Import float_acc_lems common real_extras.
From Flocq Require Import Pff2Flocq Core.

Require Import fp_utils fp_utils_specs.

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
forward_call.
Intros vret_fin.
set (Post1 := 
EX b_fin b_nrm : bool, EX t3 : int,
    PROP  ( (b_fin = true <-> is_finite (BMULT x y) = true);
            b_nrm = true <-> 
              (((FT2R x * FT2R y) = 0)%R \/
              (bpow Zaux.radix2 (emin + 2 * fprec Tdouble - 1) 
              <= Rabs (FT2R x * FT2R y))%R);
            t3 = (if b_nrm then Int.one else Int.zero))
    LOCAL ( temp _fin   (Vint (if b_fin then Int.one else Int.zero)); 
            temp _thresh (Vfloat (Binary.Bldexp (fprec Tdouble) 1024 (fprec_gt_0 Tdouble)
                  (fprec_lt_femax Tdouble) BinarySingleNaN.mode_NE
                  (Float.of_bits (Int64.repr 4607182418800017408)) 53)); 
            temp _t'3 (Vint t3);            (* guard flag *)
            temp _z (Vfloat (Float.mul x y)); temp _x (Vfloat x); temp _y (Vfloat y)) 
    SEP ()).
forward_if Post1.

-
forward.
unfold Post1; entailer!.
set (b_nrm := true).
set (t3 := tbool b_nrm).
(* because (FT2R x * FT2R y) = 0 in this branch *)
Exists vret_fin b_nrm t3.
assert (Hfin: vret_fin = true).
{ apply H. admit. }
entailer!; repeat split; intros; auto.
left. admit.

-
forward_call.  (* fabs *)
forward.
unfold Post1; entailer!.
set (b_nrm :=
  Rle_bool (bpow Zaux.radix2 (emin + 2 * fprec Tdouble - 1))
           (Rabs (FT2R x * FT2R y))).
set (t3 := tbool b_nrm).
Exists vret_fin b_nrm t3. 
entailer!; repeat split; intros; auto.

+ 
right.
apply Rle_bool_to_Rle; auto.
+
destruct H1.
exfalso. admit.
apply Rle_bool_true; auto.
+
subst t3 b_nrm.
admit.

-
unfold Post1; clear Post1.
Intros b_fin b_nrm t3.
forward.
set (Post2 := 
EX vret : bool,
    PROP  (vret = andb b_fin b_nrm)
    LOCAL ( temp _fin   (Vint (if b_fin then Int.one else Int.zero));
            temp _lb    (Vint t3);  (* unchanged lb *)
            temp _thresh (Vfloat
              (Binary.Bldexp (fprec Tdouble) 1024 (fprec_gt_0 Tdouble)
                            (fprec_lt_femax Tdouble) BinarySingleNaN.mode_NE
                            (Float.of_bits (Int64.repr 4607182418800017408)) 53));
            temp _t'3   (Vint t3); 
            temp _t'5   (Vint (if vret then Int.one else Int.zero));
            temp _z     (Vfloat (Float.mul x y));
            temp _x     (Vfloat x);
            temp _y     (Vfloat y))
    SEP ()).
forward_if Post2.

+
forward.
unfold Post2; entailer!.
Exists (b_fin && b_nrm)%bool.
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
