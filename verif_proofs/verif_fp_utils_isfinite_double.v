(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.

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
