(* Copyright 2025 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.

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
      { (* Fast2Sum_cond's disjunction: take the ulp leg via Ulp.ulp_le. *)
        left.
        apply Ulp.ulp_le.
        - apply BinarySingleNaN.fexp_correct; apply fprec_gt_0.
        - apply FLT_exp_monotone.
        - apply Float_cmp_Cle_abs; [exact Hx_fin | exact Hy_fin | exact Hcmp_true]. }
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
