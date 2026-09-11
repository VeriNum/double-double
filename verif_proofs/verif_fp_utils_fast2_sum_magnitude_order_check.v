(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.

Lemma body_fast2_sum_magnitude_order_check: semax_body Vprog Gprog f_fast2_sum_magnitude_order_check fast2_sum_magnitude_order_check_spec.
Proof.
  start_function.
  forward_call.
  Intros vret_fin.
  rename H into Hfin_spec.
  set (Post_ret :=
    EX b_r : bool,
    PROP(b_r = true -> Fast2Sum_magnitude_order_cond x y)
    LOCAL(temp _t'1 (Vint (if vret_fin then Int.one else Int.zero));
          temp _t'2 (Vint (if b_r then Int.one else Int.zero));
          temp _a (Vfloat (float_of_ftype x));
          temp _b (Vfloat (float_of_ftype y)))
    SEP()).
  forward_if Post_ret.
  -
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
    forward_call (y).
    forward_call (x).
    forward.
    unfold Post_ret; clear Post_ret.
    Exists (Float.cmp Cle
      (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype y))
      (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (float_of_ftype x))).
    entailer!.
    split.
    + intro Hcmp_true.
      unfold Fast2Sum_magnitude_order_cond.
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
  -
    forward.
    unfold Post_ret; clear Post_ret; Exists false; entailer!.
  -
    unfold Post_ret; clear Post_ret.
    Intros b_r.
    rename H into H_r.
    forward.
    Exists b_r; entailer!.
Qed.
