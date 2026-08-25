(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.

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
      PROP(b_fin = true -> TwoSum_cond x y)
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
        unfold DDConds.TwoSum_cond.
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
