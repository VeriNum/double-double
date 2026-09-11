(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.

Lemma body_fast2_mult_exact_check: semax_body Vprog Gprog f_fast2_mult_exact_check fast2_mult_exact_check_spec.
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

  -
    forward_call.
    Intros vret.
    forward.
    unfold Post_if; Exists vret; entailer!.
    split.
    +
      intro Hvret; unfold px; split; [apply (proj1 H0); exact Hvret | assumption].
    + destruct vret; simpl; auto.

  -
    forward.
    unfold Post_if; entailer!.
    Exists false.
    entailer!.

  -
    unfold Post_if; clear Post_if.
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

    +
      forward_call.
      Intros vret_xfin.
      forward.
      unfold Post_if2; clear Post_if2; Exists vret_xfin; entailer!.
      split.
      * intro Hvret_xfin; unfold py; split; [apply (proj1 H0); exact Hvret_xfin | assumption].
      * destruct vret_xfin; simpl; auto.

    +
      forward.
      unfold Post_if2; clear Post_if2; entailer!.
      Exists false.
      entailer!.

    +
      unfold Post_if2; clear Post_if2.
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

      *

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

        **
           forward.
           unfold Post_xy; clear Post_xy; Exists true; entailer!.
           left; apply H_b_zx.
           destruct b_zx; [reflexivity | simpl in H0; contradiction].

        **
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

        **
           unfold Post_xy; clear Post_xy.
           Intros b_xy.
           rename H into H_b_xy.
           forward_if.

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
           { intro Htrue.
             destruct uf eqn:Huf_eq.
             - split; [exact Hvf_eq | right; right; reflexivity].
             - discriminate Htrue. }
           { unfold uf; reflexivity. }

      *
        forward.
        unfold Post_t7; clear Post_t7; entailer!.
        Exists false.
        entailer!.

      *

        unfold Post_t7; clear Post_t7.
        Intros b_lb.
        rename H into H_lb.
        forward.
        Exists b_lb.
        entailer!.
        destruct (H_lb eq_refl) as [Hvf Hdisj].
        unfold DDConds.Fast2Mult_exact_cond.
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
