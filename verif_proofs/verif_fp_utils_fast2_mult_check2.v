(* Copyright 2025 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.

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
