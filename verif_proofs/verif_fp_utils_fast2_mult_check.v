(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.

(* fast2_mult_check(x, y) returns 1 only if Fast2Mult_cond x y holds, i.e.,
   x*y is finite and either the real product is zero or it is at least
   bpow 2 (emin + 2*p - 1) (the Fast2Mult underflow safety threshold).

   Proof structure: three intermediate PROP invariants, each carrying only
   the forward direction (b = true -> P) since the spec postcondition needs
   only that implication.
     Post_if  : captures C variable `zx = (x == 0.0) && isfinite(y)`.
     Post_if2 : captures C variable `zy = (y == 0.0) && isfinite(x)`.
     Post_t7  : captures the final return value after the threshold check.
   At the join point Post_t7 discharges Fast2Mult_cond using
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

      * (* Join: discharge Fast2Mult_cond from Post_t7.
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
        unfold DDModels.Fast2Mult_cond.
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
