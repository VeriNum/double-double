(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.
Require Import DD.verif_proofs.verif_fp_utils_short_circuit.

(* dw_plus_fp_check(x, y) returns 1 only if DWPlusFP_safe_input_cond holds:
   xh, xl, y are finite, (xh, xl) is a double-word, and |xh|, |y| <= Omega/4.

   This is the single-double-word specialization of body_dw_plus_dw_check:
   it drops the (yh, yl) double-word half entirely and, in its place, checks
   the scalar bound |y| <= Omega/4 and folds finiteness of y directly into the
   return short-circuit.  The same short_circuit_*_concl helpers discharge the
   Prop-level conjuncts at each &&-join. *)
Lemma body_dw_plus_fp_check :
  semax_body Vprog Gprog f_dw_plus_fp_check dw_plus_fp_check_spec.
Proof.
  start_function.
  (* fin_xh = isfinite_double(x->s) *)
  forward. forward_call. Intros vret_fxh. rename H into Hspec_fxh. forward.
  (* fin_xl = isfinite_double(x->t) *)
  forward. forward_call. Intros vret_fxl. rename H into Hspec_fxl. forward.
  (* fin_y = isfinite_double(y); y is a parameter, so forward_call absorbs the
     result-store _fin_y (no leading field-read, unlike the fin_xh/fin_xl calls). *)
  forward_call. Intros vret_fy. rename H into Hspec_fy.

  (* --- dwx stage 1: t'4 = fin_xh && fin_xl --- *)
  set (Post_t4 :=
    EX b4 : bool,
    PROP (b4 = true -> is_finite (fst xh) = true /\ is_finite (snd xh) = true)
    LOCAL (temp _t'4 (Vint (if b4 then Int.one else Int.zero));
           temp _fin_xh (Vint (if vret_fxh then Int.one else Int.zero));
           temp _fin_xl (Vint (if vret_fxl then Int.one else Int.zero));
           temp _fin_y (Vint (if vret_fy then Int.one else Int.zero));
           temp _x x; temp _y (Vfloat y))
    SEP (data_at Tsh dword (f2val xh) x)).
  forward_if Post_t4.
  - (* fin_xh <> 0 *)
    assert (vret_fxh = true) as Hvfxh.
    { destruct vret_fxh; auto; simpl in H; rep_lia. }
    forward.
    unfold Post_t4; Exists vret_fxl; entailer!.
    split.
    + intros Hout.
      apply (short_circuit_fin_and_concl (fst xh) (snd xh) true vret_fxl vret_fxl
              Hspec_fxh Hspec_fxl eq_refl).
      exact Hout.
    + destruct vret_fxl; simpl; auto.
  - (* fin_xh = 0 *)
    forward.
    unfold Post_t4; Exists false; entailer!.
  - (* join Post_t4: DW-equality stage --- t'5 = t'4 && (x->s + x->t == x->s) *)
    unfold Post_t4; clear Post_t4.
    Intros b4; rename H into Hb4.
    set (Post_t5 :=
      EX b5 : bool,
      PROP (b5 = true -> is_finite (fst xh) = true /\
                         is_finite (snd xh) = true /\
                         double_word_prop (fst xh) (snd xh))
      LOCAL (temp _t'5 (Vint (if b5 then Int.one else Int.zero));
             temp _fin_y (Vint (if vret_fy then Int.one else Int.zero));
             temp _x x; temp _y (Vfloat y))
      SEP (data_at Tsh dword (f2val xh) x)).
    forward_if Post_t5.
    + (* b4 = true: read x->s, x->t, x->s, then t'5 = (bool)(... == ...) *)
      assert (b4 = true) as Hb4_eq.
      { destruct b4; auto; simpl in H; rep_lia. }
      forward. forward. forward. forward.
      unfold Post_t5.
      Exists (Float.cmp Ceq
                (Float.add (float_of_ftype (fst xh)) (float_of_ftype (snd xh)))
                (float_of_ftype (fst xh))).
      entailer!.
      split.
      * intros Hout.
        apply (short_circuit_dw_eq_concl (fst xh) (snd xh) true
                 (Float.cmp Ceq
                    (Float.add (float_of_ftype (fst xh)) (float_of_ftype (snd xh)))
                    (float_of_ftype (fst xh)))
                 Hb4 eq_refl).
        exact Hout.
      * destruct (Float.cmp _ _ _); simpl; auto.
    + (* b4 = false *)
      forward.
      unfold Post_t5; Exists false; entailer!.
    + (* join Post_t5: store _dwx *)
      unfold Post_t5; clear Post_t5.
      Intros b5; rename H into Hb5.
      forward.

      (* === ldexp(1.0, 1022) returns q_omega_val === *)
      forward_call.
      forward.
      (* xh_bnd: forward_call absorbs the t'12 := x->s read + fabs, then
         forward stores _xh_bnd := (fabs(x->s) <= q_omega). *)
      forward_call (fst xh).
      forward.
      (* y_bnd: fabs(y), then _y_bnd := (fabs(y) <= q_omega) *)
      forward_call (y).
      forward.

      (* === Return cascade: t'11 = dwx && fin_y && xh_bnd && y_bnd === *)
      set (bxh := Float.cmp Cle
                    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (fst xh))
                    q_omega_val).
      set (byb := Float.cmp Cle
                    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) y)
                    q_omega_val).
      set (Post_t9 :=
        EX b9 : bool,
        PROP (b9 = true -> b5 = true /\ vret_fy = true)
        LOCAL (temp _t'9 (Vint (if b9 then Int.one else Int.zero));
               temp _y_bnd (Vint (if byb then Int.one else Int.zero));
               temp _xh_bnd (Vint (if bxh then Int.one else Int.zero));
               temp _dwx (Vint (if b5 then Int.one else Int.zero));
               temp _fin_y (Vint (if vret_fy then Int.one else Int.zero));
               temp _x x; temp _y (Vfloat y))
        SEP (data_at Tsh dword (f2val xh) x)).
      forward_if Post_t9.
      * (* dwx <> 0: b5 = true; t'9 = (bool)fin_y *)
        assert (b5 = true) as Hb5_eq.
        { destruct b5; auto; simpl in H; rep_lia. }
        forward.
        unfold Post_t9; Exists vret_fy; entailer!.
        split3.
        { destruct vret_fy; reflexivity. }
        { unfold byb, q_omega_val.
          change (femax Tdouble) with 1024%Z.
          match goal with
          | |- context [Float.cmp Cle ?a ?b] =>
              destruct (Float.cmp Cle a b); reflexivity
          end. }
        { unfold bxh, q_omega_val.
          change (femax Tdouble) with 1024%Z.
          match goal with
          | |- context [Float.cmp Cle ?a ?b] =>
              destruct (Float.cmp Cle a b); reflexivity
          end. }
      * (* dwx = 0: t'9 = 0 *)
        forward. unfold Post_t9; Exists false; entailer!.
        split.
        { unfold byb, q_omega_val.
          change (femax Tdouble) with 1024%Z.
          match goal with
          | |- context [Float.cmp Cle ?a ?b] =>
              destruct (Float.cmp Cle a b); reflexivity
          end. }
        { unfold bxh, q_omega_val.
          change (femax Tdouble) with 1024%Z.
          match goal with
          | |- context [Float.cmp Cle ?a ?b] =>
              destruct (Float.cmp Cle a b); reflexivity
          end. }
      * (* join Post_t9 *)
        unfold Post_t9; clear Post_t9.
        Intros b9; rename H into Hb9.

        (* Post_t10: extend with xh_bnd *)
        set (Post_t10 :=
          EX b10 : bool,
          PROP (b10 = true -> b5 = true /\ vret_fy = true /\ bxh = true)
          LOCAL (temp _t'10 (Vint (if b10 then Int.one else Int.zero));
                 temp _y_bnd (Vint (if byb then Int.one else Int.zero));
                 temp _t'9 (Vint (if b9 then Int.one else Int.zero));
                 temp _x x; temp _y (Vfloat y))
          SEP (data_at Tsh dword (f2val xh) x)).
        forward_if Post_t10.
        ** (* t'9 <> 0: b9 = true; t'10 = (bool)xh_bnd *)
           assert (b9 = true) as Hb9_eq.
           { destruct b9; auto; simpl in H; rep_lia. }
           forward.
           unfold Post_t10; Exists bxh; entailer!.
           split.
           { intros Hout. destruct (Hb9 eq_refl); auto. }
           { unfold bxh, q_omega_val.
             change (femax Tdouble) with 1024%Z.
             match goal with
             | |- context [Float.cmp Cle ?a ?b] =>
                 destruct (Float.cmp Cle a b); reflexivity
             end. }
        ** (* t'9 = 0 *)
           forward. unfold Post_t10; Exists false; entailer!.
        ** (* join Post_t10 *)
           unfold Post_t10; clear Post_t10.
           Intros b10; rename H into Hb10.

           (* Post_t11: extend with y_bnd. Final value to return. *)
           set (Post_t11 :=
             EX b11 : bool,
             PROP (b11 = true -> b5 = true /\ vret_fy = true /\
                                 bxh = true /\ byb = true)
             LOCAL (temp _t'11 (Vint (if b11 then Int.one else Int.zero));
                    temp _x x; temp _y (Vfloat y))
             SEP (data_at Tsh dword (f2val xh) x)).
           forward_if Post_t11.
           *** (* t'10 <> 0: b10 = true; t'11 = (bool)y_bnd *)
               assert (b10 = true) as Hb10_eq.
               { destruct b10; auto; simpl in H; rep_lia. }
               forward.
               unfold Post_t11; Exists byb; entailer!.
               split.
               { intros Hout.
                 destruct (Hb10 eq_refl) as [Hb5t [Hfyt Hbxht]]. auto. }
               { unfold byb, q_omega_val.
                 change (femax Tdouble) with 1024%Z.
                 match goal with
                 | |- context [Float.cmp Cle ?a ?b] =>
                     destruct (Float.cmp Cle a b); reflexivity
                 end. }
           *** (* t'10 = 0 *)
               forward. unfold Post_t11; Exists false; entailer!.
           *** (* join Post_t11: return t'11 *)
               unfold Post_t11; clear Post_t11.
               Intros b11; rename H into Hb11.
               forward. (* return t'11 *)
               Exists b11; entailer!.
               destruct (Hb11 eq_refl) as [Hb5t [Hfyt [Hbxht Hbybt]]].
               destruct (Hb5 Hb5t) as [Hfin_xh [Hfin_xl HDWx]].
               assert (Hfin_y : is_finite y = true) by (apply (proj1 Hspec_fy); exact Hfyt).
               unfold DDConds.DWPlusFP_safe_input_cond.
               repeat (split; try assumption).
               { apply Float_cmp_Cle_bpow1022; [exact Hfin_xh|].
                 unfold bxh, q_omega_val in Hbxht. exact Hbxht. }
               { apply Float_cmp_Cle_bpow1022; [exact Hfin_y|].
                 unfold byb, q_omega_val in Hbybt. exact Hbybt. }
Qed.
