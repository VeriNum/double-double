(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.
Require Import DD.verif_proofs.verif_fp_utils_short_circuit.
Require Import DD.accuracy_proofs.dw_opps.DWMulFP_acc.
Require Import DD.accuracy_proofs.dw_opps.DWMulDW_acc.

(* Discharge the residual `Vint (if b then Int.one else Int.zero) =
   Vint (Int.repr (Z.b2z c))` LOCAL-matching goals that entailer! spins off
   whenever a forward_if invariant carries the xh_bnd / y_bnd comparison temps.
   Each such temp equals a `Float.cmp Cle ...` value; case-splitting the
   comparison closes both sides by reflexivity. *)
(* Int.repr (Z.b2z b) is exactly the if-form used in the invariants. *)
Lemma Vint_b2z_if : forall b : bool,
  Vint (Int.repr (Z.b2z b)) = Vint (if b then Int.one else Int.zero).
Proof. intros [|]; reflexivity. Qed.

(* The stored xh_bnd / y_bnd temp is `Vint (Int.repr (Z.b2z c))` where c is the
   raw Float.cmp Cle comparison; the invariant carries `Vint (if bxh ..)` with
   bxh := that same comparison (up to convertibility of q_sqrt_val / femax).
   Rewriting both to the b2z form lets `reflexivity` close them by conversion. *)
Ltac cmp_val_eq :=
  rewrite Vint_b2z_if; reflexivity.

Ltac fix_cmp_locals :=
  solve [ repeat (first [ reflexivity | cmp_val_eq
                        | (intro; discriminate) | split ]) ].

(* dw_mult_fp_check(x, y) returns 1 only if DWTimesFP_cond holds:
   xh, xl, y finite, (xh, xl) a double-word, xh*y is either 0 or above the
   Fast2Mult underflow threshold, and |xh|,|y| <= 2^(femax/2-1).

   Structure mirrors body_dw_plus_dw_check (the dwx cascade, the ldexp bound
   constant, the fabs+<= magnitude checks, and the final return && cascade)
   together with body_fast2_mult_check (the mult_safe short-circuit
   (zxh || zy) || thresh < fabs(z)). Raw facts are carried through each
   forward_if and DWTimesFP_cond is discharged only at the final return join. *)
Lemma body_dw_mult_fp_check :
  semax_body Vprog Gprog f_dw_mult_fp_check dw_mult_fp_check_spec.
Proof.
  start_function.
  (* fin_xh = isfinite_double(x->s) *)
  forward. forward_call. Intros vret_fxh. rename H into Hspec_fxh. forward.
  (* fin_xl = isfinite_double(x->t) *)
  forward. forward_call. Intros vret_fxl. rename H into Hspec_fxl. forward.
  (* fin_y = isfinite_double(y). forward_call folds the following Sset _fin_y. *)
  forward_call. Intros vret_fy. rename H into Hspec_fy. abbreviate_semax.

  (* --- dwx: (fin_xh && fin_xl) && (x->s + x->t == x->s) ---
     if A sets _t'4 = fin_xh && fin_xl; if B (guard _t'4) sets _t'5. *)
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
  - assert (vret_fxh = true) as Hvfxh.
    { destruct vret_fxh; auto; simpl in H; rep_lia. }
    forward.
    unfold Post_t4; Exists vret_fxl; entailer!.
    split.
    + intros Hout.
      apply (short_circuit_fin_and_concl (fst xh) (snd xh) true vret_fxl vret_fxl
              Hspec_fxh Hspec_fxl eq_refl).
      exact Hout.
    + destruct vret_fxl; simpl; auto.
  - forward.
    unfold Post_t4; Exists false; entailer!.
  - unfold Post_t4; clear Post_t4.
    Intros b4; rename H into Hb4.
    set (Post_t5 :=
      EX b5 : bool,
      PROP (b5 = true -> is_finite (fst xh) = true /\
                         is_finite (snd xh) = true /\
                         double_word_prop (fst xh) (snd xh))
      LOCAL (temp _t'5 (Vint (if b5 then Int.one else Int.zero));
             temp _fin_xh (Vint (if vret_fxh then Int.one else Int.zero));
             temp _fin_xl (Vint (if vret_fxl then Int.one else Int.zero));
             temp _fin_y (Vint (if vret_fy then Int.one else Int.zero));
             temp _x x; temp _y (Vfloat y))
      SEP (data_at Tsh dword (f2val xh) x)).
    forward_if Post_t5.
    + assert (b4 = true) as Hb4_eq.
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
    + forward.
      unfold Post_t5; Exists false; entailer!.
    + unfold Post_t5; clear Post_t5.
      Intros b6; rename H into Hb6.
      forward.  (* store dwx *)

      (* === q_sqrt = ldexp(1.0, 511) = q_sqrt_val === *)
      forward_call.
      forward.
      (* xh_bnd = (fabs(x->s) <= q_sqrt) *)
      forward_call (fst xh). forward.
      (* y_bnd = (fabs(y) <= q_sqrt) *)
      forward_call y. forward.
      (* z = x->s * y *)
      forward. forward.
      (* thresh = 0x0010000000000000 * ldexp(1.0, 53) = thresh_val *)
      forward_call. forward.

      set (bxh := Float.cmp Cle
                    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble))
                                 (fst xh))
                    q_sqrt_val).
      set (byh := Float.cmp Cle
                    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble))
                                 y)
                    q_sqrt_val).
      set (px := Float.cmp Ceq (float_of_ftype (fst xh)) (Float.of_bits (Int64.repr 0)) = true
                 /\ is_finite y = true).
      set (py := Float.cmp Ceq (float_of_ftype y) (Float.of_bits (Int64.repr 0)) = true
                 /\ is_finite (fst xh) = true).

      (* --- zxh: (x->s == 0.0) && fin_y --- *)
      forward.
      set (Post_zxh :=
        EX b_zxh : bool,
        PROP (b_zxh = true -> px)
        LOCAL (temp _t'10 (Vint (if b_zxh then Int.one else Int.zero));
               temp _thresh (Vfloat thresh_val);
               temp _z (Vfloat (Float.mul (float_of_ftype (fst xh)) y));
               temp _q_sqrt (Vfloat q_sqrt_val);
               temp _xh_bnd (Vint (if bxh then Int.one else Int.zero));
               temp _y_bnd (Vint (if byh then Int.one else Int.zero));
               temp _fin_xh (Vint (if vret_fxh then Int.one else Int.zero));
               temp _fin_y (Vint (if vret_fy then Int.one else Int.zero));
               temp _dwx (Vint (if b6 then Int.one else Int.zero));
               temp _x x; temp _y (Vfloat y))
        SEP (data_at Tsh dword (f2val xh) x)).
      forward_if Post_zxh.
      * (* x->s == 0.0 : t'10 = (bool)fin_y *)
        forward.
        unfold Post_zxh; Exists vret_fy; entailer!.
        refine (conj _ (conj _ (conj _ _))).
        { intros Hout. unfold px. split;
            [ assumption | apply (proj1 Hspec_fy); exact Hout ]. }
        { destruct vret_fy; reflexivity. }
        { cmp_val_eq. }
        { cmp_val_eq. }
      * (* x->s != 0.0 : t'10 = 0 *)
        forward.
        unfold Post_zxh; Exists false; entailer!; try fix_cmp_locals.
      * unfold Post_zxh; clear Post_zxh.
        Intros b_zxh; rename H into Hb_zxh.
        forward.  (* store zxh *)

        (* --- zy: (y == 0.0) && fin_xh --- *)
        set (Post_zy :=
          EX b_zy : bool,
          PROP (b_zy = true -> py)
          LOCAL (temp _t'11 (Vint (if b_zy then Int.one else Int.zero));
                 temp _zxh (Vint (if b_zxh then Int.one else Int.zero));
                 temp _thresh (Vfloat thresh_val);
                 temp _z (Vfloat (Float.mul (float_of_ftype (fst xh)) y));
                 temp _q_sqrt (Vfloat q_sqrt_val);
                 temp _xh_bnd (Vint (if bxh then Int.one else Int.zero));
                 temp _y_bnd (Vint (if byh then Int.one else Int.zero));
                 temp _fin_y (Vint (if vret_fy then Int.one else Int.zero));
                 temp _dwx (Vint (if b6 then Int.one else Int.zero));
                 temp _x x; temp _y (Vfloat y))
          SEP (data_at Tsh dword (f2val xh) x)).
        forward_if Post_zy.
        ** (* y == 0.0 : t'11 = (bool)fin_xh *)
           forward.
           unfold Post_zy; Exists vret_fxh; entailer!; try fix_cmp_locals.
           split; [ | destruct vret_fxh; simpl; auto ].
           intros Hout.
           unfold py. split.
           { assumption. }
           { apply (proj1 Hspec_fxh). exact Hout. }
        ** (* y != 0.0 : t'11 = 0 *)
           forward.
           unfold Post_zy; Exists false; entailer!; try fix_cmp_locals.
        ** unfold Post_zy; clear Post_zy.
           Intros b_zy; rename H into Hb_zy.
           forward.  (* store zy *)

           (* --- mult_safe: (zxh || zy) || thresh < fabs(z) ---
              if C sets _t'12 = zxh || zy; if D (guard _t'12) sets _t'13. *)
           set (Post_xy :=
             EX b_xy : bool,
             PROP (b_xy = true -> px \/ py)
             LOCAL (temp _t'12 (Vint (if b_xy then Int.one else Int.zero));
                    temp _zxh (Vint (if b_zxh then Int.one else Int.zero));
                    temp _zy (Vint (if b_zy then Int.one else Int.zero));
                    temp _thresh (Vfloat thresh_val);
                    temp _z (Vfloat (Float.mul (float_of_ftype (fst xh)) y));
                    temp _q_sqrt (Vfloat q_sqrt_val);
                    temp _xh_bnd (Vint (if bxh then Int.one else Int.zero));
                    temp _y_bnd (Vint (if byh then Int.one else Int.zero));
                    temp _fin_y (Vint (if vret_fy then Int.one else Int.zero));
                    temp _dwx (Vint (if b6 then Int.one else Int.zero));
                    temp _x x; temp _y (Vfloat y))
             SEP (data_at Tsh dword (f2val xh) x)).
           forward_if Post_xy.
           *** (* zxh != 0 : t'12 = 1 *)
               forward.
               unfold Post_xy; clear Post_xy; Exists true; entailer!; try fix_cmp_locals.
               left; apply Hb_zxh.
               destruct b_zxh; [reflexivity | simpl in H; contradiction].
           *** (* zxh = 0 : t'12 = (bool)zy *)
               forward.
               unfold Post_xy; clear Post_xy; Exists (orb b_zxh b_zy);
                 entailer!; try fix_cmp_locals.
               match goal with |- ?A /\ ?B => refine (conj _ _) end.
               { intro Htrue.
                 destruct (orb_prop _ _ Htrue) as [Hzx | Hzy].
                 - left; apply Hb_zxh; exact Hzx.
                 - right; apply Hb_zy; exact Hzy. }
               { assert (b_zxh = false) as Hbzx_false.
                 { destruct b_zxh; [exfalso; discriminate H | reflexivity]. }
                 subst b_zxh; simpl; destruct b_zy; reflexivity. }
           *** (* after zxh || zy : if D checks thresh < fabs(z) *)
               unfold Post_xy; clear Post_xy.
               Intros b_xy; rename H into Hb_xy.
               set (Post_t13 :=
                 EX b_ms : bool,
                 PROP (b_ms = true -> px \/ py \/
                   Float.cmp Clt thresh_val
                     (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble))
                        (Float.mul (float_of_ftype (fst xh)) y)) = true)
                 LOCAL (temp _t'13 (Vint (if b_ms then Int.one else Int.zero));
                        temp _zxh (Vint (if b_zxh then Int.one else Int.zero));
                        temp _zy (Vint (if b_zy then Int.one else Int.zero));
                        temp _thresh (Vfloat thresh_val);
                        temp _z (Vfloat (Float.mul (float_of_ftype (fst xh)) y));
                        temp _q_sqrt (Vfloat q_sqrt_val);
                        temp _xh_bnd (Vint (if bxh then Int.one else Int.zero));
                        temp _y_bnd (Vint (if byh then Int.one else Int.zero));
                        temp _fin_y (Vint (if vret_fy then Int.one else Int.zero));
                        temp _dwx (Vint (if b6 then Int.one else Int.zero));
                        temp _x x; temp _y (Vfloat y))
                 SEP (data_at Tsh dword (f2val xh) x)).
               forward_if Post_t13.
               ---- (* t'12 != 0 : t'13 = 1, zero product confirmed *)
                    assert (b_xy = true) as Hbxy_eq
                      by (destruct b_xy; auto; simpl in H; contradiction).
                    assert (Hpxy : px \/ py) by (apply Hb_xy; exact Hbxy_eq).
                    forward.
                    unfold Post_t13; clear Post_t13; Exists true;
                      entailer!; try fix_cmp_locals.
                    repeat apply conj;
                      try reflexivity; try cmp_val_eq;
                      try (intros _);
                      try (destruct Hpxy as [Hpx | Hpy];
                             [left; exact Hpx | right; left; exact Hpy]).
               ---- (* t'12 = 0 : t'13 = (bool)(thresh < fabs(z)) *)
                    forward_call.
                    forward.
                    unfold Post_t13; clear Post_t13.
                    set (bc := Float.cmp Clt thresh_val
                                 (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble))
                                    (Float.mul (float_of_ftype (fst xh)) y))).
                    Exists bc; entailer!; try fix_cmp_locals.
                    repeat apply conj;
                      try reflexivity; try cmp_val_eq;
                      try (unfold bc; destruct (Float.cmp Clt _ _); reflexivity);
                      try (intros Hbc; right; right; exact Hbc).
               ---- (* store mult_safe *)
                    unfold Post_t13; clear Post_t13.
                    Intros b_ms; rename H into Hb_ms.
                    forward.  (* store mult_safe *)

               (* === Return cascade: dwx && fin_y && xh_bnd && y_bnd && mult_safe === *)
               set (Post_t15 :=
                 EX b15 : bool,
                 PROP (b15 = true -> b6 = true /\ vret_fy = true)
                 LOCAL (temp _t'15 (Vint (if b15 then Int.one else Int.zero));
                        temp _mult_safe (Vint (if b_ms then Int.one else Int.zero));
                        temp _xh_bnd (Vint (if bxh then Int.one else Int.zero));
                        temp _y_bnd (Vint (if byh then Int.one else Int.zero));
                        temp _fin_y (Vint (if vret_fy then Int.one else Int.zero));
                        temp _dwx (Vint (if b6 then Int.one else Int.zero));
                        temp _x x; temp _y (Vfloat y))
                 SEP (data_at Tsh dword (f2val xh) x)).
               forward_if Post_t15.
               ---- (* dwx != 0 : t'15 = (bool)fin_y *)
                    assert (b6 = true) as Hb6_eq
                      by (destruct b6; auto; simpl in H; rep_lia).
                    forward.
                    unfold Post_t15; Exists vret_fy; entailer!;
                      try (destruct vret_fy; reflexivity);
                      try (intros Hout; repeat split; auto).
               ---- forward.
                    unfold Post_t15; Exists false; entailer!.
               ---- unfold Post_t15; clear Post_t15.
                    Intros b15; rename H into Hb15.
                    set (Post_t16 :=
                      EX b16 : bool,
                      PROP (b16 = true -> b6 = true /\ vret_fy = true /\ bxh = true)
                      LOCAL (temp _t'16 (Vint (if b16 then Int.one else Int.zero));
                             temp _mult_safe (Vint (if b_ms then Int.one else Int.zero));
                             temp _xh_bnd (Vint (if bxh then Int.one else Int.zero));
                             temp _y_bnd (Vint (if byh then Int.one else Int.zero));
                             temp _dwx (Vint (if b6 then Int.one else Int.zero));
                             temp _x x; temp _y (Vfloat y))
                      SEP (data_at Tsh dword (f2val xh) x)).
                    forward_if Post_t16.
                    ++++ (* t'15 != 0 : t'16 = (bool)xh_bnd *)
                         assert (b15 = true) as Hb15_eq
                           by (destruct b15; auto; simpl in H; rep_lia).
                         forward.
                         unfold Post_t16; Exists bxh; entailer!.
                         split.
                         { intros Hout. destruct (Hb15 eq_refl); auto. }
                         { unfold bxh.
                           match goal with
                           | |- context [Float.cmp Cle ?a ?b] =>
                               destruct (Float.cmp Cle a b); reflexivity
                           end. }
                    ++++ forward.
                         unfold Post_t16; Exists false; entailer!.
                    ++++ unfold Post_t16; clear Post_t16.
                         Intros b16; rename H into Hb16.
                         set (Post_t17 :=
                           EX b17 : bool,
                           PROP (b17 = true -> b6 = true /\ vret_fy = true /\
                                               bxh = true /\ byh = true)
                           LOCAL (temp _t'17 (Vint (if b17 then Int.one else Int.zero));
                                  temp _mult_safe (Vint (if b_ms then Int.one else Int.zero));
                                  temp _y_bnd (Vint (if byh then Int.one else Int.zero));
                                  temp _x x; temp _y (Vfloat y))
                           SEP (data_at Tsh dword (f2val xh) x)).
                         forward_if Post_t17.
                         **** (* t'16 != 0 : t'17 = (bool)y_bnd *)
                              assert (b16 = true) as Hb16_eq
                                by (destruct b16; auto; simpl in H; rep_lia).
                              forward.
                              unfold Post_t17; Exists byh; entailer!.
                              split.
                              { intros Hout.
                                destruct (Hb16 eq_refl) as [Hb6t [Hfyt Hbxht]]; auto. }
                              { unfold byh.
                                match goal with
                                | |- context [Float.cmp Cle ?a ?b] =>
                                    destruct (Float.cmp Cle a b); reflexivity
                                end. }
                         **** forward.
                              unfold Post_t17; Exists false; entailer!.
                         **** unfold Post_t17; clear Post_t17.
                              Intros b17; rename H into Hb17.
                              set (Post_t18 :=
                                EX b18 : bool,
                                PROP (b18 = true -> b6 = true /\ vret_fy = true /\
                                                    bxh = true /\ byh = true /\ b_ms = true)
                                LOCAL (temp _t'18 (Vint (if b18 then Int.one else Int.zero));
                                       temp _x x; temp _y (Vfloat y))
                                SEP (data_at Tsh dword (f2val xh) x)).
                              forward_if Post_t18.
                              ----- (* t'17 != 0 : t'18 = (bool)mult_safe *)
                                    assert (b17 = true) as Hb17_eq
                                      by (destruct b17; auto; simpl in H; rep_lia).
                                    forward.
                                    unfold Post_t18; Exists b_ms; entailer!.
                                    split.
                                    { intros Hout.
                                      destruct (Hb17 eq_refl) as [Hb6t [Hfyt [Hbxht Hbyht]]].
                                      repeat split; auto. }
                                    { destruct b_ms; reflexivity. }
                              ----- forward.
                                    unfold Post_t18; Exists false; entailer!.
                              ----- unfold Post_t18; clear Post_t18.
                                    Intros b18; rename H into Hb18.
                                    forward.  (* return t'18 *)
                                    Exists b18; entailer!.
                                    (* FINAL discharge *)
                                    destruct (Hb18 eq_refl)
                                      as [Hb6t [Hfyt [Hbxht [Hbyht Hbmst]]]].
                                    destruct (Hb6 Hb6t) as [Hfxh [Hfxl Hdwp]].
                                    assert (Hfy : is_finite y = true)
                                      by (apply (proj1 Hspec_fy); exact Hfyt).
                                    assert (Hxhb : Rabs (FT2R (fst xh)) <=
                                              bpow Zaux.radix2 (femax Tdouble / 2 - 1)).
                                    { apply Float_cmp_Cle_bpow511; [exact Hfxh|].
                                      unfold bxh in Hbxht; exact Hbxht. }
                                    assert (Hyb : Rabs (FT2R y) <=
                                              bpow Zaux.radix2 (femax Tdouble / 2 - 1)).
                                    { apply Float_cmp_Cle_bpow511; [exact Hfy|].
                                      unfold byh in Hbyht; exact Hbyht. }
                                    (* BMULT (fst xh) y is finite from the factor bounds
                                       (no overflow); the finiteness half of the new
                                       Fast2Mult_cond (fst xh) y conjunct. *)
                                    destruct (sqrt_cond_facts (fst xh) y
                                                Hfxh Hfy Hxhb Hyb)
                                      as (_ & _ & _ & Hbmul_fin & _).
                                    unfold DDModels.DWTimesFP_cond, DDModels.Fast2Mult_cond.
                                    repeat (split; try assumption).
                                    (* the product bound |xh*y| <= Omega/2 is the new
                                       final conjunct; derive it from the factor bounds. *)
                                    2:{ eapply Rle_trans;
                                          [ apply aux_factor_prod; [exact Hxhb | exact Hyb] | ].
                                        apply Rmult_le_compat_r; [ apply bpow_ge_0 | lra ]. }
                                    (* remaining goal: the disjunction *)
                                    destruct (Hb_ms Hbmst) as [Hpx | [Hpy | Hclt]].
                                    ++++++ (* px : xh = 0 *)
                                           left. unfold px in Hpx.
                                           pose proof (Float_cmp_Ceq_zero_mul_FT2R_l
                                                        (float_of_ftype (fst xh)) (FT2R y)
                                                        (proj1 Hpx)) as Hr.
                                           rewrite ftype_of_float_of_ftype in Hr.
                                           exact Hr.
                                    ++++++ (* py : y = 0 *)
                                           left. unfold py in Hpy.
                                           pose proof (Float_cmp_Ceq_zero_mul_FT2R_r
                                                        (FT2R (fst xh)) (float_of_ftype y)
                                                        (proj1 Hpy)) as Hr.
                                           rewrite ftype_of_float_of_ftype in Hr.
                                           exact Hr.
                                    ++++++ (* Hclt : thresh < fabs(xh*y) : above threshold *)
                                           right.
                                           destruct (sqrt_cond_facts (fst xh) y
                                                       Hfxh Hfy Hxhb Hyb)
                                             as (_ & _ & _ & Hbmul & _).
                                           assert (Hfin_mul :
                                             is_finite (ftype_of_float
                                               (Float.mul (float_of_ftype (fst xh))
                                                          (float_of_ftype y))) = true).
                                           { exact Hbmul. }
                                           pose proof (Float_cmp_Cle_mul
                                             (float_of_ftype (fst xh)) (float_of_ftype y)
                                             (bpow Zaux.radix2 (emin + 2 * fprec Tdouble - 1))
                                             (ftype_of_float thresh_val)
                                             Hfin_mul thresh_val_finite
                                             (eq_sym thresh_val_FT2R)) as Hcmp.
                                           rewrite ?ftype_of_float_of_ftype in Hcmp.
                                           rewrite ?float_of_ftype_of_float in Hcmp.
                                           apply Rlt_le, Rlt_bool_to_Rlt,
                                                 no_underflow_real_from_round_mul.
                                           apply Rlt_bool_to_Rlt.
                                           destruct (Rlt_bool _ _) eqn:Hrb.
                                           { reflexivity. }
                                           { exfalso.
                                             match type of Hcmp with
                                             | _ = bool2val ?c => assert (E : c = true) by exact Hclt
                                             end.
                                             rewrite E in Hcmp.
                                             discriminate Hcmp. }
Qed.
