(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.
Require Import DD.verif_proofs.verif_fp_utils_short_circuit.

(* Local-matching helpers (copied from verif_fp_utils_dw_mult_fp_check): a stored
   comparison temp is `Vint (Int.repr (Z.b2z c))`, while the forward_if invariant
   carries `Vint (if c then Int.one else Int.zero)`; the two are convertible. *)
Lemma Vint_b2z_if : forall b : bool,
  Vint (Int.repr (Z.b2z b)) = Vint (if b then Int.one else Int.zero).
Proof. intros [|]; reflexivity. Qed.

Ltac cmp_val_eq :=
  rewrite Vint_b2z_if; reflexivity.

Ltac fix_cmp_locals :=
  solve [ repeat (first [ reflexivity | cmp_val_eq
                        | (intro; discriminate) | split ]) ].

(* dw_mult_dw_check(x, y) returns 1 only if DWTimesDW_cond holds.  Structure:
   body_dw_plus_dw_check's fin + dwx + dwy cascade, then the ldexp/fabs factor
   bounds and mult_safe short-circuit of body_dw_mult_fp_check, with the scalar
   y promoted to a second double-word (y->s, y->t).  Raw facts are threaded
   through each forward_if and DWTimesDW_cond is discharged only at the final
   return join.  _fin_xh and _fin_yh are carried past the DW checks because the
   zxh/zyh short-circuits read them. *)
Lemma body_dw_mult_dw_check :
  semax_body Vprog Gprog f_dw_mult_dw_check dw_mult_dw_check_spec.
Proof.
  start_function.
  (* fin_xh, fin_xl, fin_yh, fin_yl *)
  forward. forward_call. Intros vret_fxh. rename H into Hspec_fxh. forward.
  forward. forward_call. Intros vret_fxl. rename H into Hspec_fxl. forward.
  forward. forward_call. Intros vret_fyh. rename H into Hspec_fyh. forward.
  forward. forward_call. Intros vret_fyl. rename H into Hspec_fyl. forward.

  (* --- dwx: (fin_xh && fin_xl) && (x->s + x->t == x->s) --- *)
  set (Post_t5 :=
    EX b5 : bool,
    PROP (b5 = true -> is_finite (fst xh) = true /\ is_finite (snd xh) = true)
    LOCAL (temp _t'5 (Vint (if b5 then Int.one else Int.zero));
           temp _fin_xh (Vint (if vret_fxh then Int.one else Int.zero));
           temp _fin_xl (Vint (if vret_fxl then Int.one else Int.zero));
           temp _fin_yh (Vint (if vret_fyh then Int.one else Int.zero));
           temp _fin_yl (Vint (if vret_fyl then Int.one else Int.zero));
           temp _x x; temp _y y)
    SEP (data_at Tsh dword (f2val xh) x;
         data_at Tsh dword (f2val yh) y)).
  forward_if Post_t5.
  - assert (vret_fxh = true) as Hvfxh.
    { destruct vret_fxh; auto; simpl in H; rep_lia. }
    forward.
    unfold Post_t5; Exists vret_fxl; entailer!.
    split.
    + intros Hout.
      apply (short_circuit_fin_and_concl (fst xh) (snd xh) true vret_fxl vret_fxl
              Hspec_fxh Hspec_fxl eq_refl).
      exact Hout.
    + destruct vret_fxl; simpl; auto.
  - forward.
    unfold Post_t5; Exists false; entailer!.
  - unfold Post_t5; clear Post_t5.
    Intros b5; rename H into Hb5.
    set (Post_t6 :=
      EX b6 : bool,
      PROP (b6 = true -> is_finite (fst xh) = true /\
                         is_finite (snd xh) = true /\
                         double_word_prop (fst xh) (snd xh))
      LOCAL (temp _t'6 (Vint (if b6 then Int.one else Int.zero));
             temp _fin_xh (Vint (if vret_fxh then Int.one else Int.zero));
             temp _fin_yh (Vint (if vret_fyh then Int.one else Int.zero));
             temp _fin_yl (Vint (if vret_fyl then Int.one else Int.zero));
             temp _x x; temp _y y)
      SEP (data_at Tsh dword (f2val xh) x;
           data_at Tsh dword (f2val yh) y)).
    forward_if Post_t6.
    + assert (b5 = true) as Hb5_eq.
      { destruct b5; auto; simpl in H; rep_lia. }
      forward. forward. forward. forward.
      unfold Post_t6.
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
                 Hb5 eq_refl).
        exact Hout.
      * destruct (Float.cmp _ _ _); simpl; auto.
    + forward.
      unfold Post_t6; Exists false; entailer!.
    + unfold Post_t6; clear Post_t6.
      Intros b6; rename H into Hb6.
      forward. (* store _dwx *)

      (* --- dwy: (fin_yh && fin_yl) && (y->s + y->t == y->s) --- *)
      set (Post_t7 :=
        EX b7 : bool,
        PROP (b7 = true -> is_finite (fst yh) = true /\ is_finite (snd yh) = true)
        LOCAL (temp _t'7 (Vint (if b7 then Int.one else Int.zero));
               temp _dwx (Vint (if b6 then Int.one else Int.zero));
               temp _fin_xh (Vint (if vret_fxh then Int.one else Int.zero));
               temp _fin_yh (Vint (if vret_fyh then Int.one else Int.zero));
               temp _fin_yl (Vint (if vret_fyl then Int.one else Int.zero));
               temp _x x; temp _y y)
        SEP (data_at Tsh dword (f2val xh) x;
             data_at Tsh dword (f2val yh) y)).
      forward_if Post_t7.
      * assert (vret_fyh = true) as Hvfyh.
        { destruct vret_fyh; auto; simpl in H; rep_lia. }
        forward.
        unfold Post_t7; Exists vret_fyl; entailer!.
        split.
        ** intros Hout.
           apply (short_circuit_fin_and_concl (fst yh) (snd yh) true vret_fyl vret_fyl
                   Hspec_fyh Hspec_fyl eq_refl).
           exact Hout.
        ** destruct vret_fyl; simpl; auto.
      * forward. unfold Post_t7; Exists false; entailer!.
      * unfold Post_t7; clear Post_t7.
        Intros b7; rename H into Hb7.
        set (Post_t8 :=
          EX b8 : bool,
          PROP (b8 = true -> is_finite (fst yh) = true /\
                             is_finite (snd yh) = true /\
                             double_word_prop (fst yh) (snd yh))
          LOCAL (temp _t'8 (Vint (if b8 then Int.one else Int.zero));
                 temp _dwx (Vint (if b6 then Int.one else Int.zero));
                 temp _fin_xh (Vint (if vret_fxh then Int.one else Int.zero));
                 temp _fin_yh (Vint (if vret_fyh then Int.one else Int.zero));
                 temp _x x; temp _y y)
          SEP (data_at Tsh dword (f2val xh) x;
               data_at Tsh dword (f2val yh) y)).
        forward_if Post_t8.
        ** assert (b7 = true) as Hb7_eq.
           { destruct b7; auto; simpl in H; rep_lia. }
           forward. forward. forward. forward.
           unfold Post_t8.
           Exists (Float.cmp Ceq
                     (Float.add (float_of_ftype (fst yh)) (float_of_ftype (snd yh)))
                     (float_of_ftype (fst yh))).
           entailer!.
           split.
           --- intros Hout.
               apply (short_circuit_dw_eq_concl (fst yh) (snd yh) true
                        (Float.cmp Ceq
                           (Float.add (float_of_ftype (fst yh)) (float_of_ftype (snd yh)))
                           (float_of_ftype (fst yh)))
                        Hb7 eq_refl).
               exact Hout.
           --- destruct (Float.cmp _ _ _); simpl; auto.
        ** forward. unfold Post_t8; Exists false; entailer!.
        ** unfold Post_t8; clear Post_t8.
           Intros b8; rename H into Hb8.
           forward. (* store _dwy *)

           (* z = x->s * y->s *)
           forward. forward. forward.
           (* thresh = DBL_MIN * ldexp(1.0, 53) *)
           forward_call.
           forward.
           (* q_prod = ldexp(1.0, 1023) = q_prod_val
              (forward_call folds the following plain Sset _q_prod). *)
           forward_call.
           (* prod_bnd = (fabs(z) < q_prod) *)
           forward_call.
           forward.

           set (bpb := Float.cmp Clt
                         (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble))
                            (Float.mul (float_of_ftype (fst xh))
                                       (float_of_ftype (fst yh))))
                         q_prod_val).
           set (px := Float.cmp Ceq (float_of_ftype (fst xh))
                        (Float.of_bits (Int64.repr 0)) = true
                      /\ is_finite (fst yh) = true).
           set (py := Float.cmp Ceq (float_of_ftype (fst yh))
                        (Float.of_bits (Int64.repr 0)) = true
                      /\ is_finite (fst xh) = true).

           (* --- zxh: (x->s == 0.0) && fin_yh --- *)
           forward. (* load t'21 = x->s *)
           set (Post_zxh :=
             EX b_zxh : bool,
             PROP (b_zxh = true -> px)
             LOCAL (temp _t'12 (Vint (if b_zxh then Int.one else Int.zero));
                    temp _prod_bnd (Vint (if bpb then Int.one else Int.zero));
                    temp _thresh (Vfloat thresh_val);
                    temp _z (Vfloat (Float.mul (float_of_ftype (fst xh))
                                               (float_of_ftype (fst yh))));
                    temp _fin_xh (Vint (if vret_fxh then Int.one else Int.zero));
                    temp _dwx (Vint (if b6 then Int.one else Int.zero));
                    temp _dwy (Vint (if b8 then Int.one else Int.zero));
                    temp _x x; temp _y y)
             SEP (data_at Tsh dword (f2val xh) x;
                  data_at Tsh dword (f2val yh) y)).
           forward_if Post_zxh.
           ++ (* x->s == 0.0 : t'12 = (bool) fin_yh *)
              forward.
              unfold Post_zxh; Exists vret_fyh; entailer!.
              repeat apply conj;
                try reflexivity; try cmp_val_eq;
                try (destruct vret_fyh; reflexivity);
                try (intros Hout; unfold px; split;
                     [ assumption | apply (proj1 Hspec_fyh); exact Hout ]).
           ++ (* x->s != 0.0 : t'12 = 0 *)
              forward.
              unfold Post_zxh; Exists false; entailer!; try fix_cmp_locals.
           ++ unfold Post_zxh; clear Post_zxh.
              Intros b_zxh; rename H into Hb_zxh.
              forward. (* store _zxh *)

              (* --- zyh: (y->s == 0.0) && fin_xh --- *)
              forward. (* load t'20 = y->s *)
              set (Post_zyh :=
                EX b_zyh : bool,
                PROP (b_zyh = true -> py)
                LOCAL (temp _t'13 (Vint (if b_zyh then Int.one else Int.zero));
                       temp _zxh (Vint (if b_zxh then Int.one else Int.zero));
                       temp _prod_bnd (Vint (if bpb then Int.one else Int.zero));
                       temp _thresh (Vfloat thresh_val);
                       temp _z (Vfloat (Float.mul (float_of_ftype (fst xh))
                                                  (float_of_ftype (fst yh))));
                       temp _dwx (Vint (if b6 then Int.one else Int.zero));
                       temp _dwy (Vint (if b8 then Int.one else Int.zero));
                       temp _x x; temp _y y)
                SEP (data_at Tsh dword (f2val xh) x;
                     data_at Tsh dword (f2val yh) y)).
              forward_if Post_zyh.
              +++ (* y->s == 0.0 : t'13 = (bool) fin_xh *)
                  forward.
                  unfold Post_zyh; Exists vret_fxh; entailer!.
                  repeat apply conj;
                    try reflexivity; try cmp_val_eq;
                    try (destruct vret_fxh; reflexivity);
                    try (intros Hout; unfold py; split;
                         [ assumption | apply (proj1 Hspec_fxh); exact Hout ]).
              +++ (* y->s != 0.0 : t'13 = 0 *)
                  forward.
                  unfold Post_zyh; Exists false; entailer!; try fix_cmp_locals.
              +++ unfold Post_zyh; clear Post_zyh.
                  Intros b_zyh; rename H into Hb_zyh.
                  forward. (* store _zyh *)

                  (* --- mult_safe: (zxh || zyh) || thresh < fabs(z) --- *)
                  set (Post_xy :=
                    EX b_xy : bool,
                    PROP (b_xy = true -> px \/ py)
                    LOCAL (temp _t'14 (Vint (if b_xy then Int.one else Int.zero));
                           temp _zxh (Vint (if b_zxh then Int.one else Int.zero));
                           temp _zyh (Vint (if b_zyh then Int.one else Int.zero));
                           temp _prod_bnd (Vint (if bpb then Int.one else Int.zero));
                           temp _thresh (Vfloat thresh_val);
                           temp _z (Vfloat (Float.mul (float_of_ftype (fst xh))
                                                      (float_of_ftype (fst yh))));
                           temp _dwx (Vint (if b6 then Int.one else Int.zero));
                           temp _dwy (Vint (if b8 then Int.one else Int.zero));
                           temp _x x; temp _y y)
                    SEP (data_at Tsh dword (f2val xh) x;
                         data_at Tsh dword (f2val yh) y)).
                  forward_if Post_xy.
                  *** (* zxh != 0 : t'14 = 1 *)
                      forward.
                      unfold Post_xy; clear Post_xy; Exists true; entailer!; try fix_cmp_locals.
                      left; apply Hb_zxh.
                      destruct b_zxh; [reflexivity | simpl in H; contradiction].
                  *** (* zxh = 0 : t'14 = (bool) zyh *)
                      forward.
                      unfold Post_xy; clear Post_xy; Exists (orb b_zxh b_zyh);
                        entailer!; try fix_cmp_locals.
                      match goal with |- ?A /\ ?B => refine (conj _ _) end.
                      { intro Htrue.
                        destruct (orb_prop _ _ Htrue) as [Hzx | Hzy].
                        - left; apply Hb_zxh; exact Hzx.
                        - right; apply Hb_zyh; exact Hzy. }
                      { assert (b_zxh = false) as Hbzx_false.
                        { destruct b_zxh; [exfalso; discriminate H | reflexivity]. }
                        subst b_zxh; simpl; destruct b_zyh; reflexivity. }
                  *** unfold Post_xy; clear Post_xy.
                      Intros b_xy; rename H into Hb_xy.
                      set (Post_ms :=
                        EX b_ms : bool,
                        PROP (b_ms = true -> px \/ py \/
                          Float.cmp Clt thresh_val
                            (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble))
                               (Float.mul (float_of_ftype (fst xh))
                                          (float_of_ftype (fst yh)))) = true)
                        LOCAL (temp _t'15 (Vint (if b_ms then Int.one else Int.zero));
                               temp _prod_bnd (Vint (if bpb then Int.one else Int.zero));
                               temp _dwx (Vint (if b6 then Int.one else Int.zero));
                               temp _dwy (Vint (if b8 then Int.one else Int.zero));
                               temp _x x; temp _y y)
                        SEP (data_at Tsh dword (f2val xh) x;
                             data_at Tsh dword (f2val yh) y)).
                      forward_if Post_ms.
                      ---- (* t'14 != 0 : t'15 = 1, zero product confirmed *)
                           assert (b_xy = true) as Hbxy_eq
                             by (destruct b_xy; auto; simpl in H; contradiction).
                           assert (Hpxy : px \/ py) by (apply Hb_xy; exact Hbxy_eq).
                           forward.
                           unfold Post_ms; clear Post_ms; Exists true; entailer!.
                           repeat apply conj;
                             try reflexivity; try cmp_val_eq;
                             try (intros _);
                             try (destruct Hpxy as [Hpx | Hpy];
                                    [left; exact Hpx | right; left; exact Hpy]).
                      ---- (* t'14 = 0 : t'15 = (bool)(thresh < fabs(z)) *)
                           forward_call.
                           forward.
                           unfold Post_ms; clear Post_ms.
                           set (bc := Float.cmp Clt thresh_val
                                        (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble))
                                           (Float.mul (float_of_ftype (fst xh))
                                                      (float_of_ftype (fst yh))))).
                           Exists bc; entailer!.
                           repeat apply conj;
                             try reflexivity; try cmp_val_eq;
                             try (unfold bool2val; rewrite Vint_b2z_if; reflexivity);
                             try (intros Hbc; right; right; exact Hbc).
                      ---- try (unfold Post_ms; clear Post_ms).
                           Intros b_ms; rename H into Hb_ms.
                           forward. (* store _mult_safe *)

                           (* === return dwx && dwy && prod_bnd && mult_safe === *)
                           set (Post_t17 :=
                             EX b17 : bool,
                             PROP (b17 = true -> b6 = true /\ b8 = true)
                             LOCAL (temp _t'17 (Vint (if b17 then Int.one else Int.zero));
                                    temp _mult_safe (Vint (if b_ms then Int.one else Int.zero));
                                    temp _prod_bnd (Vint (if bpb then Int.one else Int.zero));
                                    temp _dwx (Vint (if b6 then Int.one else Int.zero));
                                    temp _dwy (Vint (if b8 then Int.one else Int.zero));
                                    temp _x x; temp _y y)
                             SEP (data_at Tsh dword (f2val xh) x;
                                  data_at Tsh dword (f2val yh) y)).
                           forward_if Post_t17.
                           **** (* dwx != 0 : t'17 = (bool) dwy *)
                                assert (b6 = true) as Hb6_eq
                                  by (destruct b6; auto; simpl in H; rep_lia).
                                forward.
                                unfold Post_t17; Exists b8; entailer!;
                                  try (destruct b8; reflexivity);
                                  try (intros Hout; repeat split; auto).
                           **** forward.
                                unfold Post_t17; Exists false; entailer!.
                           **** unfold Post_t17; clear Post_t17.
                                Intros b17; rename H into Hb17.
                                set (Post_t18 :=
                                  EX b18 : bool,
                                  PROP (b18 = true -> b6 = true /\ b8 = true /\ bpb = true)
                                  LOCAL (temp _t'18 (Vint (if b18 then Int.one else Int.zero));
                                         temp _mult_safe (Vint (if b_ms then Int.one else Int.zero));
                                         temp _prod_bnd (Vint (if bpb then Int.one else Int.zero));
                                         temp _x x; temp _y y)
                                  SEP (data_at Tsh dword (f2val xh) x;
                                       data_at Tsh dword (f2val yh) y)).
                                forward_if Post_t18.
                                ----- (* t'17 != 0 : t'18 = (bool) prod_bnd *)
                                    assert (b17 = true) as Hb17_eq
                                      by (destruct b17; auto; simpl in H; rep_lia).
                                    forward.
                                    unfold Post_t18; Exists bpb; entailer!.
                                    split.
                                    { intros Hout. destruct (Hb17 eq_refl); auto. }
                                    { unfold bpb.
                                      match goal with
                                      | |- context [Float.cmp Clt ?a ?b] =>
                                          destruct (Float.cmp Clt a b); reflexivity
                                      end. }
                                ----- forward.
                                    unfold Post_t18; Exists false; entailer!.
                                ----- unfold Post_t18; clear Post_t18.
                                    Intros b18; rename H into Hb18.
                                    set (Post_t19 :=
                                      EX b19 : bool,
                                      PROP (b19 = true -> b6 = true /\ b8 = true /\
                                                          bpb = true /\ b_ms = true)
                                      LOCAL (temp _t'19 (Vint (if b19 then Int.one else Int.zero));
                                             temp _mult_safe (Vint (if b_ms then Int.one else Int.zero));
                                             temp _x x; temp _y y)
                                      SEP (data_at Tsh dword (f2val xh) x;
                                           data_at Tsh dword (f2val yh) y)).
                                    forward_if Post_t19.
                                    +++++ (* t'18 != 0 : t'19 = (bool) mult_safe *)
                                         assert (b18 = true) as Hb18_eq
                                           by (destruct b18; auto; simpl in H; rep_lia).
                                         forward.
                                         unfold Post_t19; Exists b_ms; entailer!.
                                         split.
                                         { intros Hout.
                                           destruct (Hb18 eq_refl) as [Hb6t [Hb8t Hbpbt]].
                                           repeat split; auto. }
                                         { destruct b_ms; reflexivity. }
                                    +++++ forward.
                                         unfold Post_t19; Exists false; entailer!.
                                    +++++ unfold Post_t19; clear Post_t19.
                                         Intros b19; rename H into Hb19.
                                         forward. (* return t'19 *)
                                         Exists b19; entailer!.
                                         (* FINAL discharge of DWTimesDW_cond *)
                                         destruct (Hb19 eq_refl)
                                           as [Hb6t [Hb8t [Hbpbt Hbmst]]].
                                         destruct (Hb6 Hb6t) as [Hfxh [Hfxl Hdwx]].
                                         destruct (Hb8 Hb8t) as [Hfyh [Hfyl Hdwy]].
                                         (* prod_bnd discharges Fast2Mult finiteness AND the
                                            product-magnitude bound in one shot. *)
                                         destruct (prod_bnd_facts (fst xh) (fst yh))
                                           as [Hbmul_fin Hprodb].
                                         { unfold bpb in Hbpbt; exact Hbpbt. }
                                         unfold DDModels.DWTimesDW_cond, DDModels.Fast2Mult_cond.
                                         repeat (split; try assumption).
                                         (* remaining goal: the underflow disjunction *)
                                         destruct (Hb_ms Hbmst) as [Hpx | [Hpy | Hclt]].
                                         ------ (*px : x->s = 0 *)
                                                left. unfold px in Hpx.
                                                pose proof (Float_cmp_Ceq_zero_mul_FT2R_l
                                                             (float_of_ftype (fst xh))
                                                             (FT2R (fst yh))
                                                             (proj1 Hpx)) as Hr.
                                                rewrite ftype_of_float_of_ftype in Hr.
                                                exact Hr.
                                         ------ (*py : y->s = 0 *)
                                                left. unfold py in Hpy.
                                                pose proof (Float_cmp_Ceq_zero_mul_FT2R_r
                                                             (FT2R (fst xh))
                                                             (float_of_ftype (fst yh))
                                                             (proj1 Hpy)) as Hr.
                                                rewrite ftype_of_float_of_ftype in Hr.
                                                exact Hr.
                                         ------ (*Hclt : thresh < fabs(xh*yh) : above threshold *)
                                                right.
                                                assert (Hfin_mul :
                                                  is_finite (ftype_of_float
                                                    (Float.mul (float_of_ftype (fst xh))
                                                               (float_of_ftype (fst yh)))) = true)
                                                  by exact Hbmul_fin.
                                                pose proof (Float_cmp_Cle_mul
                                                  (float_of_ftype (fst xh)) (float_of_ftype (fst yh))
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
