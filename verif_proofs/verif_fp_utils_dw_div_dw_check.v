(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.
Require Import DD.verif_proofs.verif_fp_utils_short_circuit.

(* A stored comparison temp is `Vint (Int.repr (Z.b2z c))`, while the forward_if
   invariants below carry `Vint (if c then Int.one else Int.zero)`; the two are
   convertible.  Same helper as verif_fp_utils_dw_mult_dw_check. *)
Lemma Vint_b2z_if : forall b : bool,
  Vint (Int.repr (Z.b2z b)) = Vint (if b then Int.one else Int.zero).
Proof. intros [|]; reflexivity. Qed.

(* Collect the facts the cascade threads forward.  entailer! substitutes the
   `remember` equations back, so a stage's premise can arrive either as
   `HbN : bN = true -> ...` alongside `bN = true`, or with bN already replaced by
   `true` (making the antecedent provable by eq_refl).  Both are instantiated
   here, and the resulting conjunctions are flattened so every conjunct the goal
   needs is literally a hypothesis. *)
Ltac cascade_gather :=
  repeat match goal with
         | H : ?A = true -> _, H2 : ?A = true |- _ => specialize (H H2)
         end;
  repeat match goal with
         | H : _ = true -> _ |- _ => specialize (H eq_refl)
         end;
  repeat match goal with H : _ /\ _ |- _ => destruct H end.

(* Closes every side goal entailer! produces in the six return-cascade stages.
   Two shapes occur, and which one appears varies by stage (entailer! sometimes
   discharges the LOCAL parts on its own), so this handles both uniformly:

   - LOCAL matching: `Vint (Int.repr (Z.b2z b)) = Vint (if b then _ else _)`,
     closed by Vint_b2z_if / destructing the (opaque) boolean.
   - The threaded PROP implication, closed from cascade_gather's facts.

   cascade_gather runs up front so that bare `b6 = true`-style conjuncts close by
   assumption, and again after the intro so an implication goal exposed only by
   `repeat split` is handled too. *)
Ltac cascade_close :=
  cascade_gather;
  repeat split;
  repeat first
    [ reflexivity
    | assumption
    | rewrite Vint_b2z_if
    | match goal with
      | |- context [if ?bb then Int.one else Int.zero] => destruct bb
      end
    | (intro; cascade_gather; repeat split; assumption)
    | (intro; cascade_gather; tauto) ].

(* dw_div_dw_check(x, y) returns 1 only if DWDivDW_cond holds: xh, xl, yh, yl
   finite, (xh,xl) and (yh,yl) double-words, 2^(emin+2p-1) <= |1/yh|,
   2^(emin+2p) <= |yh|, |xh| and |yh| <= Omega/4, and the quotient |xh/yh| inside
   the window [2^(emin+2p-1), Omega/4].

   Structure: body_dw_mult_dw_check's fin + dwx + dwy cascade, then the magnitude
   and quotient tail of body_dw_div_fp_check with the scalar divisor promoted to
   the leading component y->s.  Raw facts are threaded through each forward_if and
   DWDivDW_cond is discharged only at the final return join.

   Twelve conjuncts come out of seven clauses, because two of them are free:

   - yh_hi (|y->s| <= 2^969) discharges the reciprocal conjunct EXACTLY.  That
     conjunct constrains the exact real reciprocal 1/FT2R yh, so for yh <> 0 it is
     equivalent to |FT2R yh| <= 2^(-(emin+2p-1)) = 2^969 -- see
     recip_lower_from_bpow_upper.  No rounded reciprocal node and no
     rounded->exact transfer are involved, so unlike the quotient bounds this test
     is non-strict and exactly as strong as the conjunct.  Its yh <> 0 side
     condition comes from yh_lo, not from the division node (BDIV_denom_ne0 would
     also supply it, but only by making the reciprocal bound depend on the
     quotient node).
   - The same clause also gives |yh| <= Omega/4 by bpow_le (969 <= 1022), so the
     check has no separate q_omega test on y->s.

   Only the quotient window needs the rounded->exact transfer, at the same two
   exponents body_dw_div_fp_check uses: the strict upper bound
   (Float_cmp_Clt_bpow1022) also yields is_finite q, so BDIV_abs_le_bpow /
   BDIV_abs_gt_bpow apply (one-directional soundness). *)
Lemma body_dw_div_dw_check :
  semax_body Vprog Gprog f_dw_div_dw_check dw_div_dw_check_spec.
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
  - assert (vret_fxh = true) as Hvfxh
      by (destruct vret_fxh; auto; simpl in H; rep_lia).
    forward.
    unfold Post_t5; Exists vret_fxl; entailer!.
    split.
    + intros Hout.
      apply (short_circuit_fin_and_concl (fst xh) (snd xh) true vret_fxl vret_fxl
              Hspec_fxh Hspec_fxl eq_refl). exact Hout.
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
             temp _fin_yh (Vint (if vret_fyh then Int.one else Int.zero));
             temp _fin_yl (Vint (if vret_fyl then Int.one else Int.zero));
             temp _x x; temp _y y)
      SEP (data_at Tsh dword (f2val xh) x;
           data_at Tsh dword (f2val yh) y)).
    forward_if Post_t6.
    + assert (b5 = true) as Hb5_eq
        by (destruct b5; auto; simpl in H; rep_lia).
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
                 Hb5 eq_refl). exact Hout.
      * destruct (Float.cmp _ _ _); simpl; auto.
    + forward.
      unfold Post_t6; Exists false; entailer!.
    + unfold Post_t6; clear Post_t6.
      Intros b6; rename H into Hb6.
      forward.                            (* store _dwx *)

      (* --- dwy: (fin_yh && fin_yl) && (y->s + y->t == y->s) --- *)
      set (Post_t7 :=
        EX b7 : bool,
        PROP (b7 = true -> is_finite (fst yh) = true /\ is_finite (snd yh) = true)
        LOCAL (temp _t'7 (Vint (if b7 then Int.one else Int.zero));
               temp _dwx (Vint (if b6 then Int.one else Int.zero));
               temp _fin_yh (Vint (if vret_fyh then Int.one else Int.zero));
               temp _fin_yl (Vint (if vret_fyl then Int.one else Int.zero));
               temp _x x; temp _y y)
        SEP (data_at Tsh dword (f2val xh) x;
             data_at Tsh dword (f2val yh) y)).
      forward_if Post_t7.
      * assert (vret_fyh = true) as Hvfyh
          by (destruct vret_fyh; auto; simpl in H; rep_lia).
        forward.
        unfold Post_t7; Exists vret_fyl; entailer!.
        split.
        ** intros Hout.
           apply (short_circuit_fin_and_concl (fst yh) (snd yh) true vret_fyl vret_fyl
                   Hspec_fyh Hspec_fyl eq_refl). exact Hout.
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
                 temp _x x; temp _y y)
          SEP (data_at Tsh dword (f2val xh) x;
               data_at Tsh dword (f2val yh) y)).
        forward_if Post_t8.
        ** assert (b7 = true) as Hb7_eq
             by (destruct b7; auto; simpl in H; rep_lia).
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
                        Hb7 eq_refl). exact Hout.
           --- destruct (Float.cmp _ _ _); simpl; auto.
        ** forward. unfold Post_t8; Exists false; entailer!.
        ** unfold Post_t8; clear Post_t8.
           Intros b8; rename H into Hb8.
           forward.                       (* store _dwy *)

           (* thresholds: q_omega = 2^1022, q_yhi = 2^969,
              q_ylo = 2^(-968), q_qlo = 2^(-969)  (stores absorbed) *)
           forward_call.
           forward_call.
           forward_call.
           forward_call.
           replace (- Int.unsigned (Int.repr 968))%Z with (-968)%Z by reflexivity.
           replace (- Int.unsigned (Int.repr 969))%Z with (-969)%Z by reflexivity.
           fold q_omega_val q_hi969_val q_lo968_val q_lo969_val.
           forward. forward_call (fst xh). forward.  (* xh_hi := fabs(x->s) <= q_omega *)
           forward. forward_call (fst yh). forward.  (* yh_hi := fabs(y->s) <= q_yhi *)
           forward. forward_call (fst yh). forward.  (* yh_lo := q_ylo <= fabs(y->s) *)
           forward.                                  (* t'24 := x->s *)
           forward.                                  (* t'25 := y->s *)
           forward.                                  (* q := t'24 / t'25 *)
           forward_call (Float.div (fst xh) (fst yh)). forward. (* qt_hi *)
           forward_call (Float.div (fst xh) (fst yh)). forward. (* qt_lo *)

           (* Abstract the five comparisons so the cascade below is name-opaque. *)
           remember (Float.cmp Cle
                       (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (fst xh))
                       q_omega_val) as bxh_hi eqn:Ebxh_hi.
           remember (Float.cmp Cle
                       (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (fst yh))
                       q_hi969_val) as byh_hi eqn:Ebyh_hi.
           remember (Float.cmp Cle q_lo968_val
                       (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (fst yh)))
                     as byh_lo eqn:Ebyh_lo.
           remember (Float.cmp Clt
                       (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble))
                          (Float.div (fst xh) (fst yh))) q_omega_val)
                     as bqt_hi eqn:Ebqt_hi.
           remember (Float.cmp Clt q_lo969_val
                       (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble))
                          (Float.div (fst xh) (fst yh))))
                     as bqt_lo eqn:Ebqt_lo.

           (* === return cascade ===
              t'18 = dwx && dwy;  t'19 = t'18 && xh_hi;  t'20 = t'19 && yh_hi;
              t'21 = t'20 && yh_lo; t'22 = t'21 && qt_hi; t'23 = t'22 && qt_lo *)
           set (Post_t18 :=
             EX b18 : bool,
             PROP (b18 = true -> b6 = true /\ b8 = true)
             LOCAL (temp _t'18 (Vint (if b18 then Int.one else Int.zero));
                    temp _qt_lo (Vint (if bqt_lo then Int.one else Int.zero));
                    temp _qt_hi (Vint (if bqt_hi then Int.one else Int.zero));
                    temp _yh_lo (Vint (if byh_lo then Int.one else Int.zero));
                    temp _yh_hi (Vint (if byh_hi then Int.one else Int.zero));
                    temp _xh_hi (Vint (if bxh_hi then Int.one else Int.zero));
                    temp _dwx (Vint (if b6 then Int.one else Int.zero));
                    temp _dwy (Vint (if b8 then Int.one else Int.zero));
                    temp _x x; temp _y y)
             SEP (data_at Tsh dword (f2val xh) x;
                  data_at Tsh dword (f2val yh) y)).
           forward_if Post_t18.
           ++ assert (b6 = true) as Hb6_eq by (destruct b6; auto; simpl in H; rep_lia).
              forward. unfold Post_t18; Exists b8; entailer!.
              cascade_close.
           ++ forward. unfold Post_t18; Exists false; entailer!; cascade_close.
           ++ unfold Post_t18; clear Post_t18.
              Intros b18; rename H into Hb18.
              set (Post_t19 :=
                EX b19 : bool,
                PROP (b19 = true -> b6 = true /\ b8 = true /\ bxh_hi = true)
                LOCAL (temp _t'19 (Vint (if b19 then Int.one else Int.zero));
                       temp _qt_lo (Vint (if bqt_lo then Int.one else Int.zero));
                       temp _qt_hi (Vint (if bqt_hi then Int.one else Int.zero));
                       temp _yh_lo (Vint (if byh_lo then Int.one else Int.zero));
                       temp _yh_hi (Vint (if byh_hi then Int.one else Int.zero));
                       temp _t'18 (Vint (if b18 then Int.one else Int.zero));
                       temp _xh_hi (Vint (if bxh_hi then Int.one else Int.zero));
                       temp _x x; temp _y y)
                SEP (data_at Tsh dword (f2val xh) x;
                     data_at Tsh dword (f2val yh) y)).
              forward_if Post_t19.
              --- assert (b18 = true) as Hb18_eq by (destruct b18; auto; simpl in H; rep_lia).
                  forward. unfold Post_t19; Exists bxh_hi; entailer!.
                  cascade_close.
              --- forward. unfold Post_t19; Exists false; entailer!; cascade_close.
              --- unfold Post_t19; clear Post_t19.
                  Intros b19; rename H into Hb19.
                  set (Post_t20 :=
                    EX b20 : bool,
                    PROP (b20 = true -> b6 = true /\ b8 = true /\
                                        bxh_hi = true /\ byh_hi = true)
                    LOCAL (temp _t'20 (Vint (if b20 then Int.one else Int.zero));
                           temp _qt_lo (Vint (if bqt_lo then Int.one else Int.zero));
                           temp _qt_hi (Vint (if bqt_hi then Int.one else Int.zero));
                           temp _yh_lo (Vint (if byh_lo then Int.one else Int.zero));
                           temp _t'19 (Vint (if b19 then Int.one else Int.zero));
                           temp _yh_hi (Vint (if byh_hi then Int.one else Int.zero));
                           temp _x x; temp _y y)
                    SEP (data_at Tsh dword (f2val xh) x;
                         data_at Tsh dword (f2val yh) y)).
                  forward_if Post_t20.
                  ---- assert (b19 = true) as Hb19_eq
                         by (destruct b19; auto; simpl in H; rep_lia).
                       forward. unfold Post_t20; Exists byh_hi; entailer!.
                       cascade_close.
                  ---- forward. unfold Post_t20; Exists false; entailer!; cascade_close.
                  ---- unfold Post_t20; clear Post_t20.
                       Intros b20; rename H into Hb20.
                       set (Post_t21 :=
                         EX b21 : bool,
                         PROP (b21 = true -> b6 = true /\ b8 = true /\
                                             bxh_hi = true /\ byh_hi = true /\
                                             byh_lo = true)
                         LOCAL (temp _t'21 (Vint (if b21 then Int.one else Int.zero));
                                temp _qt_lo (Vint (if bqt_lo then Int.one else Int.zero));
                                temp _qt_hi (Vint (if bqt_hi then Int.one else Int.zero));
                                temp _t'20 (Vint (if b20 then Int.one else Int.zero));
                                temp _yh_lo (Vint (if byh_lo then Int.one else Int.zero));
                                temp _x x; temp _y y)
                         SEP (data_at Tsh dword (f2val xh) x;
                              data_at Tsh dword (f2val yh) y)).
                       forward_if Post_t21.
                       ***** assert (b20 = true) as Hb20_eq
                               by (destruct b20; auto; simpl in H; rep_lia).
                             forward. unfold Post_t21; Exists byh_lo; entailer!.
                             cascade_close.
                       ***** forward. unfold Post_t21; Exists false; entailer!;
                             cascade_close.
                       ***** unfold Post_t21; clear Post_t21.
                             Intros b21; rename H into Hb21.
                             set (Post_t22 :=
                               EX b22 : bool,
                               PROP (b22 = true -> b6 = true /\ b8 = true /\
                                                   bxh_hi = true /\ byh_hi = true /\
                                                   byh_lo = true /\ bqt_hi = true)
                               LOCAL (temp _t'22 (Vint (if b22 then Int.one else Int.zero));
                                      temp _qt_lo (Vint (if bqt_lo then Int.one else Int.zero));
                                      temp _t'21 (Vint (if b21 then Int.one else Int.zero));
                                      temp _qt_hi (Vint (if bqt_hi then Int.one else Int.zero));
                                      temp _x x; temp _y y)
                               SEP (data_at Tsh dword (f2val xh) x;
                                    data_at Tsh dword (f2val yh) y)).
                             forward_if Post_t22.
                             { assert (b21 = true) as Hb21_eq
                                 by (destruct b21; auto; simpl in H; rep_lia).
                               forward. unfold Post_t22; Exists bqt_hi; entailer!.
                               cascade_close. }
                             { forward. unfold Post_t22; Exists false; entailer!;
                               cascade_close. }
                             unfold Post_t22; clear Post_t22.
                             Intros b22; rename H into Hb22.
                             set (Post_t23 :=
                               EX b23 : bool,
                               PROP (b23 = true -> b6 = true /\ b8 = true /\
                                                   bxh_hi = true /\ byh_hi = true /\
                                                   byh_lo = true /\ bqt_hi = true /\
                                                   bqt_lo = true)
                               LOCAL (temp _t'23 (Vint (if b23 then Int.one else Int.zero));
                                      temp _x x; temp _y y)
                               SEP (data_at Tsh dword (f2val xh) x;
                                    data_at Tsh dword (f2val yh) y)).
                             forward_if Post_t23.
                             { assert (b22 = true) as Hb22_eq
                                 by (destruct b22; auto; simpl in H; rep_lia).
                               forward. unfold Post_t23; Exists bqt_lo; entailer!.
                               cascade_close. }
                             { forward. unfold Post_t23; Exists false; entailer!;
                               cascade_close. }
                             unfold Post_t23; clear Post_t23.
                             Intros b23; rename H into Hb23.
                             forward.                    (* return t'23 *)
                             Exists b23; entailer!.

                             (* ===== discharge DWDivDW_cond ===== *)
                             destruct (Hb23 eq_refl)
                               as [Hb6t [Hb8t [Hxhht [Hyhht [Hyhlt [Hqtht Hqtlt]]]]]].
                             destruct (Hb6 Hb6t) as [Hfin_xh [Hfin_xl HDWx]].
                             destruct (Hb8 Hb8t) as [Hfin_yh [Hfin_yl HDWy]].
                             (* No `rewrite Eb..` is needed here: entailer! has
                                already substituted the five remember-equations
                                away, so Hxhht .. Hqtlt arrive as the concrete
                                Float.cmp facts the magnitude lemmas expect. *)

                             (* |xh| <= 2^1022 *)
                             assert (Hxh_hi : Rabs (FT2R (fst xh)) <=
                                       bpow Zaux.radix2 1022)
                               by (apply (Float_cmp_Cle_hi q_omega_val (fst xh)
                                            (bpow Zaux.radix2 1022) Hfin_xh
                                            q_omega_val_finite q_omega_val_FT2R);
                                   exact Hxhht).
                             (* |yh| <= 2^969  (the reciprocal-node bound) *)
                             assert (Hyh_hi : Rabs (FT2R (fst yh)) <=
                                       bpow Zaux.radix2 969)
                               by (apply (Float_cmp_Cle_hi q_hi969_val (fst yh)
                                            (bpow Zaux.radix2 969) Hfin_yh
                                            q_hi969_val_finite q_hi969_val_FT2R);
                                   exact Hyhht).
                             (* 2^(-968) <= |yh| *)
                             assert (Hyh_lo : bpow Zaux.radix2 (-968) <=
                                       Rabs (FT2R (fst yh)))
                               by (apply (Float_cmp_Cle_lo q_lo968_val (fst yh)
                                            (bpow Zaux.radix2 (-968)) Hfin_yh
                                            q_lo968_val_finite q_lo968_val_FT2R);
                                   exact Hyhlt).
                             (* yh <> 0, from the lower bound alone *)
                             assert (Hyhne : FT2R (fst yh) <> 0%R).
                             { intro Hz. rewrite Hz, Rabs_R0 in Hyh_lo.
                               pose proof (bpow_gt_0 Zaux.radix2 (-968)). lra. }
                             (* reciprocal conjunct: 2^(-969) <= |1/yh| *)
                             assert (Hrecip : bpow Zaux.radix2 (-969) <=
                                       Rabs (1 / FT2R (fst yh)))
                               by (apply (recip_lower_from_bpow_upper
                                            (FT2R (fst yh)) 969 Hyhne Hyh_hi)).
                             (* |yh| <= 2^1022, free from the 2^969 bound *)
                             assert (Hyh_om : Rabs (FT2R (fst yh)) <=
                                       bpow Zaux.radix2 1022).
                             { eapply Rle_trans; [exact Hyh_hi | apply bpow_le; lia]. }
                             (* quotient window on the rounded quotient *)
                             destruct (Float_cmp_Clt_bpow1022
                                         (Float.div (fst xh) (fst yh)))
                               as [Hfin_q Hq_hi]; [exact Hqtht |].
                             change (Float.div (fst xh) (fst yh))
                               with (BDIV (fst xh) (fst yh)) in Hfin_q, Hq_hi.
                             assert (Hqt_lo0 : bpow Zaux.radix2 (-969) <
                                       Rabs (FT2R (BDIV (fst xh) (fst yh))))
                               by (apply (Float_cmp_Clt_lo q_lo969_val
                                            (BDIV (fst xh) (fst yh))
                                            (bpow Zaux.radix2 (-969)) Hfin_q
                                            q_lo969_val_finite q_lo969_val_FT2R);
                                   exact Hqtlt).
                             assert (Hfmt1022 : generic_format radix2 fexp
                                       (bpow Zaux.radix2 1022))
                               by (apply generic_format_bpow;
                                   unfold fexp, SpecFloat.fexp, SpecFloat.emin;
                                   try change (fprec Tdouble) with 53%Z;
                                   try change (femax Tdouble) with 1024%Z;
                                   apply Z.max_lub; lia).
                             assert (Hfmt969 : generic_format radix2 fexp
                                       (bpow Zaux.radix2 (-969)))
                               by (apply generic_format_bpow;
                                   unfold fexp, SpecFloat.fexp, SpecFloat.emin;
                                   try change (fprec Tdouble) with 53%Z;
                                   try change (femax Tdouble) with 1024%Z;
                                   apply Z.max_lub; lia).
                             (* rounded -> exact transfer *)
                             assert (Hquot_hi : Rabs (FT2R (fst xh) / FT2R (fst yh)) <=
                                       bpow Zaux.radix2 1022)
                               by (apply (BDIV_abs_le_bpow (fst xh) (fst yh) 1022
                                            Hyhne Hfin_q Hfmt1022); exact Hq_hi).
                             assert (Hquot_lo : bpow Zaux.radix2 (-969) <
                                       Rabs (FT2R (fst xh) / FT2R (fst yh)))
                               by (apply (BDIV_abs_gt_bpow (fst xh) (fst yh) (-969)
                                            Hyhne Hfin_q Hfmt969); exact Hqt_lo0).
                             unfold DDModels.DWDivDW_cond.
                             repeat split; try assumption;
                             try (apply Rlt_le; exact Hquot_lo);
                             try exact Hrecip;
                             try exact Hyh_lo;
                             try exact Hxh_hi;
                             try exact Hyh_om;
                             try exact Hquot_hi.
Qed.
