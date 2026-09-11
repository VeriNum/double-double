(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.
Require Import DD.verif_proofs.verif_fp_utils_short_circuit.

Local Ltac cascade_gather :=
  repeat match goal with
         | H : ?A = true -> _, H2 : ?A = true |- _ => specialize (H H2)
         end;
  repeat match goal with
         | H : _ = true -> _ |- _ => specialize (H eq_refl)
         end;
  repeat match goal with H : _ /\ _ |- _ => destruct H end.

Local Ltac cascade_close :=
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

Lemma body_dw_div_dw_strong_precond_check :
  semax_body Vprog Gprog f_dw_div_dw_strong_precond_check dw_div_dw_strong_precond_check_spec.
Proof.
  start_function.

  forward. forward_call. Intros vret_fxh. rename H into Hspec_fxh. forward.
  forward. forward_call. Intros vret_fxl. rename H into Hspec_fxl. forward.
  forward. forward_call. Intros vret_fyh. rename H into Hspec_fyh. forward.
  forward. forward_call. Intros vret_fyl. rename H into Hspec_fyl. forward.

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
      forward.

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
           forward.

           forward_call.
           forward_call.
           forward_call.
           replace (- Int.unsigned (Int.repr 968))%Z with (-968)%Z by reflexivity.
           fold q_omega_val q_hi966_val q_lo968_val.
           forward. forward_call (fst yh). forward.
           forward. forward_call (fst yh). forward.

           remember (Float.cmp Cle
                       (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (fst yh))
                       q_hi966_val) as byh_hi eqn:Ebyh_hi.
           remember (Float.cmp Cle q_lo968_val
                       (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (fst yh)))
                     as byh_lo eqn:Ebyh_lo.

           set (Post_t15 :=
             EX b15 : bool,
             PROP (b15 = true -> b6 = true /\ b8 = true)
             LOCAL (temp _t'14 (Vint (if b15 then Int.one else Int.zero));
                    temp _q_omega (Vfloat q_omega_val);
                    temp _yh_lo (Vint (if byh_lo then Int.one else Int.zero));
                    temp _yh_hi (Vint (if byh_hi then Int.one else Int.zero));
                    temp _dwx (Vint (if b6 then Int.one else Int.zero));
                    temp _dwy (Vint (if b8 then Int.one else Int.zero));
                    temp _x x; temp _y y)
             SEP (data_at Tsh dword (f2val xh) x;
                  data_at Tsh dword (f2val yh) y)).
           forward_if Post_t15.
           ++ assert (b6 = true) as Hb6_eq by (destruct b6; auto; simpl in H; rep_lia).
              forward. unfold Post_t15; Exists b8; entailer!.
              cascade_close.
           ++ forward. unfold Post_t15; Exists false; entailer!; cascade_close.
           ++ unfold Post_t15; clear Post_t15.
              Intros b15; rename H into Hb15.
              set (Post_t16 :=
                EX b16 : bool,
                PROP (b16 = true -> b6 = true /\ b8 = true /\ byh_hi = true)
                LOCAL (temp _t'15 (Vint (if b16 then Int.one else Int.zero));
                       temp _q_omega (Vfloat q_omega_val);
                       temp _yh_lo (Vint (if byh_lo then Int.one else Int.zero));
                       temp _t'14 (Vint (if b15 then Int.one else Int.zero));
                       temp _yh_hi (Vint (if byh_hi then Int.one else Int.zero));
                       temp _x x; temp _y y)
                SEP (data_at Tsh dword (f2val xh) x;
                     data_at Tsh dword (f2val yh) y)).
              forward_if Post_t16.
              --- assert (b15 = true) as Hb15_eq by (destruct b15; auto; simpl in H; rep_lia).
                  forward. unfold Post_t16; Exists byh_hi; entailer!.
                  cascade_close.
              --- forward. unfold Post_t16; Exists false; entailer!; cascade_close.
              --- unfold Post_t16; clear Post_t16.
                  Intros b16; rename H into Hb16.
                  set (Post_t17 :=
                    EX b17 : bool,
                    PROP (b17 = true -> b6 = true /\ b8 = true /\
                                        byh_hi = true /\ byh_lo = true)
                    LOCAL (temp _t'16 (Vint (if b17 then Int.one else Int.zero));
                           temp _q_omega (Vfloat q_omega_val);
                           temp _t'15 (Vint (if b16 then Int.one else Int.zero));
                           temp _yh_lo (Vint (if byh_lo then Int.one else Int.zero));
                           temp _x x; temp _y y)
                    SEP (data_at Tsh dword (f2val xh) x;
                         data_at Tsh dword (f2val yh) y)).
                  forward_if Post_t17.
                  ---- assert (b16 = true) as Hb16_eq
                         by (destruct b16; auto; simpl in H; rep_lia).
                       forward. unfold Post_t17; Exists byh_lo; entailer!.
                       cascade_close.
                  ---- forward. unfold Post_t17; Exists false; entailer!; cascade_close.
                  ---- unfold Post_t17; clear Post_t17.
                       Intros b17; rename H into Hb17.
                       forward.
                       forward_if.
                       { forward. Exists false. entailer!. }
                       assert (b17 = true) as Hb17t
                         by (destruct b17; auto; simpl in H; rep_lia).
                       forward. forward. forward.
                       forward_call (Float.div (fst xh) (fst yh)).
                       forward.
                       set (bqt_hi := Float.cmp Clt
                         (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble))
                           (Float.div (fst xh) (fst yh))) q_omega_val).
                       forward.
                       Exists bqt_hi; entailer!.
                       split.
                       { intros Hqtht.

                             destruct (Hb17 eq_refl)
                               as [Hb6t [Hb8t [Hyhht Hyhlt]]].
                             destruct (Hb6 Hb6t) as [Hfin_xh [Hfin_xl HDWx]].
                             destruct (Hb8 Hb8t) as [Hfin_yh [Hfin_yl HDWy]].

                             assert (Hyh_hi : Rabs (FT2R (fst yh)) <=
                                       bpow Zaux.radix2 966)
                               by (apply (Float_cmp_Cle_hi q_hi966_val (fst yh)
                                            (bpow Zaux.radix2 966) Hfin_yh
                                            q_hi966_val_finite q_hi966_val_FT2R);
                                   exact Hyhht).

                             assert (Hyh_lo : bpow Zaux.radix2 (-968) <=
                                       Rabs (FT2R (fst yh)))
                               by (apply (Float_cmp_Cle_lo q_lo968_val (fst yh)
                                            (bpow Zaux.radix2 (-968)) Hfin_yh
                                            q_lo968_val_finite q_lo968_val_FT2R);
                                   exact Hyhlt).

                             assert (Hyhne : FT2R (fst yh) <> 0%R).
                             { intro Hz. rewrite Hz, Rabs_R0 in Hyh_lo.
                               pose proof (bpow_gt_0 Zaux.radix2 (-968)). lra. }

                             destruct (Float_cmp_Clt_bpow1022
                                         (Float.div (fst xh) (fst yh)))
                               as [Hfin_q Hq_hi]; [exact Hqtht |].
                             change (Float.div (fst xh) (fst yh))
                               with (BDIV (fst xh) (fst yh)) in Hfin_q, Hq_hi.
                             assert (Hfmt1022 : generic_format radix2 fexp
                                       (bpow Zaux.radix2 1022))
                               by (apply generic_format_bpow;
                                   unfold fexp, SpecFloat.fexp, SpecFloat.emin;
                                   try change (fprec Tdouble) with 53%Z;
                                   try change (femax Tdouble) with 1024%Z;
                                   apply Z.max_lub; lia).

                             assert (Hquot_hi : Rabs (FT2R (fst xh) / FT2R (fst yh)) <=
                                       bpow Zaux.radix2 1022)
                               by (apply (BDIV_abs_le_bpow (fst xh) (fst yh) 1022
                                            Hyhne Hfin_q Hfmt1022); exact Hq_hi).
                             unfold DDConds.DWDivDW_strong_precond.
                             repeat split; try assumption;
                             try exact Hyh_hi;
                             try exact Hyh_lo;
                             try exact Hquot_hi. }
                       { destruct bqt_hi; reflexivity. }
Qed.

Lemma body_dw_div_dw_weak_precond_check :
  semax_body Vprog Gprog f_dw_div_dw_weak_precond_check dw_div_dw_weak_precond_check_spec.
Proof.
  start_function.
  forward. forward_call. Intros vret_fxh. rename H into Hspec_fxh. forward.
  forward. forward_call. Intros vret_fxl. rename H into Hspec_fxl. forward.
  forward. forward_call. Intros vret_fyh. rename H into Hspec_fyh. forward.
  forward. forward_call. Intros vret_fyl. rename H into Hspec_fyl. forward.

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
    forward. unfold Post_t5; Exists vret_fxl; entailer!.
    split.
    + intros Hout.
      apply (short_circuit_fin_and_concl (fst xh) (snd xh) true vret_fxl vret_fxl
              Hspec_fxh Hspec_fxl eq_refl). exact Hout.
    + destruct vret_fxl; simpl; auto.
  - forward. unfold Post_t5; Exists false; entailer!.
  - unfold Post_t5; clear Post_t5. Intros b5; rename H into Hb5.
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
    + forward. unfold Post_t6; Exists false; entailer!.
    + unfold Post_t6; clear Post_t6. Intros b6; rename H into Hb6. forward.
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
        forward. unfold Post_t7; Exists vret_fyl; entailer!.
        split.
        ** intros Hout.
           apply (short_circuit_fin_and_concl (fst yh) (snd yh) true vret_fyl vret_fyl
                   Hspec_fyh Hspec_fyl eq_refl). exact Hout.
        ** destruct vret_fyl; simpl; auto.
      * forward. unfold Post_t7; Exists false; entailer!.
      * unfold Post_t7; clear Post_t7. Intros b7; rename H into Hb7.
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
        ** unfold Post_t8; clear Post_t8. Intros b8; rename H into Hb8. forward.
           forward_call.
           forward_call.
           replace (- Int.unsigned (Int.repr 968))%Z with (-968)%Z by reflexivity.
           fold q_hi966_val q_lo968_val.
           forward. forward_call (fst yh). forward.
           forward. forward_call (fst yh). forward.

           remember (Float.cmp Cle
                       (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (fst yh))
                       q_hi966_val) as byh_hi eqn:Ebyh_hi.
           remember (Float.cmp Cle q_lo968_val
                       (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (fst yh)))
                     as byh_lo eqn:Ebyh_lo.

           set (Post_t13 :=
             EX b13 : bool,
             PROP (b13 = true -> b6 = true /\ b8 = true)
             LOCAL (temp _t'13 (Vint (if b13 then Int.one else Int.zero));
                    temp _yh_lo (Vint (if byh_lo then Int.one else Int.zero));
                    temp _yh_hi (Vint (if byh_hi then Int.one else Int.zero));
                    temp _dwx (Vint (if b6 then Int.one else Int.zero));
                    temp _dwy (Vint (if b8 then Int.one else Int.zero));
                    temp _x x; temp _y y)
             SEP (data_at Tsh dword (f2val xh) x;
                  data_at Tsh dword (f2val yh) y)).
           forward_if Post_t13.
           ++ assert (b6 = true) as Hb6_eq
                by (destruct b6; auto; simpl in H; rep_lia).
              forward. unfold Post_t13; Exists b8; entailer!. cascade_close.
           ++ forward. unfold Post_t13; Exists false; entailer!; cascade_close.
           ++ unfold Post_t13; clear Post_t13. Intros b13; rename H into Hb13.
              set (Post_t14 :=
                EX b14 : bool,
                PROP (b14 = true -> b6 = true /\ b8 = true /\ byh_hi = true)
                LOCAL (temp _t'14 (Vint (if b14 then Int.one else Int.zero));
                       temp _yh_lo (Vint (if byh_lo then Int.one else Int.zero));
                       temp _t'13 (Vint (if b13 then Int.one else Int.zero));
                       temp _yh_hi (Vint (if byh_hi then Int.one else Int.zero));
                       temp _x x; temp _y y)
                SEP (data_at Tsh dword (f2val xh) x;
                     data_at Tsh dword (f2val yh) y)).
              forward_if Post_t14.
              --- assert (b13 = true) as Hb13_eq
                    by (destruct b13; auto; simpl in H; rep_lia).
                  forward. unfold Post_t14; Exists byh_hi; entailer!. cascade_close.
              --- forward. unfold Post_t14; Exists false; entailer!; cascade_close.
              --- unfold Post_t14; clear Post_t14. Intros b14; rename H into Hb14.
                  set (Post_t15 :=
                    EX b15 : bool,
                    PROP (b15 = true -> b6 = true /\ b8 = true /\
                                        byh_hi = true /\ byh_lo = true)
                    LOCAL (temp _t'15 (Vint (if b15 then Int.one else Int.zero));
                           temp _x x; temp _y y)
                    SEP (data_at Tsh dword (f2val xh) x;
                         data_at Tsh dword (f2val yh) y)).
                  forward_if Post_t15.
                  ---- assert (b14 = true) as Hb14_eq
                         by (destruct b14; auto; simpl in H; rep_lia).
                       forward. unfold Post_t15; Exists byh_lo; entailer!.
                       cascade_close.
                  ---- forward. unfold Post_t15; Exists false; entailer!;
                       cascade_close.
                  ---- unfold Post_t15; clear Post_t15.
                       Intros b15; rename H into Hb15.
                       forward. Exists b15; entailer!.
                       destruct (Hb15 eq_refl)
                         as [Hb6t [Hb8t [Hyhht Hyhlt]]].
                       destruct (Hb6 Hb6t) as [_ [_ HDWx]].
                       destruct (Hb8 Hb8t) as [Hfin_yh [_ HDWy]].
                       assert (Hyh_hi : Rabs (FT2R (fst yh)) <=
                                 bpow Zaux.radix2 966)
                         by (apply (Float_cmp_Cle_hi q_hi966_val (fst yh)
                                      (bpow Zaux.radix2 966) Hfin_yh
                                      q_hi966_val_finite q_hi966_val_FT2R);
                             exact Hyhht).
                       assert (Hyh_lo : bpow Zaux.radix2 (-968) <=
                                 Rabs (FT2R (fst yh)))
                         by (apply (Float_cmp_Cle_lo q_lo968_val (fst yh)
                                      (bpow Zaux.radix2 (-968)) Hfin_yh
                                      q_lo968_val_finite q_lo968_val_FT2R);
                             exact Hyhlt).
                       unfold DDConds.DWDivDW_weak_precond.
                       repeat split; try assumption;
                       try exact Hyh_hi; try exact Hyh_lo.
Qed.
