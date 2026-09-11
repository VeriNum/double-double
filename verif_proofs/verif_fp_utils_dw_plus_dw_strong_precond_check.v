(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.
Require Import DD.verif_proofs.verif_fp_utils_short_circuit.

Lemma body_dw_plus_dw_strong_precond_check :
  semax_body Vprog Gprog f_dw_plus_dw_strong_precond_check dw_plus_dw_strong_precond_check_spec.
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
  -
    assert (vret_fxh = true) as Hvfxh.
    { destruct vret_fxh; auto; simpl in H; rep_lia. }
    forward.
    unfold Post_t5; Exists vret_fxl; entailer!.

    split.
    + intros Hout.
      apply (short_circuit_fin_and_concl (fst xh) (snd xh) true vret_fxl vret_fxl
              Hspec_fxh Hspec_fxl eq_refl).
      exact Hout.
    + destruct vret_fxl; simpl; auto.
  -
    forward.
    unfold Post_t5; Exists false; entailer!.
  -
    unfold Post_t5; clear Post_t5.
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
    +
      assert (b5 = true) as Hb5_eq.
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
    +
      forward.
      unfold Post_t6; Exists false; entailer!.
    +
      unfold Post_t6; clear Post_t6.
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
           forward.

           forward_call.
           forward.

           forward_call (fst xh).
           forward.

           forward.
           forward_call (fst yh).
           forward.

           set (bxh := Float.cmp Cle
                         (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (fst xh))
                         q_omega_val).
           set (byh := Float.cmp Cle
                         (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (fst yh))
                         q_omega_val).
           set (Post_t12 :=
             EX b12 : bool,
             PROP (b12 = true -> b6 = true /\ b8 = true)
             LOCAL (temp _t'12 (Vint (if b12 then Int.one else Int.zero));
                    temp _yh_bnd (Vint (if byh then Int.one else Int.zero));
                    temp _xh_bnd (Vint (if bxh then Int.one else Int.zero));
                    temp _q_omega (Vfloat q_omega_val);
                    temp _dwy (Vint (if b8 then Int.one else Int.zero));
                    temp _dwx (Vint (if b6 then Int.one else Int.zero));
                    temp _x x; temp _y y)
             SEP (data_at Tsh dword (f2val xh) x;
                  data_at Tsh dword (f2val yh) y)).
           forward_if Post_t12.
           ++
              assert (b6 = true) as Hb6_eq.
              { destruct b6; auto; simpl in H; rep_lia. }
              forward.
              unfold Post_t12; Exists b8; entailer!.
              split3.
              { destruct b8; reflexivity. }
              { unfold byh, q_omega_val.
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
           ++
              forward. unfold Post_t12; Exists false; entailer!.
              split.
              { unfold byh, q_omega_val.
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
           ++
              unfold Post_t12; clear Post_t12.
              Intros b12; rename H into Hb12.

              set (Post_t13 :=
                EX b13 : bool,
                PROP (b13 = true -> b6 = true /\ b8 = true /\ bxh = true)
                LOCAL (temp _t'13 (Vint (if b13 then Int.one else Int.zero));
                       temp _yh_bnd (Vint (if byh then Int.one else Int.zero));
                       temp _t'12 (Vint (if b12 then Int.one else Int.zero));
                       temp _x x; temp _y y)
                SEP (data_at Tsh dword (f2val xh) x;
                     data_at Tsh dword (f2val yh) y)).
              forward_if Post_t13.
              +++
                  assert (b12 = true) as Hb12_eq.
                  { destruct b12; auto; simpl in H; rep_lia. }
                  forward.
                  unfold Post_t13; Exists bxh; entailer!.
                  split.
                  { intros Hout. destruct (Hb12 eq_refl); auto. }
                  { unfold bxh, q_omega_val.
                    change (femax Tdouble) with 1024%Z.
                    match goal with
                    | |- context [Float.cmp Cle ?a ?b] =>
                        destruct (Float.cmp Cle a b); reflexivity
                    end. }
              +++
                  forward. unfold Post_t13; Exists false; entailer!.
              +++
                  unfold Post_t13; clear Post_t13.
                  Intros b13; rename H into Hb13.

                  set (Post_t14 :=
                    EX b14 : bool,
                    PROP (b14 = true -> b6 = true /\ b8 = true /\
                                        bxh = true /\ byh = true)
                    LOCAL (temp _t'14 (Vint (if b14 then Int.one else Int.zero));
                           temp _x x; temp _y y)
                    SEP (data_at Tsh dword (f2val xh) x;
                         data_at Tsh dword (f2val yh) y)).
                  forward_if Post_t14.
                  ++++
                       assert (b13 = true) as Hb13_eq.
                       { destruct b13; auto; simpl in H; rep_lia. }
                       forward.
                       unfold Post_t14; Exists byh; entailer!.
                       split.
                       { intros Hout.
                         destruct (Hb13 eq_refl) as [Hb6t [Hb8t Hbxht]].
                         auto. }
                       { unfold byh, q_omega_val.
                         change (femax Tdouble) with 1024%Z.
                         match goal with
                         | |- context [Float.cmp Cle ?a ?b] =>
                             destruct (Float.cmp Cle a b); reflexivity
                         end. }
                  ++++
                       forward. unfold Post_t14; Exists false; entailer!.
                  ++++
                       unfold Post_t14; clear Post_t14.
                       Intros b14; rename H into Hb14.
                       forward.
                       Exists b14; entailer!.

                       destruct (Hb14 eq_refl) as [Hb6t [Hb8t [Hbxht Hbyht]]].
                       destruct (Hb6 Hb6t) as [Hfin_xh [Hfin_xl HDWx]].
                       destruct (Hb8 Hb8t) as [Hfin_yh [Hfin_yl HDWy]].
                       unfold DDConds.DWPlusDW_strong_precond.
                       repeat (split; try assumption).
                       { apply Float_cmp_Cle_bpow1022; [exact Hfin_xh|].
                         unfold bxh, q_omega_val in Hbxht.
                         exact Hbxht. }
                       { apply Float_cmp_Cle_bpow1022; [exact Hfin_yh|].
                         unfold byh, q_omega_val in Hbyht.
                         exact Hbyht. }
Qed.

Lemma body_dw_plus_dw_weak_precond_check :
  semax_body Vprog Gprog f_dw_plus_dw_weak_precond_check
    dw_plus_dw_weak_precond_check_spec.
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
  - assert (vret_fxh = true) as Hvfxh.
    { destruct vret_fxh; auto; simpl in H; rep_lia. }
    forward. unfold Post_t5; Exists vret_fxl; entailer!.
    split.
    + intros Hout.
      apply (short_circuit_fin_and_concl
        (fst xh) (snd xh) true vret_fxl vret_fxl
        Hspec_fxh Hspec_fxl eq_refl Hout).
    + destruct vret_fxl; reflexivity.
  - forward. unfold Post_t5; Exists false; entailer!.
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
    + assert (b5 = true) as Hb5_eq.
      { destruct b5; auto; simpl in H; rep_lia. }
      forward. forward. forward. forward.
      unfold Post_t6.
      Exists (Float.cmp Ceq
        (Float.add (float_of_ftype (fst xh))
                   (float_of_ftype (snd xh)))
        (float_of_ftype (fst xh))).
      entailer!.
      split.
      * intros Hout.
        apply (short_circuit_dw_eq_concl
          (fst xh) (snd xh) true
          (Float.cmp Ceq
            (Float.add (float_of_ftype (fst xh))
                       (float_of_ftype (snd xh)))
            (float_of_ftype (fst xh))) Hb5 eq_refl Hout).
      * destruct (Float.cmp _ _ _); reflexivity.
    + forward. unfold Post_t6; Exists false; entailer!.
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
      * assert (vret_fyh = true) as Hvfyh.
        { destruct vret_fyh; auto; simpl in H; rep_lia. }
        forward. unfold Post_t7; Exists vret_fyl; entailer!.
        split.
        ** intros Hout.
           apply (short_circuit_fin_and_concl
             (fst yh) (snd yh) true vret_fyl vret_fyl
             Hspec_fyh Hspec_fyl eq_refl Hout).
        ** destruct vret_fyl; reflexivity.
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
        ** assert (b7 = true) as Hb7_eq.
           { destruct b7; auto; simpl in H; rep_lia. }
           forward. forward. forward. forward.
           unfold Post_t8.
           Exists (Float.cmp Ceq
             (Float.add (float_of_ftype (fst yh))
                        (float_of_ftype (snd yh)))
             (float_of_ftype (fst yh))).
           entailer!.
           split.
           --- intros Hout.
               apply (short_circuit_dw_eq_concl
                 (fst yh) (snd yh) true
                 (Float.cmp Ceq
                   (Float.add (float_of_ftype (fst yh))
                              (float_of_ftype (snd yh)))
                   (float_of_ftype (fst yh))) Hb7 eq_refl Hout).
           --- destruct (Float.cmp _ _ _); reflexivity.
        ** forward. unfold Post_t8; Exists false; entailer!.
        ** unfold Post_t8; clear Post_t8.
           Intros b8; rename H into Hb8.
           forward.
           set (Post_t9 :=
             EX b9 : bool,
             PROP (b9 = true -> b6 = true /\ b8 = true)
             LOCAL (temp _t'9 (Vint (if b9 then Int.one else Int.zero));
                    temp _dwy (Vint (if b8 then Int.one else Int.zero));
                    temp _dwx (Vint (if b6 then Int.one else Int.zero));
                    temp _x x; temp _y y)
             SEP (data_at Tsh dword (f2val xh) x;
                  data_at Tsh dword (f2val yh) y)).
           forward_if Post_t9.
           ++ assert (b6 = true) as Hb6_eq.
              { destruct b6; auto; simpl in H; rep_lia. }
              forward. unfold Post_t9; Exists b8; entailer!.
              destruct b8; reflexivity.
           ++ forward. unfold Post_t9; Exists false; entailer!.
           ++ unfold Post_t9; clear Post_t9.
              Intros b9; rename H into Hb9.
              forward. Exists b9; entailer!.
              destruct (Hb9 eq_refl) as [Hb6t Hb8t].
              destruct (Hb6 Hb6t) as [_ [_ HDWx]].
              destruct (Hb8 Hb8t) as [_ [_ HDWy]].
              unfold DWPlusDW_weak_precond. exact (conj HDWx HDWy).
Qed.
