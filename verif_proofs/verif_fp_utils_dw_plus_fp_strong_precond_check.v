(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.
Require Import DD.verif_proofs.verif_fp_utils_short_circuit.

Lemma body_dw_plus_fp_strong_precond_check :
  semax_body Vprog Gprog f_dw_plus_fp_strong_precond_check dw_plus_fp_strong_precond_check_spec.
Proof.
  start_function.

  forward. forward_call. Intros vret_fxh. rename H into Hspec_fxh. forward.

  forward. forward_call. Intros vret_fxl. rename H into Hspec_fxl. forward.

  forward_call. Intros vret_fy. rename H into Hspec_fy.

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
  -
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
  -
    forward.
    unfold Post_t4; Exists false; entailer!.
  -
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
    +
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
    +
      forward.
      unfold Post_t5; Exists false; entailer!.
    +
      unfold Post_t5; clear Post_t5.
      Intros b5; rename H into Hb5.
      forward.

      forward_call.
      forward.

      forward_call (fst xh).
      forward.

      forward_call (y).
      forward.

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
      *
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
      *
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
      *
        unfold Post_t9; clear Post_t9.
        Intros b9; rename H into Hb9.

        set (Post_t10 :=
          EX b10 : bool,
          PROP (b10 = true -> b5 = true /\ vret_fy = true /\ bxh = true)
          LOCAL (temp _t'10 (Vint (if b10 then Int.one else Int.zero));
                 temp _y_bnd (Vint (if byb then Int.one else Int.zero));
                 temp _t'9 (Vint (if b9 then Int.one else Int.zero));
                 temp _x x; temp _y (Vfloat y))
          SEP (data_at Tsh dword (f2val xh) x)).
        forward_if Post_t10.
        **
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
        **
           forward. unfold Post_t10; Exists false; entailer!.
        **
           unfold Post_t10; clear Post_t10.
           Intros b10; rename H into Hb10.

           set (Post_t11 :=
             EX b11 : bool,
             PROP (b11 = true -> b5 = true /\ vret_fy = true /\
                                 bxh = true /\ byb = true)
             LOCAL (temp _t'11 (Vint (if b11 then Int.one else Int.zero));
                    temp _x x; temp _y (Vfloat y))
             SEP (data_at Tsh dword (f2val xh) x)).
           forward_if Post_t11.
           ***
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
           ***
               forward. unfold Post_t11; Exists false; entailer!.
           ***
               unfold Post_t11; clear Post_t11.
               Intros b11; rename H into Hb11.
               forward.
               Exists b11; entailer!.
               destruct (Hb11 eq_refl) as [Hb5t [Hfyt [Hbxht Hbybt]]].
               destruct (Hb5 Hb5t) as [Hfin_xh [Hfin_xl HDWx]].
               assert (Hfin_y : is_finite y = true) by (apply (proj1 Hspec_fy); exact Hfyt).
               unfold DDConds.DWPlusFP_strong_precond.
               repeat (split; try assumption).
               { apply Float_cmp_Cle_bpow1022; [exact Hfin_xh|].
                 unfold bxh, q_omega_val in Hbxht. exact Hbxht. }
               { apply Float_cmp_Cle_bpow1022; [exact Hfin_y|].
                 unfold byb, q_omega_val in Hbybt. exact Hbybt. }
Qed.
