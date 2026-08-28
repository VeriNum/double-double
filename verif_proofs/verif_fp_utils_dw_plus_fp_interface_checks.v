(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.
Require Import DD.verif_proofs.verif_fp_utils_short_circuit.

Lemma body_dw_plus_fp_input_check :
  semax_body Vprog Gprog f_dw_plus_fp_input_check
    dw_plus_fp_input_check_spec.
Proof.
  start_function.
  forward. forward_call. Intros vret_fxh. rename H into Hspec_fxh. forward.
  forward. forward_call. Intros vret_fxl. rename H into Hspec_fxl. forward.
  forward_call. Intros vret_fy. rename H into Hspec_fy.

  set (Post_t4 :=
    EX b4 : bool,
    PROP (b4 = true ->
          is_finite (fst value) = true /\ is_finite (snd value) = true)
    LOCAL (temp _t'4 (Vint (if b4 then Int.one else Int.zero));
           temp _fin_xh (Vint (if vret_fxh then Int.one else Int.zero));
           temp _fin_xl (Vint (if vret_fxl then Int.one else Int.zero));
           temp _fin_y (Vint (if vret_fy then Int.one else Int.zero));
           temp _x x; temp _y (Vfloat y))
    SEP (data_at Tsh dword (f2val value) x)).
  forward_if Post_t4.
  - assert (vret_fxh = true) as Hvfxh.
    { destruct vret_fxh; auto; simpl in H; rep_lia. }
    forward.
    unfold Post_t4; Exists vret_fxl; entailer!.
    split.
    + intros Hout.
      apply (short_circuit_fin_and_concl
        (fst value) (snd value) true vret_fxl vret_fxl
        Hspec_fxh Hspec_fxl eq_refl Hout).
    + destruct vret_fxl; reflexivity.
  - forward. unfold Post_t4; Exists false; entailer!.
  - unfold Post_t4; clear Post_t4.
    Intros b4; rename H into Hb4.
    set (Post_t5 :=
      EX b5 : bool,
      PROP (b5 = true ->
            is_finite (fst value) = true /\
            is_finite (snd value) = true /\
            double_word_prop (fst value) (snd value))
      LOCAL (temp _t'5 (Vint (if b5 then Int.one else Int.zero));
             temp _fin_y (Vint (if vret_fy then Int.one else Int.zero));
             temp _x x; temp _y (Vfloat y))
      SEP (data_at Tsh dword (f2val value) x)).
    forward_if Post_t5.
    + assert (b4 = true) as Hb4_eq.
      { destruct b4; auto; simpl in H; rep_lia. }
      forward. forward. forward. forward.
      unfold Post_t5.
      Exists (Float.cmp Ceq
        (Float.add (float_of_ftype (fst value))
                   (float_of_ftype (snd value)))
        (float_of_ftype (fst value))).
      entailer!.
      split.
      * intros Hout.
        apply (short_circuit_dw_eq_concl
          (fst value) (snd value) true
          (Float.cmp Ceq
            (Float.add (float_of_ftype (fst value))
                       (float_of_ftype (snd value)))
            (float_of_ftype (fst value))) Hb4 eq_refl Hout).
      * destruct (Float.cmp _ _ _); reflexivity.
    + forward. unfold Post_t5; Exists false; entailer!.
    + unfold Post_t5; clear Post_t5.
      Intros b5; rename H into Hb5.
      forward.
      set (Post_t6 :=
        EX b6 : bool,
        PROP (b6 = true -> b5 = true /\ vret_fy = true)
        LOCAL (temp _t'6 (Vint (if b6 then Int.one else Int.zero));
               temp _dwx (Vint (if b5 then Int.one else Int.zero));
               temp _fin_y (Vint (if vret_fy then Int.one else Int.zero));
               temp _x x; temp _y (Vfloat y))
        SEP (data_at Tsh dword (f2val value) x)).
      forward_if Post_t6.
      * assert (b5 = true) as Hb5_eq.
        { destruct b5; auto; simpl in H; rep_lia. }
        forward. unfold Post_t6; Exists vret_fy; entailer!.
        destruct vret_fy; reflexivity.
      * forward. unfold Post_t6; Exists false; entailer!.
      * unfold Post_t6; clear Post_t6.
        Intros b6; rename H into Hb6.
        forward. Exists b6; entailer!.
        destruct (Hb6 eq_refl) as [Hb5t Hfyt].
        destruct (Hb5 Hb5t) as [_ [_ HDW]].
        unfold DWPlusFP_input_cond. exact HDW.
Qed.

Lemma body_dword_finite_check :
  semax_body Vprog Gprog f_dword_finite_check dword_finite_check_spec.
Proof.
  start_function.
  forward. forward_call. Intros vret_s. rename H into Hspec_s. forward.
  forward. forward_call. Intros vret_t. forward.
  set (Post_s :=
    PROP (is_finite (fst value) = true)
    LOCAL (temp _fin_s (Vint (if vret_s then Int.one else Int.zero));
           temp _fin_t (Vint (if vret_t then Int.one else Int.zero));
           temp _x x)
    SEP (data_at Tsh dword (f2val value) x)).
  forward_if Post_s.
  - forward. Exists false. entailer!.
  - forward. unfold Post_s. entailer!.
    apply (proj1 Hspec_s). destruct vret_s; auto.
  - unfold Post_s; clear Post_s.
    assert_PROP (is_finite (fst value) = true) as Hfin_s by entailer!.
    set (Post_t :=
      PROP (is_finite_p value)
      LOCAL (temp _fin_s (Vint (if vret_s then Int.one else Int.zero));
             temp _fin_t (Vint (if vret_t then Int.one else Int.zero));
             temp _x x)
      SEP (data_at Tsh dword (f2val value) x)).
    forward_if Post_t.
    + forward. Exists false. entailer!.
    + forward. unfold Post_t. entailer!.
      split; [exact Hfin_s |].
      match goal with
      | Hspec_t : vret_t = true <-> is_finite (snd value) = true |- _ =>
          apply (proj1 Hspec_t); destruct vret_t; auto
      end.
    + unfold Post_t; clear Post_t.
      assert_PROP (is_finite_p value) as Hfin by entailer!.
      forward. Exists true. entailer!.
Qed.
