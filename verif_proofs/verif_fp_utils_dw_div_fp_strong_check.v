(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.
Require Import DD.verif_proofs.verif_fp_utils_short_circuit.

Lemma body_dw_div_fp_strong_check :
  semax_body Vprog Gprog f_dw_div_fp_strong_check dw_div_fp_strong_check_spec.
Proof.
  start_function.
  forward_call (x, xh, y).
  Intros bweak. rename H into Hbweak.
  forward_if.
  - forward. Exists false. entailer!.
  - assert (bweak = true) as Hbweakt
      by (destruct bweak; auto; simpl in H; rep_lia).
    destruct (Hbweak Hbweakt)
      as [Hfin_xh [Hfin_xl [Hfin_y Hweak]]].
    destruct Hweak as [HDWx Hxh_lo].

    forward_call.
    fold q_omega_val.
    forward.
    forward_call (fst xh).

    set (bxh_hi := Float.cmp Cle
      (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (fst xh))
      q_omega_val).
    set (by_zero := Float.cmp Ceq y (Float.of_bits (Int64.repr 0))).
    set (Post_bad :=
      EX bad : bool,
      PROP (bad = false -> bxh_hi = true)
      LOCAL (temp _t'4 (Vint (if bad then Int.one else Int.zero));
             temp _q_omega (Vfloat q_omega_val);
             temp _x x; temp _y (Vfloat y))
      SEP (data_at Tsh dword (f2val xh) x)).
    forward_if Post_bad.
    + forward.
      unfold Post_bad. Exists true. entailer!.
    + forward.
      unfold Post_bad. Exists by_zero. entailer!.
      split.
      * intros _. unfold bxh_hi.
        destruct (Float.cmp Cle
          (Binary.Babs (fprec Tdouble) (femax Tdouble)
            (abs_nan (fprec Tdouble) (femax Tdouble)
              (fprec_gt_one Tdouble)) (fst xh)) q_omega_val)
          eqn:Hcmp; auto.
        change (femax Tdouble) with 1024%Z in Hcmp.
        rewrite Hcmp in H0. contradiction.
      * unfold bool2val.
        unfold by_zero.
        destruct (Float.cmp Ceq y (Float.of_bits (Int64.repr 0)));
          reflexivity.
    + unfold Post_bad; clear Post_bad.
      Intros bad.
      match goal with
      | Hpost : bad = false -> bxh_hi = true |- _ =>
          rename Hpost into Hbad_result
      end.
      forward_if.
      * forward. Exists false. entailer!.
      * assert (bad = false) as Hbadf.
        { destruct bad.
          - exfalso. apply Int.one_not_zero.
            match goal with
            | Hcontra : Int.one = Int.zero |- _ => exact Hcontra
            end.
          - reflexivity. }
        assert (Hbxh_hi : bxh_hi = true)
          by (apply Hbad_result; exact Hbadf).

        forward.
        forward.
        forward_call (Float.div (fst xh) y).
        set (bqt_hi := Float.cmp Clt
          (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble))
            (Float.div (fst xh) y)) q_omega_val).
        forward.
        Exists bqt_hi; entailer!.
        split.
        { intros Hbqtht.
          assert (Hxh_hi : Rabs (FT2R (fst xh)) <=
                    /4 * bpow Zaux.radix2 (femax Tdouble)).
          { apply Float_cmp_Cle_bpow1022; [exact Hfin_xh|].
            exact Hbxh_hi. }
          destruct (Float_cmp_Clt_bpow1022 (Float.div (fst xh) y))
            as [Hfin_q Hq_hi].
          { unfold bqt_hi in Hbqtht; exact Hbqtht. }
          change (Float.div (fst xh) y) with (BDIV (fst xh) y)
            in Hfin_q, Hq_hi.
          assert (Hyne : FT2R y <> 0%R)
            by (apply (BDIV_denom_ne0 (fst xh) y Hfin_y Hfin_q)).
          assert (Hfmt1022 :
                    generic_format radix2 fexp (bpow Zaux.radix2 1022)).
          { apply generic_format_bpow.
            unfold fexp, SpecFloat.fexp, SpecFloat.emin;
              try change (fprec Tdouble) with 53%Z;
              try change (femax Tdouble) with 1024%Z.
            apply Z.max_lub; lia. }
          assert (Hquot_hi : Rabs (FT2R (fst xh) / FT2R y) <=
                    bpow Zaux.radix2 1022).
          { apply (BDIV_abs_le_bpow (fst xh) y 1022
                    Hyne Hfin_q Hfmt1022).
            exact Hq_hi. }
          assert (Hq4 : (/4 * bpow Zaux.radix2 (femax Tdouble)
                        = bpow Zaux.radix2 (femax Tdouble - 2))%R).
          { replace (femax Tdouble) with
              (2 + (femax Tdouble - 2))%Z at 1 by lia.
            rewrite bpow_plus. simpl. lra. }
          unfold DDConds.DWDivFP_strong_precond.
          repeat split; try assumption;
            try (rewrite <- Hq4; exact Hxh_hi);
            try exact Hquot_hi. }
        { unfold bqt_hi.
          destruct (Float.cmp Clt
            (Binary.Babs (fprec Tdouble) 1024
              (abs_nan (fprec Tdouble) 1024
                (fprec_gt_one Tdouble)) (Float.div (fst xh) y))
            q_omega_val); reflexivity. }
Qed.

Lemma body_dw_div_fp_weak_check :
  semax_body Vprog Gprog f_dw_div_fp_weak_check dw_div_fp_weak_check_spec.
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
  - assert (vret_fxh = true) as Hvfxh
      by (destruct vret_fxh; auto; simpl in H; rep_lia).
    forward. unfold Post_t4; Exists vret_fxl; entailer!.
    split.
    + intros Hout.
      apply (short_circuit_fin_and_concl (fst xh) (snd xh) true vret_fxl vret_fxl
              Hspec_fxh Hspec_fxl eq_refl). exact Hout.
    + destruct vret_fxl; simpl; auto.
  - forward. unfold Post_t4; Exists false; entailer!.
  - unfold Post_t4; clear Post_t4. Intros b4; rename H into Hb4.
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
    + assert (b4 = true) as Hb4_eq
        by (destruct b4; auto; simpl in H; rep_lia).
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
                 Hb4 eq_refl). exact Hout.
      * destruct (Float.cmp _ _ _); simpl; auto.
    + forward. unfold Post_t5; Exists false; entailer!.
    + unfold Post_t5; clear Post_t5. Intros b5; rename H into Hb5.
      forward.
      forward_call.
      replace (- Int.unsigned (Int.repr 968))%Z with (-968)%Z by reflexivity.
      fold q_lo968_val.
      forward.
      set (bxh_zero := Float.cmp Ceq (float_of_ftype (fst xh))
                         (Float.of_bits (Int64.repr 0))).
      set (bxh_floor := Float.cmp Cle q_lo968_val
                         (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble))
                           (fst xh))).
      set (Post_xh_lo :=
        EX bxh_lo : bool,
        PROP (bxh_lo = true -> bxh_zero = true \/ bxh_floor = true)
        LOCAL (temp _t'7 (Vint (if bxh_lo then Int.one else Int.zero));
               temp _q_plo (Vfloat q_lo968_val);
               temp _dwx (Vint (if b5 then Int.one else Int.zero));
               temp _fin_y (Vint (if vret_fy then Int.one else Int.zero));
               temp _x x; temp _y (Vfloat y))
        SEP (data_at Tsh dword (f2val xh) x)).
      forward_if Post_xh_lo.
      * forward. unfold Post_xh_lo; Exists true; entailer!.
      * forward. forward_call (fst xh). forward.
        unfold Post_xh_lo; Exists bxh_floor; entailer!.
        unfold bool2val.
        change (Vint (if bxh_floor then Int.one else Int.zero) =
                Vint (Int.repr (Z.b2z bxh_floor))).
        destruct bxh_floor; reflexivity.
      * unfold Post_xh_lo; clear Post_xh_lo.
        Intros bxh_lo; rename H into Hbxh_lo. forward.

        set (Post_t9 :=
          EX b9 : bool,
          PROP (b9 = true -> b5 = true /\ vret_fy = true)
          LOCAL (temp _t'9 (Vint (if b9 then Int.one else Int.zero));
                 temp _xh_lo (Vint (if bxh_lo then Int.one else Int.zero));
                 temp _dwx (Vint (if b5 then Int.one else Int.zero));
                 temp _fin_y (Vint (if vret_fy then Int.one else Int.zero));
                 temp _x x; temp _y (Vfloat y))
          SEP (data_at Tsh dword (f2val xh) x)).
        forward_if Post_t9.
        ** assert (b5 = true) as Hb5_eq
             by (destruct b5; auto; simpl in H; rep_lia).
           forward. unfold Post_t9; Exists vret_fy; entailer!.
           repeat split;
           try (now (let H := fresh in intros H; repeat split; assumption));
           try unfold bxh_lo; try unfold bxh_floor; try unfold bxh_zero;
           repeat first
             [ reflexivity
             | assumption
             | match goal with
               | |- context [Float.cmp ?cc ?aa ?dd] => destruct (Float.cmp cc aa dd)
               | |- context [if ?bb then Int.one else Int.zero] => destruct bb
               end ].
        ** forward. unfold Post_t9; Exists false; entailer!;
           repeat split;
           try unfold bxh_lo; try unfold bxh_floor; try unfold bxh_zero;
           repeat first
             [ reflexivity
             | assumption
             | match goal with
               | |- context [Float.cmp ?cc ?aa ?dd] => destruct (Float.cmp cc aa dd)
               | |- context [if ?bb then Int.one else Int.zero] => destruct bb
               end ].
        ** unfold Post_t9; clear Post_t9. Intros b9; rename H into Hb9.
           set (Post_t10 :=
             EX b10 : bool,
             PROP (b10 = true -> b5 = true /\ vret_fy = true /\ bxh_lo = true)
             LOCAL (temp _t'10 (Vint (if b10 then Int.one else Int.zero));
                    temp _x x; temp _y (Vfloat y))
             SEP (data_at Tsh dword (f2val xh) x)).
           forward_if Post_t10.
           *** assert (b9 = true) as Hb9_eq
                 by (destruct b9; auto; simpl in H; rep_lia).
               forward. unfold Post_t10; Exists bxh_lo; entailer!.
               split.
               { intros Hout. destruct (Hb9 eq_refl); auto. }
               { destruct bxh_lo; reflexivity. }
           *** forward. unfold Post_t10; Exists false; entailer!.
           *** unfold Post_t10; clear Post_t10. Intros b10; rename H into Hb10.
               forward. Exists b10; entailer!.
               destruct (Hb10 eq_refl) as [Hb5t [Hfyt Hlot]].
               destruct (Hb5 Hb5t) as [Hfin_xh [Hfin_xl HDWx]].
               assert (Hfin_y : is_finite y = true)
                 by (apply (proj1 Hspec_fy); exact Hfyt).
               assert (Hxh_lo : FT2R (fst xh) = 0 \/
                         bpow Zaux.radix2 (-968) <= Rabs (FT2R (fst xh))).
               { destruct (Hbxh_lo Hlot) as [Hzero | Hfloor].
                 - left. unfold bxh_zero in Hzero.
                   pose proof (Float_cmp_Ceq_zero_FT2R _ Hzero) as Hz.
                   rewrite ftype_of_float_of_ftype in Hz. exact Hz.
                 - right.
                   apply (Float_cmp_Cle_lo q_lo968_val (fst xh)
                            (bpow Zaux.radix2 (-968)) Hfin_xh
                            q_lo968_val_finite q_lo968_val_FT2R).
                   unfold bxh_floor in Hfloor; exact Hfloor. }
               unfold DDConds.DWDivFP_weak_precond.
               repeat split; assumption.
Qed.
