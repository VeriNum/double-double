(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.
Require Import DD.verif_proofs.verif_fp_utils_short_circuit.

(* [dw_div_fp_strong_precond_check] establishes [DWDivFP_strong_precond]: finite inputs,
   a double-word dividend, a finite leading quotient, the required dividend
   window, and the quotient ceiling.  There is no lower quotient bound.  A
   strict ceiling on the rounded quotient proves its finiteness and a nonzero
   divisor.  [BDIV_abs_le_bpow] transfers that ceiling to the exact quotient. *)
Lemma body_dw_div_fp_strong_precond_check :
  semax_body Vprog Gprog f_dw_div_fp_strong_precond_check dw_div_fp_strong_precond_check_spec.
Proof.
  start_function.
  (* fin_xh = isfinite_double(x->s) *)
  forward. forward_call. Intros vret_fxh. rename H into Hspec_fxh. forward.
  (* fin_xl = isfinite_double(x->t) *)
  forward. forward_call. Intros vret_fxl. rename H into Hspec_fxl. forward.
  (* fin_y = isfinite_double(y) *)
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
  - assert (vret_fxh = true) as Hvfxh
      by (destruct vret_fxh; auto; simpl in H; rep_lia).
    forward.
    unfold Post_t4; Exists vret_fxl; entailer!.
    split.
    + intros Hout.
      apply (short_circuit_fin_and_concl (fst xh) (snd xh) true vret_fxl vret_fxl
              Hspec_fxh Hspec_fxl eq_refl). exact Hout.
    + destruct vret_fxl; simpl; auto.
  - forward.
    unfold Post_t4; Exists false; entailer!.
  - (* join Post_t4: t'5 = t'4 && (x->s + x->t == x->s) *)
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
    + forward.
      unfold Post_t5; Exists false; entailer!.
    + (* join Post_t5: store _dwx, then ldexp thresholds and bounds *)
      unfold Post_t5; clear Post_t5.
      Intros b5; rename H into Hb5.
      forward.                          (* _dwx := t'5 *)
      forward_call.                     (* q_omega := ldexp(1.0, 1022) = q_omega_val (store absorbed) *)
      forward_call.                     (* q_plo   := ldexp(1.0, -968) = q_lo968_val (store absorbed) *)
      (* Normalize the negated exponent and fold the two threshold constants.
         There is no q_qlo any more: the guard has no quotient floor. *)
      replace (- Int.unsigned (Int.repr 968))%Z with (-968)%Z by reflexivity.
      fold q_omega_val q_lo968_val.
      forward. forward_call (fst xh). forward.   (* xh_hi := fabs(x->s) <= q_omega *)
      set (bxh_hi := Float.cmp Cle
                       (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (fst xh))
                       q_omega_val).
      forward.                          (* t'17 := x->s for the zero test *)
      set (bxh_zero := Float.cmp Ceq (float_of_ftype (fst xh))
                         (Float.of_bits (Int64.repr 0))).
      set (bxh_floor := Float.cmp Cle q_lo968_val
                         (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble))
                           (fst xh))).
      set (Post_xh_lo :=
        EX bxh_lo : bool,
        PROP (bxh_lo = true -> bxh_zero = true \/ bxh_floor = true)
        LOCAL (temp _t'9 (Vint (if bxh_lo then Int.one else Int.zero));
               temp _q_plo (Vfloat q_lo968_val);
               temp _q_omega (Vfloat q_omega_val);
               temp _xh_hi (Vint (Int.repr (Z.b2z bxh_hi)));
               temp _dwx (Vint (if b5 then Int.one else Int.zero));
               temp _fin_y (Vint (if vret_fy then Int.one else Int.zero));
               temp _x x; temp _y (Vfloat y))
        SEP (data_at Tsh dword (f2val xh) x)).
      forward_if Post_xh_lo.
      * forward.
        unfold Post_xh_lo; Exists true; entailer!.
      * forward. forward_call (fst xh). forward.
        unfold Post_xh_lo; Exists bxh_floor; entailer!.
        unfold bool2val.
        change (Vint (if bxh_floor then Int.one else Int.zero) =
                Vint (Int.repr (Z.b2z bxh_floor))).
        destruct bxh_floor; reflexivity.
      * unfold Post_xh_lo; clear Post_xh_lo.
        Intros bxh_lo; rename H into Hbxh_lo.
        forward.                       (* xh_lo := t'9 *)
      forward.                          (* t'15 := x->s *)
      forward.                          (* q := t'18 / y *)
      forward_call (Float.div (fst xh) y). forward. (* qt_hi := fabs(q) < q_omega *)

      set (bqt_hi := Float.cmp Clt
                       (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble))
                          (Float.div (fst xh) y)) q_omega_val).

      (* Return cascade: t'12 = dwx && fin_y; ... ; t'15 = t'14 && qt_hi.
         One level shorter than before: the qt_lo conjunct is gone. *)
      set (Post_t11 :=
        EX b11 : bool,
        PROP (b11 = true -> b5 = true /\ vret_fy = true)
        LOCAL (temp _t'12 (Vint (if b11 then Int.one else Int.zero));
               temp _qt_hi (Vint (if bqt_hi then Int.one else Int.zero));
               temp _xh_lo (Vint (if bxh_lo then Int.one else Int.zero));
               temp _xh_hi (Vint (if bxh_hi then Int.one else Int.zero));
               temp _dwx (Vint (if b5 then Int.one else Int.zero));
               temp _fin_y (Vint (if vret_fy then Int.one else Int.zero));
               temp _x x; temp _y (Vfloat y))
        SEP (data_at Tsh dword (f2val xh) x)).
      forward_if Post_t11.
      * assert (b5 = true) as Hb5_eq by (destruct b5; auto; simpl in H; rep_lia).
        forward. unfold Post_t11; Exists vret_fy; entailer!.
        repeat split;
        try (now (let H := fresh in intros H; repeat split; assumption));
        try unfold bxh_hi; try unfold bxh_lo; try unfold bqt_hi;
        try change (femax Tdouble) with 1024%Z;
        repeat first
          [ reflexivity
          | assumption
          | match goal with
            | |- context [Float.cmp ?cc ?aa ?dd] => destruct (Float.cmp cc aa dd)
            | |- context [if ?bb then Int.one else Int.zero] => destruct bb
            end ].
      * forward. unfold Post_t11; Exists false; entailer!;
        repeat split;
        try unfold bxh_hi; try unfold bxh_lo; try unfold bqt_hi;
        try change (femax Tdouble) with 1024%Z;
        repeat first
          [ reflexivity
          | assumption
          | match goal with
            | |- context [Float.cmp ?cc ?aa ?dd] => destruct (Float.cmp cc aa dd)
            | |- context [if ?bb then Int.one else Int.zero] => destruct bb
            end ].
      * unfold Post_t11; clear Post_t11.
        Intros b11; rename H into Hb11.
        set (Post_t12 :=
          EX b12 : bool,
          PROP (b12 = true -> b5 = true /\ vret_fy = true /\ bxh_hi = true)
          LOCAL (temp _t'13 (Vint (if b12 then Int.one else Int.zero));
                 temp _qt_hi (Vint (if bqt_hi then Int.one else Int.zero));
                 temp _xh_lo (Vint (if bxh_lo then Int.one else Int.zero));
                 temp _t'12 (Vint (if b11 then Int.one else Int.zero));
                 temp _xh_hi (Vint (if bxh_hi then Int.one else Int.zero));
                 temp _x x; temp _y (Vfloat y))
          SEP (data_at Tsh dword (f2val xh) x)).
        forward_if Post_t12.
        ** assert (b11 = true) as Hb13_eq by (destruct b11; auto; simpl in H; rep_lia).
           forward. unfold Post_t12; Exists bxh_hi; entailer!.
           split.
           { intros Hout. destruct (Hb11 eq_refl); auto. }
           { repeat split;
             try unfold bxh_hi; try unfold bxh_lo; try unfold bqt_hi;
             try change (femax Tdouble) with 1024%Z;
             repeat first
               [ reflexivity
               | assumption
               | match goal with
                 | |- context [Float.cmp ?cc ?aa ?dd] => destruct (Float.cmp cc aa dd)
                 | |- context [if ?bb then Int.one else Int.zero] => destruct bb
                 end ]. }
        ** forward. unfold Post_t12; Exists false; entailer!;
           repeat split;
           try unfold bxh_hi; try unfold bxh_lo; try unfold bqt_hi;
           try change (femax Tdouble) with 1024%Z;
           repeat first
             [ reflexivity
             | assumption
             | match goal with
               | |- context [Float.cmp ?cc ?aa ?dd] => destruct (Float.cmp cc aa dd)
               | |- context [if ?bb then Int.one else Int.zero] => destruct bb
               end ].
        ** unfold Post_t12; clear Post_t12.
           Intros b12; rename H into Hb12.
           set (Post_t13 :=
             EX b13 : bool,
             PROP (b13 = true -> b5 = true /\ vret_fy = true /\
                                 bxh_hi = true /\ bxh_lo = true)
             LOCAL (temp _t'14 (Vint (if b13 then Int.one else Int.zero));
                    temp _qt_hi (Vint (if bqt_hi then Int.one else Int.zero));
                    temp _t'13 (Vint (if b12 then Int.one else Int.zero));
                    temp _xh_lo (Vint (if bxh_lo then Int.one else Int.zero));
                    temp _x x; temp _y (Vfloat y))
             SEP (data_at Tsh dword (f2val xh) x)).
           forward_if Post_t13.
           *** assert (b12 = true) as Hb14_eq by (destruct b12; auto; simpl in H; rep_lia).
               forward. unfold Post_t13; Exists bxh_lo; entailer!.
               split.
               { intros Hout. destruct (Hb12 eq_refl) as [? [? ?]]; auto. }
               { repeat split;
                 try unfold bxh_hi; try unfold bxh_lo; try unfold bqt_hi;
                 try change (femax Tdouble) with 1024%Z;
                 repeat first
                   [ reflexivity
                   | assumption
                   | match goal with
                     | |- context [Float.cmp ?cc ?aa ?dd] => destruct (Float.cmp cc aa dd)
                     | |- context [if ?bb then Int.one else Int.zero] => destruct bb
                     end ]. }
           *** forward. unfold Post_t13; Exists false; entailer!;
               repeat split;
               try unfold bxh_hi; try unfold bxh_lo; try unfold bqt_hi;
               try change (femax Tdouble) with 1024%Z;
               repeat first
                 [ reflexivity
                 | assumption
                 | match goal with
                   | |- context [Float.cmp ?cc ?aa ?dd] => destruct (Float.cmp cc aa dd)
                   | |- context [if ?bb then Int.one else Int.zero] => destruct bb
                   end ].
           *** unfold Post_t13; clear Post_t13.
               Intros b13; rename H into Hb13.
               set (Post_t14 :=
                 EX b14 : bool,
                 PROP (b14 = true -> b5 = true /\ vret_fy = true /\
                                     bxh_hi = true /\ bxh_lo = true /\ bqt_hi = true)
                 LOCAL (temp _t'15 (Vint (if b14 then Int.one else Int.zero));
                        temp _t'14 (Vint (if b13 then Int.one else Int.zero));
                        temp _qt_hi (Vint (if bqt_hi then Int.one else Int.zero));
                        temp _x x; temp _y (Vfloat y))
                 SEP (data_at Tsh dword (f2val xh) x)).
               forward_if Post_t14.
               **** assert (b13 = true) as Hb15_eq by (destruct b13; auto; simpl in H; rep_lia).
                    forward. unfold Post_t14; Exists bqt_hi; entailer!.
                    split.
                    { intros Hout. destruct (Hb13 eq_refl) as [? [? [? ?]]]; auto. }
                    { repeat split;
                      try unfold bxh_hi; try unfold bxh_lo; try unfold bqt_hi;
                      try change (femax Tdouble) with 1024%Z;
                      repeat first
                        [ reflexivity
                        | assumption
                        | match goal with
                          | |- context [Float.cmp ?cc ?aa ?dd] => destruct (Float.cmp cc aa dd)
                          | |- context [if ?bb then Int.one else Int.zero] => destruct bb
                          end ]. }
               **** forward. unfold Post_t14; Exists false; entailer!;
                    repeat split;
                    try unfold bxh_hi; try unfold bxh_lo; try unfold bqt_hi;
                    try change (femax Tdouble) with 1024%Z;
                    repeat first
                      [ reflexivity
                      | assumption
                      | match goal with
                        | |- context [Float.cmp ?cc ?aa ?dd] => destruct (Float.cmp cc aa dd)
                        | |- context [if ?bb then Int.one else Int.zero] => destruct bb
                        end ].
               **** unfold Post_t14; clear Post_t14.
                    Intros b14; rename H into Hb14.
                    forward.                 (* return t'16 *)
                    Exists b14; entailer!.
                    destruct (Hb14 eq_refl)
                      as [Hb5t [Hfyt [Hbxhht [Hbxhlt Hbqtht]]]].
                    destruct (Hb5 Hb5t) as [Hfin_xh [Hfin_xl HDWx]].
                    assert (Hfin_y : is_finite y = true)
                      by (apply (proj1 Hspec_fy); exact Hfyt).
                    (* magnitude facts *)
                    assert (Hxh_hi : Rabs (FT2R (fst xh)) <=
                              /4 * bpow Zaux.radix2 (femax Tdouble))
                      by (apply Float_cmp_Cle_bpow1022;
                          [exact Hfin_xh | unfold bxh_hi in Hbxhht; exact Hbxhht]).
                    assert (Hxh_lo : FT2R (fst xh) = 0 \/
                              bpow Zaux.radix2 (-968) <= Rabs (FT2R (fst xh))).
                    { destruct (Hbxh_lo Hbxhlt) as [Hzero | Hfloor].
                      - left. unfold bxh_zero in Hzero.
                        pose proof (Float_cmp_Ceq_zero_FT2R _ Hzero) as Hz.
                        rewrite ftype_of_float_of_ftype in Hz. exact Hz.
                      - right.
                        apply (Float_cmp_Cle_lo q_lo968_val (fst xh)
                                 (bpow Zaux.radix2 (-968)) Hfin_xh
                                 q_lo968_val_finite q_lo968_val_FT2R).
                        unfold bxh_floor in Hfloor; exact Hfloor. }
           (* The single strict ceiling test serves both purposes: it gives the
              quotient upper bound and finiteness of RN(xh/y), which is
                       the cond's fifth conjunct (and forces y <> 0). *)
                    destruct (Float_cmp_Clt_bpow1022 (Float.div (fst xh) y))
                      as [Hfin_q Hq_hi].
                    { unfold bqt_hi in Hbqtht; exact Hbqtht. }
                    change (Float.div (fst xh) y) with (BDIV (fst xh) y) in Hfin_q, Hq_hi.
                    assert (Hyne : FT2R y <> 0%R)
                      by (apply (BDIV_denom_ne0 (fst xh) y Hfin_y Hfin_q)).
                    assert (Hfmt1022 : generic_format radix2 fexp (bpow Zaux.radix2 1022))
                      by (apply generic_format_bpow;
                          unfold fexp, SpecFloat.fexp, SpecFloat.emin;
                          try change (fprec Tdouble) with 53%Z;
                          try change (femax Tdouble) with 1024%Z;
                          apply Z.max_lub; lia).
                    (* transfer the quotient ceiling to the exact quotient *)
                    assert (Hquot_hi : Rabs (FT2R (fst xh) / FT2R y) <=
                              bpow Zaux.radix2 1022).
                    { apply (BDIV_abs_le_bpow (fst xh) y 1022 Hyne Hfin_q Hfmt1022).
                      exact Hq_hi. }
                    (* /4*Omega = bpow(femax-2) *)
                    assert (Hq4 : (/4 * bpow Zaux.radix2 (femax Tdouble)
                                  = bpow Zaux.radix2 (femax Tdouble - 2))%R).
                    { replace (femax Tdouble) with (2 + (femax Tdouble - 2))%Z at 1 by lia.
                      rewrite bpow_plus. simpl. lra. }
                    unfold DDConds.DWDivFP_strong_precond.
                    (* conjuncts 1-4 (finiteness/double-word) and conjunct 5
                       (finiteness of the quotient node) close by assumption; the
                       remaining three are the two magnitude windows. *)
                    repeat split; try assumption;
                    try (rewrite <- Hq4; exact Hxh_hi);
                    try exact Hquot_hi;
                    try exact Hxh_lo.
Qed.

(* The default interface checks only the input part of the mixed condition.
   Finiteness is still tested here so the floating-point comparisons have their
   intended real-number meaning, but it is not exposed in the postcondition. *)
Lemma body_dw_div_fp_weak_precond_check :
  semax_body Vprog Gprog f_dw_div_fp_weak_precond_check dw_div_fp_weak_precond_check_spec.
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
               destruct (Hb10 eq_refl) as [Hb5t [_ Hlot]].
               destruct (Hb5 Hb5t) as [Hfin_xh [_ HDWx]].
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
               split; assumption.
Qed.
