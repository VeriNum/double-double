(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.
Require Import DD.verif_proofs.verif_fp_utils_short_circuit.

(* dw_div_fp_check(x, y) returns 1 only if DWDivFP_cond holds:
   xh, xl, y finite, (xh, xl) a double-word, |xh| within [2^(emin+2p), Omega/4],
   and the quotient |xh/y| within [2^(emin+2p-1), Omega/4].

   The finiteness + double-word (dwx) cascade is identical to body_dw_plus_fp_check;
   the |xh| window is two magnitude comparisons on xh (via Float_cmp_Cle_bpow1022 for
   the Omega/4 upper bound and Float_cmp_Cle_lo for the 2^(emin+2p) lower bound).
   The quotient window is tested on the ROUNDED quotient q = RN(xh/y): the strict
   upper bound (Float_cmp_Clt_bpow1022) also yields is_finite q, hence FT2R y <> 0
   (BDIV_denom_ne0), so BDIV_abs_le_bpow / BDIV_abs_gt_bpow transfer the rounded
   bounds to the exact quotient (rounded->exact soundness, one-directional). *)
Lemma body_dw_div_fp_check :
  semax_body Vprog Gprog f_dw_div_fp_check dw_div_fp_check_spec.
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
      forward_call.                     (* q_qlo   := ldexp(1.0, -969) = q_lo969_val (store absorbed) *)
      (* Normalize the negated integer exponents and fold the threshold constants
         so the temps read as q_omega_val / q_lo968_val / q_lo969_val. *)
      replace (- Int.unsigned (Int.repr 968))%Z with (-968)%Z by reflexivity.
      replace (- Int.unsigned (Int.repr 969))%Z with (-969)%Z by reflexivity.
      fold q_omega_val q_lo968_val q_lo969_val.
      forward. forward_call (fst xh). forward.   (* xh_hi := fabs(x->s) <= q_omega *)
      forward. forward_call (fst xh). forward.   (* xh_lo := q_plo <= fabs(x->s) *)
      forward.                          (* t'18 := x->s *)
      forward.                          (* q := t'18 / y *)
      forward_call (Float.div (fst xh) y). forward. (* qt_hi := fabs(q) < q_omega *)
      forward_call (Float.div (fst xh) y). forward. (* qt_lo := q_qlo < fabs(q) *)

      set (bxh_hi := Float.cmp Cle
                       (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (fst xh))
                       q_omega_val).
      set (bxh_lo := Float.cmp Cle q_lo968_val
                       (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble)) (fst xh))).
      set (bqt_hi := Float.cmp Clt
                       (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble))
                          (Float.div (fst xh) y)) q_omega_val).
      set (bqt_lo := Float.cmp Clt q_lo969_val
                       (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble))
                          (Float.div (fst xh) y))).

      (* === return cascade: t'13 = dwx && fin_y; ... ; t'17 = t'16 && qt_lo === *)
      set (Post_t13 :=
        EX b13 : bool,
        PROP (b13 = true -> b5 = true /\ vret_fy = true)
        LOCAL (temp _t'13 (Vint (if b13 then Int.one else Int.zero));
               temp _qt_lo (Vint (if bqt_lo then Int.one else Int.zero));
               temp _qt_hi (Vint (if bqt_hi then Int.one else Int.zero));
               temp _xh_lo (Vint (if bxh_lo then Int.one else Int.zero));
               temp _xh_hi (Vint (if bxh_hi then Int.one else Int.zero));
               temp _dwx (Vint (if b5 then Int.one else Int.zero));
               temp _fin_y (Vint (if vret_fy then Int.one else Int.zero));
               temp _x x; temp _y (Vfloat y))
        SEP (data_at Tsh dword (f2val xh) x)).
      forward_if Post_t13.
      * assert (b5 = true) as Hb5_eq by (destruct b5; auto; simpl in H; rep_lia).
        forward. unfold Post_t13; Exists vret_fy; entailer!.
        repeat split;
        try (now (let H := fresh in intros H; repeat split; assumption));
        try unfold bxh_hi; try unfold bxh_lo; try unfold bqt_hi; try unfold bqt_lo;
        try change (femax Tdouble) with 1024%Z;
        repeat first
          [ reflexivity
          | assumption
          | match goal with
            | |- context [Float.cmp ?cc ?aa ?dd] => destruct (Float.cmp cc aa dd)
            | |- context [if ?bb then Int.one else Int.zero] => destruct bb
            end ].
      * forward. unfold Post_t13; Exists false; entailer!;
        repeat split;
        try unfold bxh_hi; try unfold bxh_lo; try unfold bqt_hi; try unfold bqt_lo;
        try change (femax Tdouble) with 1024%Z;
        repeat first
          [ reflexivity
          | assumption
          | match goal with
            | |- context [Float.cmp ?cc ?aa ?dd] => destruct (Float.cmp cc aa dd)
            | |- context [if ?bb then Int.one else Int.zero] => destruct bb
            end ].
      * unfold Post_t13; clear Post_t13.
        Intros b13; rename H into Hb13.
        set (Post_t14 :=
          EX b14 : bool,
          PROP (b14 = true -> b5 = true /\ vret_fy = true /\ bxh_hi = true)
          LOCAL (temp _t'14 (Vint (if b14 then Int.one else Int.zero));
                 temp _qt_lo (Vint (if bqt_lo then Int.one else Int.zero));
                 temp _qt_hi (Vint (if bqt_hi then Int.one else Int.zero));
                 temp _xh_lo (Vint (if bxh_lo then Int.one else Int.zero));
                 temp _t'13 (Vint (if b13 then Int.one else Int.zero));
                 temp _xh_hi (Vint (if bxh_hi then Int.one else Int.zero));
                 temp _x x; temp _y (Vfloat y))
          SEP (data_at Tsh dword (f2val xh) x)).
        forward_if Post_t14.
        ** assert (b13 = true) as Hb13_eq by (destruct b13; auto; simpl in H; rep_lia).
           forward. unfold Post_t14; Exists bxh_hi; entailer!.
           split.
           { intros Hout. destruct (Hb13 eq_refl); auto. }
           { repeat split;
             try unfold bxh_hi; try unfold bxh_lo; try unfold bqt_hi; try unfold bqt_lo;
             try change (femax Tdouble) with 1024%Z;
             repeat first
               [ reflexivity
               | assumption
               | match goal with
                 | |- context [Float.cmp ?cc ?aa ?dd] => destruct (Float.cmp cc aa dd)
                 | |- context [if ?bb then Int.one else Int.zero] => destruct bb
                 end ]. }
        ** forward. unfold Post_t14; Exists false; entailer!;
           repeat split;
           try unfold bxh_hi; try unfold bxh_lo; try unfold bqt_hi; try unfold bqt_lo;
           try change (femax Tdouble) with 1024%Z;
           repeat first
             [ reflexivity
             | assumption
             | match goal with
               | |- context [Float.cmp ?cc ?aa ?dd] => destruct (Float.cmp cc aa dd)
               | |- context [if ?bb then Int.one else Int.zero] => destruct bb
               end ].
        ** unfold Post_t14; clear Post_t14.
           Intros b14; rename H into Hb14.
           set (Post_t15 :=
             EX b15 : bool,
             PROP (b15 = true -> b5 = true /\ vret_fy = true /\
                                 bxh_hi = true /\ bxh_lo = true)
             LOCAL (temp _t'15 (Vint (if b15 then Int.one else Int.zero));
                    temp _qt_lo (Vint (if bqt_lo then Int.one else Int.zero));
                    temp _qt_hi (Vint (if bqt_hi then Int.one else Int.zero));
                    temp _t'14 (Vint (if b14 then Int.one else Int.zero));
                    temp _xh_lo (Vint (if bxh_lo then Int.one else Int.zero));
                    temp _x x; temp _y (Vfloat y))
             SEP (data_at Tsh dword (f2val xh) x)).
           forward_if Post_t15.
           *** assert (b14 = true) as Hb14_eq by (destruct b14; auto; simpl in H; rep_lia).
               forward. unfold Post_t15; Exists bxh_lo; entailer!.
               split.
               { intros Hout. destruct (Hb14 eq_refl) as [? [? ?]]; auto. }
               { repeat split;
                 try unfold bxh_hi; try unfold bxh_lo; try unfold bqt_hi; try unfold bqt_lo;
                 try change (femax Tdouble) with 1024%Z;
                 repeat first
                   [ reflexivity
                   | assumption
                   | match goal with
                     | |- context [Float.cmp ?cc ?aa ?dd] => destruct (Float.cmp cc aa dd)
                     | |- context [if ?bb then Int.one else Int.zero] => destruct bb
                     end ]. }
           *** forward. unfold Post_t15; Exists false; entailer!;
               repeat split;
               try unfold bxh_hi; try unfold bxh_lo; try unfold bqt_hi; try unfold bqt_lo;
               try change (femax Tdouble) with 1024%Z;
               repeat first
                 [ reflexivity
                 | assumption
                 | match goal with
                   | |- context [Float.cmp ?cc ?aa ?dd] => destruct (Float.cmp cc aa dd)
                   | |- context [if ?bb then Int.one else Int.zero] => destruct bb
                   end ].
           *** unfold Post_t15; clear Post_t15.
               Intros b15; rename H into Hb15.
               set (Post_t16 :=
                 EX b16 : bool,
                 PROP (b16 = true -> b5 = true /\ vret_fy = true /\
                                     bxh_hi = true /\ bxh_lo = true /\ bqt_hi = true)
                 LOCAL (temp _t'16 (Vint (if b16 then Int.one else Int.zero));
                        temp _qt_lo (Vint (if bqt_lo then Int.one else Int.zero));
                        temp _t'15 (Vint (if b15 then Int.one else Int.zero));
                        temp _qt_hi (Vint (if bqt_hi then Int.one else Int.zero));
                        temp _x x; temp _y (Vfloat y))
                 SEP (data_at Tsh dword (f2val xh) x)).
               forward_if Post_t16.
               **** assert (b15 = true) as Hb15_eq by (destruct b15; auto; simpl in H; rep_lia).
                    forward. unfold Post_t16; Exists bqt_hi; entailer!.
                    split.
                    { intros Hout. destruct (Hb15 eq_refl) as [? [? [? ?]]]; auto. }
                    { repeat split;
                      try unfold bxh_hi; try unfold bxh_lo; try unfold bqt_hi; try unfold bqt_lo;
                      try change (femax Tdouble) with 1024%Z;
                      repeat first
                        [ reflexivity
                        | assumption
                        | match goal with
                          | |- context [Float.cmp ?cc ?aa ?dd] => destruct (Float.cmp cc aa dd)
                          | |- context [if ?bb then Int.one else Int.zero] => destruct bb
                          end ]. }
               **** forward. unfold Post_t16; Exists false; entailer!;
                    repeat split;
                    try unfold bxh_hi; try unfold bxh_lo; try unfold bqt_hi; try unfold bqt_lo;
                    try change (femax Tdouble) with 1024%Z;
                    repeat first
                      [ reflexivity
                      | assumption
                      | match goal with
                        | |- context [Float.cmp ?cc ?aa ?dd] => destruct (Float.cmp cc aa dd)
                        | |- context [if ?bb then Int.one else Int.zero] => destruct bb
                        end ].
               **** unfold Post_t16; clear Post_t16.
                    Intros b16; rename H into Hb16.
                    set (Post_t17 :=
                      EX b17 : bool,
                      PROP (b17 = true -> b5 = true /\ vret_fy = true /\
                                          bxh_hi = true /\ bxh_lo = true /\
                                          bqt_hi = true /\ bqt_lo = true)
                      LOCAL (temp _t'17 (Vint (if b17 then Int.one else Int.zero));
                             temp _x x; temp _y (Vfloat y))
                      SEP (data_at Tsh dword (f2val xh) x)).
                    forward_if Post_t17.
                    ***** assert (b16 = true) as Hb16_eq by (destruct b16; auto; simpl in H; rep_lia).
                          forward. unfold Post_t17; Exists bqt_lo; entailer!.
                          split.
                          { intros Hout. destruct (Hb16 eq_refl) as [? [? [? [? ?]]]];
                            repeat split; assumption. }
                          { repeat split;
                            try unfold bxh_hi; try unfold bxh_lo; try unfold bqt_hi; try unfold bqt_lo;
                            try change (femax Tdouble) with 1024%Z;
                            repeat first
                              [ reflexivity
                              | assumption
                              | match goal with
                                | |- context [Float.cmp ?cc ?aa ?dd] => destruct (Float.cmp cc aa dd)
                                | |- context [if ?bb then Int.one else Int.zero] => destruct bb
                                end ]. }
                    ***** forward. unfold Post_t17; Exists false; entailer!;
                          repeat split;
                          try unfold bxh_hi; try unfold bxh_lo; try unfold bqt_hi; try unfold bqt_lo;
                          try change (femax Tdouble) with 1024%Z;
                          repeat first
                            [ reflexivity
                            | assumption
                            | match goal with
                              | |- context [Float.cmp ?cc ?aa ?dd] => destruct (Float.cmp cc aa dd)
                              | |- context [if ?bb then Int.one else Int.zero] => destruct bb
                              end ].
                    ***** unfold Post_t17; clear Post_t17.
                          Intros b17; rename H into Hb17.
                          forward.                 (* return t'17 *)
                          Exists b17; entailer!.
                          destruct (Hb17 eq_refl)
                            as [Hb5t [Hfyt [Hbxhht [Hbxhlt [Hbqtht Hbqtlt]]]]].
                          destruct (Hb5 Hb5t) as [Hfin_xh [Hfin_xl HDWx]].
                          assert (Hfin_y : is_finite y = true)
                            by (apply (proj1 Hspec_fy); exact Hfyt).
                          (* magnitude facts *)
                          assert (Hxh_hi : Rabs (FT2R (fst xh)) <=
                                    /4 * bpow Zaux.radix2 (femax Tdouble))
                            by (apply Float_cmp_Cle_bpow1022;
                                [exact Hfin_xh | unfold bxh_hi in Hbxhht; exact Hbxhht]).
                          assert (Hxh_lo : bpow Zaux.radix2 (-968) <= Rabs (FT2R (fst xh))).
                          { apply (Float_cmp_Cle_lo q_lo968_val (fst xh)
                                     (bpow Zaux.radix2 (-968)) Hfin_xh
                                     q_lo968_val_finite q_lo968_val_FT2R).
                            unfold bxh_lo in Hbxhlt; exact Hbxhlt. }
                          destruct (Float_cmp_Clt_bpow1022 (Float.div (fst xh) y))
                            as [Hfin_q Hq_hi].
                          { unfold bqt_hi in Hbqtht; exact Hbqtht. }
                          change (Float.div (fst xh) y) with (BDIV (fst xh) y) in Hfin_q, Hq_hi.
                          assert (Hyne : FT2R y <> 0%R)
                            by (apply (BDIV_denom_ne0 (fst xh) y Hfin_y Hfin_q)).
                          assert (Hqt_lo0 : bpow Zaux.radix2 (-969) <
                                    Rabs (FT2R (BDIV (fst xh) y))).
                          { apply (Float_cmp_Clt_lo q_lo969_val (BDIV (fst xh) y)
                                     (bpow Zaux.radix2 (-969)) Hfin_q
                                     q_lo969_val_finite q_lo969_val_FT2R).
                            unfold bqt_lo in Hbqtlt; exact Hbqtlt. }
                          (* generic_format of the thresholds *)
                          assert (Hfmt1022 : generic_format radix2 fexp (bpow Zaux.radix2 1022))
                            by (apply generic_format_bpow;
                                unfold fexp, SpecFloat.fexp, SpecFloat.emin;
                                try change (fprec Tdouble) with 53%Z;
                                try change (femax Tdouble) with 1024%Z;
                                apply Z.max_lub; lia).
                          assert (Hfmt969 : generic_format radix2 fexp (bpow Zaux.radix2 (-969)))
                            by (apply generic_format_bpow;
                                unfold fexp, SpecFloat.fexp, SpecFloat.emin;
                                try change (fprec Tdouble) with 53%Z;
                                try change (femax Tdouble) with 1024%Z;
                                apply Z.max_lub; lia).
                          (* transfer quotient bounds to the exact quotient *)
                          assert (Hquot_hi : Rabs (FT2R (fst xh) / FT2R y) <=
                                    bpow Zaux.radix2 1022).
                          { apply (BDIV_abs_le_bpow (fst xh) y 1022 Hyne Hfin_q Hfmt1022).
                            exact Hq_hi. }
                          assert (Hquot_lo : bpow Zaux.radix2 (-969) <
                                    Rabs (FT2R (fst xh) / FT2R y)).
                          { apply (BDIV_abs_gt_bpow (fst xh) y (-969) Hyne Hfin_q Hfmt969).
                            exact Hqt_lo0. }
                          (* /4*Omega = bpow(femax-2) *)
                          assert (Hq4 : (/4 * bpow Zaux.radix2 (femax Tdouble)
                                        = bpow Zaux.radix2 (femax Tdouble - 2))%R).
                          { replace (femax Tdouble) with (2 + (femax Tdouble - 2))%Z at 1 by lia.
                            rewrite bpow_plus. simpl. lra. }
                          unfold DDModels.DWDivFP_cond.
                          (* conjuncts 1-4 (finiteness/double-word) and, up to conversion,
                             the |xh/y| upper bound and |xh| lower bound close by assumption;
                             the two remaining bounds are the strict quotient lower bound and
                             the /4*Omega = bpow(femax-2) rewrite for |xh|. *)
                          repeat split; try assumption;
                          try (apply Rlt_le; exact Hquot_lo);
                          try (rewrite <- Hq4; exact Hxh_hi);
                          try exact Hquot_hi;
                          try exact Hxh_lo.
Qed.
