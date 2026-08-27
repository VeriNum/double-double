(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.
Require Import DD.verif_proofs.verif_fp_utils_short_circuit.

(* Local matching helpers: a stored comparison temporary is
   `Vint (Int.repr (Z.b2z c))`, while the forward_if invariant
   carries `Vint (if c then Int.one else Int.zero)`; the two are convertible. *)
Local Ltac cmp_val_eq :=
  rewrite Vint_b2z_if; reflexivity.

Local Ltac fix_cmp_locals :=
  solve [ repeat (first [ reflexivity | cmp_val_eq
                        | (intro; discriminate) | split ]) ].

(* [dw_mult_dw_check] establishes [DWTimesDW_mixed_safe_input_cond]: finite
   double-word inputs and a strict bound on the rounded leading product.
   [prod_bnd_facts] converts that test into product finiteness and the
   [Omega/2] real bound.  The check does not exclude the [Fast2Mult] underflow
   gap because the exported mixed guarantee covers it. *)
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
           forward. (* store _dwy *)

           (* z = x->s * y->s *)
           forward. forward. forward.
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

           (* Return dwx && dwy && prod_bnd.
              This is a pure conjunction: two nested
              short-circuit levels, each carrying one more raw fact forward. *)
           set (Post_t11 :=
             EX b11 : bool,
             PROP (b11 = true -> b6 = true /\ b8 = true)
             LOCAL (temp _t'11 (Vint (if b11 then Int.one else Int.zero));
                    temp _prod_bnd (Vint (if bpb then Int.one else Int.zero));
                    temp _dwx (Vint (if b6 then Int.one else Int.zero));
                    temp _dwy (Vint (if b8 then Int.one else Int.zero));
                    temp _x x; temp _y y)
             SEP (data_at Tsh dword (f2val xh) x;
                  data_at Tsh dword (f2val yh) y)).
           forward_if Post_t11.
           *** (* dwx != 0 : t'11 = (bool) dwy *)
               assert (b6 = true) as Hb6_eq
                 by (destruct b6; auto; simpl in H; rep_lia).
               forward.
               unfold Post_t11; Exists b8; entailer!.
               (* entailer! discharges the PROP (b6 is already true here); what
                  is left is the two LOCAL matches for _t'11 and _prod_bnd. *)
               split.
               { destruct b8; reflexivity. }
               { cmp_val_eq. }
           *** forward.
               unfold Post_t11; Exists false; entailer!.
               cmp_val_eq.  (* residual _prod_bnd LOCAL match *)
           *** unfold Post_t11; clear Post_t11.
               Intros b11; rename H into Hb11.
               set (Post_t12 :=
                 EX b12 : bool,
                 PROP (b12 = true -> b6 = true /\ b8 = true /\ bpb = true)
                 LOCAL (temp _t'12 (Vint (if b12 then Int.one else Int.zero));
                        temp _prod_bnd (Vint (if bpb then Int.one else Int.zero));
                        temp _x x; temp _y y)
                 SEP (data_at Tsh dword (f2val xh) x;
                      data_at Tsh dword (f2val yh) y)).
               forward_if Post_t12.
               **** (* t'11 != 0 : t'12 = (bool) prod_bnd *)
                    assert (b11 = true) as Hb11_eq
                      by (destruct b11; auto; simpl in H; rep_lia).
                    forward.
                    unfold Post_t12; Exists bpb; entailer!.
                    split.
                    { intros Hout. destruct (Hb11 eq_refl); auto. }
                    { unfold bpb.
                      match goal with
                      | |- context [Float.cmp Clt ?a ?b] =>
                          destruct (Float.cmp Clt a b); reflexivity
                      end. }
               **** forward.
                    unfold Post_t12; Exists false; entailer!.
               **** unfold Post_t12; clear Post_t12.
                    Intros b12; rename H into Hb12.
                    forward. (* return t'12 *)
                    Exists b12; entailer!.
                    (* Final discharge: the six conjuncts of DWTimesDW_mixed_safe_input_cond.
                       No underflow disjunct to prove -- that is the whole point
                       of the weakening -- so prod_bnd_facts closes both
                       remaining goals (Fast2Mult finiteness and the
                       product magnitude bound) in one shot. *)
                    destruct (Hb12 eq_refl) as [Hb6t [Hb8t Hbpbt]].
                    destruct (Hb6 Hb6t) as [Hfxh [Hfxl Hdwx]].
                    destruct (Hb8 Hb8t) as [Hfyh [Hfyl Hdwy]].
                    destruct (prod_bnd_facts (fst xh) (fst yh))
                      as [Hbmul_fin Hprodb].
                    { unfold bpb in Hbpbt; exact Hbpbt. }
                    unfold DDConds.DWTimesDW_mixed_safe_input_cond, DDConds.Fast2Mult_acc_only_cond.
                    repeat (split; try assumption).
Qed.
