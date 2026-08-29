(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.
Require Import DD.verif_proofs.verif_fp_utils_short_circuit.

(* Discharge the residual local goals
   `Vint (if b then Int.one else Int.zero) = Vint (Int.repr (Z.b2z c))`
   that entailer! produces
   whenever a forward_if invariant carries the xh_bnd / y_bnd comparison temps.
   Each such temp equals a `Float.cmp Cle ...` value; analyzing the comparison
   closes both sides by reflexivity. *)
(* Int.repr (Z.b2z b) is exactly the if expression used in the invariants. *)
(* The stored xh_bnd / y_bnd temp is `Vint (Int.repr (Z.b2z c))` where c is the
   raw Float.cmp Cle comparison; the invariant carries `Vint (if bxh ..)` with
   bxh := that same comparison (up to convertibility of q_sqrt_val / femax).
   Rewriting both to the b2z form lets `reflexivity` close them by conversion. *)
Local Ltac cmp_val_eq :=
  rewrite Vint_b2z_if; reflexivity.

Local Ltac fix_cmp_locals :=
  solve [ repeat (first [ reflexivity | cmp_val_eq
                        | (intro; discriminate) | split ]) ].

(* [dw_mult_fp_strong_precond_check] establishes [DWTimesFP_strong_precond]: finite
   inputs, a double-word operand, and a strict bound on the rounded leading
   product.  [prod_bnd_facts] converts that test into product finiteness and the
   [Omega/2] real bound.  The check does not exclude the [Fast2Mult] underflow
   gap because the exported mixed guarantee covers it. *)
Lemma body_dw_mult_fp_strong_precond_check :
  semax_body Vprog Gprog f_dw_mult_fp_strong_precond_check dw_mult_fp_strong_precond_check_spec.
Proof.
  start_function.
  (* fin_xh = isfinite_double(x->s) *)
  forward. forward_call. Intros vret_fxh. rename H into Hspec_fxh. forward.
  (* fin_xl = isfinite_double(x->t) *)
  forward. forward_call. Intros vret_fxl. rename H into Hspec_fxl. forward.
  (* fin_y = isfinite_double(y). forward_call folds the following Sset _fin_y. *)
  forward_call. Intros vret_fy. rename H into Hspec_fy. abbreviate_semax.

  (* --- dwx: (fin_xh && fin_xl) && (x->s + x->t == x->s) ---
     if A sets _t'4 = fin_xh && fin_xl; if B (guard _t'4) sets _t'5. *)
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
  - assert (vret_fxh = true) as Hvfxh.
    { destruct vret_fxh; auto; simpl in H; rep_lia. }
    forward.
    unfold Post_t4; Exists vret_fxl; entailer!.
    split.
    + intros Hout.
      apply (short_circuit_fin_and_concl (fst xh) (snd xh) true vret_fxl vret_fxl
              Hspec_fxh Hspec_fxl eq_refl).
      exact Hout.
    + destruct vret_fxl; simpl; auto.
  - forward.
    unfold Post_t4; Exists false; entailer!.
  - unfold Post_t4; clear Post_t4.
    Intros b4; rename H into Hb4.
    set (Post_t5 :=
      EX b5 : bool,
      PROP (b5 = true -> is_finite (fst xh) = true /\
                         is_finite (snd xh) = true /\
                         double_word_prop (fst xh) (snd xh))
      LOCAL (temp _t'5 (Vint (if b5 then Int.one else Int.zero));
             temp _fin_xh (Vint (if vret_fxh then Int.one else Int.zero));
             temp _fin_xl (Vint (if vret_fxl then Int.one else Int.zero));
             temp _fin_y (Vint (if vret_fy then Int.one else Int.zero));
             temp _x x; temp _y (Vfloat y))
      SEP (data_at Tsh dword (f2val xh) x)).
    forward_if Post_t5.
    + assert (b4 = true) as Hb4_eq.
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
    + forward.
      unfold Post_t5; Exists false; entailer!.
    + unfold Post_t5; clear Post_t5.
      Intros b6; rename H into Hb6.
      forward.  (* store dwx *)

      (* z = x->s * y *)
      forward. forward.
      (* q_prod = ldexp(1.0, 1023) = q_prod_val
         (forward_call folds the following plain Sset _q_prod). *)
      forward_call.
      (* prod_bnd = (fabs(z) < q_prod) *)
      forward_call. forward.

      set (bpb := Float.cmp Clt
                    (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble))
                       (Float.mul (float_of_ftype (fst xh)) y))
                    q_prod_val).

      (* Return cascade: dwx && fin_y && prod_bnd.
         A pure conjunction, as in body_dw_plus_fp_strong_precond_check: two nested
         short-circuit levels, each carrying one more raw fact forward. *)
      set (Post_t8 :=
        EX b8 : bool,
        PROP (b8 = true -> b6 = true /\ vret_fy = true)
        LOCAL (temp _t'8 (Vint (if b8 then Int.one else Int.zero));
               temp _prod_bnd (Vint (if bpb then Int.one else Int.zero));
               temp _fin_y (Vint (if vret_fy then Int.one else Int.zero));
               temp _dwx (Vint (if b6 then Int.one else Int.zero));
               temp _x x; temp _y (Vfloat y))
        SEP (data_at Tsh dword (f2val xh) x)).
      forward_if Post_t8.
      * (* dwx != 0 : t'8 = (bool)fin_y *)
        assert (b6 = true) as Hb6_eq
          by (destruct b6; auto; simpl in H; rep_lia).
        forward.
        unfold Post_t8; Exists vret_fy; entailer!.
        split.
        { destruct vret_fy; reflexivity. }
        { cmp_val_eq. }
      * forward.
        unfold Post_t8; Exists false; entailer!; try fix_cmp_locals.
      * unfold Post_t8; clear Post_t8.
        Intros b8; rename H into Hb8.
        set (Post_t9 :=
          EX b9 : bool,
          PROP (b9 = true -> b6 = true /\ vret_fy = true /\ bpb = true)
          LOCAL (temp _t'9 (Vint (if b9 then Int.one else Int.zero));
                 temp _prod_bnd (Vint (if bpb then Int.one else Int.zero));
                 temp _x x; temp _y (Vfloat y))
          SEP (data_at Tsh dword (f2val xh) x)).
        forward_if Post_t9.
        ** (* t'8 != 0 : t'9 = (bool)prod_bnd *)
           assert (b8 = true) as Hb8_eq
             by (destruct b8; auto; simpl in H; rep_lia).
           forward.
           unfold Post_t9; Exists bpb; entailer!.
           split.
           { intros Hout. destruct (Hb8 eq_refl); auto. }
           { unfold bpb.
             match goal with
             | |- context [Float.cmp Clt ?a ?b] =>
                 destruct (Float.cmp Clt a b); reflexivity
             end. }
        ** forward.
           unfold Post_t9; Exists false; entailer!.
        ** unfold Post_t9; clear Post_t9.
           Intros b9; rename H into Hb9.
           forward.  (* return t'9 *)
           Exists b9; entailer!.
           (* Final discharge: the three conjuncts of DWTimesFP_strong_precond.
              No underflow disjunct to prove -- that is the whole point of the
              weakening -- so prod_bnd_facts closes both remaining goals
              (Fast2Mult finiteness and the product magnitude bound) in one
              shot and nothing else is needed. *)
           destruct (Hb9 eq_refl) as [Hb6t [Hfyt Hbpbt]].
           destruct (Hb6 Hb6t) as [Hfxh [Hfxl Hdwp]].
           assert (Hfy : is_finite y = true)
             by (apply (proj1 Hspec_fy); exact Hfyt).
           destruct (prod_bnd_facts (fst xh) y)
             as [Hbmul_fin Hprodb].
           { unfold bpb in Hbpbt; exact Hbpbt. }
           unfold DDConds.DWTimesFP_strong_precond.
           repeat (split; try assumption).
Qed.

Lemma body_dw_mult_fp_weak_precond_check :
  semax_body Vprog Gprog f_dw_mult_fp_weak_precond_check
    dw_mult_fp_weak_precond_check_spec.
Proof.
  start_function.
  forward_call (x, xh, y).
  Intros b; rename H into Hb.
  forward.
  Exists b; entailer!.
Qed.
