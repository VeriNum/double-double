(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* verif_fp_utils_short_circuit.v: pure propositional helper lemmas that
   factor out the three short-circuit patterns appearing in
   body_dw_plus_dw_strong_precond_check. These are not VST proofs — they are standalone
   boolean / conjunction arithmetic that the main body proof's entailer!
   sites cite via `apply short_circuit_*_concl`. *)

Require Import DD.verif_proofs.verif_fp_utils_common.

(* short_circuit_fin_and_concl: the dwx/dwy first stage.
   C: `dwx_stage1 := fin_a && fin_b` where each fin_X has an iff spec. *)
Lemma short_circuit_fin_and_concl :
  forall (a b : ftype Tdouble) (vret_a vret_b b_out : bool),
  (vret_a = true <-> is_finite a = true) ->
  (vret_b = true <-> is_finite b = true) ->
  (b_out = if vret_a then vret_b else false) ->
  b_out = true ->
  is_finite a = true /\ is_finite b = true.
Proof.
  intros a b vret_a vret_b b_out Hspec_a Hspec_b Hcomb Hout.
  destruct vret_a eqn:Ea; [|subst b_out; discriminate].
  destruct vret_b eqn:Eb; [|subst b_out; discriminate].
  split.
  - apply (proj1 Hspec_a); reflexivity.
  - apply (proj1 Hspec_b); reflexivity.
Qed.

(* short_circuit_dw_eq_concl: the dwx/dwy second stage.
   C: `dwx := dwx_stage1 && (a + b == a)`. Reuses Phase 1.1's
   Float_add_eq_dw to lift the FP equality to the double-word relation. *)
Lemma short_circuit_dw_eq_concl :
  forall (a b : ftype Tdouble) (vret_pre b_out : bool),
  (vret_pre = true -> is_finite a = true /\ is_finite b = true) ->
  (b_out = if vret_pre
           then Float.cmp Ceq
                  (Float.add (float_of_ftype a) (float_of_ftype b))
                  (float_of_ftype a)
           else false) ->
  b_out = true ->
  is_finite a = true /\ is_finite b = true /\
  double_word_prop a b.
Proof.
  intros a b vret_pre b_out Hpre Hcomb Hout.
  destruct vret_pre eqn:Epre; [|subst b_out; discriminate].
  destruct (Hpre eq_refl) as [Hfin_a Hfin_b].
  split; [exact Hfin_a | split; [exact Hfin_b|]].
  apply Float_add_eq_dw; [exact Hfin_a | exact Hfin_b |].
  subst b_out; exact Hout.
Qed.

(* short_circuit_magbnd_concl: the xh_bnd / yh_bnd stage.
   C: `xh_bnd := fabs(a) <= q_omega`.  Reuses Phase 1.1's
   Float_cmp_Cle_bpow1022 to lift the comparison to the magnitude bound. *)
Lemma short_circuit_magbnd_concl :
  forall (a : ftype Tdouble) (b_out : bool),
  is_finite a = true ->
  b_out = Float.cmp Cle
            (Binary.Babs _ _ (abs_nan _ _ (fprec_gt_one Tdouble))
                         (float_of_ftype a))
            q_omega_val ->
  b_out = true ->
  Rabs (FT2R a) <= /4 * bpow Zaux.radix2 (femax Tdouble).
Proof.
  intros a b_out Hfin_a Hcomb Hout.
  rewrite Hcomb in Hout.
  apply Float_cmp_Cle_bpow1022; assumption.
Qed.
