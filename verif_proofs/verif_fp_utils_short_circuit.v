(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.

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
