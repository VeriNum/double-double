(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** This file contains lemmas about the FLT format. These lemmas 
are used to bridge theorems about FLX format to theorems about FLT format. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common.
Require Import DWPlus DDModels DWord_defs.
Require Import Fast2Mult_acc TwoSum_acc Fast2Sum_acc.
Require Import DW_acc_lemmas.
From Flocq Require Import Pff2Flocq Core.

Require Import mathcomp.ssreflect.ssreflect.

(* for choice functions : choice = fun x0 : Z => negb (Z.even x0) *)
From Stdlib Require Import Logic.FunctionalExtensionality.

Section FLT_with_NANS.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Let ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 
Notation u   := (bpow Zaux.radix2 (- fprec t)).

Fact fexp_not_FTZ :  Exp_not_FTZ fexp.
Proof.
rewrite /Exp_not_FTZ/fexp; intros.
have H1: (1 - fprec t <= 0)%Z.
pose proof (@fprec_lb t); lia.
destruct (Z.le_ge_cases  (e - fprec t) (SpecFloat.emin (fprec t) (femax t))).
apply Z.max_r in H; rewrite H => //.
destruct (Z.le_ge_cases  (SpecFloat.emin (fprec t) (femax t) + 1 - fprec t)
   (SpecFloat.emin (fprec t) (femax t))) => //.
apply Z.max_r in H0; rewrite H0; try lia => //.
apply Z.max_l in H0; rewrite H0; try lia => //.
apply Z.max_l in H; rewrite H => //.
destruct (Z.le_ge_cases  (e - fprec t + 1 - fprec t) 
  (SpecFloat.emin (fprec t) (femax t))) .
apply Z.max_r in H0; rewrite H0; try lia => //.
apply Z.max_l in H0; rewrite H0; try lia => //.
Qed.

(** A quarter of the overflow threshold is strictly below its predecessor. *)
Lemma Omega4_lt_predOmega :
  /4 * bpow radix2 (femax t) <
  Ulp.pred radix2 fexp (bpow radix2 (femax t)).
Proof.
have HpredEq :
  Ulp.pred radix2 fexp (bpow radix2 (femax t)) =
  bpow radix2 (femax t) - bpow radix2 (fexp (femax t)).
{ apply Ulp.pred_bpow. }
rewrite HpredEq.
have Hfexp : fexp (femax t) = (femax t - fprec t)%Z.
{ unfold SpecFloat.fexp, SpecFloat.emin.
  pose proof fprec_lb t; pose proof femax_lb t; lia. }
rewrite Hfexp.
have Heq14 : /4 * bpow radix2 (femax t) = bpow radix2 (femax t - 2).
{ have H14 : (/4:R) = bpow radix2 (-2) by (simpl; lra).
  rewrite H14 -bpow_plus. f_equal; lia. }
rewrite Heq14.
have H1 :
  bpow radix2 (femax t - fprec t) <= bpow radix2 (femax t - 2).
{ apply bpow_le. pose proof fprec_lb t; lia. }
have H2 :
  bpow radix2 (femax t) = 4 * bpow radix2 (femax t - 2).
{ have H4 : (4:R) = bpow radix2 2 by (simpl; lra).
  rewrite H4 -bpow_plus. f_equal; lia. }
have H3 : 0 < bpow radix2 (femax t - 2) by apply bpow_gt_0.
nra.
Qed.

(* Lemma 2.1 *)
Lemma roundN_plus_ulp_FLT  (a b : ftype t) : 
      ( (FT2R a + FT2R b) <> 0) ->
        Rmax (ulp (FT2R a) /2) (ulp (FT2R b)/ 2) <= Rabs (rounded t (FT2R a + FT2R b)).
Proof.
move=> sn0.
have Hv: Valid_exp fexp by apply FLT.FLT_exp_valid.
have Hexp: Exp_not_FTZ fexp by apply  fexp_not_FTZ.
have Hv2: 
Valid_rnd (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
  by apply BinarySingleNaN.valid_rnd_round_mode.
have Ha: generic_format radix2 fexp (FT2R a) by
  rewrite -!B2R_float_of_ftype; apply Binary.generic_format_B2R. 
have Hb: generic_format radix2 fexp (FT2R b) by 
  rewrite -!B2R_float_of_ftype; apply Binary.generic_format_B2R. 
have Hrnd: rounded t (FT2R a + FT2R b) <> 0.
rewrite /rounded; apply Plus_error.round_plus_neq_0 => //.
have Hbpow : 
bpow radix2 (@emin t) / 2 <=
bpow radix2 (@emin t) .
  apply Rdiv_le_left; try nra.
  refine (Rle_trans _ _ _ _  (Rmult_le_compat_l _ 1 _ _ _ ));
  try nra. apply bpow_ge_0.
destruct (Req_dec (FT2R a) 0). 
{ move : sn0. rewrite H Rplus_0_l. 
  move=> sn0. 
  rewrite /rounded round_generic => //.
  apply Rmax_lub.
  refine (Rle_trans _ (ulp 0) _ _ _ ).
  rewrite /ulp ulp_FLT_0 => //. 
  refine (Rle_trans _ _ _ _ (ulp_le_abs radix2 fexp _ _ _)) => //.
  apply ulp_ge_ulp_0 => //.
  apply Rdiv_le_left; try nra.
  refine (Rle_trans _ _ _ _  (Rmult_le_compat_l _ 1 _ _ _ ));
    try nra.  rewrite Rmult_1_r. apply ulp_le_abs => //. 
  apply Rabs_pos. } 
destruct (Req_dec (FT2R b) 0). 
{ move : sn0. rewrite H0 Rplus_0_r. 
  move=> sn0. 
  rewrite /rounded round_generic => //.
  apply Rmax_lub.
  apply Rdiv_le_left; try nra.
  refine (Rle_trans _ _ _ _  (Rmult_le_compat_l _ 1 _ _ _ ));
    try nra.  rewrite Rmult_1_r. apply ulp_le_abs => //. 
  apply Rabs_pos.
  refine (Rle_trans _ (ulp 0) _ _ _ ).
  rewrite /ulp ulp_FLT_0 => //.
  refine (Rle_trans _ _ _ _ (ulp_le_abs radix2 fexp _ _ _)) => //.
  apply ulp_ge_ulp_0 => //. } 
unfold Rmax.
destruct (Rle_dec (ulp (FT2R a) /2) (ulp (FT2R b) / 2)).
destruct (Rle_or_lt (bpow radix2 (@emin t + fprec t)) (Rabs (FT2R b))).
{ rewrite Rplus_comm.
  refine (Rle_trans _ _ _ _  _).
  2: apply round_plus_ge_ulp => //.
  replace (FT2R b / IZR radix2) with (FT2R b  * bpow radix2 (-1)) => //.
  rewrite ulp_FLT_exact_shift /ulp/fexp/FLT_exp => //=. 
  field_simplify; try nra. 
  apply mag_ge_bpow => //.
  eapply Rle_trans.
  2: apply H1. apply bpow_le. rewrite /emin. lia.
  have : 
  (SpecFloat.emin (fprec t) (femax t) + fprec t + 1  <= mag radix2 (FT2R b))%Z.
  apply mag_ge_bpow => //.
  eapply Rle_trans.
  2: apply H1. apply bpow_le. rewrite /emin. lia.
  lia. rewrite Rplus_comm => //. } 
rewrite Rplus_comm.
  refine (Rle_trans _ _ _ _  _).
2: apply round_plus_ge_ulp => //.
rewrite /ulp !ulp_FLT_small => //.
  refine (Rlt_trans _ _ _ _ H1). 
rewrite Rabs_div_Raux.
apply Rdiv_lt_left.
apply Rabs_pos_lt.
apply not_0_IZR => //.
  refine (Rle_lt_trans _ _ _ _  (Rmult_lt_compat_l _ 1 _ _ _ ));
    try nra.  
apply Rabs_pos_lt => //.
simpl; rewrite Rabs_right; try nra.
apply not_0_IZR => //.
rewrite Rplus_comm => //.
apply Rnot_le_lt in n.
destruct (Rle_or_lt (bpow radix2 (@emin t + fprec t)) (Rabs (FT2R a))).
{ refine (Rle_trans _ _ _ _  _).
  2: apply round_plus_ge_ulp => //.
  replace (FT2R a / IZR radix2) with (FT2R a  * bpow radix2 (-1)) => //.
  rewrite ulp_FLT_exact_shift /ulp/fexp/FLT_exp => //=. 
  field_simplify; try nra. 
  apply mag_ge_bpow => //.
  eapply Rle_trans.
  2: apply H1. apply bpow_le. rewrite /emin. lia.
  have : 
  (SpecFloat.emin (fprec t) (femax t) + fprec t + 1  <= mag radix2 (FT2R a))%Z.
  apply mag_ge_bpow => //.
  eapply Rle_trans.
  2: apply H1. apply bpow_le. rewrite /emin. lia.
  lia. } 
refine (Rle_trans _ _ _ _  _).
2: apply round_plus_ge_ulp => //.
rewrite /ulp !ulp_FLT_small => //.
  refine (Rlt_trans _ _ _ _ H1). 
rewrite Rabs_div_Raux.
apply Rdiv_lt_left.
apply Rabs_pos_lt.
apply not_0_IZR => //.
  refine (Rle_lt_trans _ _ _ _  (Rmult_lt_compat_l _ 1 _ _ _ ));
    try nra.  
apply Rabs_pos_lt => //.
simpl; rewrite Rabs_right; try nra.
apply not_0_IZR => //.
Qed.

End FLT_with_NANS.
