(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** This file contains accuracy proofs for double-word 
plus a (double-word, floating-point number *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common.
Require Import DWPlus DDModels DWord_defs Fast2Mult_acc TwoSum_acc Fast2Sum_acc.
Require Import DWPlus_acc_helpers.
From Flocq Require Import Pff2Flocq Core.

Require Import mathcomp.ssreflect.ssreflect.

(* for choice functions : choice = fun x0 : Z => negb (Z.even x0) *)
From Stdlib Require Import Logic.FunctionalExtensionality.

Section AccuracyDWPlusFP.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Variables (xh xl y : ftype t).
Let zh := (FT2R (fst (DWPlusFP xh xl y))).
Let zl := (FT2R (snd (DWPlusFP xh xl y))).
Let xr := (FT2R xh + FT2R xl).
Let yr := (FT2R y).
Let sl := snd (TwoSumF xh y).
Let v  := BPLUS xl sl.

(* start section hyps *)
Hypothesis  xE : double_word xh xl.
Hypothesis FIN : is_finite_p (DWPlusFP xh xl y). 
Hypothesis Hp3 : (3 <= fprec t)%Z.
(* end section hyps *)

Notation u   := (bpow Zaux.radix2 (- fprec t)).
Definition relative_error_DWPlusFP := Rabs (((zh + zl) - (xr  + yr)) / (xr  + yr)).
Definition errorDWFP := (FT2R xh + FT2R xl + FT2R y) - (zh + zl).
Local Notation p := (fprec t).
Definition rnd := 
  (round radix2 (SpecFloat.fexp (fprec t) (femax t)) (Generic_fmt.Znearest choice)). 

(* connect paper proofs to local defs *)
Fact rel_errorE: relative_error_DWPlusFP = Rabs errorDWFP * (Rabs (/( (FT2R xh + FT2R xl) + FT2R y))).
Proof.
rewrite /relative_error_DWPlusFP /errorDWFP /Rdiv !Rabs_mult -Ropp_minus_distr Rabs_Ropp //.
Qed.

Lemma DWPlusFP_0 : xr + yr = 0 -> zh + zl = 0.
Proof.
move => H0. 
pose proof DWPlusFP_eq xh xl y FIN.
rewrite /F2Rp in H. 
destruct (Req_dec xr 0).
{ have xh0: FT2R xh = 0.
move: xE; rewrite /double_word. 
fold xr; by rewrite H1 /rounded round_0.
(* cases on underflow *)
destruct (Rle_or_lt (bpow radix2 (@emin t + fprec t - 1)) (Rabs xr)).
{  have Hv2: 
Valid_rnd (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
  by apply BinarySingleNaN.valid_rnd_round_mode.
have Hxl: FT2R xl = 0.
move: H2 xE; subst xr; rewrite /double_word xh0; move => H2.
rewrite /rounded round_FLT_FLX Rplus_0_l => //. move => Hz. 
apply: (@eq_0_round_0_FLX radix2 (fprec t) _ 
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) Hv2) => //.
fold (@emin t); by rewrite Rplus_0_l in H2.
rewrite DWPlusFP0f in H => //; try lia. fold zl zh in H.
inversion H. move : H0; subst xr. rewrite H1; subst yr; nra.
rewrite /DWPlus.double_word; repeat split.
1,2 : rewrite -!B2R_float_of_ftype;
apply: generic_format_FLX_FLT;
  apply: Binary.generic_format_B2R.
by rewrite xh0 Hxl Rplus_0_l round_0.
rewrite -!B2R_float_of_ftype;
apply: generic_format_FLX_FLT;
  apply: Binary.generic_format_B2R. }  
have Hxl : FT2R xl = 0.
{  move: xE; subst xr; rewrite /double_word. 
rewrite /rounded round_generic. rewrite xh0 Rplus_0_l => //.
apply Plus_error.FLT_format_plus_small.
apply fprec_gt_0.
1,2 : rewrite -!B2R_float_of_ftype;
  apply: Binary.generic_format_B2R.
fold (@emin t). eapply Rle_trans. apply Rlt_le, H2.
apply bpow_le; lia. } 

rewrite DWPlusFP0f in H => //; try lia. fold zl zh in H.
inversion H. move : H0; subst xr. rewrite H1; subst yr; nra.
rewrite /DWPlus.double_word; repeat split.
1,2 : rewrite -!B2R_float_of_ftype;
apply: generic_format_FLX_FLT;
  apply: Binary.generic_format_B2R.
by rewrite xh0 Hxl Rplus_0_l round_0.
rewrite -!B2R_float_of_ftype;
apply: generic_format_FLX_FLT;
  apply: Binary.generic_format_B2R. }  

move: H. 
unfold DWPlus.DWPlusFP.
rewrite DWPlus.TwoSum_correct => //.
rewrite -!Rplus_assoc.
replace (FT2R xl + FT2R xh) with xr. fold yr.
rewrite H0 Rplus_0_l. 
rewrite F2Sum.Fast2Sum0 => //. fold zl zh. move => Hz.
inversion Hz => //=; lra.
move => x.
apply round_NE_opp.
apply Fth; lia.
rewrite /TwoSum_sum/fst/TwoSum.
rewrite round_NE_opp.
rewrite Bayleyaux.round_round => //; lia.
subst xr. rewrite Rplus_comm => //. lia.
1,2 : rewrite -!B2R_float_of_ftype;
apply: generic_format_FLX_FLT;
  apply: Binary.generic_format_B2R.
Qed.

Theorem relative_errorDWPlusFP_correct : relative_error_DWPlusFP <= 2 * u ^ 2.
Proof.
have Hf : generic_format radix2 (FLX_exp (fprec t)) (FT2R y).
{ apply (@generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t)).
  rewrite -!B2R_float_of_ftype. 
  apply (Binary.generic_format_B2R). }  
destruct (@DWPlusFP_correct (fprec t) (fprec_gt_one t) choice eq_refl 
  Hp3 (FT2R xh) (FT2R xl) (FT2R y) Hf) => // .
apply dw_word_DWdouble => //.
apply Rle_trans with (relative_errorDWFP (fprec t) choice (FT2R xh) (FT2R xl) (FT2R y)) => //.
apply Req_le.
rewrite /relative_error_DWPlusFP/relative_errorDWFP. 
pose proof DWPlusFP_eq xh  xl y FIN.
 rewrite /F2Rp/DWPlus.DWPlusFP in H1.
repeat f_equal.
all: by rewrite H1.
Qed.

Theorem relative_errorDWPlusFP_correct' : 
  exists del, (zh + zl) = (xr + yr) * (1 + del) /\
    Rabs del <= 2 * u ^ 2.
Proof.
have Hf : generic_format radix2 (FLX_exp (fprec t)) (FT2R y).
{ apply (@generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t)). 
  rewrite -!B2R_float_of_ftype. 
  apply (Binary.generic_format_B2R). }  
destruct (@DWPlusFP_correct (fprec t) (fprec_gt_one t) choice eq_refl 
  Hp3 (FT2R xh) (FT2R xl) (FT2R y) Hf) => // .
apply dw_word_DWdouble => //.
destruct (Req_dec (xr + yr) 0) as [Hx0|Hx0].
{ exists 0; rewrite Hx0; split; [field_simplify; 
  now rewrite DWPlusFP_0 | now rewrite Rabs_R0; nra]. } 
exists (((zh + zl) - (xr  + yr)) / (xr  + yr)); split. 
{ now field_simplify. } 
apply relative_errorDWPlusFP_correct.
Qed.

End AccuracyDWPlusFP.


