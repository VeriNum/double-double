(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** This file contains helper lemmas for accuracy proofs  about double-words *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common FLT_helpers.
Require Import DWPlus DDModels DWord_defs Fast2Mult_acc TwoSum_acc Fast2Sum_acc.
From Flocq Require Import Pff2Flocq Core.

Require Import mathcomp.ssreflect.ssreflect.

(* for choice functions : choice = fun x0 : Z => negb (Z.even x0) *)
From Stdlib Require Import Logic.FunctionalExtensionality.

Section DWHighBnd.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

(* Bridge: if a double-word (xh, xl) satisfies |xh + xl| < Omega/4 then 
|xh| <= Omega/4 (the high-part bound used in DWPlusFP_relative_error_input_cond / DWPlusDW_relative_error_input_cond).
The implication holds because Omega/4 = 2^(femax - 2) is a power of two, hence 
in generic_format, and round-to-nearest cannot push a value with |x| < B above 
B when B is representable. *)
Lemma dw_high_bnd_of_sum (xh xl : ftype t)
  (Hdw  : double_word_prop xh xl)
  (Hsum : Rabs (FT2R xh + FT2R xl) < /4 * (bpow radix2 (femax t))) :
  Rabs (FT2R xh) <= /4 * (bpow radix2 (femax t)).
Proof.
have Hquot : /4 * bpow radix2 (femax t) = bpow radix2 (femax t - 2).
{ have -> : (femax t - 2 = -2 + femax t)%Z by ring.
  rewrite bpow_plus. cbn. nra. }
have Hvexp : Valid_exp (SpecFloat.fexp (fprec t) (femax t))
  by apply FLT.FLT_exp_valid; apply fprec_gt_0.
have Hfmt : generic_format radix2 (SpecFloat.fexp (fprec t) (femax t))
                             (bpow radix2 (femax t - 2)).
{ apply generic_format_bpow; auto.
  rewrite /SpecFloat.fexp /SpecFloat.emin.
  pose proof (fprec_lt_femax t).
  pose proof (@fprec_lb t).
  apply Z.max_lub; lia. }
rewrite /double_word_prop/rounded in Hdw.
rewrite Hdw Hquot.
apply (@abs_round_le_generic radix2 _ Hvexp _
                              (BinarySingleNaN.valid_rnd_round_mode _)).
- exact Hfmt.
- apply Rlt_le. rewrite -Hquot. exact Hsum.
Qed.

End DWHighBnd.

Section DWLowBounds.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (@common.emin t).
Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Notation ulp := (Ulp.ulp Zaux.radix2 fexp).

Local Instance valid_fexp_inst_low : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.

(** The low component of a double word is at most half an ulp of its high
    component. *)
Lemma dw_low_le_half_ulp (xh xl : ftype t) :
  double_word_prop xh xl ->
  Rabs (FT2R xl) <= /2 * ulp (FT2R xh).
Proof.
rewrite /double_word_prop /rounded => Hdw.
have Hxl : FT2R xl =
  - (round radix2 fexp (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
       (FT2R xh + FT2R xl) - (FT2R xh + FT2R xl))
  by rewrite -Hdw; ring.
have Hulp : ulp (FT2R xh) =
  ulp (round radix2 fexp (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
       (FT2R xh + FT2R xl)) by rewrite -Hdw.
rewrite Hxl Rabs_Ropp Hulp.
apply Ulp.error_le_half_ulp_round; FLT_basics.
Qed.

(** Relative form of [dw_low_le_half_ulp].  If the high component is
    subnormal, the double-word relation forces the low component to zero. *)
Lemma dw_low_le_u_high (xh xl : ftype t) :
  double_word_prop xh xl ->
  Rabs (FT2R xl) <=
    bpow radix2 (- fprec t) * Rabs (FT2R xh).
Proof.
move => Hdw.
have Hhalf := dw_low_le_half_ulp xh xl Hdw.
have Hxh0 : 0 <= Rabs (FT2R xh) by apply Rabs_pos.
destruct (Rle_lt_dec (bpow radix2 (emin + fprec t - 1))
                     (Rabs (FT2R xh))) as [Hnormal | Hsub].
- have Hrel : ulp (FT2R xh) <=
      Rabs (FT2R xh) * bpow radix2 (1 - fprec t)
    by apply ulp_FLT_le.
  have Hbpow : bpow radix2 (1 - fprec t) =
      2 * bpow radix2 (- fprec t).
  { have -> : (1 - fprec t = 1 + - fprec t)%Z by lia.
    rewrite bpow_plus. have -> : bpow radix2 1 = 2%R by reflexivity.
    ring. }
  nra.
- have Hulp : ulp (FT2R xh) = bpow radix2 emin.
  { apply ulp_FLT_small;
      first [ apply fprec_gt_0
            | eapply Rlt_trans; [exact Hsub | apply bpow_lt; lia] ]. }
  have Hxl0 : FT2R xl = 0.
  { apply (generic_format_below_emin_eq_zero (t:=t));
      [apply generic_format_FLT_FT2R |].
    rewrite Hulp in Hhalf.
    have Heta := bpow_gt_0 radix2 emin.
    eapply Rle_lt_trans; [exact Hhalf |]. lra. }
  rewrite Hxl0 Rabs_R0.
  apply Rmult_le_pos; [apply bpow_ge_0 | exact Hxh0].
Qed.

End DWLowBounds.
