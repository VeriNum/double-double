(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** This file contains helper lemmas for accuracy proofs  about double-words *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common.
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