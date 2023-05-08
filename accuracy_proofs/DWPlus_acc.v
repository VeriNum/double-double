Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics.
Require Import DWPlus DDModels Fast2Mult_acc TwoSum_acc.
From Flocq Require Import Pff2Flocq Core.

Require Import mathcomp.ssreflect.ssreflect.

Section AccuracyDWPlusFP.
Context {NANS: Nans} {t : type}.





Variables (xh xl y : ftype t).
Notation zh := (FT2R (fst (DWPlusFP xh xl y))).
Notation zl := (FT2R (snd (DWPlusFP xh xl y))).
Let xr  := (FT2R xh + FT2R xl).
Let yr  := (FT2R y).

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 
Notation u   := (bpow Zaux.radix2 (- fprec t)).

Definition relative_error_DWPlusFP := Rabs (((zh + zl) - (xr  + yr)) / (xr  + yr)).

Hypothesis FIN : is_finite_p (DWPlusFP xh xl y). 
Hypothesis Hp3 : (3 <= (fprec t))%Z.

Hypothesis DW:   DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl).


Theorem relative_errorDWPlusFP_correct : relative_error_DWPlusFP <= 2 * u ^ 2.
Proof.
have Hf : generic_format radix2 (FLX_exp (fprec t)) (FT2R y).
{ apply (@generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t)). unfold FT2R.
  apply (Binary.generic_format_B2R (fprec t) (femax t) y). }  
destruct (@DWPlusFP_correct (fprec t) (fprec_gt_one t) choice eq_refl 
  Hp3 (FT2R xh) (FT2R xl) (FT2R y) Hf) => // .
apply Rle_trans with (relative_errorDWFP (fprec t) choice (FT2R xh) (FT2R xl) (FT2R y)) => //.
apply Req_le.
rewrite /relative_errorDWFP/relative_error_DWPlusFP/zh/zl/xr/yr/DWPlusFP. 
repeat f_equal.
{ rewrite /TwoSum_sum.
pose proof @TwoSumF_correct NANS t xh y.
rewrite /TwoSumF_err/TwoSumF_sum in H1.
Qed.

End AccuracyDWPlusFP.

