Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common.
Require Import DWPlus DDModels Fast2Mult_acc TwoSum_acc.
From Flocq Require Import Pff2Flocq Core.

Require Import mathcomp.ssreflect.ssreflect.

Context {NANS: Nans} {t : type}.

Section AccuracyDWPlusFP.

Variables (xh xl y : ftype t).
Notation zh := (FT2R (fst (DWPlusFP xh xl y))).
Notation zl := (FT2R (snd (DWPlusFP xh xl y))).
Let xr  := (FT2R xh + FT2R xl).
Let yr  := (FT2R y).

Hypothesis FIN : is_finite_p (DWPlusFP xh xl y). 
Hypothesis FINA : is_finite_p (TwoSumF xh y) (* should follow from FIN *).
Hypothesis FINB : Binary.is_finite _ _ (BPLUS xl (TwoSumF_err xh y)) = true (* should follow from FIN *).
Hypothesis Hp3 : (3 <= (fprec t))%Z.
Hypothesis DW  :   DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl).
Hypothesis HUF1 :   bpow radix2 ((@DDModels.emin t) + fprec t - 1) <=
  Rabs (FT2R (TwoSumF_sum xh y) + FT2R (BPLUS xl (TwoSumF_err xh y))).
Hypothesis HUF2 : bpow radix2 ((@DDModels.emin t) + fprec t - 1) <=
  Rabs (FT2R xl + FT2R (TwoSumF_err xh y)).
Hypothesis HUF3 : bpow radix2 ((@DDModels.emin t) + fprec t - 1) <= Rabs (FT2R xh + FT2R y).
Hypothesis Hle  : Rabs (FT2R (BPLUS xl (TwoSumF_err xh y))) <= Rabs (FT2R (TwoSumF_sum xh y)).


Theorem DWPlusFP_eq_no_underflow :
  DWPlus.DWPlusFP (fprec t) choice (FT2R xh) (FT2R xl) (FT2R y) = F2Rp (DWPlusFP xh xl y).
Proof.
move : FIN. move => []. 
pose proof round_FLT_FLX radix2 (@DDModels.emin t).
move => FIN1 FIN2. rewrite /DWPlus.DWPlusFP/DWPlusFP.
replace ( TwoSumF xh y) with ( TwoSumF_sum xh y,  TwoSumF_err xh y) => //.
replace (Fast2Sum (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y))) with
  (Fast2Sum_sum (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y)), 
  Fast2Sum_err (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y))) => //.
rewrite -FastTwoSumEq_no_underflow => //.
{ rewrite /TwoSum_err/TwoSum_sum TwoSumEq_no_underflow/fst/snd => //. 
f_equal. 
BPLUS_correct t xl (TwoSumF_err xh y). 
replace ( TwoSumF xh y) with ( TwoSumF_sum xh y,  TwoSumF_err xh y) => //.
rewrite /F2Rp/FT2R/fst/snd -H => //=. }  
Qed. 


Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 
Notation u   := (bpow Zaux.radix2 (- fprec t)).

Definition relative_error_DWPlusFP := Rabs (((zh + zl) - (xr  + yr)) / (xr  + yr)).

Theorem relative_errorDWPlusFP_correct : relative_error_DWPlusFP <= 2 * u ^ 2.
Proof.
have Hf : generic_format radix2 (FLX_exp (fprec t)) (FT2R y).
{ apply (@generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t)). unfold FT2R.
  apply (Binary.generic_format_B2R (fprec t) (femax t) y). }  
destruct (@DWPlusFP_correct (fprec t) (fprec_gt_one t) choice eq_refl 
  Hp3 (FT2R xh) (FT2R xl) (FT2R y) Hf) => // .
apply Rle_trans with (relative_errorDWFP (fprec t) choice (FT2R xh) (FT2R xl) (FT2R y)) => //.
apply Req_le.
rewrite /relative_error_DWPlusFP/relative_errorDWFP. 
pose proof DWPlusFP_eq_no_underflow. rewrite /F2Rp/DWPlus.DWPlusFP in H1.
repeat f_equal.
all: by rewrite H1.
Qed.

End AccuracyDWPlusFP.

