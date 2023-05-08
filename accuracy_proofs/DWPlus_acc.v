Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics.
Require Import DDModels Fast2Mult_acc TwoSum_acc.
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

Hypothesis FIN  : is_finite_p (DWPlusFP xh xl y). 

Theorem relative_errorDWPlusFP_correct : relative_error_DWPlusFP <= 2 * u ^ 2.
Proof.
move: FIN.
rewrite /relative_error_DWPlusFP /zh /fst /DWPlusFP /xr. 
set (s1l := snd (TwoSumF xh y)).
set (s1h := fst (TwoSumF xh y)).
have: FT2R (snd (TwoSumF xh y)) = FT2R xh + yr - FT2R (fst (TwoSumF xh y)).
apply(@TwoSumF_correct NANS t xh y). admit.
destruct (TwoSumF xh y) => /=. 
move => H0 []; rewrite /fst/snd; move => FIN1 FIN2.
destruct FIN as (FIN1 & FIN2). 

have H0 : FT2R (snd (TwoSumF xh y)) = FT2R xh + yr - FT2R (fst (TwoSumF xh y)).
apply(@TwoSumF_correct NANS t xh y). admit.
destruct (TwoSumF xh y) => /=. simpl in H0.

destruct s1. 


Search Ulp.ulp FLT_exp.

Admitted.

End AccuracyDWPlusFP.

