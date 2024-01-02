Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs common dd_tactics.
Require Import DDModels.
From Flocq Require Import Pff2Flocq Core.

Require Import mathcomp.ssreflect.ssreflect.


Section TwoMultCorrect.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (@common.emin t).

Variables (a b : ftype t).

Hypothesis (FIN : is_finite_p (Fast2Mult a b)).

Lemma Fast2MultModel_correct 
(UF  :  (FT2R a * FT2R b) <> 0 -> 
  bpow Zaux.radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R a * FT2R b)) :
  FT2R (Fast2Mult_err a b) =  FT2R a * FT2R b - FT2R (Fast2Mult_mul a b).
Proof.
set (m := BMULT a b).
set (p := BFMA a b (BOPP m)).
destruct FIN as (FINm & FINp). 
unfold Fast2Mult_mul, Fast2Mult_err, fst, snd in *; simpl in *.
fold m in FINp. fold m.
BFMA_correct t a b (BOPP m).
unfold m.
rewrite -!B2R_float_of_ftype.
rewrite /BOPP float_of_ftype_of_float.
rewrite Binary.B2R_Bopp !B2R_float_of_ftype.
rewrite round_generic => //.  
set (x1:= FT2R a * FT2R b).
set (x2:= FT2R (BMULT a b)).
replace (x1 + - x2) with ( - (x2 - x1)) by nra.
apply Generic_fmt.generic_format_opp.
subst x1 x2.
BMULT_correct t a b; rewrite !B2R_float_of_ftype.
apply (Mult_error.mult_error_FLT (Zaux.radix2) emin (fprec t)
  (Generic_fmt.Znearest choice) (FT2R a) (FT2R b)) => //;
apply generic_format_FLT_FT2R.
Qed.


Lemma TwoMult_is_DW  
(UF  :  (FT2R a * FT2R b) <> 0 -> 
  bpow Zaux.radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R a * FT2R b)) :
  double_word (Fast2Mult_mul a b) (Fast2Mult_err a b).
Proof.
  rewrite /double_word Fast2MultModel_correct // /TwoSumF_sum /= /common.rounded. 
destruct FIN as (FINm & FINp).
unfold Fast2Mult_mul, Fast2Mult_err, Fast2Mult, fst, snd in *.
  BMULT_correct t a b.
by rewrite -!B2R_float_of_ftype.
Qed.

End TwoMultCorrect.

Section TwoMultAcc. 
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (@common.emin t).
Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 
Notation u   := (bpow Zaux.radix2 (- fprec t)).

Variables (a b : ftype t).

Hypothesis (FIN : is_finite_p (Fast2Mult a b)).

Theorem Fast2Mult_accuracy_norm: 
forall UF  :  (FT2R a * FT2R b) <> 0 -> 
  bpow Zaux.radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R a * FT2R b),
    Rabs (FT2R (Fast2Mult_err a b))  <= /2 * ulp (FT2R a * FT2R b).
Proof.
intros; rewrite Fast2MultModel_correct; auto. unfold Fast2Mult_mul. simpl.
rewrite Rabs_minus_sym. 
pose proof error_le_half_ulp
  Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) choice (FT2R a * FT2R b) as HE.
destruct FIN as (FINs & FINd); simpl in FINs. 
BMULT_correct t a b. 
by rewrite !B2R_float_of_ftype.
Qed.


End TwoMultAcc.

