Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics.
Require Import DDModels.
From Flocq Require Import Pff2Flocq.

Require Import mathcomp.ssreflect.ssreflect.

Section TwoMultCorrect.

Context {NANS: Nans} {t : type}.

Notation emin := (@emin t).

Variables (a b : ftype t).
Hypothesis (FIN : is_finite_p (Fast2Mult a b)).
Hypothesis (UF  :  (FT2R a * FT2R b) <> 0 -> 
  bpow Zaux.radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R a * FT2R b)). 

Lemma Fast2MultModel_correct :
  FT2R a * FT2R b = FT2R (Fast2Mult_mul a b) + FT2R (Fast2Mult_err a b).
Proof.
set (m := BMULT a b).
set (p := BFMA a b (BOPP m)).
destruct FIN as (FINm & FINp). 
unfold Fast2Mult_mul, Fast2Mult_err, fst, snd in *; simpl in *.
fold m in FINp. fold m.
BFMA_correct t a b (BOPP m).
unfold m.
rewrite Binary.B2R_Bopp.
BMULT_correct t a b. 
(* rewriting correctly here requires some careful manipulation *)
set (x:= (Binary.B2R _ _ a * Binary.B2R _ _ b - Generic_fmt.round _ _ _
     (Binary.B2R _ _ a * Binary.B2R _ _  b))).
set (y:= Generic_fmt.round _ _ _ (Binary.B2R _ _ a * Binary.B2R _ _ b) ).
rewrite (Generic_fmt.round_generic (Zaux.radix2) (FLT.FLT_exp emin (fprec t))
  (Generic_fmt.Znearest choice)).
subst y x; field_simplify; auto.
clear y; subst x. 
set (x1:= Binary.B2R _ _ a * Binary.B2R _ _ b).
set (x2:= Generic_fmt.round _ _ _ x1).
replace (x1 - x2) with ( - (x2 - x1)) by nra.
apply Generic_fmt.generic_format_opp.
subst x1 x2. 
apply (Mult_error.mult_error_FLT (Zaux.radix2) emin (fprec t)
  (Generic_fmt.Znearest choice) (FT2R a) (FT2R b)). 
apply Binary.generic_format_B2R.
apply Binary.generic_format_B2R.
(* use hyp of no underflow *)
apply UF.
Qed.

Lemma TwoMult_is_DW : 
  double_word (Fast2Mult_mul a b) (Fast2Mult_err a b).
Proof.
  rewrite /double_word/common.rounded-Fast2MultModel_correct // /Fast2Mult_mul/Fast2Mult /=. 
destruct FIN as (FINm & FINp).
unfold Fast2Mult, Fast2Mult_mul, Fast2Mult_err, fst, snd in *.
  BMULT_correct t a b.
Qed.

End TwoMultCorrect.


