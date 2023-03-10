(* This file contains the floating-point functional model in IEEE-754
  format of the 2Sum algorithm, along with a theorem regarding the 
  correctness of the 2Sum algorithm *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics.
Require Import DDModels.
From Flocq Require Import Pff2Flocq.

Require Import mathcomp.ssreflect.ssreflect.

Section AccuracyA13.

Context {NANS: Nans} {t : type}.

Lemma TwoSumF_correct (a b : ftype t) (FIN : is_finite_p (TwoSumF a b) ) :
  FT2R (TwoSumF_err a b) = FT2R a + FT2R b - FT2R (TwoSumF_sum a b).
Proof.
set (s  := BPLUS a b).
set (a' := BMINUS s b).
set (b' := BMINUS s a').
set (da := BMINUS a a').
set (db := BMINUS b b').
destruct FIN as (FINs & FINd).
(* use TwoSum correct from Flocq *)
pose proof (TwoSum_correct (@emin t) (fprec t) choice 
    (fprec_gt_one t) emin_le_0 choiceP (FT2R b) (FT2R a)) as Hc.
rewrite Rplus_comm; rewrite <- Hc; clear Hc; rewrite_format.
(* algebra *)
rewrite <- Rplus_opp, Rplus_comm, <- Rplus_assoc.
replace (FT2R b + FT2R a) with (FT2R a + FT2R b) by nra.
(* rewrites from correctness theorems *)
unfold TwoSumF_err, TwoSumF_sum, TwoSumF, fst, snd in *.
BPLUS_correct t a b; field_simplify.
fold s a' b' da db in FINd; fold s a' b' da db. BPLUS_correct t da db.
rewrite Rplus_comm; repeat f_equal.
{ subst db; BMINUS_correct t b b'.
  subst b' s; BMINUS_correct t (BPLUS a b) a'; rewrite H4.
  repeat f_equal.
  subst a'. BMINUS_correct t (BPLUS a b) b; rewrite H4.
  repeat f_equal. }
{ subst da; BMINUS_correct t a a'.
  subst a' s. BMINUS_correct t (BPLUS a b) b; rewrite H4.
  repeat f_equal. }
all: apply Binary.generic_format_B2R.
Qed.

Lemma Fast2MultModel_correct (a b : ftype t) (FIN : is_finite_p (Fast2Mult a b) ) :
  FT2R a * FT2R b = FT2R (Fast2Mult_mul a b) + FT2R (Fast2Mult_err a b).
Proof.
set (m := BMULT a b).
set (p := BFMA a b (BOPP m)).
destruct FIN as (FINm & FINp).

assert (FINab : 
  Binary.is_finite _ _ a = true /\ Binary.is_finite _ _ b = true).
{ unfold Fast2Mult in FINm; simpl in FINm; destruct a; destruct b; 
  simpl in FINm; split; try discriminate; auto; destruct s1; destruct s0;
  try discriminate; auto. }
destruct FINab as (FINa & FINb).
assert (FINm2 : Binary.is_finite _ _ (BOPP m) = true).
{ unfold Fast2Mult in FINm; simpl in FINm; fold m in FINm; destruct m; 
  simpl in FINm;  try discriminate; auto. }
unfold Fast2Mult_err, Fast2Mult_mul, Fast2Mult, fst, snd; fold m.

pose proof @generic_fmt_fexp_FLT t as Hgen; fold choice (@emin t) in Hgen.

pose proof (Binary.Bfma_correct  (fprec t) (femax t) 
  (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan t) BinarySingleNaN.mode_NE) a b (BOPP m)
  FINa FINb FINm2 as A. 
pose proof (is_finite_fma_no_overflow a b (BOPP m) FINp) as HOV; cbv zeta in A.
apply Rlt_bool_true in HOV; unfold FT2R, common.rounded in HOV; rewrite HOV in A; clear HOV;
  destruct A as (A & _); unfold BFMA, BINOP, FT2R.
  rewrite Hgen in A; rewrite A; clear A.

replace ((Binary.B2R (fprec t) (femax t) a * Binary.B2R (fprec t) (femax t) b +
   Binary.B2R (fprec t) (femax t) (BOPP m))) with
  (Binary.B2R (fprec t) (femax t) a * Binary.B2R (fprec t) (femax t) b -
   Binary.B2R (fprec t) (femax t) m).
subst m.

pose proof (Binary.Bmult_correct  (fprec t) (femax t) 
  (fprec_gt_0 t) (fprec_lt_femax t) (mult_nan t) BinarySingleNaN.mode_NE) a b as B.
pose proof (is_finite_BMULT_no_overflow a b FINm) as HOV; cbv zeta in B.
apply Rlt_bool_true in HOV; unfold FT2R, common.rounded in HOV; rewrite HOV in B; clear HOV;
  destruct B as (B & _); unfold BMULT, BINOP, FT2R.
  rewrite Hgen in B; rewrite B; clear B.

pose proof Generic_fmt.round_generic (Zaux.radix2) (FLT.FLT_exp (@emin t) (fprec t))
  (Generic_fmt.Znearest choice) as H0.
set (x:=
  (Binary.B2R (fprec t) (femax t) a * Binary.B2R (fprec t) (femax t) b -
   Generic_fmt.round Zaux.radix2 (FLT.FLT_exp emin (fprec t))
     (Generic_fmt.Znearest choice)
     (Binary.B2R (fprec t) (femax t) a * Binary.B2R (fprec t) (femax t) b))).
set (y:= Generic_fmt.round Zaux.radix2 (FLT.FLT_exp emin (fprec t))
  (Generic_fmt.Znearest choice)
  (Binary.B2R (fprec t) (femax t) a * Binary.B2R (fprec t) (femax t) b) ).
rewrite H0.
subst x; subst y.
field_simplify; auto.

subst x.
set (x1:= Binary.B2R (fprec t) (femax t) a * Binary.B2R (fprec t) (femax t) b).
set (x2:= Generic_fmt.round Zaux.radix2 (FLT.FLT_exp emin (fprec t))
     (Generic_fmt.Znearest choice) x1).
replace (x1 - x2) with ( - (x2 - x1)) by nra.
apply Generic_fmt.generic_format_opp.

pose proof Mult_error.mult_error_FLT (Zaux.radix2) (@emin t) (fprec t)
  (Generic_fmt.Znearest choice) (FT2R a) (FT2R b) as Hc; 
unfold FT2R in Hc.
subst x1; subst x2.
apply Hc. 
apply Binary.generic_format_B2R.
apply Binary.generic_format_B2R.
intros.
admit.
subst m.
unfold BOPP.
rewrite Binary.B2R_Bopp; auto.
Admitted.

End AccuracyA13.

Section isDWord.
Context {NANS: Nans} {t : type}.

Lemma TwoSum_is_DW (a b : ftype t) (Hfin: is_finite_p (TwoSumF a b)) : 
  double_word (TwoSumF_sum a b) (TwoSumF_err a b).
Proof.
  rewrite /double_word TwoSumF_correct // /TwoSumF_sum /= /common.rounded. 
destruct Hfin as (FINm & FINp).
unfold TwoSumF_err, TwoSumF_sum, TwoSumF, fst, snd in *.
  BPLUS_correct t a b.
Qed.

Lemma TwoMult_is_DW (a b : ftype t) (Hfin: is_finite_p (Fast2Mult a b)) : 
  double_word (Fast2Mult_mul a b) (Fast2Mult_err a b).
Proof.
  rewrite /double_word/common.rounded-Fast2MultModel_correct // /Fast2Mult_mul/Fast2Mult /=. 
destruct Hfin as (FINm & FINp).
unfold Fast2Mult, Fast2Mult_mul, Fast2Mult_err, fst, snd in *.
  BMULT_correct t a b.
Qed.

End isDWord.

Section AccuracyDWPlus.
Context {NANS: Nans} {t : type}.

Variables (a b c : ftype t).
Notation zh := (FT2R (fst (DWPlusFP a b c))).
Notation zl := (FT2R (snd (DWPlusFP a b c))).
Notation x  := (FT2R a + FT2R b).
Notation y  := (FT2R c).

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 
Notation u   := (bpow Zaux.radix2 (- fprec t)).

Definition relative_errorDWPlusFP := Rabs (((zh + zl) - (x  + y)) / (x  + y)).

Theorem relative_errorDWPlusFP_correct : relative_errorDWPlusFP <= 2 * u ^ 2.
Admitted.



End AccuracyDWPlus.

