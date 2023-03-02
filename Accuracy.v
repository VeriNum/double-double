(* This file contains the floating-point functional model in IEEE-754
  format of the 2Sum algorithm, along with a theorem regarding the 
  correctness of the 2Sum algorithm *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs.
Require Import DDModels.
From Flocq Require Import Pff2Flocq.


Section Accuracy.

Context {NANS: Nans} {t : type}.

Lemma TwoSumF_correct (a b : ftype t) (FIN : is_finite_p (TwoSumF a b) ) :
  FT2R (TwoSumF_err a b) = FT2R a + FT2R b - FT2R (TwoSumF_sum a b).
Proof.
(* all steps are finite from FIN *)
set (s  := BPLUS a b).
set (a' := BMINUS s b).
set (b' := BMINUS s a').
set (da := BMINUS a a').
set (db := BMINUS b b').
destruct FIN as (FINs & FINd).
assert (FINab : 
  Binary.is_finite _ _ a = true /\ Binary.is_finite _ _ b = true).
{ unfold TwoSumF in FINs; simpl in FINs; destruct a; destruct b; 
  simpl in FINs; split; try discriminate; auto; destruct s1; destruct s0;
  try discriminate; auto. }
destruct FINab as (FINa & FINb).
assert (FINdab : 
  Binary.is_finite _ _ da = true /\ Binary.is_finite _ _ db = true).
{ unfold TwoSumF in FINd; fold s a' b' da db in FINd; simpl in FINd; destruct da; destruct db; 
  simpl in FINd; split; try discriminate; auto; destruct s1; destruct s0;
  try discriminate; auto. }
destruct FINdab as (FINda & FINdb).
assert (FINa' : 
  Binary.is_finite _ _ a' = true).
{ subst da. destruct a; destruct a'; try discriminate; auto; destruct s1; destruct s0;
  try discriminate; auto. }
assert (FINb' : 
  Binary.is_finite _ _ b' = true).
{ subst db. destruct b; destruct b'; try discriminate; auto; destruct s1; destruct s0;
  try discriminate; auto. 
(* end all steps are finite *) }
(* invoke flocq 2Sum theorem over FLT *)
pose proof (TwoSum_correct (@emin t) (fprec t) choice 
    (fprec_gt_one t) emin_le_0 choiceP (FT2R b) (FT2R a)) as Hc.
rewrite Rplus_comm; rewrite <- Hc; clear Hc.
pose proof @generic_fmt_fexp_FLT t as Hgen; fold choice (@emin t)  in Hgen.
(* invoke flocq binary op correctness theorems for rewrites *)
unfold TwoSumF_err, TwoSumF_sum, TwoSumF, fst, snd.
fold s a' b' da db; unfold s.
rewrite <- Rplus_opp, Rplus_comm, <- Rplus_assoc.
pose proof (Binary.Bplus_correct  (fprec t) (femax t) 
  (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE a b FINa FINb) as S.
pose proof (is_finite_sum_no_overflow a b FINs) as HOV.
replace (FT2R b + FT2R a) with (FT2R a + FT2R b) by nra.
apply Rlt_bool_true in HOV; unfold FT2R in HOV; rewrite HOV in S; clear HOV; 
  destruct S as (S & _); unfold BPLUS, BINOP, FT2R; 
  rewrite Hgen in S; rewrite S; field_simplify.
pose proof (Binary.Bplus_correct  (fprec t) (femax t) 
  (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE da db FINda FINdb) as D.
pose proof (is_finite_sum_no_overflow  da db FINd) as HOV.
apply Rlt_bool_true in HOV; unfold FT2R in HOV; rewrite HOV in D; clear HOV;
  destruct D as (D & _); unfold BPLUS, BINOP, FT2R; 
  rewrite Hgen in D; rewrite D; f_equal.
rewrite Rplus_comm; f_equal.
subst db.
pose proof (Binary.Bminus_correct  (fprec t) (femax t) 
  (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE b b' FINb FINb') as DB.
pose proof (is_finite_minus_no_overflow  b b' FINdb) as HOV.
apply Rlt_bool_true in HOV; unfold FT2R in HOV; rewrite HOV in DB; clear HOV;
  destruct DB as (DB & _); unfold BMINUS, BINOP, FT2R; 
  rewrite Hgen in DB; rewrite DB; repeat f_equal.
subst b'.
pose proof (Binary.Bminus_correct  (fprec t) (femax t) 
  (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE s a' FINs FINa') as DB'.
pose proof (is_finite_minus_no_overflow  s a' FINb') as HOV.
apply Rlt_bool_true in HOV; unfold FT2R in HOV; rewrite HOV in DB'; clear HOV;
  destruct DB' as (DB' & _); unfold BMINUS, BINOP, FT2R; 
  rewrite Hgen in DB'; rewrite DB'; repeat f_equal.
{ subst s. unfold BPLUS, BINOP, FT2R. apply S. } 
{ subst a'.
  pose proof (Binary.Bminus_correct  (fprec t) (femax t) 
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE s b FINs FINb) as DA'.
  pose proof (is_finite_minus_no_overflow  s b FINa') as HOV.
  apply Rlt_bool_true in HOV; unfold FT2R in HOV; rewrite HOV in DA'; clear HOV;
    destruct DA' as (DA' & _); unfold BMINUS, BINOP, FT2R; 
    rewrite Hgen in DA'; rewrite DA'; repeat f_equal.
  { subst s. unfold BPLUS, BINOP, FT2R; apply S. } 
}
subst da.
pose proof (Binary.Bminus_correct  (fprec t) (femax t) 
  (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE a a' FINa FINa') as DA.
pose proof (is_finite_minus_no_overflow  a a' FINda) as HOV.
apply Rlt_bool_true in HOV; unfold FT2R in HOV; rewrite HOV in DA; clear HOV;
  destruct DA as (DA & _); unfold BMINUS, BINOP, FT2R; 
  rewrite Hgen in DA; rewrite DA; repeat f_equal.
{ subst a'.
  pose proof (Binary.Bminus_correct  (fprec t) (femax t) 
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE s b FINs FINb) as DA'.
  pose proof (is_finite_minus_no_overflow s b FINa') as HOV.
  apply Rlt_bool_true in HOV; unfold FT2R in HOV; rewrite HOV in DA'; clear HOV;
    destruct DA' as (DA' & _); unfold BMINUS, BINOP, FT2R; 
    rewrite Hgen in DA'; rewrite DA'; repeat f_equal.
  { subst s. unfold BPLUS, BINOP, FT2R; apply S. } 
}
apply Binary.generic_format_B2R.
apply Binary.generic_format_B2R.
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

End Accuracy.

