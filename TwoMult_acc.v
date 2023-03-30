(* This file contains the floating-point functional model in IEEE-754
  format of the 2Sum algorithm, along with a theorem regarding the 
  correctness of the 2Sum algorithm *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics.
Require Import DDModels.
From Flocq Require Import Pff2Flocq.

Require Import mathcomp.ssreflect.ssreflect.

Ltac BFMA_correct t a b s:=
unfold FT2R;
match goal with | FIN : Binary.is_finite _ _ (BFMA a b s) = true |- context [Binary.B2R _ _ (BFMA a b s)] =>
  let X:= fresh in set (X:= Binary.B2R _ _ (BFMA a b s)); unfold BFMA in X ;
  let H4 := fresh in pose proof (is_finite_fma_no_overflow a b s FIN) as H4; apply Rlt_bool_true in H4;
  unfold FT2R in H4;
  let H := fresh in 
  assert (H : Binary.is_finite _ _ a = true /\ Binary.is_finite _ _ b = true /\ Binary.is_finite _ _ s = true);
  [destruct a; destruct b; destruct s; 
      simpl in FIN; split; try discriminate; auto;
          match goal with | H: Binary.is_finite _ _
                   (BFMA (Binary.B754_infinity _ _ ?s4)
                      (Binary.B754_infinity _ _ ?s0) (Binary.B754_infinity _ _ ?s3)) = _ |- Binary.is_finite _ _ _ = _ =>
            destruct s4; destruct s0; destruct s3; try discriminate; auto end 
  | ]; 
    let H1 := fresh in let H2 := fresh in  destruct H as (H1 & H2 & HS);
    let H3 := fresh in pose proof (Binary.Bfma_correct  (fprec t) (femax t) 
        (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan t) BinarySingleNaN.mode_NE a b s H1 H2 HS) as H3; cbv zeta in H3;
    rewrite H4 in H3;
    destruct H3 as (H3 & _); clear H4 ; unfold BFMA in X; subst X; try field_simplify_round; 
    rewrite H3; try reflexivity 
end.

Section TwoMultCorrect.

Context {NANS: Nans} {t : type}.

Variables (a b : ftype t).
Hypothesis (FIN : is_finite_p (Fast2Mult a b)).
Hypothesis (UF  : bpow Zaux.radix2 (@emin t + 2 * fprec t - 1) <= Rabs (FT2R a * FT2R b)). 

Lemma Fast2MultModel_correct :
  FT2R a * FT2R b = FT2R (Fast2Mult_mul a b) + FT2R (Fast2Mult_err a b).
Proof.
set (m := BMULT a b).
set (p := BFMA a b (BOPP m)).
destruct FIN as (FINm & FINp).
(*unfold Fast2Mult_mul, Fast2Mult_err, fst, snd in *; simpl in *.
fold m in FINp. fold m.
BFMA_correct t a b (BOPP m).
unfold m.
rewrite Binary.B2R_Bopp.
BMULT_correct t a b. 
*)
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
etransitivity.

 revert Hc. rewrite_format. intros.
apply Hc. 
apply Binary.generic_format_B2R.
apply Binary.generic_format_B2R.
intros.

simpl in FINm.
destruct (BMULT a b); try discriminate; simpl; auto.
admit. 
pose proof Binary.bounded_ge_emin (fprec t) (femax t) m e e0. 
unfold Binary.B2R.

Search SpecFloat.bounded.
admit.
subst m.
unfold BOPP.
rewrite Binary.B2R_Bopp; auto.
Admitted.


Lemma TwoMult_is_DW : 
  double_word (Fast2Mult_mul a b) (Fast2Mult_err a b).
Proof.
  rewrite /double_word/common.rounded-Fast2MultModel_correct // /Fast2Mult_mul/Fast2Mult /=. 
destruct FIN as (FINm & FINp).
unfold Fast2Mult, Fast2Mult_mul, Fast2Mult_err, fst, snd in *.
  BMULT_correct t a b.
Qed.

End TwoMultCorrect.

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

