(* This file contains the floating-point functional model in IEEE-754
  format of the 2Sum algorithm, along with a theorem regarding the 
  correctness of the 2Sum algorithm *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics.
Require Import DDModels.
From Flocq Require Import Pff2Flocq Core.
Require Import F2SumFLT.

Require Import mathcomp.ssreflect.ssreflect.

Section TwoSumCorrect.

Context {NANS: Nans} {t : type}.

Variables (a b : ftype t).
Hypothesis (FIN : is_finite_p (TwoSumF a b)).

Theorem TwoSumF_correct :
  FT2R (TwoSumF_err a b) = FT2R a + FT2R b - FT2R (TwoSumF_sum a b).
Proof.
set (s  := BPLUS a b).
set (a' := BMINUS s b).
set (b' := BMINUS s a').
set (da := BMINUS a a').
set (db := BMINUS b b').
destruct FIN as (FINs & FINd).
(* use TwoSum correct from Flocq, not double-double paper *)
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

Theorem TwoSum_is_DW: 
  double_word (TwoSumF_sum a b) (TwoSumF_err a b).
Proof.
  rewrite /double_word TwoSumF_correct // /TwoSumF_sum /= /common.rounded. 
destruct FIN as (FINm & FINp).
unfold TwoSumF_err, TwoSumF_sum, TwoSumF, fst, snd in *.
  BPLUS_correct t a b.
Qed.

End TwoSumCorrect.


Section TwoSumAcc. 

Context {NANS: Nans} {t : type}.

Variables (a b : ftype t).
Hypothesis (FIN : is_finite_p (TwoSumF a b)).

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 
Notation u   := (bpow Zaux.radix2 (- fprec t)).

Theorem TwoSum_accuracy: 
    Rabs (FT2R (TwoSumF_err a b))  <= /2 * ulp (FT2R a + FT2R b).
Proof.
rewrite TwoSumF_correct; auto. unfold TwoSumF_sum. simpl.
rewrite Rabs_minus_sym. 
pose proof error_le_half_ulp
  Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) choice (FT2R a + FT2R b) as HE.
destruct FIN as (FINs & FINd); simpl in FINs. 
BPLUS_correct t a b. fold (@FT2R t); auto. 
Qed.

End TwoSumAcc.

Section FastTwoSumCorrect.

Context {NANS: Nans} {t : type}.

Notation FE := (FLT_exp (@emin t) (fprec t)).

Variables (a b : ftype t).
Hypothesis FIN : is_finite_p (Fast2Sum a b).
Hypothesis Hle : Rabs (FT2R b) <= Rabs (FT2R a).

Theorem FastTwoSum_correct :
  FT2R (Fast2Sum_err a b) = FT2R a + FT2R b - FT2R (Fast2Sum_sum a b).
Proof.
set (s := BPLUS a b).
set (z := BMINUS s a).
move: FIN.
rewrite /Fast2Sum_err/Fast2Sum_sum/Fast2Sum/fst/snd/=.
move => []; rewrite /fst/snd; fold s z; move => FINs FINd.
BMINUS_correct t b z; field_simplify. clear H4.
unfold z.
have FINsa: Binary.is_finite (fprec t) (femax t) (BMINUS s a) = true.
{ move : FINd. fold z; destruct z => /=; destruct b => /= ; try discriminate; auto. } 
BMINUS_correct t s a; field_simplify. unfold s in *. BPLUS_correct t a b; field_simplify.
have Ga: generic_format radix2 (FLT_exp (@emin t) (fprec t)) (FT2R a) by
  apply (Binary.generic_format_B2R (fprec t) (femax t)).
have Gb: generic_format radix2 (FLT_exp (@emin t) (fprec t)) (FT2R b) by
  apply (Binary.generic_format_B2R (fprec t) (femax t)).
have Hr : (radix2 <= 3)%Z by (simpl; auto).
(** apply lemmas from paper_proofs.F2SumFLT *)
have: Fast2Sum_correct_flt radix2 (@emin t) (fprec t) choice (FT2R a) (FT2R b). 
apply F2Sum_correct_abs_flt => //. apply (fprec_gt_one t).
rewrite /Fast2Sum_correct_flt/Fast2Sum_flt/fst/snd; fold (@FT2R t); 
  move => H; rewrite H; f_equal.
Qed.

Theorem Fast2Sum_is_DW: 
  double_word (Fast2Sum_sum a b) (Fast2Sum_err a b).
Proof.
  rewrite /double_word FastTwoSum_correct // /Fast2Sum_sum /= /common.rounded. 
destruct FIN as (FINm & FINp).
unfold Fast2Sum_err, Fast2Sum_sum, Fast2Sum, fst, snd in *.
  BPLUS_correct t a b.
Qed.

End FastTwoSumCorrect.

Section FastTwoSumAcc.
Context {NANS: Nans} {t : type}.

Variables (a b : ftype t).
Hypothesis FIN : is_finite_p (Fast2Sum a b).
Hypothesis Hle : Rabs (FT2R b) <= Rabs (FT2R a).

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 
Notation u   := (bpow Zaux.radix2 (- fprec t)).

Theorem FastTwoSum_accuracy: 
    Rabs (FT2R (Fast2Sum_err a b))  <= /2 * ulp (FT2R a + FT2R b).
Proof.
rewrite FastTwoSum_correct; auto. unfold Fast2Sum_sum. simpl.
rewrite Rabs_minus_sym. 
pose proof error_le_half_ulp
  Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) choice (FT2R a + FT2R b) as HE.
destruct FIN as (FINs & FINd); simpl in FINs. 
BPLUS_correct t a b. fold (@FT2R t); auto. 
Qed.

End FastTwoSumAcc.
