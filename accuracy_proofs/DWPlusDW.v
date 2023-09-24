Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common.
Require Import Fast2Mult_acc TwoSum_acc DWPlus_acc.
Require Import DWPlus DDModels.
From Flocq Require Import Pff2Flocq Core.

Require Import mathcomp.ssreflect.ssreflect.

(* for choice functions : choice = fun x0 : Z => negb (Z.even x0) *)
Require Import Logic.FunctionalExtensionality.

Section AccuracyDWPlusDW.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Variables (xh xl yh yl : ftype t).

Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Let ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 
Notation u   := (bpow Zaux.radix2 (- fprec t)).

Let emin :=  (@DDModels.emin t).

Hypothesis  xE : double_word xh xl.
Hypothesis  yE : double_word yh yl.
Hypothesis FIN : is_finite_p (AccurateDWPlusDW xh xl yh yl). 
Hypothesis Hp3 : (3 <= fprec t)%Z.

Let xhr := (FT2R xh).
Let xlr := (FT2R xl).
Let yhr := (FT2R yh).
Let ylr := (FT2R yl).

Let zh := (FT2R (fst (AccurateDWPlusDW xh xl yh yl))).
Let zl := (FT2R (snd (AccurateDWPlusDW xh xl yh yl))).

Definition relative_error_DWPlusDW := 
  Rabs ((zh + zl - (xhr + xlr + yhr + ylr)) / (xhr + xlr + yhr + ylr)).
Definition errorDWDW := ((xhr + xlr + yhr + ylr) - (zh + zl)).
Local Notation p := (fprec t).
Definition rnd := 
  (round radix2 (SpecFloat.fexp (fprec t) (femax t)) (Generic_fmt.Znearest choice)). 

(* connect paper proofs to local defs *)
Fact rel_errorE: relative_error_DWPlusDW = Rabs errorDWDW * (Rabs (/( xhr + xlr + yhr + ylr))).
Proof.
rewrite /relative_error_DWPlusDW  /Rdiv !Rabs_mult -Ropp_minus_distr Rabs_Ropp //.
Qed.

Fact FIN1 : 
is_finite_p (TwoSumF xl yl). Admitted.

Fact FIN2 : 
is_finite_p (TwoSumF xh yh). Admitted.

Fact FIN3 :
is_finite_p 
  (Fast2Sum (TwoSumF_sum xh yh) 
    (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl))). Admitted. 

Fact ORD1 : 
    Rabs (FT2R (BPLUS (TwoSumF_err xh yh) 
      (TwoSumF_sum xl yl))) <= Rabs (FT2R (TwoSumF_sum xh yh)).
Proof.
rewrite /TwoSumF_sum/TwoSumF/fst/snd.
have HFIN: is_finite (BPLUS (TwoSumF_err xh yh) (BPLUS xl yl)) = true. admit.
remember (BPLUS xl yl) as f1.
remember (TwoSumF_err xh yh) as f2.
BPLUS_correct t f2 f1. clear H4.
rewrite Heqf2 Heqf1.
rewrite TwoSumF_correct.
rewrite /TwoSumF_sum/TwoSumF/fst.
 Admitted.


Lemma relative_errorDWDW_eq :
relative_errorDWDW p choice xhr xlr yhr ylr = relative_error_DWPlusDW.
Proof.
rewrite /relative_errorDWDW/relative_error_DWPlusDW.
f_equal. f_equal; try nra. f_equal; try nra.
unfold zh, zl. rewrite /AccurateDWPlusDW.
remember (TwoSum_sum _ _ xlr ylr) as f1.
remember (TwoSum_sum _ _ xhr yhr) as f2.
remember (TwoSum_err _ _ xhr yhr) as f3.
remember (TwoSum_err _ _ xlr ylr) as f4.
pose proof TwoSumEq_FLT xl yl FIN1 as H. move: H.
pose proof TwoSumEq_FLT xh yh FIN2 as H1. move: H1.
replace (TwoSumF xh yh) with (TwoSumF_sum xh yh, TwoSumF_err xh yh) => //.
replace (TwoSumF xl yl) with (TwoSumF_sum xl yl, TwoSumF_err xl yl) => //.
replace (TwoSum p choice (FT2R xl) (FT2R yl)) with
  (TwoSum_sum p choice xlr ylr, TwoSum_err p choice xlr ylr) => //.
replace (TwoSum p choice (FT2R xh) (FT2R yh)) with
  (TwoSum_sum p choice xhr yhr, TwoSum_err p choice xhr yhr) => //.
rewrite/F2Rp. move => HA HB. rewrite /fst/snd in HA, HB. 
  inversion HA; clear HA. inversion HB; clear HB.
rewrite H0 in Heqf2; clear H0.
rewrite H1 in Heqf3; clear H1.
rewrite H2 in Heqf1; clear H2.
rewrite H3 in Heqf4; clear H3.
remember (F2Sum.Fast2Sum _ _ f2 _) as f5.
pose proof FastTwoSumEq_FLT (TwoSumF_sum xh yh)
  (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl)) FIN3 ORD1. 
rewrite -Heqf2 in H.
Admitted.

Theorem relative_errorDWPlusDW_correct :
relative_error_DWPlusDW <= (3 * u^2) / (1 - 4 * u).
Proof.
have HDWx: DWPlus.double_word p choice xhr xlr by 
  (unfold xhr, xlr; apply @dw_word_DWdouble => //).
have HDWy: DWPlus.double_word p choice yhr ylr by 
  (unfold yhr, ylr; apply @dw_word_DWdouble => //).
pose proof @DWPlusDW_relerr_bound (fprec t) 
  (fprec_gt_one t) choice eq_refl Hp3 xhr xlr yhr ylr
  HDWx HDWy.
Admitted.

End AccuracyDWPlusDW.


