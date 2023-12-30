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

Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Let ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 
Notation u   := (bpow Zaux.radix2 (- fprec t)).

(* TODO put in general file *)
Lemma double_word_underflow (xh xl: ftype t) : 
  double_word xh xl -> 
  Rabs (FT2R xh + FT2R xl) < 
      bpow radix2 (@emin t + fprec t - 1) -> 
  FT2R xl = 0.
Proof.
rewrite /double_word. intros DWx Hr. move: DWx. 
rewrite /rounded round_generic; [ nra|
  apply Plus_error.FLT_format_plus_small => //].
1,2: rewrite -B2R_float_of_ftype; 
  apply Binary.generic_format_B2R.
eapply Rle_trans.
apply Rlt_le, Hr.
apply bpow_le; rewrite /emin; lia.
Qed.

Lemma generic_format_FLT_FT2R (x : ftype t) : 
generic_format radix2 fexp (FT2R x).
Proof.
rewrite -B2R_float_of_ftype. 
apply Binary.generic_format_B2R.
Qed.

Lemma generic_format_FLX_FT2R (x : ftype t) : 
generic_format radix2 (FLX_exp (fprec t)) (FT2R x).
Proof.
rewrite -B2R_float_of_ftype. 
eapply (@generic_format_FLX_FLT radix2 emin).
apply Binary.generic_format_B2R.
Qed.

Fact fprec_gt_1 : (1 < fprec t)%Z.
Proof. pose proof (@fprec_lb t). lia. Qed.

Fact fexp_valid : Valid_exp fexp. 
Proof. apply FLT.FLT_exp_valid. apply fprec_gt_0. Qed.


Local Hint Resolve generic_format_FLT_FT2R 
                   generic_format_FLX_FT2R 
                   fprec_gt_1
                   fexp_valid : base.

Lemma double_word_0 (xh xl : ftype t) : 
  double_word xh xl -> 
  FT2R xh = 0 ->  
  FT2R xl = 0.
Proof.
rewrite /double_word.
intros DWx H0. rewrite H0 in DWx.
rewrite DWx Rplus_0_l /rounded 
  round_generic => //; auto with base.
Qed.


Ltac  field_simplify_format :=
  match goal with |- context [generic_format _ _ ?a ] => 
    field_simplify a
  end;  
  try apply generic_format_0;
  auto with base.

(* END TODO but check local hints *)


Variables (xh xl yh yl : ftype t).

Let xhr := (FT2R xh).
Let xlr := (FT2R xl).
Let yhr := (FT2R yh).
Let ylr := (FT2R yl).

Local Notation p := (fprec t).
(* connect paper proofs to local defs *)
Definition DWPlusDW :=
  F2Sum.Fast2Sum p choice
           (fst
              (F2Sum.Fast2Sum p choice (TwoSum_sum p choice xhr yhr)
                 (round radix2 (FLX_exp p) (Znearest choice)
                    (TwoSum_err p choice xhr yhr + TwoSum_sum p choice xlr ylr))))
           (round radix2 (FLX_exp p) (Znearest choice)
              (TwoSum_err p choice xlr ylr +
               snd
                 (F2Sum.Fast2Sum p choice (TwoSum_sum p choice xhr yhr)
                    (round radix2 (FLX_exp p) (Znearest choice)
                       (TwoSum_err p choice xhr yhr + TwoSum_sum p choice xlr ylr)))))
.

Let emin :=  (@DDModels.emin t).

Hypothesis  xE : double_word xh xl.
Hypothesis  yE : double_word yh yl.
Hypothesis Hp3 : (3 <= fprec t)%Z.

Definition rnd_FLT := 
  (round radix2 (SpecFloat.fexp (fprec t) (femax t)) (Generic_fmt.Znearest choice)). 


Let f0 := BPLUS xh yh.
Let x  := TwoSumF_err xl yl.
Let x1 := TwoSumF_err xh yh.
Let y1 := BPLUS xl yl.
Let f1 := BPLUS x1 y1.
Let y  := snd (Fast2Sum f0 f1).

Fact FIN1
  (FIN : is_finite_p (AccurateDWPlusDW xh xl yh yl)): 
  is_finite_p (Fast2Sum f0 f1).
Proof. 
move : FIN. 
rewrite /is_finite_p/AccurateDWPlusDW.
rewrite /Fast2Sum/TwoSumF/snd/fst.
move => [] . repeat subexpr_finite => //.
Qed.


Fact FIN2
  (FIN : is_finite_p (AccurateDWPlusDW xh xl yh yl)): 
is_finite_p (TwoSumF xh yh).
Proof.
move : FIN. 
rewrite /is_finite_p/AccurateDWPlusDW.
rewrite /Fast2Sum/TwoSumF/snd/fst.
move => [] . repeat subexpr_finite; split => //.
Qed.

Fact FIN3
  (FIN : is_finite_p (AccurateDWPlusDW xh xl yh yl)): 
is_finite (BPLUS x1 y1) = true.
Proof. 
move : FIN. 
rewrite /is_finite_p/AccurateDWPlusDW.
rewrite /Fast2Sum/TwoSumF/snd/fst.
move => []. repeat subexpr_finite => //.
Qed.

Fact FIN4
  (FIN : is_finite_p (AccurateDWPlusDW xh xl yh yl)): 
is_finite_p (TwoSumF xl yl).
Proof. 
move : FIN. 
rewrite /is_finite_p/AccurateDWPlusDW.
rewrite /Fast2Sum/TwoSumF/snd/fst.
move => [] . repeat subexpr_finite; split => //.
Qed.

Fact FIN5
  (FIN : is_finite_p (AccurateDWPlusDW xh xl yh yl)): 
is_finite (BPLUS x y) = true.
Proof. 
move : FIN. 
rewrite /is_finite_p/AccurateDWPlusDW.
rewrite /Fast2Sum/TwoSumF/snd/fst.
move => []. repeat subexpr_finite => //.
Qed.

(* the result of the FLT format algorithm and the FLX format algorithm are 
  equal, regardless of underflow. *)
Lemma DWPlusDWEq_FLT 
  (FIN : is_finite_p (AccurateDWPlusDW xh xl yh yl)): 
  DWPlusDW = F2Rp (AccurateDWPlusDW xh xl yh yl).
Proof.

pose proof (FIN1 FIN) as fin1.
pose proof (FIN2 FIN) as fin2.
pose proof (FIN3 FIN) as fin3.
pose proof (FIN4 FIN) as fin4.
pose proof (FIN5 FIN) as fin5.

move: FIN.
rewrite /AccurateDWPlusDW/is_finite_p/DWPlusDW.
move => [].

replace (TwoSumF xh yh) with (BPLUS xh yh, TwoSumF_err xh yh) => //. 
replace (TwoSumF xl yl) with (BPLUS xl yl, TwoSumF_err xl yl) => //.

replace (Fast2Sum f0 f1) with 
  (fst (Fast2Sum f0 f1), y) => //.
set (f3:= (BPLUS (TwoSumF_err xl yl) y)) => //.
pose proof FastTwoSumEq_FLT (fst (Fast2Sum f0 f1)) f3 as H1.
  move : H1.

replace (Fast2Sum (fst (Fast2Sum f0 f1)) f3) with
  (fst (Fast2Sum (fst (Fast2Sum f0 f1)) f3), 
      snd (Fast2Sum (fst (Fast2Sum f0 f1)) f3)) => //.
match goal with |-context [F2Sum.Fast2Sum _ _ ?a ?b] => 
  set (A := a); set (B := b)
end.
replace (F2Sum.Fast2Sum p choice A B) with 
  (fst (F2Sum.Fast2Sum p choice A B), 
    snd (F2Sum.Fast2Sum p choice A B)) => //.
rewrite /F2Rp. 

  move => H1 HFIN1 HFIN2.

rewrite -H1 => //. clear H1. subst A B. 
match goal with |-context [F2Sum.Fast2Sum _ _ ?a ?b] => 
  set (A := a); set (B := b)
end.
replace (F2Sum.Fast2Sum p choice A B) with 
  (fst (F2Sum.Fast2Sum p choice A B), 
    snd (F2Sum.Fast2Sum p choice A B)) => //.
rewrite /F2Sum.Fast2Sum/F2SumFLX.Fast2Sum/fst/snd.
replace (Fast2Sum f0 f1) with 
  (fst (Fast2Sum f0 f1), snd (Fast2Sum f0 f1)) => //.

have Hf0: TwoSum_sum p choice xhr yhr = FT2R f0.
subst f0. rewrite /TwoSum_sum.
rewrite TwoSumEq_FLT /F2Rp/snd => //. 

have Hx1 : TwoSum_err p choice xhr yhr = FT2R x1.
subst x1. rewrite /TwoSum_err/TwoSumF_err.
rewrite TwoSumEq_FLT /F2Rp/snd => //. 

have Hy1 : TwoSum_sum p choice xlr ylr = FT2R y1.
subst y1. rewrite /TwoSum_sum.
rewrite TwoSumEq_FLT /F2Rp/snd => //.

have Hf1: round radix2 (FLX_exp p) (Znearest choice) 
          (TwoSum_err p choice xhr yhr + 
              TwoSum_sum p choice xlr ylr) = FT2R f1.
subst f1.
BPLUS_correct t x1 y1.
rewrite -rnd_plus_FLT_FLX_eq.
f_equal. f_equal => //.

have Heq1: FT2R (fst (Fast2Sum f0 f1)) = 
  (fst (F2Sum.Fast2Sum p choice (FT2R f0) (FT2R f1))).
by rewrite (FastTwoSumEq_FLT f0 f1 fin1).

have HA: A = FT2R (fst (Fast2Sum f0 f1)).
{ subst A. 
rewrite Heq1 /F2Sum.Fast2Sum/F2SumFLX.Fast2Sum/fst.
f_equal. f_equal => //. }

have Hx: TwoSum_err p choice xlr ylr = FT2R x.
subst x. rewrite /TwoSum_err/TwoSumF_err.
rewrite TwoSumEq_FLT /F2Rp/snd => //. 

have Heq2: FT2R (snd (Fast2Sum f0 f1)) = 
  (snd (F2Sum.Fast2Sum p choice (FT2R f0) (FT2R f1))).
by rewrite (FastTwoSumEq_FLT f0 f1 fin1).

have Hy: snd (F2Sum.Fast2Sum p choice (TwoSum_sum p choice xhr yhr)
  (round radix2 (FLX_exp p) (Znearest choice)
  (TwoSum_err p choice xhr yhr + TwoSum_sum p choice xlr ylr))) = FT2R y. 
subst y. 
rewrite Heq2. 
rewrite /F2Sum.Fast2Sum/F2SumFLX.Fast2Sum/snd.
repeat f_equal => //.

have HB: B = FT2R f3.
{ subst B f3. 
replace (TwoSumF_err xl yl) with x => //.
BPLUS_correct t x y.
rewrite -rnd_plus_FLT_FLX_eq.
f_equal. f_equal => //. } 

repeat f_equal => //.
Qed.


Let zh := (FT2R (fst (AccurateDWPlusDW xh xl yh yl))).
Let zl := (FT2R (snd (AccurateDWPlusDW xh xl yh yl))). 

Definition relative_error_DWPlusDW := 
  Rabs ((zh + zl - (xhr + xlr + yhr + ylr)) / (xhr + xlr + yhr + ylr)).
Definition errorDWDW := ((xhr + xlr + yhr + ylr) - (zh + zl)).


Definition rnd := 
  (round radix2 (SpecFloat.fexp (fprec t) (femax t)) (Generic_fmt.Znearest choice)). 

(* connect paper proofs to local defs *)
Fact rel_errorE: relative_error_DWPlusDW = 
    Rabs errorDWDW * (Rabs (/( xhr + xlr + yhr + ylr))).
Proof.
rewrite /relative_error_DWPlusDW  
  /Rdiv !Rabs_mult -Ropp_minus_distr Rabs_Ropp //.
Qed.

Hypothesis FIN : is_finite_p (AccurateDWPlusDW xh xl yh yl). 

Lemma relative_errorDWDW_eq :
relative_errorDWDW p choice xhr xlr yhr ylr = relative_error_DWPlusDW.
Proof.
rewrite /relative_errorDWDW/relative_error_DWPlusDW.
f_equal. f_equal; try nra. f_equal; try nra.
unfold zh, zl.
fold DWPlusDW. 
rewrite DWPlusDWEq_FLT => //. 
Qed.

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
move: H. by rewrite relative_errorDWDW_eq.
Qed.

End AccuracyDWPlusDW.


