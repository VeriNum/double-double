Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common.
Require Import Fast2Mult_acc TwoSum_acc DWPlus_acc.
Require Import DWPlus DDModels DWord_defs.
From Flocq Require Import Pff2Flocq Core.

Require Import mathcomp.ssreflect.ssreflect.

(* for choice functions : choice = fun x0 : Z => negb (Z.even x0) *)
Require Import Logic.FunctionalExtensionality.

Section AccuracyDWPlusDW.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Notation u := (bpow Zaux.radix2 (- fprec t)).
Notation p := (fprec t).

Variables (xh xl yh yl : ftype t).

Let ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 
Let emin :=  (@DDModels.emin t).

Let xhr := (FT2R xh).
Let xlr := (FT2R xl).
Let yhr := (FT2R yh).
Let ylr := (FT2R yl).

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


(* start section hypotheses *)
Hypothesis  xE : double_word xh xl.
Hypothesis  yE : double_word yh yl.
Hypothesis Hp3 : (3 <= fprec t)%Z.
Hypothesis FIN : is_finite_p (AccurateDWPlusDW xh xl yh yl). 
(* end section hypotheses *)

Let f0 := BPLUS xh yh.
Let x  := TwoSumF_err xl yl.
Let x1 := TwoSumF_err xh yh.
Let y1 := BPLUS xl yl.
Let f1 := BPLUS x1 y1.
Let y  := snd (Fast2Sum f0 f1).

Ltac prove_finite := 
move : FIN;
rewrite /is_finite_p/AccurateDWPlusDW;
rewrite /Fast2Sum/TwoSumF/snd/fst;
move => [] ; repeat subexpr_finite => //
.

Fact FIN1 : is_finite_p (Fast2Sum f0 f1).
Proof. prove_finite. Qed.

Fact FIN2 : is_finite_p (TwoSumF xh yh).
Proof. prove_finite. Qed.

Fact FIN3 : is_finite (BPLUS x1 y1) = true.
Proof. prove_finite. Qed.

Fact FIN4 : is_finite_p (TwoSumF xl yl).
Proof. prove_finite. Qed.

Fact FIN5 : is_finite (BPLUS x y) = true.
Proof. prove_finite. Qed.

(* the result of the FLT format algorithm and the FLX format algorithm are 
  equal, regardless of underflow. *)
Lemma DWPlusDWEq_FLT : 
  DWPlusDW = F2Rp (AccurateDWPlusDW xh xl yh yl).
Proof.

pose proof FIN1 as fin1.
pose proof FIN2 as fin2.
pose proof FIN3 as fin3.
pose proof FIN4 as fin4.
pose proof FIN5 as fin5.

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

Lemma DWPlusDW_0 : (xhr + xlr + yhr + ylr) = 0 -> zh + zl = 0.
Proof.
unfold zh, zl.
have: DWPlusDW = F2Rp (AccurateDWPlusDW xh xl yh yl) by 
  apply  DWPlusDWEq_FLT =>//. 
rewrite /F2Rp.
replace DWPlusDW with
  (fst DWPlusDW, snd DWPlusDW) => //.
move => H1.
inversion H1. rewrite -H0 -H2 ; clear H1 H0 H2.

destruct (Req_dec (xhr + xlr) 0).
{ have xh0: xhr = 0.
move: xE; rewrite /double_word. 
by rewrite H /rounded round_0.
rewrite H Rplus_0_l.
move =>  Hy.
have yh0: yhr = 0.
move: yE; rewrite /double_word. 
by rewrite Hy /rounded round_0.
have xl0 : xlr = 0 by apply (double_word_0 xh).
have yl0 : ylr = 0 by apply (double_word_0 yh).
rewrite xh0 yh0  xl0 yl0. 
rewrite /TwoSum_err/TwoSum_sum //=.
repeat (try rewrite !Rplus_0_l;
        try rewrite !Rminus_0_r;
        try rewrite !round_0; 
        try nra). }
 
move => H1.
have : yhr + ylr = - (xhr + xlr) by nra.
move => H3.
have Hxy : (yhr = -xhr).
move: xE yE; rewrite /double_word. 
rewrite H3 /rounded round_NE_opp. 
move => HxE HyE. 
move: xE yE; rewrite /double_word. 
rewrite H3 /rounded round_NE_opp. 
rewrite /yhr/xhr HxE HyE //=.
have Hxyl : (ylr = -xlr) by nra.
have : TwoSum_sum p choice xhr yhr = 0 /\ 
        TwoSum_err p choice xhr yhr = 0.
apply null_case_pre => //; try nra.
apply generic_format_FLX_FT2R.
have : TwoSum_sum p choice xlr ylr = 0 /\ 
        TwoSum_err p choice xlr ylr = 0.
apply null_case_pre => //; try nra.
apply generic_format_FLX_FT2R.
move => [] HA HB [] HC HD. rewrite HA HB HC HD.
repeat (try rewrite !Rplus_0_l;
        try rewrite !Rminus_0_r;
        try rewrite !round_0; 
        try nra). 
Qed.

Theorem relative_errorDWPlusFP_correct' : 
  exists del, (zh + zl) = (xhr + xlr + yhr + ylr) * (1 + del) /\
    Rabs del <= (3 * u^2) / (1 - 4 * u).
Proof.
destruct (Req_dec (xhr + xlr + yhr + ylr) 0) as [Hx0|Hx0].
{ exists 0; rewrite Hx0; split; [field_simplify ; by apply DWPlusDW_0
  | rewrite Rabs_R0 /u //=].
apply Rdiv_le_0_compat_Raux; try nra.
move : Hp3.
rewrite fprec_eq.
move => Hp3'.
apply Rlt_Rminus.
refine (Rle_lt_trans _ 
  (4 * / IZR (Z.pow_pos 2 3)) _ _ _); try nra.
apply Generic_proof.Rdiv_le_mult_pos; try nra.
rewrite !Zpower_pos_powerRZ power_RZ_inv; try nra.
rewrite Rmult_assoc.
rewrite -powerRZ_add; try nra.
suff : powerRZ 2 (- Z.pos (fprecp t) + 3) <= 1; 
  try nra. rewrite -(@powerRZ_O 2).
apply Pff.Rle_powerRZ; try nra; lia. } 
exists (((zh + zl) - (xhr + xlr + yhr + ylr)) / (xhr + xlr + yhr + ylr)); split. 
{ now field_simplify. } 
apply relative_errorDWPlusDW_correct.
Qed.


End AccuracyDWPlusDW.


