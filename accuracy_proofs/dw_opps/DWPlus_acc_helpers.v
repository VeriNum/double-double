(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** This file contains helper lemmas for accuracy proofs 
for double-word  plus a (double-word, floating-point number *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common FLT_lemmas.
Require Import DWPlus DDModels DWord_defs.
Require Import Fast2Mult_acc TwoSum_acc Fast2Sum_acc.
Require Import DW_acc_lemmas.
From Flocq Require Import Pff2Flocq Core.

Require Import mathcomp.ssreflect.ssreflect.

(* for choice functions : choice = fun x0 : Z => negb (Z.even x0) *)
From Stdlib Require Import Logic.FunctionalExtensionality.


Section FiniteFactsDWPlusFP.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Variables (xh xl y : ftype t).

Hypothesis FIN : is_finite_p (DWPlusFP xh xl y). 

Ltac prove_finite := 
  move: FIN;
  rewrite /DWPlusFP/is_finite_p //=;
  move => [];
  subexpr_finite => //
  .

Fact FIN3 : is_finite (BPLUS xh y) = true.
Proof. prove_finite. Qed.

Fact FINxh : is_finite xh = true.
Proof. prove_finite. Qed.

Fact FIN1 : is_finite_p (TwoSumF xh y).
Proof.
Proof. prove_finite. Qed.

Let sl := snd (TwoSumF xh y).

Fact FIN2 : is_finite (BPLUS xl sl) = true.
Proof. prove_finite. Qed.

Fact FINxl : is_finite xl = true.
Proof. prove_finite. Qed.

End FiniteFactsDWPlusFP.

Section  CorrectDWPlusFP'.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Let ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 
Let emin :=  (@common.emin t).

Variables (xh xl y : ftype t).

Hypothesis  xE : double_word xh xl.
Hypothesis FIN : is_finite_p (DWPlusFP xh xl y). 
Hypothesis Hp3 : (3 <= fprec t)%Z.

Theorem DWPlusFP_eq :
  DWPlus.DWPlusFP (fprec t) choice (FT2R xh) (FT2R xl) (FT2R y) = F2Rp (DWPlusFP xh xl y).
Proof.
have FIN3: (is_finite_p (TwoSumF xh y)) by
apply: (FIN1 _ xl _) => //.
have FIN4 : is_finite (BPLUS xl (snd (TwoSumF xh y))) = true by
apply: FIN2 => //.
move : FIN. move => [].
rewrite /DWPlus.DWPlusFP/DWPlusFP/fst/snd.
replace  (TwoSumF xh y ) with
  (fst (TwoSumF xh y), snd (TwoSumF xh y )) => //.
replace
(Fast2Sum (fst (TwoSumF xh y)) (BPLUS xl (snd (TwoSumF xh y))))
with 
(fst (Fast2Sum (fst (TwoSumF xh y)) (BPLUS xl (snd (TwoSumF xh y)))),
snd (Fast2Sum (fst (TwoSumF xh y)) (BPLUS xl (snd (TwoSumF xh y))))) => //.
move => FIN1 FIN2. 
have Heq: (TwoSum (fprec t) choice (FT2R xh) (FT2R y)) =
  (TwoSum_sum (fprec t) choice (FT2R xh) (FT2R y) ,
    TwoSum_err (fprec t) choice (FT2R xh) (FT2R y) ) => //.
have Herr : TwoSum_err (fprec t) choice (FT2R xh) (FT2R y) = FT2R (snd (TwoSumF xh y)).
{ pose proof TwoSumEq_FLT xh y FIN3. rewrite Heq in H. 
inversion H. rewrite H2 /TwoSumF => //. } 
have Hsum : TwoSum_sum (fprec t) choice (FT2R xh) (FT2R y) = FT2R (fst (TwoSumF xh y)).
{ pose proof TwoSumEq_FLT xh y FIN3. rewrite Heq in H. 
inversion H. rewrite H1 /TwoSumF => //. } 

rewrite Herr Hsum.
destruct (Req_dec (FT2R xh + FT2R y) 0).
{ apply TwoSumF_eq in H => //.
inversion H.
rewrite Fast2Sum_2sum0' => //; 
rewrite /TwoSumF/fst/snd.
rewrite H2 H1 Rplus_0_r.
rewrite F2Sum.Fast2Sum0f round_generic => //. 
1,2,3: rewrite -!B2R_float_of_ftype.
all: try apply (generic_format_FLX_FLT radix2 emin);
try apply Binary.generic_format_B2R.
now rewrite H2 H1. } 

destruct (Rle_or_lt 
(bpow radix2 (emin + fprec t - 1))  
(Rabs
  (FT2R xl +
   FT2R (snd (TwoSumF xh y))))) as [HUF|HUF].

{ rewrite -FastTwoSumEq_FLT => //; f_equal.
BPLUS_correct t xl (snd (TwoSumF xh y)).
rewrite (round_FLT_FLX radix2 (@common.emin t)) => //.
by rewrite !B2R_float_of_ftype. }

rewrite -FastTwoSumEq_FLT => //; f_equal.
rewrite BPLUS_UF_exact => //.
rewrite round_generic => //; f_equal.
apply: (generic_format_FLX_FLT _ emin).
apply: Plus_error.FLT_format_plus_small.
1,2 : rewrite -!B2R_float_of_ftype;
  apply: Binary.generic_format_B2R.
 
refine (Rle_trans _ _ _ (Rlt_le _ _ _) _ ). apply HUF.
apply bpow_le; lia.
Qed.

Lemma DWPlusFP_double_word : 
double_word (fst (DWPlusFP xh xl y)) (snd (DWPlusFP xh xl y)).
Proof.
apply DWdouble_word_dw => [//=|].
have Hp : (1 < fprec t)%Z by lia.
have Hch: choice = (fun n : Z => negb (Z.even n)) by
apply functional_extensionality; rewrite /choice //=.
pose proof (DWPlusFP_correct Hp Hch Hp3).
specialize (H (FT2R xh) (FT2R xl) (FT2R y)).
pose proof DWPlusFP_eq.
move: H0.
destruct (DWPlus.DWPlusFP _ _ (FT2R xh) (FT2R xl) (FT2R y)).
destruct (DWPlusFP xh xl y).
simpl in *. rewrite /F2Rp. move => H1. inversion H1; subst.
apply H.
rewrite -B2R_float_of_ftype.
apply (@generic_format_FLX_FLT radix2 emin),
   Binary.generic_format_B2R.
apply dw_word_DWdouble => //.
Qed.

Lemma DWPlusFP_double_word' : 
rounded t (FT2R (fst (DWPlusFP xh xl y)) + FT2R (snd (DWPlusFP xh xl y)) ) = 
  FT2R (fst (DWPlusFP xh xl y)).
Proof.
symmetry. apply DWPlusFP_double_word.
Qed.

End CorrectDWPlusFP'.

Require Import Interval.Tactic.

Section DWPlusFPFinite.
Context {NANS: Nans} .
Variables (xh xl y : ftype Tdouble).

Hypothesis DWx : double_word xh xl.
Notation t:= Tdouble.

Lemma TwoSumF_sum_finite
(HFINxh: Binary.is_finite (fprec t) (femax t) (float_of_ftype xh) = true)
(HFINy : Binary.is_finite (fprec t) (femax t) (float_of_ftype y) = true)
(Hxh : Rabs (FT2R xh) <= /2 * (bpow radix2 (femax t)))
(Hy :  Rabs (FT2R y)  <= /4 * (bpow radix2 (femax t))) :
let sh := TwoSumF_sum xh y in
Binary.is_finite (fprec t) (femax t) (float_of_ftype sh) = true.
Proof.
rewrite /TwoSumF_sum/TwoSumF_err/TwoSumF/fst/snd => //.
have Hov1: 
        (Rabs
           (round radix2 (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
              (Binary.B2R (fprec t) (femax t) xh + Binary.B2R (fprec t) (femax t) y))) <
        (bpow radix2 (femax t)).
pose proof
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R xh)
  (FT2R y) ).
destruct H as (d1 & Hd & B).  
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.  
move: Hd . unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
match goal with |- Rabs ?a < _ =>
field_simplify a; interval with (i_prec 128)
end. 

 pose proof 
  (@Binary.Bplus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
  BinarySingleNaN.mode_NE xh y
  HFINxh HFINy) as Hp.
move: Hp.
rewrite Rlt_bool_true. move =>  [] A [] Hp _; auto.
auto. 
Qed.

Notation fexp:= ((SpecFloat.fexp (fprec t) (femax t))).

Lemma TwoSumF_err_finite_ubnd
(Hxh : Rabs (FT2R xh) <= /4 * (bpow radix2 (femax t))):
  FT2R xh <=  / 2 * bpow radix2 (femax t).
Proof.
apply Rabs_le_inv in Hxh; destruct Hxh as [_ Hxh].
have Hpos : (0 < bpow radix2 (femax t)) by apply bpow_gt_0.
nra.
Qed.

Lemma TwoSumF_err_finite_lbnd
(Hxh : Rabs (FT2R xh) <= /4 * (bpow radix2 (femax t))):
 - (/ 2 * bpow radix2 (femax t)) <= FT2R xh.
Proof.
apply Rabs_le_inv in Hxh; destruct Hxh as [Hxh _].
have Hpos : (0 < bpow radix2 (femax t)) by apply bpow_gt_0.
nra.
Qed.

Lemma TwoSumF_err_finite_bnd
(Hxh : Rabs (FT2R xh) <= /4 * (bpow radix2 (femax t))):
Rabs (FT2R xh) <=  (/ 2 * bpow radix2 (femax t)) .
Proof.
have Hpos : (0 < bpow radix2 (femax t)) by apply bpow_gt_0.
refine (Rle_trans _ _ _ Hxh _); nra.
Qed.

Lemma TwoSumF_err_finite'
(HFINxh: Binary.is_finite (fprec t) (femax t) (float_of_ftype xh) = true)
(HFINy : Binary.is_finite (fprec t) (femax t) (float_of_ftype y) = true)
(Hy : Rabs (FT2R y) <= /4 * (bpow radix2 (femax t)))
(Hxh : Rabs (FT2R xh) <= /4 * (bpow radix2 (femax t))):
let sl := TwoSumF_err xh y in
Binary.is_finite (fprec t) (femax t) (float_of_ftype sl) = true.
Proof.
rewrite /TwoSumF_sum/TwoSumF_err/TwoSumF/fst/snd => //.
have HA:
Rabs (FT2R xh) <= / 2 * IZR (Z.pow_pos 2 1024) by
  (apply TwoSumF_err_finite_bnd ;auto).
have HFIN : Binary.is_finite (fprec t) (femax t) (float_of_ftype (BPLUS xh y)) = true by
   apply TwoSumF_sum_finite => //. 

have Hxhb:  FT2R xh <=  / 2 * bpow radix2 (femax t).
apply TwoSumF_err_finite_ubnd => //.

pose proof
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R (BPLUS xh y))
  (-FT2R y) ).

have Hov1: 
        (Rabs
           (round radix2 (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
              (Binary.B2R (fprec t) (femax t) (xh + y)%F64 - Binary.B2R (fprec t) (femax t) y))) <
        (bpow radix2 (femax t)).
{ destruct H as (d1 & Hd & B).  
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.  
rewrite -is_finite_Binary in HFIN.
destruct (BPLUS_accurate' _ _ _ HFIN) as (d6 & Hd6 & B).
rewrite B. clear B. 
move: Hd  Hd6. unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxhb, Hy.
simpl in Hxhb.
match goal with |- Rabs ?a < _ =>
field_simplify a;
interval with (i_prec 128)
end. }

have FIN1 : is_finite (xh + y - y)%F64 = true.
pose proof 
  (@Binary.Bminus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
  BinarySingleNaN.mode_NE ( xh + y)%F64 y
  HFIN HFINy) as Hp.
move: Hp.
rewrite Rlt_bool_true. move =>  [] A [] Hp _; auto.
auto. clear H.
(* *)
pose proof
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R (BPLUS xh y))
  (-FT2R (xh + y - y)%F64) ).

have Hov2: 
        (Rabs
           (round radix2 (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
              (Binary.B2R (fprec t) (femax t) (xh + y)%F64 - Binary.B2R (fprec t) (femax t) 
                (xh + y - y)%F64))) <
        (bpow radix2 (femax t)).
{ destruct H as (d1 & Hd & B).  
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.
destruct (BMINUS_accurate' _ _ _ FIN1) as (d2 & Hd2 & B).
rewrite B. clear B. 
rewrite -is_finite_Binary in HFIN.
destruct (BPLUS_accurate' _ _ _ HFIN) as (d3 & Hd3 & B).
rewrite B. clear B. 
move: Hd  Hd2 Hd3. unfold  default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
match goal with |- Rabs ?a < _ =>
field_simplify a;
interval with (i_prec 128)
end. }

have FIN2 : is_finite (xh + y - (xh + y - y))%F64 = true.
rewrite is_finite_Binary in FIN1.
pose proof 
  (@Binary.Bminus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
  BinarySingleNaN.mode_NE ( xh + y)%F64 (xh + y - y)%F64
  HFIN FIN1 ) as Hp.
move: Hp.
rewrite Rlt_bool_true. move =>  [] A [] Hp _; auto.
auto.
clear H.
(* *)
pose proof
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R y)
  (-FT2R (xh + y - (xh + y - y))%F64) ).

have Hov3: 
        (Rabs
           (round radix2 (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
              (Binary.B2R (fprec t) (femax t) y - Binary.B2R (fprec t) (femax t) 
                (xh + y - (xh + y - y))%F64))) <
        (bpow radix2 (femax t)).
{ destruct H as (d1 & Hd & B).  
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.
destruct (BMINUS_accurate' _ _ _ FIN2) as (d2 & Hd2 & B).
rewrite B. clear B. 
destruct (BMINUS_accurate' _ _ _ FIN1) as (d4 & Hd4 & B).
rewrite B. clear B.
rewrite -is_finite_Binary in HFIN.
destruct (BPLUS_accurate' _ _ _ HFIN) as (d3 & Hd3 & B).
rewrite B. clear B.
move: Hd  Hd2 Hd3 Hd4. unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
match goal with |- Rabs ?a < _ =>
field_simplify a;
interval with (i_prec 128)
end. } 

have FINR : is_finite (y - (xh + y - (xh + y - y)))%F64 = true.
rewrite is_finite_Binary in FIN2.
pose proof 
  (@Binary.Bminus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
  BinarySingleNaN.mode_NE y (xh + y - (xh + y - y))%F64
  HFINy FIN2 ) as Hp.
move: Hp.
rewrite Rlt_bool_true. move =>  [] A [] Hp _; auto.
auto.
clear H.
(* *)
pose proof
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R xh)
  (-FT2R (xh + y - y)%F64) ).

have Hov4: 
        (Rabs
           (round radix2 (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
              (Binary.B2R (fprec t) (femax t) xh - Binary.B2R (fprec t) (femax t) 
                (xh + y - y)%F64))) <
        (bpow radix2 (femax t)).
{ destruct H as (d1 & Hd & B).  
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.
destruct (BMINUS_accurate' _ _ _ FIN1) as (d2 & Hd2 & B).
rewrite B. clear B. 
rewrite -is_finite_Binary in HFIN.
destruct (BPLUS_accurate' _ _ _ HFIN) as (d3 & Hd3 & B).
rewrite B. clear B. 
move: Hd Hd2 Hd3. unfold  default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
match goal with |- Rabs ?a < _ =>
field_simplify a;
interval with (i_prec 128)
end. } 

have FINL : is_finite (xh - (xh + y - y))%F64 = true.
rewrite is_finite_Binary in FIN1.
pose proof 
  (@Binary.Bminus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
  BinarySingleNaN.mode_NE xh (xh + y - y)%F64
  HFINxh FIN1 ) as Hp.
move: Hp.
rewrite Rlt_bool_true. move =>  [] A [] Hp _; auto.
auto.
clear H.
(* *)
pose proof (Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R (xh - (xh + y - y))%F64)
  (FT2R (y - (xh + y - (xh + y - y)))%F64) ).

have HOV1: 
Rabs (round radix2 (SpecFloat.fexp (fprec t) (femax t)) 
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
(FT2R (xh - (xh + y - y))%F64 + FT2R (y - (xh + y - (xh + y - y)))%F64)) < bpow radix2 (femax t).

destruct H as (d1 & Hd & B).
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.  

pose proof (@BMINUS_accurate' _ _ _ y (xh + y - (xh + y - y))%F64).
destruct H as (d2 & Hd2 & B). auto.
rewrite B. clear B.

pose proof (@BMINUS_accurate' _ _ _ (xh + y)%F64 (xh + y - y)%F64).
destruct H as (d3 & Hd3 & B). auto.
rewrite B. clear B.

pose proof (@BMINUS_accurate' _ _ _ xh (xh + y - y)%F64).
destruct H as (d4 & Hd4 & B). auto.
rewrite B. clear B.

pose proof (@BMINUS_accurate' _ _ _ (xh + y)%F64 y).
destruct H as (d5 & Hd5 & B). auto.
rewrite B. clear B.

rewrite -is_finite_Binary in HFIN.
destruct (BPLUS_accurate' _ _ _ HFIN) as (d6 & Hd6 & B).
rewrite B. clear B. 

move: Hd Hd2 Hd3 Hd4 Hd5 Hd6. unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
match goal with |- Rabs ?a < _ =>
field_simplify a;
interval with (i_prec 128)
end.


pose proof 
  (@Binary.Bplus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
  BinarySingleNaN.mode_NE ( (xh - (xh + y - y))%F64) 
  (y - (xh + y - (xh + y - y)))%F64
  FINL FINR) as Hp.
move: Hp.
rewrite Rlt_bool_true. move =>  [] A [] Hp _; auto.
auto.
Qed.


Lemma TwoSumF_err_finite
(HFINxh: Binary.is_finite (fprec t) (femax t) (float_of_ftype xh) = true)
(HFINy : Binary.is_finite (fprec t) (femax t) (float_of_ftype y) = true)
(Hxh : Rabs (FT2R xh) <= / 4 * bpow radix2 (femax t))
(Hy :  Rabs (FT2R y)  <= /4 * (bpow radix2 (femax t)))  :
let sl := TwoSumF_err xh y in
Binary.is_finite (fprec t) (femax t) (float_of_ftype sl) = true.
Proof.
rewrite /TwoSumF_sum/TwoSumF_err/TwoSumF/fst/snd => //.
have HA:
Rabs (FT2R xh) <= / 2 * IZR (Z.pow_pos 2 1024) by
  (apply TwoSumF_err_finite_bnd ; try auto).
have HFIN : Binary.is_finite (fprec t) (femax t) (float_of_ftype (BPLUS xh y)) = true.
apply TwoSumF_sum_finite => //.
(* *)
pose proof
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R (BPLUS xh y))
  (-FT2R y) ).

have Hov1: 
        (Rabs
           (round radix2 (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
              (Binary.B2R (fprec t) (femax t) (xh + y)%F64 - Binary.B2R (fprec t) (femax t) y))) <
        (bpow radix2 (femax t)).
{ destruct H as (d1 & Hd & B).  
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.  
rewrite -is_finite_Binary in HFIN.
destruct (BPLUS_accurate' _ _ _ HFIN) as (d6 & Hd6 & B).
rewrite B. clear B. 
move: Hd  Hd6. unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
match goal with |- Rabs ?a < _ =>
field_simplify a;
interval with (i_prec 128)
end. } 
have FIN1 : is_finite (xh + y - y)%F64 = true.
pose proof 
  (@Binary.Bminus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t)) 
  BinarySingleNaN.mode_NE ( xh + y)%F64 y
  HFIN HFINy) as Hp.
move: Hp.
rewrite Rlt_bool_true. move =>  [] A [] Hp _; auto.
auto. clear H.
(* *)
pose proof
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R (BPLUS xh y))
  (-FT2R (xh + y - y)%F64) ).

have Hov2: 
        (Rabs
           (round radix2 (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
              (Binary.B2R (fprec t) (femax t) (xh + y)%F64 - Binary.B2R (fprec t) (femax t) 
                (xh + y - y)%F64))) <
        (bpow radix2 (femax t)).
{ destruct H as (d1 & Hd & B).  
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.
destruct (BMINUS_accurate' _ _ _ FIN1) as (d2 & Hd2 & B).
rewrite B. clear B. 
rewrite -is_finite_Binary in HFIN.
destruct (BPLUS_accurate' _ _ _ HFIN) as (d3 & Hd3 & B).
rewrite B. clear B. 
move: Hd  Hd2 Hd3. unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
match goal with |- Rabs ?a < _ =>
field_simplify a;
interval with (i_prec 128)
end. } 

have FIN2 : is_finite (xh + y - (xh + y - y))%F64 = true.
rewrite is_finite_Binary in FIN1.
pose proof 
  (@Binary.Bminus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t)) 
  BinarySingleNaN.mode_NE ( xh + y)%F64 (xh + y - y)%F64
  HFIN FIN1 ) as Hp.
move: Hp.
rewrite Rlt_bool_true. move =>  [] A [] Hp _; auto.
auto.
clear H.
(* *)
pose proof
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R y)
  (-FT2R (xh + y - (xh + y - y))%F64) ).

have Hov3: 
        (Rabs
           (round radix2 (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
              (Binary.B2R (fprec t) (femax t) y - Binary.B2R (fprec t) (femax t) 
                (xh + y - (xh + y - y))%F64))) <
        (bpow radix2 (femax t)).
{ destruct H as (d1 & Hd & B).  
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.
destruct (BMINUS_accurate' _ _ _ FIN2) as (d2 & Hd2 & B).
rewrite B. clear B. 
destruct (BMINUS_accurate' _ _ _ FIN1) as (d4 & Hd4 & B).
rewrite B. clear B.
rewrite -is_finite_Binary in HFIN.
destruct (BPLUS_accurate' _ _ _ HFIN) as (d3 & Hd3 & B).
rewrite B. clear B.
move: Hd  Hd2 Hd3 Hd4. unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
match goal with |- Rabs ?a < _ =>
field_simplify a;
interval with (i_prec 128) 
end. } 

have FINR : is_finite (y - (xh + y - (xh + y - y)))%F64 = true.
rewrite is_finite_Binary in FIN2.
pose proof 
  (@Binary.Bminus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t)) 
  BinarySingleNaN.mode_NE y (xh + y - (xh + y - y))%F64
  HFINy FIN2 ) as Hp.
move: Hp.
rewrite Rlt_bool_true. move =>  [] A [] Hp _; auto.
auto.
clear H.
(* *)
pose proof
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R xh)
  (-FT2R (xh + y - y)%F64) ).

have Hov4: 
        (Rabs
           (round radix2 (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
              (Binary.B2R (fprec t) (femax t) xh - Binary.B2R (fprec t) (femax t) 
                (xh + y - y)%F64))) <
        (bpow radix2 (femax t)).
{ destruct H as (d1 & Hd & B).  
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.
destruct (BMINUS_accurate' _ _ _ FIN1) as (d2 & Hd2 & B).
rewrite B. clear B. 
rewrite -is_finite_Binary in HFIN.
destruct (BPLUS_accurate' _ _ _ HFIN) as (d3 & Hd3 & B).
rewrite B. clear B. 
move: Hd Hd2 Hd3. unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
match goal with |- Rabs ?a < _ =>
field_simplify a;
interval with (i_prec 128)
end. } 

have FINL : is_finite (xh - (xh + y - y))%F64 = true.
rewrite is_finite_Binary in FIN1.
pose proof 
  (@Binary.Bminus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
  BinarySingleNaN.mode_NE xh (xh + y - y)%F64
  HFINxh FIN1 ) as Hp.
move: Hp.
rewrite Rlt_bool_true. move =>  [] A [] Hp _; auto.
auto.
clear H.
(* *)


pose proof (Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R (xh - (xh + y - y))%F64)
  (FT2R (y - (xh + y - (xh + y - y)))%F64) ).


have HOV1: 
Rabs (round radix2 (SpecFloat.fexp (fprec t) (femax t)) 
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
(FT2R (xh - (xh + y - y))%F64 + FT2R (y - (xh + y - (xh + y - y)))%F64)) < bpow radix2 (femax t).

destruct H as (d1 & Hd & B).
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.  

pose proof (@BMINUS_accurate' _ _ _ y (xh + y - (xh + y - y))%F64).
destruct H as (d2 & Hd2 & B). auto.
rewrite B. clear B.

pose proof (@BMINUS_accurate' _ _ _ (xh + y)%F64 (xh + y - y)%F64).
destruct H as (d3 & Hd3 & B). auto.
rewrite B. clear B.

pose proof (@BMINUS_accurate' _ _ _ xh (xh + y - y)%F64).
destruct H as (d4 & Hd4 & B). auto.
rewrite B. clear B.

pose proof (@BMINUS_accurate' _ _ _ (xh + y)%F64 y).
destruct H as (d5 & Hd5 & B). auto.
rewrite B. clear B.

rewrite -is_finite_Binary in HFIN.
destruct (BPLUS_accurate' _ _ _ HFIN) as (d6 & Hd6 & B).
rewrite B. clear B. 

move: Hd Hd2 Hd3 Hd4 Hd5 Hd6. unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
match goal with |- Rabs ?a < _ =>
field_simplify a;
interval with (i_prec 128)
end.

pose proof 
  (@Binary.Bplus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
  BinarySingleNaN.mode_NE ( (xh - (xh + y - y))%F64) 
  (y - (xh + y - (xh + y - y)))%F64
  FINL FINR) as Hp.
move: Hp.
rewrite Rlt_bool_true. move =>  [] A [] Hp _; auto.
auto.
Qed.

Theorem is_finite_p_TwoSum
(HFINxh: Binary.is_finite (fprec t) (femax t) (float_of_ftype xh) = true)
(HFINy : Binary.is_finite (fprec t) (femax t) (float_of_ftype y) = true)
(Hxh : Rabs (FT2R xh) <= /4 * (bpow radix2 (femax t)))
(Hy :  Rabs (FT2R y)  <= /4 * (bpow radix2 (femax t)))  :
is_finite_p (TwoSumF xh y).
Proof.
rewrite /is_finite_p; split.
apply TwoSumF_sum_finite => //.
apply TwoSumF_err_finite_bnd => //.
apply TwoSumF_err_finite => //.
Qed.

Let sh := TwoSumF_sum xh y.
Let sl := TwoSumF_err xh y.

Lemma xl_bnd 
(Hxh : Rabs (FT2R xh) <= /2 * (bpow radix2 (femax t))) :
Rabs (FT2R xl) <= / 2 * IZR (Z.pow_pos 2 971). 
Proof.
apply dw_ulp in DWx.
refine (Rle_trans _ _ _  DWx _).
set g:=
/ 2 * ulp radix2 (SpecFloat.fexp (fprec t) (femax t)) 
    ( bpow radix2 (femax t - 1)).
refine (Rle_trans _ g _  _ _).
rewrite /g.
apply Rmult_le_compat_l; try nra.
apply ulp_le. 
apply BinarySingleNaN.fexp_correct.
apply (fprec_gt_0 t).
apply FLT_exp_monotone.
refine (Rle_trans _ _  _  Hxh _).
rewrite Rabs_pos_eq; [simpl; try nra | apply bpow_ge_0].
subst g. rewrite ulp_bpow. simpl; nra.
Qed.

Theorem DWPlusFP_zh_finite
(HFINxh: Binary.is_finite (fprec t) (femax t) (float_of_ftype xh) = true)
(HFINxl: Binary.is_finite (fprec t) (femax t) (float_of_ftype xl) = true)
(HFINy : Binary.is_finite (fprec t) (femax t) (float_of_ftype y) = true)
(Hxhl : Rabs (FT2R xh) <= /4 * (bpow radix2 (femax t)))
(Hy :  Rabs (FT2R y)  <= /4 * (bpow radix2 (femax t))):
let zh := Fast2Sum_sum sh (BPLUS xl sl) in
 Binary.is_finite (fprec t) (femax t) (float_of_ftype zh) = true.
Proof.
rewrite /Fast2Sum_err/fst/snd => //.
rewrite /Fast2Sum_sum/fst/Fast2Sum.

have Hxh:
Rabs (FT2R xh) <= / 2 * IZR (Z.pow_pos 2 1024). by
  (apply TwoSumF_err_finite_bnd ; try auto).

have HFIN : Binary.is_finite (fprec t) (femax t) (float_of_ftype (BPLUS xh y)) = true.
apply TwoSumF_sum_finite => //.

have Hxl :Rabs (FT2R xl) <= / 2 * IZR (Z.pow_pos 2 971) by
  apply xl_bnd => //.

have HFINsl :
Binary.is_finite (fprec t) (femax t) (float_of_ftype sl) = true by
apply TwoSumF_err_finite => //.

destruct (TwoSumF_error xh y 
  (is_finite_p_TwoSum HFINxh HFINy Hxhl Hy))  as (d1 & B1 & Hd1).
fold sl in B1. 

have HFINxsl : 
Binary.is_finite (fprec t) (femax t) (xl + sl)%F64 = true.
pose proof 
  (@Binary.Bplus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
  BinarySingleNaN.mode_NE xl sl HFINxl HFINsl
   ) as Hp.
 move: Hp.
rewrite Rlt_bool_true. move =>  A.
destruct A, H0 => //.

destruct
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R xl)
  (FT2R sl )) as 
(d & Hd & B).
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite -B2R_float_of_ftype in B. rewrite B. clear B.

rewrite B1 B2R_float_of_ftype .

move: Hd Hd1. rewrite /Relative.u_ro; simpl. move => Hd Hd1.
match goal with |- context [Rabs ?a ] =>
 field_simplify a;
 interval with (i_prec 128)
end.

pose proof 
  (@Binary.Bplus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t)) 
  BinarySingleNaN.mode_NE sh (xl + sl)%F64
   ) as Hp.
 move: Hp.
rewrite Rlt_bool_true. move =>  A.
destruct A => //. destruct H0 => //.

destruct
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R sh)
  (FT2R (xl + sl)%F64 )) as 
(d & Hd & B).
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite -B2R_float_of_ftype in B. rewrite B. clear B.

rewrite -is_finite_Binary in HFINxsl.
destruct (BPLUS_accurate' _ _ _ HFINxsl) as (d6 & Hd6 & B).
rewrite B. clear B. 

rewrite B1 B2R_float_of_ftype .

subst sh; rewrite /TwoSumF_sum/fst/TwoSumF.
rewrite -is_finite_Binary in HFIN.
destruct (BPLUS_accurate' _ _ _ HFIN) as (d5 & Hd5 & B).
rewrite B. clear B. 

interval with (i_prec 128). 
Qed.

Theorem DWPlusFP_zl_finite
(HFINxh: Binary.is_finite (fprec t) (femax t) (float_of_ftype xh) = true)
(HFINxl: Binary.is_finite (fprec t) (femax t) (float_of_ftype xl) = true)
(HFINy : Binary.is_finite (fprec t) (femax t) (float_of_ftype y) = true)
(Hxhl : Rabs (FT2R xh) <= /4 * (bpow radix2 (femax t)))
(Hy :  Rabs (FT2R y)  <= /4 * (bpow radix2 (femax t))) :
let zl := Fast2Sum_err sh (BPLUS xl sl) in
Binary.is_finite (fprec t) (femax t) (float_of_ftype zl) = true.
Proof.
have Hxh:
Rabs (FT2R xh) <= / 2 * IZR (Z.pow_pos 2 1024). by
  (apply TwoSumF_err_finite_bnd ; try auto).

set zh := Fast2Sum_sum sh (BPLUS xl sl).
have : Binary.is_finite (fprec t) (femax t) (float_of_ftype zh) = true . 
apply DWPlusFP_zh_finite => //.
rewrite /Fast2Sum_err/fst/snd => //.
rewrite /Fast2Sum_sum/fst/Fast2Sum.
move => FINzh.

have Hu :Rabs (FT2R xl) <= / 2 * IZR (Z.pow_pos 2 971)
 by apply xl_bnd => //.

have HFINxsl :
is_finite (xl + sl)%F64 = true.
rewrite -is_finite_Binary in FINzh.
apply BPLUS_finite_e in FINzh. 
destruct FINzh => //.

destruct (TwoSumF_error xh y 
  (is_finite_p_TwoSum HFINxh HFINy Hxhl Hy)) 
  as (d2s & Heq & Hd). fold sl in Heq.

have HFINsh: 
Binary.is_finite (fprec t) (femax t) sh = true.
apply TwoSumF_sum_finite => //.

have FINR : 
Binary.is_finite (fprec t) (femax t) (sh + (xl + sl) - sh)%F64 = true.
{ 
pose proof 
  (@Binary.Bminus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t)) 
  BinarySingleNaN.mode_NE (sh + (xl + sl))%F64 
  sh) as Hp.
move: Hp.
rewrite Rlt_bool_true.  move => Hp; auto.
destruct Hp => //. destruct H0. auto.

pose proof (Plus_error.FLT_plus_error_N_ex   
      Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R (sh + (xl + sl))%F64)
  (-FT2R sh) ).
destruct H as (d1 & Hd2 & B). 
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite -!B2R_float_of_ftype in B.
rewrite B. clear B.

rewrite -is_finite_Binary in FINzh.
destruct (BPLUS_accurate' _ _ _ FINzh) as (d6 & Hd6 & B).
rewrite B2R_float_of_ftype.
rewrite B. clear B. 

destruct (BPLUS_accurate' _ _ _ HFINxsl) as (d5 & Hd5 & B).
rewrite B. clear B. rewrite !B2R_float_of_ftype.

subst sh. move: HFINsh. rewrite /TwoSumF_sum/fst/TwoSumF.
  move => HFINsh.
rewrite -is_finite_Binary in HFINsh.
destruct (BPLUS_accurate' _ _ _ HFINsh) as (d4 & Hd4 & B).
rewrite B. clear B. 

rewrite Heq.

move: Hd5 Hd6 Hd2 Hd. unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
match goal with |- Rabs ?a < _ =>
field_simplify a;
interval with (i_prec 128)
end. }  

pose proof 
  (@Binary.Bminus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t)) 
  BinarySingleNaN.mode_NE (xl + sl)%F64) 
  (sh + (xl + sl) - sh)%F64 as Hp.
move: Hp.
rewrite Rlt_bool_true.  move => Hp; auto.
destruct Hp => //. 

destruct H0. auto.

pose proof (Plus_error.FLT_plus_error_N_ex   
      Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R (xl + sl)%F64)
  (-FT2R (sh + (xl + sl) - sh)%F64) ).
destruct H as (d1 & Hd1 & B). 
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite -!FT2R_ftype_of_float.
rewrite B. clear B.

rewrite -is_finite_Binary in FINR.
pose proof (@BMINUS_accurate' _ _ _ 
          (sh + (xl + sl))%F64 sh FINR).
destruct H as (d3 & Hd3 & B). 
rewrite B. clear B.

rewrite -is_finite_Binary in FINzh.
pose proof (@BPLUS_accurate' _ _ _ 
          sh (xl + sl)%F64 FINzh).
destruct H as (d4 & Hd4 & B). 
rewrite B. clear B.

pose proof (@BPLUS_accurate' _ _ _ xl sl HFINxsl).
destruct H as (d2 & Hd2 & B). 
rewrite B. clear B.

rewrite Heq.

subst sh. move: HFINsh. rewrite /TwoSumF_sum/fst/TwoSumF.
  move => HFINsh.
rewrite -is_finite_Binary in HFINsh.
destruct (BPLUS_accurate' _ _ _ HFINsh) as (d5 & Hd5 & B).
rewrite B. clear B. 

move: Hd5 Hd4 Hd2 Hd3 Hd1. unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.

match goal with |-context[Rabs ?a] =>
field_simplify a;
interval with (i_prec 128)
end.
Qed.

Let zh := Fast2Sum_sum sh (BPLUS xl sl) .
Let zl := Fast2Sum_err sh (BPLUS xl sl) .

Theorem DWPlusFP_finite
(HFINxh: Binary.is_finite (fprec t) (femax t) (float_of_ftype xh) = true)
(HFINxl: Binary.is_finite (fprec t) (femax t) (float_of_ftype xl) = true)
(HFINy : Binary.is_finite (fprec t) (femax t) (float_of_ftype y) = true)
(Hxhl : Rabs (FT2R xh) <= /4 * (bpow radix2 (femax t)))
(Hy :  Rabs (FT2R y)  <= /4 * (bpow radix2 (femax t))):
is_finite_p (DWPlusFP xh xl y).
Proof.
rewrite /is_finite_p/DWPlusFP.
replace (TwoSumF _ _) with (sh,sl) => //.
replace (Fast2Sum _ _) with (zh,zl) => //.
rewrite /fst/snd => //.
rewrite /Fast2Sum_sum/fst/Fast2Sum. split.
apply DWPlusFP_zh_finite => //.
apply DWPlusFP_zl_finite => //.
Qed.

(* Backward-compatible variant taking the sum-form precondition.
   Used by external callers (e.g. DWPlusFP_vcfloat) that haven't yet
   migrated to the high-part bound; internally bridges via
   dw_high_bnd_of_sum. *)
Corollary DWPlusFP_finite_from_sum
(HFINxh: Binary.is_finite (fprec t) (femax t) (float_of_ftype xh) = true)
(HFINxl: Binary.is_finite (fprec t) (femax t) (float_of_ftype xl) = true)
(HFINy : Binary.is_finite (fprec t) (femax t) (float_of_ftype y) = true)
(Hxhl : Rabs (FT2R xh + FT2R xl) < /4 * (bpow radix2 (femax t)))
(Hy :   Rabs (FT2R y) < /4 * (bpow radix2 (femax t))) :
is_finite_p (DWPlusFP xh xl y).
Proof.
have Hdw : double_word_prop xh xl
  by rewrite /double_word_prop; exact DWx.
apply DWPlusFP_finite => //.
- by apply (dw_high_bnd_of_sum xh xl Hdw Hxhl).
- by apply Rlt_le.
Qed.

End DWPlusFPFinite.