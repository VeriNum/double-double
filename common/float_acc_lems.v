(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* This file contains lemmas regarding the accuracy of floating point 
  operations such as BPLUS, BFMA, and BMULT. *)

Require Import vcfloat.VCFloat.
Require Import common op_defs.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Flocq.Core.Generic_fmt Flocq.Core.FLX.
From Flocq Require Import Pff2Flocq Core.

Set Bullet Behavior "Strict Subproofs".

Section TVar. 

Notation is_finite := vcfloat.FPCore.is_finite.

Variable t : type.

Section General. 

Lemma neg_zero_is_finite :
  Binary.is_finite (fprec t) (femax t) neg_zero = true.
Proof. simpl; auto. Qed.

Lemma generic_round_property:
  forall  (x: R),
exists delta epsilon : R,
   delta * epsilon = 0 /\
  (Rabs delta <= default_rel t)%R /\
  (Rabs epsilon <= default_abs t)%R /\
   Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
               x = (x * (1+delta)+epsilon)%R.
Proof.
intros.
destruct (Relative.error_N_FLT Zaux.radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t) 
             (fprec_gt_0 t) (fun x0 : Z => negb (Z.even x0)) x)
  as [delta [epsilon [? [? [? ?]]]]].
exists delta, epsilon.
split; [ | split]; auto.
Qed.

Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Notation radix2 := Zaux.radix2.

Fact rnd_plus_FLT_FLX_eq {STD: is_standard t} (a b : R) :
  generic_format radix2 fexp a -> generic_format radix2 fexp b ->
  round radix2 (FLX_exp (fprec t)) (Generic_fmt.Znearest choice) (a + b) = 
  round radix2 (SpecFloat.fexp (fprec t) (femax t)) (Generic_fmt.Znearest choice) (a +  b).
Proof.
  move => Hga Hgb.
  case : (Rlt_dec (Rabs (a  +  b)) (bpow radix2 (@emin t + fprec t - 1))) => Huf1.
  - 
  have Hg : Generic_fmt.generic_format radix2 fexp (a + b).
  apply Plus_error.FLT_format_plus_small => //; try apply generic_format_FLT_FT2R.
  eapply Rle_trans. apply Rlt_le.
  apply Huf1. rewrite /emin.
  apply bpow_le; lia.
  rewrite !Generic_fmt.round_generic => //; try nra.
  by apply (@FLT.generic_format_FLX_FLT radix2 (@emin t)).
  - 
  apply Rnot_lt_le in Huf1.
  by rewrite FLT.round_FLT_FLX.
Qed.

Fact rnd_plus_FLT_FLX_eq' {STD: is_standard t} (a b : ftype t) :
  round radix2 (FLX_exp (fprec t)) (Generic_fmt.Znearest choice) (FT2R a + FT2R b) = 
  round radix2 (SpecFloat.fexp (fprec t) (femax t)) (Generic_fmt.Znearest choice) (FT2R a + FT2R b).
Proof.
  apply rnd_plus_FLT_FLX_eq; apply generic_format_FLT_FT2R.
Qed.

Notation Omega  := (bpow radix2 (femax t)). 

Lemma is_finite_no_overflow {STD: is_standard t} (a : ftype t) :
  is_finite a = true -> Rabs (FT2R a) < Omega.
Proof.
  rewrite -!B2R_float_of_ftype; intros; apply Binary.abs_B2R_lt_emax.
Qed.

End General. 

Section FMA. 
  
(* Define a commonly used hypothesis *)  
Definition fma_no_overflow  (x y z: R) : Prop :=
  (Rabs (rounded t  (x * y + z)) < Raux.bpow Zaux.radix2 (femax t))%R.

(** Standard epsilon delta error bounds for FMA from no overflow hyp *)
Lemma fma_accurate {NAN : Nans } {STD: is_standard t} : 
   forall x (FINx: is_finite x = true) 
          y (FINy: is_finite y = true) 
          z (FINz: is_finite z = true)
          (FIN: fma_no_overflow (FT2R x) 
              (FT2R y) (FT2R z)), 
  exists delta, exists epsilon,
   delta * epsilon = 0 /\
   Rabs delta <= default_rel t  /\
   Rabs epsilon <= default_abs t /\ 
   (FT2R (BFMA x y z) = (FT2R x * FT2R y + FT2R z) * (1+delta) + epsilon)%R.
Proof.
intros.
rewrite !is_finite_Binary in FINx FINz FINy.
set (xb := float_of_ftype x).
set (yb := float_of_ftype y).
set (zb := float_of_ftype z).
pose proof (Binary.Bfma_correct (fprec t) (femax t) 
        (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan (fprec t) (femax t) (fprec_gt_one t))
                      BinarySingleNaN.mode_NE xb yb zb FINx FINy FINz).
cbv zeta in H.
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) 
              (Binary.B2R _ _ xb * Binary.B2R _ _ yb + Binary.B2R _ _ zb)))
        (Raux.bpow Zaux.radix2 (femax t))).
destruct H0.
-
destruct H as [? _].
rewrite <- B2R_float_of_ftype; unfold BFMA; 
  fold xb yb zb.
rewrite !float_of_ftype_of_float H.
unfold xb, yb, zb.
rewrite !B2R_float_of_ftype.
apply generic_round_property.
-
red in FIN. unfold rounded in FIN.
unfold xb, yb, zb in H0.
rewrite !B2R_float_of_ftype in H0.
lra.
Qed.

(** Relate local is_finite def and Binary.is_finite *)
Lemma is_finite_fma_no_overflow_aux {NAN: Nans} {STD: is_standard t} : 
  forall x y z
  (HFINb : is_finite (BFMA x y z) = true),
  Binary.is_finite _ _  (Binary.Bfma (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE
      (float_of_ftype x) (float_of_ftype y) (float_of_ftype z)) = true. 
Proof.
intros. 
rewrite is_finite_Binary in HFINb.
unfold BFMA in HFINb.
set (F:=
  (Binary.Bfma (fprec t) (femax t) (fprec_gt_0 t) 
  (fprec_lt_femax t) ((fma_nan (fprec t) (femax t) (fprec_gt_one t))) BinarySingleNaN.mode_NE
     (float_of_ftype x) (float_of_ftype y) (float_of_ftype z))) in *.
destruct F; simpl; auto;
rewrite float_of_ftype_of_float in HFINb;
simpl in HFINb; auto.
Qed.

(** Finite def implies no overflow *)
Lemma is_finite_fma_no_overflow {NAN: Nans} {STD: is_standard t} : 
  forall x y z
  (HFINb : is_finite (BFMA x y z) = true),
  fma_no_overflow (FT2R x) (FT2R y) (FT2R z).
Proof.
intros.
red. set (ov:= bpow Zaux.radix2 (femax t)).
pose proof Rle_or_lt ov (Rabs (rounded t (FT2R x * FT2R y + FT2R z)))  as Hor;
  destruct Hor; auto.
apply Rlt_bool_false in H.
pose proof is_finite_fma_no_overflow_aux x y z HFINb.
assert (HFIN: is_finite x = true /\
  is_finite y = true /\ 
  is_finite z = true).
{ rewrite !is_finite_Binary. 
destruct (float_of_ftype x);
destruct (float_of_ftype y);
destruct (float_of_ftype z);
simpl in *; try discriminate; repeat split; auto.
all: destruct s; destruct s0; destruct s1; simpl in *; try discriminate; auto. }
destruct HFIN as (A & B & C). 
unfold rounded, ov in H. 
set (xb := float_of_ftype x).
set (yb := float_of_ftype y).
set (zb := float_of_ftype z).
rewrite !is_finite_Binary in A B C.
pose proof (Binary.Bfma_correct (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan (fprec t) (femax t) (fprec_gt_one t)) 
        BinarySingleNaN.mode_NE xb yb zb A B C) as H1.
simpl in H1, H.
rewrite <- !B2R_float_of_ftype in H.
fold xb yb zb in H, H0.
rewrite H in H1; clear H.
destruct 
(Binary.Bfma _ _ _ _ _ _ xb yb zb);
 try discriminate.
Qed.

(** No overflow and finite operands imply that the FMA result is finite. *)
Lemma no_overflow_fma_is_finite {NAN: Nans} {STD: is_standard t} :
  forall (a b c : ftype t),
  is_finite a = true -> is_finite b = true -> is_finite c = true ->
  Rabs (rounded t (FT2R a * FT2R b + FT2R c)) <
    bpow Zaux.radix2 (femax t) ->
  is_finite (BFMA a b c) = true.
Proof.
  intros a b c Ha Hb Hc Hov.
  rewrite !is_finite_Binary in Ha, Hb, Hc.
  rewrite is_finite_Binary /BFMA float_of_ftype_of_float.
  pose proof (Binary.Bfma_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t)
    (fma_nan (fprec t) (femax t) (fprec_gt_one t))
    BinarySingleNaN.mode_NE (float_of_ftype a) (float_of_ftype b)
    (float_of_ftype c) Ha Hb Hc) as H.
  cbv zeta in H.
  rewrite !B2R_float_of_ftype in H.
  unfold rounded in Hov.
  apply Rlt_bool_true in Hov.
  rewrite Hov in H.
  destruct H as (_ & HF & _).
  exact HF.
Qed.

(** Finite FMA implies operands are finite *)
Lemma BFMA_finite_e {NAN: Nans} {STD: is_standard t} :
 forall (a b c: ftype t)
 (Hfin : is_finite (BFMA a b c) = true),
 is_finite a = true  /\ 
 is_finite b = true /\ 
 is_finite c = true.
Proof.
unfold BFMA; intros.
rewrite is_finite_Binary float_of_ftype_of_float in Hfin.
rewrite !is_finite_Binary.
destruct (float_of_ftype a), (float_of_ftype b), 
  (float_of_ftype c);
  inversion Hfin; clear Hfin; subst; auto;
destruct s,s0, s1; discriminate; auto.
Qed.

(** Standard epsilon delta error bounds for FMA from finite hyp *)
Lemma fma_accurate' {NAN: Nans} {STD: is_standard t} : 
   forall  (x y z : ftype t)
          (FIN:  is_finite  (BFMA x y z) = true), 
  exists delta, exists epsilon,
   delta * epsilon = 0 /\
   Rabs delta <= default_rel t /\
   Rabs epsilon <= default_abs t /\ 
   (FT2R (BFMA x y z) = (FT2R x * FT2R y + FT2R z) * (1+delta) + epsilon)%R.
Proof.
intros.
apply fma_accurate; auto;
pose proof is_finite_fma_no_overflow_aux x y z FIN;
   try eapply (BFMA_finite_e _ _ _ FIN).
apply is_finite_fma_no_overflow; auto.
Qed.

(** Relate BFMA to round NE in FLT format *)
Lemma BFMA_round_correct {NAN: Nans} {STD: is_standard t} :  
  forall a b c (Hfin : is_finite (BFMA a b c) = true),
  let fexp := (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t)) in
  round Zaux.radix2 fexp (Znearest choice) (FT2R a * FT2R b + FT2R c) = FT2R (BFMA a b c).
Proof.
intros.
pose proof (is_finite_fma_no_overflow a b c Hfin) as Hfin1.
destruct (BFMA_finite_e a b c Hfin) as (HA & HB & HC).
rewrite !is_finite_Binary in HA, HB, HC.
pose proof (Binary.Bfma_correct  (fprec t) (femax t) 
        (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan (fprec t) (femax t) 
        (fprec_gt_one t)) BinarySingleNaN.mode_NE (float_of_ftype a) 
        (float_of_ftype b) (float_of_ftype c) HA HB HC) as Hbfma.
simpl in Hbfma; rewrite !B2R_float_of_ftype in Hbfma.
apply Rlt_bool_true in Hfin1; rewrite Hfin1 in Hbfma; clear Hfin1;
destruct Hbfma as (Hbfma & _).
rewrite -Hbfma -!B2R_float_of_ftype /BFMA !float_of_ftype_of_float; 
f_equal.
Qed.  

End FMA. 

Section Mult.

Definition Bmult_no_overflow  (x y: R) : Prop :=
  (Rabs (rounded t (x * y)) < Raux.bpow Zaux.radix2 (femax t))%R.

Lemma BMULT_accurate {NAN: Nans} {STD: is_standard t} :
   forall (x y : ftype t) (FIN: Bmult_no_overflow (FT2R x) (FT2R y)), 
  exists delta, exists epsilon,
   delta * epsilon = 0 /\
   Rabs delta <= default_rel t /\
   Rabs epsilon <= default_abs t /\ 
   (FT2R (BMULT x y) = (FT2R x * FT2R y) * (1+delta) + epsilon)%R.
Proof.
intros.
set (xb := float_of_ftype x).
set (yb := float_of_ftype y).
pose proof (Binary.Bmult_correct (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) 
                (mult_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE xb yb).
cbv zeta in H.
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) 
              (Binary.B2R _ _ xb * Binary.B2R _ _ yb)))
        (Raux.bpow Zaux.radix2 (femax t))). 
destruct H0.
{ destruct H as [? _].
unfold BMULT, BINOP. fold xb yb.
rewrite FT2R_ftype_of_float H.
rewrite <- B2R_float_of_ftype;
  fold xb yb.
unfold xb, yb.
rewrite !B2R_float_of_ftype.
apply generic_round_property. } 
red in FIN. unfold rounded in FIN.
unfold xb, yb in H0.
rewrite !B2R_float_of_ftype in H0.
lra.
Qed.

Lemma is_finite_BMULT_no_overflow {NAN: Nans} {STD: is_standard t} :
  forall (x y : ftype t) 
  (HFINb : is_finite (BMULT x y) = true),
  Bmult_no_overflow (FT2R x) (FT2R y).
Proof.
intros.
pose proof Rle_or_lt (bpow Zaux.radix2 (femax t)) 
  (Rabs (rounded t (FT2R x * FT2R y)))  as Hor;
  destruct Hor; auto.
apply Rlt_bool_false in H; red.
unfold rounded in H.
set (xb := float_of_ftype x).
set (yb := float_of_ftype y).
pose proof (Binary.Bmult_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (mult_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE xb yb) as
  H0.
rewrite <- !B2R_float_of_ftype in H.
rewrite <- !B2R_float_of_ftype.
fold xb yb in H; rewrite H in H0. 
fold xb yb. unfold BMULT, BINOP in HFINb.
fold xb yb in HFINb. 
  rewrite is_finite_Binary float_of_ftype_of_float in HFINb.
destruct ((Binary.Bmult _ _ _ _ _ _ xb yb));
simpl;  try discriminate. 
Qed.

(** No overflow and finite operands imply that multiplication is finite. *)
Lemma no_overflow_mult_is_finite {NAN: Nans} {STD: is_standard t} :
  forall (a b : ftype t),
  is_finite a = true -> is_finite b = true ->
  Rabs (rounded t (FT2R a * FT2R b)) < bpow Zaux.radix2 (femax t) ->
  is_finite (BMULT a b) = true.
Proof.
  intros a b Ha Hb Hov.
  rewrite !is_finite_Binary in Ha, Hb.
  rewrite is_finite_Binary /BMULT/BINOP float_of_ftype_of_float.
  pose proof (Binary.Bmult_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t)
    (mult_nan (fprec t) (femax t) (fprec_gt_one t))
    BinarySingleNaN.mode_NE (float_of_ftype a) (float_of_ftype b)) as H.
  cbv zeta in H.
  rewrite !B2R_float_of_ftype in H.
  unfold rounded in Hov.
  apply Rlt_bool_true in Hov.
  rewrite Hov in H.
  destruct H as (_ & HF & _).
  rewrite HF Ha Hb //.
Qed.

Lemma BMULT_accurate' {NAN: Nans} {STD: is_standard t} : 
  forall
  (x y : ftype t) 
  (FIN: is_finite (BMULT  x y) = true), 
  exists delta, exists epsilon,
   delta * epsilon = 0 /\
   Rabs delta <= default_rel t /\
   Rabs epsilon <= default_abs t /\ 
   (FT2R (BMULT x y) = (FT2R x * FT2R y) * (1+delta) + epsilon)%R.
Proof.
intros. 
pose proof BMULT_accurate x y (is_finite_BMULT_no_overflow x y FIN); auto.
Qed.

Lemma BMULT_finite_e {NAN: Nans} {STD: is_standard t} :
 forall (a b : ftype t)
 (Hfin : is_finite (BMULT  a b) = true),
 is_finite a = true  /\ 
 is_finite b = true.
Proof.
unfold BMULT, BINOP; intros.
rewrite is_finite_Binary float_of_ftype_of_float in Hfin.
rewrite !is_finite_Binary.
destruct (float_of_ftype a), (float_of_ftype b); 
  inversion Hfin; clear Hfin; subst; auto.
Qed.  

(** Relate BMULT to round NE in FLT format *)
Lemma BMULT_round_correct {NAN: Nans} {STD: is_standard t} :  
  forall a b (Hfin : is_finite (BMULT a b) = true),
  let fexp := (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t)) in
  round Zaux.radix2 fexp (Znearest choice) (FT2R a * FT2R b ) = FT2R (BMULT a b).
Proof.
intros.
pose proof (is_finite_BMULT_no_overflow a b Hfin) as Hfin1.
destruct (BMULT_finite_e a b Hfin) as (HA & HB).
rewrite !is_finite_Binary in HA, HB.
pose proof (Binary.Bmult_correct  (fprec t) (femax t) 
        (fprec_gt_0 t) (fprec_lt_femax t) (mult_nan (fprec t) (femax t) 
        (fprec_gt_one t)) BinarySingleNaN.mode_NE (float_of_ftype a) 
        (float_of_ftype b)) as Hbmult.
simpl in Hbmult; rewrite !B2R_float_of_ftype in Hbmult.
apply Rlt_bool_true in Hfin1; rewrite Hfin1 in Hbmult; clear Hfin1;
destruct Hbmult as (Hbmult & _).
rewrite -Hbmult -!B2R_float_of_ftype !float_of_ftype_of_float;
f_equal.
Qed.

(* Numerator finiteness from BDIV finiteness.  Unlike BMULT_finite_e we can
   only conclude finiteness of the numerator a: a finite quotient a/b can arise
   with b infinite (a/inf = 0), so is_finite b is not implied. *)
Lemma BDIV_finite_e {NAN: Nans} {STD: is_standard t} :
 forall (a b : ftype t)
 (Hfin : is_finite (BDIV a b) = true),
 is_finite a = true.
Proof.
unfold BDIV, BINOP; intros.
rewrite is_finite_Binary float_of_ftype_of_float in Hfin.
rewrite !is_finite_Binary.
destruct (float_of_ftype a), (float_of_ftype b);
  cbn [Binary.Bdiv] in Hfin; try discriminate; auto.
Qed.

(* Division analogue of Bmult_no_overflow / is_finite_BMULT_no_overflow.
   Unlike multiplication, Bdiv_correct carries a divisor-nonzero side
   condition (B2R y <> 0), so the no-overflow fact takes FT2R b <> 0. *)
Definition Bdiv_no_overflow (x y: R) : Prop :=
  (Rabs (rounded t (x / y)) < Raux.bpow Zaux.radix2 (femax t))%R.

Lemma is_finite_BDIV_no_overflow {NAN: Nans} {STD: is_standard t} :
  forall (x y : ftype t)
  (Hy : FT2R y <> 0%R)
  (HFINb : is_finite (BDIV x y) = true),
  Bdiv_no_overflow (FT2R x) (FT2R y).
Proof.
intros.
pose proof Rle_or_lt (bpow Zaux.radix2 (femax t))
  (Rabs (rounded t (FT2R x / FT2R y)))  as Hor;
  destruct Hor; auto.
apply Rlt_bool_false in H; red.
unfold rounded in H.
set (xb := float_of_ftype x).
set (yb := float_of_ftype y).
assert (Hy' : Binary.B2R _ _ yb <> 0%R) by (rewrite B2R_float_of_ftype; exact Hy).
pose proof (Binary.Bdiv_correct  (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (div_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE xb yb Hy') as
  H0.
rewrite <- !B2R_float_of_ftype in H.
rewrite <- !B2R_float_of_ftype.
fold xb yb in H; rewrite H in H0.
fold xb yb. unfold BDIV, BINOP in HFINb.
fold xb yb in HFINb.
  rewrite is_finite_Binary float_of_ftype_of_float in HFINb.
destruct ((Binary.Bdiv _ _ _ _ _ _ xb yb));
simpl;  try discriminate.
Qed.

(* Converse: a division whose rounded quotient stays below the overflow
   threshold (with finite numerator and nonzero divisor) yields a finite BDIV.
   Analog of no_overflow_mult_is_finite; note is_finite (Bdiv) = is_finite x. *)
Lemma no_overflow_div_is_finite {NAN: Nans} {STD: is_standard t} :
  forall (a b : ftype t),
  is_finite a = true -> FT2R b <> 0%R ->
  Rabs (rounded t (FT2R a / FT2R b)) < bpow Zaux.radix2 (femax t) ->
  is_finite (BDIV a b) = true.
Proof.
  intros a b Ha Hb Hov.
  rewrite is_finite_Binary in Ha.
  rewrite is_finite_Binary /BDIV/BINOP float_of_ftype_of_float.
  assert (Hb' : Binary.B2R _ _ (float_of_ftype b) <> 0%R)
    by (rewrite B2R_float_of_ftype; exact Hb).
  pose proof (Binary.Bdiv_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (div_nan (fprec t) (femax t) (fprec_gt_one t))
    BinarySingleNaN.mode_NE (float_of_ftype a) (float_of_ftype b) Hb') as H.
  cbv zeta in H.
  rewrite !B2R_float_of_ftype in H.
  unfold rounded in Hov.
  apply Rlt_bool_true in Hov.
  rewrite Hov in H.
  destruct H as (_ & HF & _).
  rewrite HF. exact Ha.
Qed.

(** Relate BDIV to round NE in FLT format (divisor nonzero) *)
Lemma BDIV_round_correct {NAN: Nans} {STD: is_standard t} :
  forall a b (Hb : FT2R b <> 0%R) (Hfin : is_finite (BDIV a b) = true),
  let fexp := (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t)) in
  round Zaux.radix2 fexp (Znearest choice) (FT2R a / FT2R b) = FT2R (BDIV a b).
Proof.
intros.
pose proof (is_finite_BDIV_no_overflow a b Hb Hfin) as Hfin1.
assert (Hb' : Binary.B2R _ _ (float_of_ftype b) <> 0%R)
  by (rewrite B2R_float_of_ftype; exact Hb).
pose proof (Binary.Bdiv_correct  (fprec t) (femax t)
        (fprec_gt_0 t) (fprec_lt_femax t) (div_nan (fprec t) (femax t)
        (fprec_gt_one t)) BinarySingleNaN.mode_NE (float_of_ftype a)
        (float_of_ftype b) Hb') as Hbdiv.
simpl in Hbdiv; rewrite !B2R_float_of_ftype in Hbdiv.
apply Rlt_bool_true in Hfin1; rewrite Hfin1 in Hbdiv; clear Hfin1;
destruct Hbdiv as (Hbdiv & _).
rewrite -Hbdiv -!B2R_float_of_ftype !float_of_ftype_of_float;
f_equal.
Qed.

Lemma BMULT_not_zero  {NAN: Nans} {STD: is_standard t} :
  forall (x y : ftype t)
  (Hfin : Binary.is_finite_strict _ _ (float_of_ftype (BMULT x y)) = true),
  (FT2R x * FT2R y)%R = 0 -> False.
Proof.
  unfold BMULT, BINOP; simpl.
  intros x y H H1.
  rewrite <- !B2R_float_of_ftype in H1.
  rewrite float_of_ftype_of_float in H.
  assert (Hx : Binary.is_finite_strict _ _  (float_of_ftype x) = true). 
  {destruct (float_of_ftype x), (float_of_ftype y); try discriminate; auto. } 
  assert (Hy : Binary.is_finite_strict _ _  (float_of_ftype y) = true). 
  {destruct (float_of_ftype x), (float_of_ftype y); try discriminate; auto. } 
  destruct (float_of_ftype x), (float_of_ftype y); 
  cbv [Binary.Bmult]; try discriminate.
  apply Rmult_integral in H1; destruct H1.
  { pose proof (Binary.B2R_Bsign_inj _ _ 
    (Binary.B754_finite (fprec t) (femax t) s m e e0)) 
    (Binary.B754_zero (fprec t) (femax t) s) as Hp;  
  rewrite Hp in H; clear Hp; auto. }
  pose proof (Binary.B2R_Bsign_inj _ _ 
    (Binary.B754_finite (fprec t) (femax t) s0 m0 e1 e2)) 
    (Binary.B754_zero (fprec t) (femax t) s0) as Hp;  
  rewrite Hp in H; clear Hp; auto.
Qed.

End Mult.

Section Plus. 

Lemma BPLUS_finite_e {NAN: Nans} {STD: is_standard t} :
 forall (a b : ftype t)
 (Hfin : is_finite (BPLUS  a b) = true),
 is_finite a = true  /\ 
 is_finite b = true.
Proof.
unfold BPLUS, BINOP; intros.
rewrite is_finite_Binary float_of_ftype_of_float in Hfin.
rewrite !is_finite_Binary.
destruct (float_of_ftype a), (float_of_ftype b); 
  inversion Hfin; clear Hfin; subst; simpl; auto.
destruct s,s0; discriminate; auto.
Qed.

Lemma BPLUS_UF_exact {NAN: Nans} {STD: is_standard t} :
 forall (a b : ftype t),
  is_finite (BPLUS a b) = true ->
  Rabs (FT2R a + FT2R b) < bpow radix2 ((@common.emin t) + fprec t - 1) ->
   FT2R (BPLUS a b) = FT2R a + FT2R b.
Proof.
intros a b FIN BND.
have Hgeneric: 
  generic_format radix2 (SpecFloat.fexp (fprec t) (femax t)) (Rabs (FT2R a + FT2R b)).
-
apply generic_format_abs.
rewrite -!B2R_float_of_ftype.
apply Plus_error.FLT_format_plus_small => //;
try apply (Binary.generic_format_B2R (fprec t) (femax t)).
apply Rlt_le.
rewrite !B2R_float_of_ftype.
refine (Rlt_le_trans _ _ _ BND _).
apply bpow_le; unfold emin; lia.
-
destruct (BPLUS_finite_e a b FIN) as [FINa  FINb].
rewrite !is_finite_Binary in FINa FINb.
set (ap := float_of_ftype a).
set (bp := float_of_ftype b).
pose proof (Binary.Bplus_correct  (fprec t) (femax t) (fprec_gt_0 t) 
                    (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
                      BinarySingleNaN.mode_NE ap bp FINa FINb) as H0.
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) 
                  (Binary.B2R _ _ ap + Binary.B2R _ _ bp)))
        (Raux.bpow Zaux.radix2 (femax t))) as H.
destruct H.
+
destruct H0 as [H0 _].
rewrite /BPLUS/BINOP -B2R_float_of_ftype float_of_ftype_of_float H0.
rewrite round_generic !B2R_float_of_ftype => //.
apply generic_format_abs_inv => //.
+
exfalso.
eapply Rle_not_lt.
apply H.
eapply Rle_lt_trans; [ | eapply Rlt_trans; [apply BND|]].
apply abs_round_le_generic => //.
apply fexp_valid.
apply valid_rnd_NE.
rewrite !B2R_float_of_ftype; nra.
apply bpow_lt.
rewrite /emin /SpecFloat.emin.
pose proof (fprec_gt_one t).
pose proof (fprec_lt_femax t).
lia.
Qed.

Definition Bplus_no_overflow (x y: R) : Prop :=
  (Rabs ( Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE)  (x + y )) < Raux.bpow Zaux.radix2 (femax t))%R.


Lemma BPLUS_B2R_zero {NAN: Nans} (a : ftype t)  {STD: is_standard t} :
  is_finite a = true ->
  FT2R (BPLUS a (Zconst t 0)) = FT2R a.
Proof.
unfold BPLUS, BINOP, Zconst; 
rewrite is_finite_Binary FT2R_ftype_of_float
  -B2R_float_of_ftype float_of_ftype_of_float; intros.
destruct (float_of_ftype a);
unfold neg_zero; simpl; try discriminate; auto.
destruct s; simpl; auto.
Qed.

Lemma BPLUS_accurate {NAN: Nans} {STD: is_standard t} :
 forall      (x : ftype t) (FINx: is_finite x = true) 
             (y : ftype t) (FINy: is_finite y = true) 
          (FIN: Bplus_no_overflow (FT2R x) (FT2R y)), 
  exists delta, 
   Rabs delta <= default_rel t /\
   (FT2R (BPLUS x y ) = (FT2R x + FT2R y) * (1+delta))%R.
Proof.
intros.
rewrite !is_finite_Binary in FINx FINy.
set (xb := float_of_ftype x).
set (yb := float_of_ftype y).
pose proof (Binary.Bplus_correct  (fprec t) (femax t) (fprec_gt_0 t) 
                    (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
                      BinarySingleNaN.mode_NE xb yb FINx FINy).
cbv zeta in H.
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) 
                  (Binary.B2R _ _ xb + Binary.B2R _ _ yb)))
        (Raux.bpow Zaux.radix2 (femax t))).
destruct H0.
-
destruct H as [? _].
unfold BPLUS, BINOP.
fold xb yb.
rewrite FT2R_ftype_of_float H.
assert (A: Generic_fmt.generic_format Zaux.radix2
       (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
       (FT2R x) ).
rewrite <- B2R_float_of_ftype.
apply Binary.generic_format_B2R.
assert (B: Generic_fmt.generic_format Zaux.radix2
       (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
       (FT2R y) ).
rewrite <- B2R_float_of_ftype.
apply Binary.generic_format_B2R.
pose proof Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R x) (FT2R y) A B.
unfold Relative.u_ro in H1. fold (default_rel t) in H1.
destruct H1 as (d & Hd & Hd').
assert (  Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
    (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
    (FT2R x + FT2R y)  =  Generic_fmt.round Zaux.radix2
        (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
        (Generic_fmt.Znearest (fun x0 : Z => negb (Z.even x0)))
        (FT2R x + FT2R y)) by auto.
rewrite <- H1 in Hd'. clear H1. 
rewrite <- !B2R_float_of_ftype in Hd'.
fold xb yb in Hd'.
rewrite Hd'; clear Hd'.
exists d; split; auto.
eapply Rle_trans; [apply Hd |].
apply Rdiv_le_left.
apply Fourier_util.Rlt_zero_pos_plus1. 
apply default_rel_gt_0.
eapply Rle_trans with (default_rel t * 1); try nra.
f_equal. unfold xb, yb; rewrite !B2R_float_of_ftype; auto.
-
red in FIN.
rewrite <-!B2R_float_of_ftype in FIN; auto.
fold xb yb in FIN; lra.
Qed.

Lemma is_finite_sum_no_overflow {NAN: Nans} {STD: is_standard t} :
  forall x y
  (HFINb : is_finite (BPLUS x y) = true),
  Bplus_no_overflow (FT2R x) (FT2R y).
Proof.
intros x y.
rewrite is_finite_Binary; intros.
pose proof Rle_or_lt (bpow Zaux.radix2 (femax t)) (Rabs (rounded t (FT2R x + FT2R y)))  as Hor;
  destruct Hor; auto.
apply Rlt_bool_false in H.
assert (HFIN: is_finite x = true /\ is_finite y = true).
{ unfold BPLUS, BINOP in HFINb. rewrite !is_finite_Binary. 
    rewrite float_of_ftype_of_float in HFINb;
    destruct (float_of_ftype x), (float_of_ftype y); 
    simpl in *; split; try discriminate; auto; 
    destruct s; destruct s0; simpl in *; try discriminate; auto. }
unfold rounded in H.
rewrite !is_finite_Binary in HFIN.
destruct HFIN as (A & B). 
pose proof (Binary.Bplus_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE 
  (float_of_ftype x) (float_of_ftype y) A B) as
  H0.
rewrite <- !B2R_float_of_ftype in H.
rewrite H in H0;
destruct H0 as ( C & _).
unfold BPLUS, BINOP in HFINb.
    rewrite float_of_ftype_of_float in HFINb.
destruct ((Binary.Bplus (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) 
             (plus_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE 
  (float_of_ftype x) (float_of_ftype y)));
simpl; try discriminate.
Qed.

Lemma no_overflow_sum_is_finite {NAN: Nans} {STD: is_standard t} :
  forall x y
  (H1  : is_finite x = true)
  (H2  : is_finite y = true) 
  (Hov : Bplus_no_overflow (FT2R x) (FT2R y)),
  is_finite (BPLUS x y) = true.
Proof.
intros x y.
rewrite !is_finite_Binary; 
  unfold Bplus_no_overflow, BPLUS, BINOP; intros.
rewrite float_of_ftype_of_float.
pose proof (Binary.Bplus_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE 
  (float_of_ftype x) (float_of_ftype y) H1 H2) as
  H0.
remember (Rlt_bool _ _ ) as HB; destruct HB.  
destruct H0 as (_ & HP  &_); auto.
exfalso.
unfold Rlt_bool in HeqHB.
remember (Rcompare _ _) as HR; destruct HR; try discriminate.
symmetry in HeqHR. 
apply Rcompare_Eq_inv in HeqHR.
rewrite !B2R_float_of_ftype in HeqHR; nra.
symmetry in HeqHR. 
apply Rcompare_Gt_inv in HeqHR.
rewrite !B2R_float_of_ftype in HeqHR; nra.
Qed.

Lemma BPLUS_accurate' {NAN: Nans} {STD: is_standard t} :
  forall (x y : ftype t) 
  (FIN: is_finite (BPLUS  x y) = true), 
  exists delta, 
   Rabs delta <= default_rel t /\
   (FT2R (BPLUS x y ) = (FT2R x + FT2R y) * (1+delta))%R.
Proof.
intros.
eapply BPLUS_accurate.
1,2: rewrite is_finite_Binary; 
rewrite is_finite_Binary in FIN;
unfold BPLUS, BINOP in FIN;
rewrite float_of_ftype_of_float in FIN;
destruct (float_of_ftype x); destruct (float_of_ftype y); 
        simpl; try discriminate; auto; 
  destruct s; destruct s0; simpl; try discriminate; auto.
apply is_finite_sum_no_overflow; auto.
Qed.

(** Relate BPLUS to round NE in FLT format *)
Lemma BPLUS_round_correct {NAN: Nans} {STD: is_standard t} :  
  forall a b (Hfin : is_finite (BPLUS a b) = true),
  let fexp := (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t)) in
  round Zaux.radix2 fexp (Znearest choice) (FT2R a + FT2R b ) = FT2R (BPLUS a b).
Proof.
intros.
pose proof (is_finite_sum_no_overflow a b Hfin) as Hfin1.
destruct (BPLUS_finite_e a b Hfin) as (HA & HB).
rewrite !is_finite_Binary in HA, HB.
pose proof (Binary.Bplus_correct  (fprec t) (femax t) 
        (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) 
        (fprec_gt_one t)) BinarySingleNaN.mode_NE (float_of_ftype a) 
        (float_of_ftype b)) as Hbplus.
simpl in Hbplus; rewrite !B2R_float_of_ftype in Hbplus.
apply Rlt_bool_true in Hfin1; rewrite Hfin1 in Hbplus; clear Hfin1;
destruct Hbplus as (Hbplus & _) => //.
rewrite -Hbplus -!B2R_float_of_ftype !float_of_ftype_of_float; 
f_equal. 
Qed. 

Lemma BPLUS_fin_symm {NAN: Nans} {STD: is_standard t} :
  forall (x y : ftype t),
  is_finite (BPLUS  x y) = true -> is_finite (BPLUS y x) = true.
Proof.
  move => x y Hfin.
  destruct (BPLUS_finite_e _ _ Hfin) as [Hx Hy].
  pose proof (is_finite_sum_no_overflow x y Hfin) as Hbnd.
  pose proof (Binary.Bplus_correct  (fprec t) (femax t) 
        (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) 
        (fprec_gt_one t)) BinarySingleNaN.mode_NE (float_of_ftype y) 
        (float_of_ftype x)) as Hbplus.
simpl in Hbplus; rewrite !B2R_float_of_ftype in Hbplus.
apply Rlt_bool_true in Hbnd. 
rewrite Rplus_comm in Hbnd. 
rewrite Hbnd in Hbplus; clear Hbnd.
destruct Hbplus as (_ & Hbplus & _) => //; 
[rewrite -is_finite_Binary => // | rewrite -is_finite_Binary => //| ].
rewrite is_finite_Binary /BPLUS/BINOP !float_of_ftype_of_float => //. 
Qed.

Lemma BPLUS_comm {NAN: Nans} {STD: is_standard t} :
  forall (x y : ftype t) 
  (FIN: is_finite (BPLUS  x y) = true), 
  FT2R (BPLUS x y) = FT2R (BPLUS y x).
Proof.
  move => x y Hfin.
  rewrite -!BPLUS_round_correct; [ | apply BPLUS_fin_symm | exact Hfin] => //.
  rewrite Rplus_comm => //. 
Qed.

End Plus. 

Section Minus.

Lemma BMINUS_zero {NAN: Nans} (a : ftype t)  {STD: is_standard t} :
is_finite a = true ->
FT2R (BMINUS a a) = FT2R (Zconst t 0).
Proof.
unfold BMINUS, Zconst, BINOP.
pose proof (Binary.Bminus_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE 
    (float_of_ftype a) (float_of_ftype a)) as
  H0. 
rewrite is_finite_Binary.
intros;
destruct (float_of_ftype a);
unfold neg_zero; simpl; try discriminate; auto.
destruct s; simpl; auto.
rewrite Rlt_bool_true in H0.
destruct H0 as (A & _); auto.
rewrite FT2R_ftype_of_float A Rminus_diag round_0.
rewrite FT2R_ftype_of_float; simpl; auto.
rewrite Rminus_diag round_0 Rabs_R0; 
apply bpow_gt_0.
Qed.

Definition Bminus_no_overflow (x y: R) : Prop :=
  (Rabs ( Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE)  (x - y )) < Raux.bpow Zaux.radix2 (femax t))%R.


Lemma BMINUS_finite_e {NAN: Nans} {STD: is_standard t} :
 forall (a b : ftype t)
 (Hfin : is_finite (BMINUS a b) = true),
 is_finite a = true  /\ 
 is_finite b = true.
Proof.
unfold BMINUS, BINOP; intros.
rewrite is_finite_Binary float_of_ftype_of_float in Hfin.
rewrite !is_finite_Binary.
destruct (float_of_ftype a), (float_of_ftype b); 
  inversion Hfin; clear Hfin; subst; simpl; auto.
destruct s,s0; discriminate; auto.
Qed.

Lemma is_finite_minus_no_overflow {NAN: Nans} {STD: is_standard t} :
  forall x y
  (HFINb : is_finite (BMINUS x y) = true),
  Bminus_no_overflow (FT2R x) (FT2R y).
Proof.
intros.
pose proof Rle_or_lt (bpow Zaux.radix2 (femax t)) (Rabs (rounded t (FT2R x - FT2R y)))  as Hor;
  destruct Hor; auto.
apply Rlt_bool_false in H.
assert (HFIN: is_finite x = true /\is_finite y = true).
rewrite !is_finite_Binary; 
rewrite is_finite_Binary in HFINb.
{ unfold BMINUS, BINOP in HFINb. 
rewrite float_of_ftype_of_float in HFINb;
    destruct (float_of_ftype x); destruct (float_of_ftype y); 
          simpl in *; split; try discriminate; auto;
    destruct s; destruct s0; simpl in *; try discriminate; auto. }
rewrite !is_finite_Binary in HFIN;
rewrite !is_finite_Binary in HFINb;
destruct HFIN as (A & B).
unfold rounded in H.
pose proof (Binary.Bminus_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE 
    (float_of_ftype x) (float_of_ftype y) A B) as
  H0.
rewrite <- !B2R_float_of_ftype in H.
rewrite H in H0;
destruct H0 as ( C & _).
unfold BMINUS, BINOP in HFINb.
rewrite float_of_ftype_of_float in HFINb.
destruct ((Binary.Bminus (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) 
             (plus_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE 
              (float_of_ftype x) (float_of_ftype y)));
simpl; try discriminate.
Qed.

Lemma no_overflow_minus_is_finite {NAN: Nans} {STD: is_standard t} :
  forall x y
  (H1  : is_finite x = true)
  (H2  : is_finite y = true) 
  (Hov : Bminus_no_overflow (FT2R x) (FT2R y)),
  is_finite (BMINUS x y) = true.
Proof.
intros x y.
rewrite !is_finite_Binary; 
  unfold Bminus_no_overflow, BMINUS, BINOP; intros.
rewrite float_of_ftype_of_float.
pose proof (Binary.Bminus_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE 
  (float_of_ftype x) (float_of_ftype y) H1 H2) as
  H0.
remember (Rlt_bool _ _ ) as HB; destruct HB.  
destruct H0 as (_ & HP  &_); auto.
exfalso.
unfold Rlt_bool in HeqHB.
remember (Rcompare _ _) as HR; destruct HR; try discriminate.
symmetry in HeqHR. 
apply Rcompare_Eq_inv in HeqHR.
rewrite !B2R_float_of_ftype in HeqHR; nra.
symmetry in HeqHR. 
apply Rcompare_Gt_inv in HeqHR.
rewrite !B2R_float_of_ftype in HeqHR; nra.
Qed.

Lemma BMINUS_accurate {NAN: Nans} {STD: is_standard t} :
 forall      (x : ftype t) (FINx: is_finite x = true) 
             (y : ftype t) (FINy: is_finite y = true) 
          (FIN: Bminus_no_overflow (FT2R x) (FT2R y)), 
  exists delta, 
   Rabs delta <= default_rel t /\
   (FT2R (BMINUS x y ) = (FT2R x - FT2R y) * (1+delta))%R.
Proof.
intros.
rewrite !is_finite_Binary in FINx FINy.
set (xb := float_of_ftype x).
set (yb := float_of_ftype y).
pose proof (Binary.Bminus_correct  (fprec t) (femax t) (fprec_gt_0 t) 
                    (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
                      BinarySingleNaN.mode_NE xb yb FINx FINy).
cbv zeta in H.
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) 
                  (Binary.B2R _ _ xb - Binary.B2R _ _ yb)))
        (Raux.bpow Zaux.radix2 (femax t))).
destruct H0.
-
destruct H as [? _].
unfold BMINUS, BINOP.
fold xb yb.
rewrite FT2R_ftype_of_float H.
assert (A: Generic_fmt.generic_format Zaux.radix2
       (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
       (FT2R x) ).
rewrite <- B2R_float_of_ftype.
apply Binary.generic_format_B2R.
assert (B: Generic_fmt.generic_format Zaux.radix2
       (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
       (-FT2R y) ).
rewrite <- B2R_float_of_ftype.
apply Generic_fmt.generic_format_opp.
apply Binary.generic_format_B2R.
pose proof Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R x) (-FT2R y) A B.
unfold Relative.u_ro in H1. fold (default_rel t) in H1.
destruct H1 as (d & Hd & Hd').
assert (  Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
    (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
    (FT2R x - FT2R y)  =  Generic_fmt.round Zaux.radix2
        (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
        (Generic_fmt.Znearest (fun x0 : Z => negb (Z.even x0)))
        (FT2R x - FT2R y)) by auto.
replace (_ +- _) with ( FT2R x - FT2R y) in Hd' by nra.
rewrite <- H1 in Hd'. clear H1. 
rewrite <- !B2R_float_of_ftype in Hd'.
fold xb yb in Hd'.
rewrite Hd'; clear Hd'.
exists d; split; auto.
eapply Rle_trans; [apply Hd |].
apply Rdiv_le_left.
apply Fourier_util.Rlt_zero_pos_plus1. 
apply default_rel_gt_0.
eapply Rle_trans with (default_rel t * 1); try nra.
f_equal. unfold xb, yb; rewrite !B2R_float_of_ftype; auto.
-
red in FIN.
rewrite <-!B2R_float_of_ftype in FIN; auto.
fold xb yb in FIN; lra.
Qed.

Lemma BMINUS_accurate' {NAN: Nans} {STD: is_standard t} :
  forall (x y : ftype t) 
  (FIN: is_finite (BMINUS  x y) = true), 
  exists delta, 
   Rabs delta <= default_rel t /\
   (FT2R (BMINUS x y ) = (FT2R x - FT2R y) * (1+delta))%R.
Proof.
intros.
eapply BMINUS_accurate.
1,2: rewrite is_finite_Binary; 
rewrite is_finite_Binary in FIN;
unfold BMINUS, BINOP in FIN;
rewrite float_of_ftype_of_float in FIN;
destruct (float_of_ftype x); destruct (float_of_ftype y); 
        simpl; try discriminate; auto; 
  destruct s; destruct s0; simpl; try discriminate; auto.
apply is_finite_minus_no_overflow; auto.
Qed.

(** Relate BMINUS to round NE in FLT format *)
Lemma BMINUS_round_correct {NAN: Nans} {STD: is_standard t} :  
  forall a b (Hfin : is_finite (BMINUS a b) = true),
  let fexp := (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t)) in
  round Zaux.radix2 fexp (Znearest choice) (FT2R a - FT2R b ) = FT2R (BMINUS a b).
Proof.
intros.
pose proof (is_finite_minus_no_overflow a b Hfin) as Hfin1.
destruct (BMINUS_finite_e a b Hfin) as (HA & HB).
rewrite !is_finite_Binary in HA, HB.
pose proof (Binary.Bminus_correct  (fprec t) (femax t) 
        (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) 
        (fprec_gt_one t)) BinarySingleNaN.mode_NE (float_of_ftype a) 
        (float_of_ftype b)) as Hbminus.
simpl in Hbminus; rewrite !B2R_float_of_ftype in Hbminus.
apply Rlt_bool_true in Hfin1; rewrite Hfin1 in Hbminus; clear Hfin1;
destruct Hbminus as (Hbminus & _) => //.
rewrite -Hbminus -!B2R_float_of_ftype !float_of_ftype_of_float; 
f_equal. 
Qed. 


End Minus.

Section Opp.

(** Relate BOPP to Binary.Bopp. *)
Lemma BOPP_binary {NAN: Nans} {STD: is_standard t} :  
forall a (Hfin : is_finite (BOPP a) = true \/ is_finite a = true),
let fexp := (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t)) in
- (FT2R a) = FT2R (BOPP a).
Proof.
rewrite /BOPP; intros.
rewrite FT2R_ftype_of_float -B2R_float_of_ftype Binary.B2R_Bopp; auto.
Qed.

(* Relate BOPP to Binary.Bopp for finite *)
Lemma BOPP_is_finite {NAN: Nans} {STD: is_standard t} :  
forall a,  is_finite (BOPP a) = true <-> is_finite a = true.
Proof.
intros; rewrite !is_finite_Binary /BOPP; 
try rewrite float_of_ftype_of_float; 
try rewrite Binary.is_finite_Bopp; tauto.
Qed.

End Opp.
End TVar. 
