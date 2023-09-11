(* This file contains accuracy and correctness proofs for the
  TwoSum and Fast2Sum algorithms in the FLT format *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics.
Require Import DWPlus DDModels common.
Require Import F2SumFLT F2SumFLX.
From Flocq Require Import Pff2Flocq Core.
Require Import mathcomp.ssreflect.ssreflect.

Section TwoSumCorrect.

Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (@DD.DDModels.emin t).
Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 
Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Let rnd_mode:= (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE).

Theorem round_plus_ge_ulp :
  forall (x y : ftype t),
  rounded t (FT2R x + FT2R y) <> 0%R ->
  (ulp (FT2R x /IZR radix2) <= Rabs (rounded t (FT2R x + FT2R y)))%R.
Proof with auto with typeclass_instances.
intros.
have HGy: generic_format radix2 fexp (FT2R y) by
  rewrite -B2R_float_of_ftype; apply Binary.generic_format_B2R. 
have HGx: generic_format radix2 fexp (FT2R x) by
  rewrite -B2R_float_of_ftype; apply Binary.generic_format_B2R. 
case (Req_dec (FT2R x) 0); intros Zx.
{ rewrite Zx Rplus_0_l.
rewrite /rounded round_generic => //.
unfold Rdiv; rewrite Rmult_0_l.
rewrite HGy.
unfold F2R; simpl; rewrite Rabs_mult.
rewrite (Rabs_pos_eq (bpow radix2 _)); [ |apply bpow_ge_0].
case (Z.eq_dec (Ztrunc (scaled_mantissa radix2 fexp (FT2R y))) 0); intros Hm.
contradict H.
rewrite Zx HGy Hm; unfold F2R; simpl.
rewrite Rplus_0_l Rmult_0_l.
apply round_0...
apply Rle_trans with (1*bpow radix2 (cexp radix2 fexp (FT2R y)))%R.
rewrite Rmult_1_l.
rewrite -ulp_neq_0...
apply: ulp_ge_ulp_0.
intros K; apply Hm.
rewrite K scaled_mantissa_0.
apply Ztrunc_IZR.
apply Rmult_le_compat_r.
apply bpow_ge_0.
rewrite <- abs_IZR.
apply IZR_le.
apply (Zlt_le_succ 0).
by apply Z.abs_pos. } 
destruct (Plus_error.round_plus_F2R radix2 fexp 
 (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) (FT2R x) (FT2R y) 
  HGx HGy Zx) as (m,Hm).
case (Z.eq_dec m 0); intros Zm.
contradict H.
rewrite /rounded  Hm Zm.
apply F2R_0.
rewrite /rounded Hm -F2R_Zabs.
rewrite ulp_neq_0.
rewrite -(Rmult_1_l (bpow radix2 _)).
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply IZR_le.
apply (Zlt_le_succ 0).
now apply Z.abs_pos.
apply Rmult_integral_contrapositive_currified with (1 := Zx).
apply Rinv_neq_0_compat.
apply Rgt_not_eq, radix_pos.
Qed.


Lemma TwoSumF_eq (xh y: ftype t):
FT2R xh + FT2R y = 0 -> 
is_finite_p (TwoSumF xh y) -> 
F2Rp (TwoSumF xh y) = (0,0).
Proof.
move => H. rewrite /F2Rp/TwoSumF/is_finite_p/fst/snd.
move => [] FIN1 FIN2. 
set (a:= (BMINUS xh (BMINUS (BPLUS xh y) y))) in *.
set (b:= (BMINUS y (BMINUS (BPLUS xh y) (BMINUS (BPLUS xh y) y)))) in *.
BPLUS_correct t a b.
clear H5; subst a b.
set (c:= (BMINUS (BPLUS xh y) y)) in *.
rewrite -is_finite_Binary in H3.
BMINUS_correct t xh c. clear H7; subst c.
set (d:= (BMINUS (BPLUS xh y) (BMINUS (BPLUS xh y) y))) in *. 
rewrite -is_finite_Binary in H4.
rewrite !B2R_float_of_ftype.
BMINUS_correct t y d; clear H9; subst d.
set (a:= BPLUS xh y) in *. 
set (b:= (BMINUS a y)) in *.
rewrite -is_finite_Binary in H8.
BMINUS_correct t a b; clear H11; subst b.
rewrite -is_finite_Binary in H10.
rewrite !B2R_float_of_ftype.
BMINUS_correct t a y; clear H13; subst a.
rewrite -is_finite_Binary in H11.
rewrite !B2R_float_of_ftype.
BPLUS_correct t xh y; clear H15. 
rewrite H round_0
  !Rminus_0_l round_NE_opp Ropp_involutive.
f_equal.
rewrite -(round_0 radix2 fexp 
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)).
f_equal.
apply Rplus_opp_r_uniq in H.
rewrite !B2R_float_of_ftype.
rewrite H !round_NE_opp Ropp_involutive.
rewrite -Rcomplements.Ropp_plus_minus_distr 
  round_NE_opp !Rplus_opp .
apply Rminus_diag_eq; f_equal.
symmetry; rewrite round_generic => //.
apply generic_format_round.
apply Binary.fexp_correct, fprec_gt_0.
apply valid_rnd_N.
Qed.

Variables (a b : ftype t).

Lemma BPLUS_UF_exact:
  is_finite (BPLUS a b) = true -> 
  Rabs (FT2R a + FT2R b) < bpow radix2 (emin + fprec t - 1) -> 
   FT2R (BPLUS a b) = FT2R a + FT2R b.
Proof.
intros FIN BND. 
BPLUS_correct t a b.
rewrite round_generic => //.
by rewrite !B2R_float_of_ftype.
apply Plus_error.FLT_format_plus_small => //;
rewrite -B2R_float_of_ftype;
try apply (Binary.generic_format_B2R (fprec t) (femax t)).
apply Rlt_le.
rewrite B2R_float_of_ftype.
refine (Rlt_le_trans _ _ _ BND _). 
apply bpow_le; fold emin; lia.
Qed.

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
pose proof (@Flocq.Pff.Pff2Flocq.TwoSum_correct emin (fprec t) choice 
    (fprec_gt_one t) emin_le_0 choiceP (FT2R b) (FT2R a)) as Hc.
rewrite Rplus_comm; rewrite <- Hc; clear Hc; rewrite_format.
(* algebra *)
rewrite <- Rplus_opp, Rplus_comm, <- Rplus_assoc.
replace (FT2R b + FT2R a) with (FT2R a + FT2R b) by nra.
(* rewrites from correctness theorems *)
unfold TwoSumF_err, TwoSumF_sum, TwoSumF, fst, snd in *.
BPLUS_correct t a b; rewrite !B2R_float_of_ftype; field_simplify.
fold s a' b' da db in FINd; fold s a' b' da db.
BPLUS_correct t da db. 
rewrite Rplus_comm; repeat f_equal.
{ subst db; rewrite -is_finite_Binary in H6. 
  BMINUS_correct t b b'.
  subst b' s; rewrite -is_finite_Binary in H9. 
  BMINUS_correct t (BPLUS a b) a'. 
  unfold BPLUS, BINOP. rewrite FT2R_ftype_of_float H4.
  repeat f_equal; try rewrite B2R_float_of_ftype => //.
  subst a'; rewrite -is_finite_Binary in H12. 
  BMINUS_correct t (BPLUS a b) b.
  unfold BPLUS, BINOP. rewrite FT2R_ftype_of_float H4.
  repeat f_equal; try rewrite B2R_float_of_ftype => //. } 
{ subst da; rewrite -is_finite_Binary in H5.  
  BMINUS_correct t a a'.
  subst a' s; rewrite -is_finite_Binary in H9.  
  BMINUS_correct t (BPLUS a b) b.
  unfold BPLUS, BINOP. rewrite FT2R_ftype_of_float H4.
  repeat f_equal; try rewrite B2R_float_of_ftype => //. }
all: rewrite -B2R_float_of_ftype; apply Binary.generic_format_B2R.
Qed.

Theorem TwoSumF_error :
  exists del, 
  FT2R (TwoSumF_err a b) = (FT2R a + FT2R b) * del /\
  Rabs del <= /2 * bpow radix2(-fprec t + 1). 
Proof.
rewrite TwoSumF_correct.
rewrite /TwoSumF_sum/TwoSumF/fst/snd.
destruct FIN as (FINs & _).
simpl in FINs.
destruct (BPLUS_accurate' t a b FINs) as (del & A & B).
rewrite B; exists (-del); split; [field_simplify; nra|].
rewrite Rabs_Ropp.
refine (Rle_trans _ _ _ A _ ).
now apply Req_le; rewrite /default_rel.
Qed.

Theorem TwoSum_is_DW: 
  double_word (TwoSumF_sum a b) (TwoSumF_err a b).
Proof.
  rewrite /double_word TwoSumF_correct // /TwoSumF_sum /= /common.rounded. 
destruct FIN as (FINm & FINp).
unfold TwoSumF_err, TwoSumF_sum, TwoSumF, fst, snd in *.
  BPLUS_correct t a b.
by rewrite !B2R_float_of_ftype.
Qed.

Lemma TwoSumEq_no_underflow 
(HU1 : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R a + FT2R b)):
TwoSum (fprec t) choice (FT2R a) (FT2R b) = F2Rp (TwoSumF a b).
Proof.
move : FIN. move => []. 
pose proof round_FLT_FLX radix2 emin. 
have Heq1 : TwoSum (fprec t) choice (FT2R a) (FT2R b) = 
  (TwoSum_sum (fprec t) choice (FT2R a) (FT2R b), TwoSum_err (fprec t) choice (FT2R a) (FT2R b)).
{ simpl; auto. }
rewrite Heq1.
have Heq2 : TwoSumF a b = 
  (TwoSumF_sum a b, TwoSumF_err a b).
{ simpl; auto. }
rewrite Heq2 /F2Rp.
clear Heq1 Heq2.
move => FIN1 FIN2 /=.
have Heq : 
TwoSum_sum (fprec t) choice (FT2R a) (FT2R b) = FT2R (TwoSumF_sum a b).
{ move: FIN1. rewrite /TwoSum_sum/TwoSumF_sum/F2Rp/fst/snd/=. move => FIN1.
BPLUS_correct t a b; field_simplify. rewrite H => //. rewrite !B2R_float_of_ftype => //. }
f_equal => //.
rewrite TwoSumF_correct DWPlus.TwoSum_correct => //. f_equal => //.
apply fprec_gt_one.
all: apply (@generic_format_FLX_FLT radix2 emin); 
rewrite -B2R_float_of_ftype;
apply Binary.generic_format_B2R.
Qed.

(* results of FLT and FLX algorithms are equal regardless of underflow *) 
Lemma TwoSumEq_FLT : 
TwoSum (fprec t) choice (FT2R a) (FT2R b) = F2Rp (TwoSumF a b).
Proof.
move : FIN; clear FIN. rewrite /TwoSumF/is_finite_p/fst/snd.
move => FIN; destruct FIN as (FINA & FINB). 
rewrite /TwoSum/F2Rp/fst/snd.
destruct (Rlt_or_le (Rabs (FT2R a + FT2R b)) (bpow radix2 (emin + fprec t - 1)) ) as
   [BND | BND].
{ have A : generic_format radix2 (FLT_exp emin (fprec t)) (FT2R a + FT2R b).
  { apply Plus_error.FLT_format_plus_small;
    try rewrite -B2R_float_of_ftype;
    try apply (Binary.generic_format_B2R (fprec t) (femax t)).
    apply (fprec_gt_0 t). apply Rlt_le. 
    try rewrite -FT2R_ftype_of_float ftype_of_float_of_ftype.
    refine (Rlt_le_trans _ _ _ BND _). 
    apply bpow_le; fold emin; lia. } 
rewrite !BPLUS_UF_exact => //. f_equal.
rewrite round_generic => //. 
by apply (generic_format_FLX_FLT _ emin).
set (f1:= (BMINUS a (BMINUS (BPLUS a b) b))) in *.
set (f2:= (BMINUS b (BMINUS (BPLUS a b) 
  (BMINUS (BPLUS a b) b)))) in *.
BPLUS_correct t f1 f2; subst f1 f2; clear H4.
set (f3:= (BMINUS (BPLUS a b) b)) in *.
rewrite -is_finite_Binary in H2. 
BMINUS_correct t a f3; subst f3; clear H6. 
set (f4:= (BPLUS a b)) in *.
rewrite -is_finite_Binary in H5. 
BMINUS_correct t f4 b; subst f4; clear H8.
set (f5:= (BMINUS (BPLUS a b) 
  (BMINUS (BPLUS a b) b))) in *.
rewrite -is_finite_Binary in H3.
 rewrite -!FT2R_ftype_of_float !ftype_of_float_of_ftype.
BMINUS_correct t b f5; subst f5; clear H10.
set (f4:= (BPLUS a b)) in *.
set (f6:= (BMINUS f4 b)) in *. 
rewrite -is_finite_Binary in H9.
BMINUS_correct t f4 f6; subst f6; clear H12.
rewrite -is_finite_Binary in H11.
BMINUS_correct t f4 b; subst f4; clear H14. 
 rewrite -!FT2R_ftype_of_float !ftype_of_float_of_ftype.
rewrite !BPLUS_UF_exact => //.
rewrite -!B2R_float_of_ftype.
rewrite -!B2R_float_of_ftype in A.
rewrite !round_generic => //;
match goal with |- context [generic_format _ _ ?A] =>
    try field_simplify A end; 
(try apply: Binary.generic_format_B2R;
try apply (generic_format_FLX_FLT _ emin);
try apply: Binary.generic_format_B2R;
try apply: generic_format_0) => //. }
by apply TwoSumEq_no_underflow.
Qed.

Lemma TwoSum0 : 
FT2R a = 0 -> 
F2Rp (TwoSumF a b) = (FT2R b,0).
Proof.
move: FIN. 
rewrite /F2Rp/fst/snd/TwoSumF/is_finite_p/fst/snd.
move => [] FIN1 FIN2 H. 
f_equal. BPLUS_correct t a b. clear H5.  
fold (@FT2R t); rewrite H Rplus_0_l.
rewrite -!B2R_float_of_ftype.
apply round_generic. 
apply BinarySingleNaN.valid_rnd_round_mode.
try apply Binary.generic_format_B2R. 
set (y3:= (BMINUS (BPLUS a b) b)) in *. 
set (y1:= (BMINUS a y3)) in *. 
set (y2:= (BMINUS b (BMINUS (BPLUS a b) y3))) in *. 
BPLUS_correct t y1 y2; clear H5; subst y1 y2.
rewrite -is_finite_Binary in H3.
BMINUS_correct t a y3; clear H7.
 rewrite -!FT2R_ftype_of_float !ftype_of_float_of_ftype.
rewrite H Rminus_0_l round_NE_opp.
rewrite -(round_0
radix2 (SpecFloat.fexp (fprec t) (femax t))
        (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)).
f_equal.
set (y5:= (BMINUS (BPLUS a b) y3)) in *.
rewrite -is_finite_Binary in H4.
BMINUS_correct t b y5. clear H9.
rewrite Rplus_comm Rplus_opp.
apply Rminus_diag_eq. f_equal; subst y5.
rewrite -is_finite_Binary in H8.
BMINUS_correct t (BPLUS a b) y3. clear H11.
BPLUS_correct t a b. 
 rewrite -!FT2R_ftype_of_float !ftype_of_float_of_ftype.
  rewrite H Rplus_0_l; clear H13.
subst y3.
rewrite -is_finite_Binary in H10.
BMINUS_correct t (BPLUS a b) b; clear H15.
BPLUS_correct t a b.
 rewrite -!FT2R_ftype_of_float !ftype_of_float_of_ftype;
rewrite H Rplus_0_l.
rewrite !round_generic; try nra;
match goal with |-context [generic_format _ _ ?a] => 
  field_simplify a
end; try rewrite -B2R_float_of_ftype;
    try apply Binary.generic_format_B2R;
    try apply:generic_format_0.
Qed.

End TwoSumCorrect.

Section TwoSumAcc. 

Context {NANS: Nans} {t : type} {STD: is_standard t}.

Variables (a b : ftype t).

Notation emin := (@DD.DDModels.emin t).

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
BPLUS_correct t a b. 
rewrite !B2R_float_of_ftype; auto. 
Qed.

End TwoSumAcc.

Section FastTwoSumCorrect.

Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation FE := (FLT_exp (@emin t) (fprec t)).
Notation emin := (@DD.DDModels.emin t).

Lemma Fast2Sum_2sum0 (xl: ftype t): 
F2Sum.Fast2Sum (fprec t) choice 0
  (round radix2 (FLX_exp (fprec t)) (Znearest choice)
     (FT2R xl)) = (FT2R xl, 0).
Proof.
rewrite /F2Sum.Fast2Sum/Fast2Sum 
  Rplus_0_l Rminus_0_r !round_generic.
f_equal; nra.
all: apply (generic_format_FLX_FLT radix2 emin);
try rewrite -B2R_float_of_ftype;
try apply Binary.generic_format_B2R.
rewrite Rminus_eq_0; 
  apply generic_format_0.
Qed.

Lemma Fast2Sum_2sum0' (xl a b: ftype t): 
FT2R a = 0 -> FT2R b = 0 -> 
is_finite_p (DDModels.Fast2Sum a (BPLUS xl b)) -> 
F2Rp (DDModels.Fast2Sum a (BPLUS xl b)) = (FT2R xl,0). 
Proof.
move => H1 H2.
rewrite /is_finite_p/DDModels.Fast2Sum/F2Rp/fst/snd; 
  move => [] FIN1 FIN2.
set (f:= (BPLUS xl b)) in *.
f_equal.
{ BPLUS_correct t a f; fold (@FT2R t).
rewrite H1 Rplus_0_l; subst f.
rewrite -is_finite_Binary in H5.
BPLUS_correct t xl b; 
try rewrite -B2R_float_of_ftype;
rewrite H2 Rplus_0_r !round_generic; try nra.
all: try apply (generic_format_FLX_FLT radix2 emin);
try apply Binary.generic_format_B2R. } 
set (f1:= (BMINUS (BPLUS a f) a)) in *. 
BMINUS_correct t f f1; subst f.
rewrite -is_finite_Binary in H4.
BPLUS_correct t xl b; fold (@FT2R t); 
rewrite H2 Rplus_0_r.
subst f1.
set (f1:= BPLUS a (BPLUS xl b)) in *.
rewrite -is_finite_Binary in H5.
try rewrite B2R_float_of_ftype.
BMINUS_correct t f1 a. 
try rewrite B2R_float_of_ftype.
  rewrite H1 Rminus_0_r. 
subst f1.  
set (f1:= (BPLUS xl b)) in *.
rewrite -is_finite_Binary in H10.
BPLUS_correct t a f1. subst f1;
try rewrite B2R_float_of_ftype.
  rewrite H1 Rplus_0_l. 
BPLUS_correct t xl b; 
try rewrite B2R_float_of_ftype;
rewrite H2 Rplus_0_r !round_generic; try nra.
all: try rewrite -B2R_float_of_ftype;
  try apply (generic_format_FLX_FLT radix2 emin);
try apply Binary.generic_format_B2R. 
rewrite Rminus_eq_0; apply generic_format_0.
Qed.


Variables (a b : ftype t).
Hypothesis FIN : is_finite_p (DD.DDModels.Fast2Sum a b).
Hypothesis Hle : Rabs (FT2R b) <= Rabs (FT2R a).

Theorem FastTwoSum_correct :
  FT2R (Fast2Sum_err a b) = FT2R a + FT2R b - FT2R (Fast2Sum_sum a b).
Proof.
set (s := BPLUS a b).
set (z := BMINUS s a).
move: FIN.
rewrite /Fast2Sum_err/Fast2Sum_sum/DDModels.Fast2Sum/fst/snd/=.
move => []; rewrite /fst/snd; fold s z; move => FINs FINd.
BMINUS_correct t b z; field_simplify. clear H4.
unfold z.
have FINsa: is_finite z = true by rewrite is_finite_Binary.
unfold z in FINsa.
BMINUS_correct t s a; field_simplify. unfold s in *. BPLUS_correct t a b; field_simplify.
have Ga: generic_format radix2 (FLT_exp emin (fprec t)) (FT2R a) by
  rewrite -B2R_float_of_ftype;
  apply (Binary.generic_format_B2R (fprec t) (femax t)).
have Gb: generic_format radix2 (FLT_exp emin (fprec t)) (FT2R b) by
  rewrite -B2R_float_of_ftype;
  apply (Binary.generic_format_B2R (fprec t) (femax t)).
have Hr : (radix2 <= 3)%Z by (simpl; auto).
(** apply lemmas from paper_proofs.F2SumFLT *)
have: Fast2Sum_correct_flt radix2 emin (fprec t) choice (FT2R a) (FT2R b). 
apply F2Sum_correct_abs_flt => //. apply (fprec_gt_one t).
rewrite /Fast2Sum_correct_flt/Fast2Sum_flt/fst/snd; 
  rewrite -!B2R_float_of_ftype;
  move => H. rewrite H; f_equal.
  rewrite -!B2R_float_of_ftype in H9.
  rewrite /BPLUS/BINOP float_of_ftype_of_float => //.
Qed.

Theorem Fast2Sum_is_DW: 
  double_word (Fast2Sum_sum a b) (Fast2Sum_err a b).
Proof.
  rewrite /double_word FastTwoSum_correct // /Fast2Sum_sum /= /common.rounded. 
destruct FIN as (FINm & FINp).
unfold Fast2Sum_err, Fast2Sum_sum, DDModels.Fast2Sum, fst, snd in *.
  BPLUS_correct t a b.
by rewrite -!B2R_float_of_ftype.
Qed.

Lemma FastTwoSumEq_no_underflow  
  (HU1 : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R a + FT2R b)):
  DD.paper_proofs.F2Sum.Fast2Sum (fprec t) choice (FT2R a) (FT2R b) = F2Rp (DD.DDModels.Fast2Sum a b).
Proof.
rewrite /DD.DDModels.Fast2Sum.
move : FIN. move => []. 
pose proof round_FLT_FLX radix2 emin. 
pose proof @DD.paper_proofs.F2SumFLX.F2Sum_correct_proof
  radix2 (fprec t). rewrite /F2SumFLX.Fast2Sum_correct in H0.
have Heq1 : F2Sum.Fast2Sum (fprec t) choice (FT2R a) (FT2R b) = 
  (fst (DD.paper_proofs.F2Sum.Fast2Sum (fprec t) choice (FT2R a) (FT2R b)), 
    snd (DD.paper_proofs.F2Sum.Fast2Sum (fprec t) choice (FT2R a) (FT2R b))).
{ simpl; auto. }
rewrite Heq1.
have Heq2 : DD.DDModels.Fast2Sum a b = 
  (DD.DDModels.Fast2Sum_sum a b, DD.DDModels.Fast2Sum_err a b).
{ simpl; auto. }
rewrite Heq2 /F2Rp.
clear Heq1 Heq2.
move => FIN1 FIN2.
have Heq : 
fst (DD.paper_proofs.F2Sum.Fast2Sum (fprec t) choice (FT2R a) (FT2R b)) = FT2R (DD.DDModels.Fast2Sum_sum a b).
{ move: FIN1. rewrite /DD.DDModels.Fast2Sum_err/DD.DDModels.Fast2Sum_sum/F2Rp/fst/snd/=. move => FIN1.
BPLUS_correct t a b; field_simplify. 
rewrite -!B2R_float_of_ftype H => //. 
by rewrite !B2R_float_of_ftype.  }
f_equal => //.
rewrite DD.accuracy_proofs.TwoSum_acc.FastTwoSumCorrect.FastTwoSum_correct. 
rewrite DD.paper_proofs.F2SumFLX.F2Sum_correct_abs => //. f_equal => //.
apply fprec_gt_one.
apply Bayleyaux.rnd_p_sym. apply choiceP.
all: apply (@generic_format_FLX_FLT radix2 emin); 
rewrite -B2R_float_of_ftype;
apply Binary.generic_format_B2R.
Qed.

(* the result of the FLT format algorithm and the FLX format algorithm are 
  equal, regardless of underflow. *)
Lemma FastTwoSumEq_FLT : 
  DD.paper_proofs.F2Sum.Fast2Sum (fprec t) choice (FT2R a) (FT2R b) = F2Rp (DD.DDModels.Fast2Sum a b).
Proof.
move : FIN; clear FIN. rewrite /DDModels.Fast2Sum/is_finite_p/fst/snd.
move => FIN; destruct FIN as (FINA & FINB).
rewrite /DD.DDModels.Fast2Sum/F2Sum.Fast2Sum/Fast2Sum/F2Rp/fst/snd.
destruct (Rlt_or_le (Rabs (FT2R a + FT2R b)) (bpow radix2 (emin + fprec t - 1)) ) as
   [BND | BND].
{ have A : generic_format radix2 (FLT_exp emin (fprec t)) (FT2R a + FT2R b).
  { apply Plus_error.FLT_format_plus_small;
    try rewrite -B2R_float_of_ftype;    
    try apply (Binary.generic_format_B2R (fprec t) (femax t)).
    apply (fprec_gt_0 t). apply Rlt_le.
    rewrite B2R_float_of_ftype.
    refine (Rlt_le_trans _ _ _ BND _). 
    apply bpow_le; fold emin; lia. } 
rewrite !BPLUS_UF_exact => //. f_equal.
rewrite round_generic => //. 
by apply (generic_format_FLX_FLT _ emin).
set (y:= (BMINUS (BPLUS a b) a)) in *.
BMINUS_correct t b y.
subst y.
rewrite -is_finite_Binary in H3.
BMINUS_correct t (BPLUS a b) a.
    rewrite B2R_float_of_ftype.
rewrite !BPLUS_UF_exact => //.
rewrite -!B2R_float_of_ftype.
rewrite -!B2R_float_of_ftype in A.
rewrite !round_generic => //;
match goal with |- context [generic_format _ _ ?A] =>
    try field_simplify A end; 
(try apply: Binary.generic_format_B2R;
try apply (generic_format_FLX_FLT _ emin);
try apply: Binary.generic_format_B2R;
try apply: generic_format_0) => //. }
by apply FastTwoSumEq_no_underflow.
Qed.

End FastTwoSumCorrect.

Section FastTwoSumAcc.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Variables (a b : ftype t).
Hypothesis FIN : is_finite_p (DD.DDModels.Fast2Sum a b).
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
BPLUS_correct t a b. 
by rewrite !B2R_float_of_ftype.
Qed.


End FastTwoSumAcc.


