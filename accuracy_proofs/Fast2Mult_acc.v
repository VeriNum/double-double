Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs common dd_tactics.
Require Import DDModels.
From Flocq Require Import Pff2Flocq Core.

Require Import mathcomp.ssreflect.ssreflect.

Section TwoMultCorrect.
Context {NANS: Nans} {t : type} {STD: is_standard t}.
Notation emin := (@DD.DDModels.emin t).
Variables (a b : ftype t).
Hypothesis (FIN : is_finite_p (Fast2Mult a b)).
Hypothesis (UF  :  (FT2R a * FT2R b) <> 0 -> 
  bpow Zaux.radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R a * FT2R b)). 


Lemma Fast2MultModel_correct :
  FT2R (Fast2Mult_err a b) =  FT2R a * FT2R b - FT2R (Fast2Mult_mul a b).
Proof.
set (m := BMULT a b).
set (p := BFMA a b (BOPP m)).
destruct FIN as (FINm & FINp). 
unfold Fast2Mult_mul, Fast2Mult_err, fst, snd in *; simpl in *.
fold m in FINp. fold m.
BFMA_correct t a b (BOPP m).
unfold m.
rewrite -!B2R_float_of_ftype.
unfold BOPP. rewrite float_of_ftype_of_float.
rewrite Binary.B2R_Bopp.
rewrite !B2R_float_of_ftype.
BMULT_correct t a b.
(* rewriting correctly here requires some careful manipulation *)
set (y:= round radix2 
        (SpecFloat.fexp (fprec t) (femax t)) 
      (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) (Binary.B2R _ _ 
    (float_of_ftype a) * Binary.B2R _ _ (float_of_ftype b)) ).
set (x:= (Binary.B2R _ _ 
        (float_of_ftype a) * Binary.B2R _ _ (float_of_ftype b) - y)).
rewrite (Generic_fmt.round_generic (Zaux.radix2) (FLT.FLT_exp emin (fprec t))
  (Generic_fmt.Znearest choice)); auto.
subst y; subst x. 
rewrite !B2R_float_of_ftype.
set (x1:= FT2R a * FT2R b).
set (x2:= round radix2 
        (SpecFloat.fexp (fprec t) (femax t)) 
      (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) x1).
replace (x1 - x2) with ( - (x2 - x1)) by nra.
apply Generic_fmt.generic_format_opp.
subst x1 x2.
apply (Mult_error.mult_error_FLT (Zaux.radix2) emin (fprec t)
  (Generic_fmt.Znearest choice) (FT2R a) (FT2R b)).
1,2: rewrite -!B2R_float_of_ftype;
apply Binary.generic_format_B2R.
(* use hyp of no underflow *)
apply UF.
Qed.

Lemma TwoMult_is_DW : 
  double_word (Fast2Mult_mul a b) (Fast2Mult_err a b).
Proof.
  rewrite /double_word Fast2MultModel_correct // /TwoSumF_sum /= /common.rounded. 
destruct FIN as (FINm & FINp).
unfold Fast2Mult_mul, Fast2Mult_err, Fast2Mult, fst, snd in *.
  BMULT_correct t a b.
by rewrite -!B2R_float_of_ftype.
Qed.

End TwoMultCorrect.

Section TwoMultAcc. 
Context {NANS: Nans} {t : type} {STD: is_standard t}.
Notation emin := (@DD.DDModels.emin t).
Variables (a b : ftype t).
Hypothesis (FIN : is_finite_p (Fast2Mult a b)).

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 
Notation u   := (bpow Zaux.radix2 (- fprec t)).

Theorem Fast2Mult_accuracy_norm: 
forall UF  :  (FT2R a * FT2R b) <> 0 -> 
  bpow Zaux.radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R a * FT2R b),
    Rabs (FT2R (Fast2Mult_err a b))  <= /2 * ulp (FT2R a * FT2R b).
Proof.
intros; rewrite Fast2MultModel_correct; auto. unfold Fast2Mult_mul. simpl.
rewrite Rabs_minus_sym. 
pose proof error_le_half_ulp
  Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) choice (FT2R a * FT2R b) as HE.
destruct FIN as (FINs & FINd); simpl in FINs. 
BMULT_correct t a b. 
by rewrite !B2R_float_of_ftype.
Qed.

(*
Theorem Fast2Mult_accuracy: 
    Rabs (FT2R (Fast2Mult_err a b))  <= 3/4 * ulp (FT2R a * FT2R b).
Proof.
rewrite /Fast2Mult_err/Fast2Mult/snd.
set (m := BMULT a b).
destruct FIN as (FINm & FINp). 
unfold Fast2Mult_mul, Fast2Mult_err, fst, snd in FINm, FINp.
  simpl in FINm, FINp.
fold m in FINp. 
BFMA_correct t a b (BOPP m).
rewrite Binary.B2R_Bopp.
match goal with |-context [round _ _ _ ?z] => 
  set y:= z
end.
destruct (Rle_or_lt (bpow radix2 (emin + fprec t - 1)) (Rabs y)) as [Hy|Hy].
{ destruct (@relative_error_FLT t y choice Hy) as (del & A & B).
rewrite B; subst y; unfold m. 
BMULT_correct t a b.
set (x:= (Binary.B2R (fprec t) (femax t) a * Binary.B2R (fprec t) (femax t) b)).
rewrite Rabs_mult.
match goal with |-context [Rabs (?z + - ?y)] => 
  replace (Rabs ((z + - y))) with 
      (Rabs ((y - z)))
end.
refine (Rle_trans _ _ _ _ _).
apply Rmult_le_compat_r; [apply Rabs_pos|].
apply error_le_half_ulp; apply Binary.fexp_correct;
  apply (fprec_gt_0 t).
refine (Rle_trans _ _ _ (Rmult_le_compat_l _ _ _ _ _) _).
apply Rmult_le_pos; [nra | apply ulp_ge_0 ].
now apply (@relative_er_ub_FLT t).
nra.
rewrite <- Rabs_Ropp.
f_equal. nra. }
destruct (@absolute_error_FLT_UF t y choice Hy) as (eta & A & B).
rewrite B; subst y; unfold m. 
BMULT_correct t a b.
set (x:= (Binary.B2R (fprec t) (femax t) a * Binary.B2R (fprec t) (femax t) b)).
refine (Rle_trans _ _ _ (Rabs_triang _ _ ) _).
match goal with |-context [Rabs (?z + - ?y)] => 
  replace (Rabs ((z + - y))) with 
      (Rabs ((y - z)))
end.
refine (Rle_trans _ _ _ (Rplus_le_compat _ _ _ _ _ _) _).
apply error_le_half_ulp; apply Binary.fexp_correct;
  apply (fprec_gt_0 t).
refine (Rle_trans _ _ (1/4 * ulp x) A _).
unfold float_acc_lems.emin, SpecFloat.emin.
Search SpecFloat.emin.
Prec_gt_0

Search (1 < fprec _)%Z.
Search ( _ < _ -> _ <= _)%Z.
Search (_ - _ <= _)%Z.
Search (bpow _ _ <= bpow _ _).

apply A. 
refine (Rle_trans _ _ _   (Rplus_le_compat_l _ _ _ _) _).
refine (Rle_trans _ _ _ _ _).
apply (Rplus_le_compat_l). apply A. 

Search (_ < fprec _)%Z.


refine (Rle_trans _ _ _ (Rabs_le_minus _ _ _ _) _).
apply error_le_half_ulp; apply Binary.fexp_correct; admit. 
subst y.
unfold m. 
BMULT_correct t a b.
set (x:= (Binary.B2R (fprec t) (femax t) a * Binary.B2R (fprec t) (femax t) b)).
match goal with |-context [Rabs (?z + - ?y)] => 
  replace (Rabs ((z + - y))) with 
      (Rabs ((y - z)))
end.
match goal with |-context [ulp (?z + - ?y)] => 
  replace (ulp ((z + - y))) with 
      (ulp ((y - z)))
end.
destruct (Req_dec x 0) as [Hab |Hab].
{ rewrite Hab round_0. admit. } 
refine (Rle_trans _ _ _ (Rplus_le_compat _ _ _ _ _ _) _).
refine (Rmult_le_compat_l _ _ _ _ _ ); [nra|].

round_ge_generic
Search (Ulp.ulp _ _ (Ulp.ulp _ _ _)).
Search (_  + _ <= _ + _).
pose proof error_le_ulp radix2 (SpecFloat.fexp (fprec t) (femax t)) 
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE). 

(Binary.B2R (fprec t) (femax t) a * Binary.B2R (fprec t) (femax t) b)
rewrite round_NE_opp.
pose proof error_le_ulp. 
match goal with |-context [round _ _ _ ?z] => 
  set y:= z
end.

Search (bpow _ (_ + 2 * _ - 1)).

destruct (@absolute_error_FLT_UF t (FT2R a * FT2R b) choice) as
  (eta & A & B); auto.
refine (Rlt_trans _ _ _ UF _). 
apply bpow_lt; unfold emin, float_acc_lems.emin. lia. 
subst y; rewrite B; unfold FT2R.
match goal with |-context [round _ _ _ ?a] => 
  field_simplify a
end.
rewrite round_NE_opp.
unfold ulp. simpl.
Search round Rle.

destruct 
  (Relative.relative_error_N_FLT'_ex_separate radix2 emin (fprec t)
  (fprec_gt_0 t) choice y) as (y' & B & [eta[D]] & _ & _). 
eapply Rle_trans. 2: apply error_le_half_ulp.
refine (Rle_trans _ _ _ (error_le_half_ulp _ _ _ _) _);
    [now apply FLT_exp_valid|]. 
Relative.relative_error_N_FLX'_ex
pose proof error_le_half_ulp
  Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) choice (FT2R a * FT2R b) as HE.


generic_round_property
destruct (Req_dec (FT2R a * FT2R b) 0) as [Hab |Hab].
rewrite Fast2MultModel_correct; auto. unfold Fast2Mult_mul. simpl.
rewrite Rabs_minus_sym. 
pose proof error_le_half_ulp
  Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) choice (FT2R a * FT2R b) as HE.
destruct FIN as (FINs & FINd); simpl in FINs. 
BMULT_correct t a b. fold (@FT2R t); auto.
Qed.
*)

End TwoMultAcc.

