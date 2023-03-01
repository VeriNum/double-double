(* This file contains the floating-point functional model in IEEE-754
  format of the 2Sum algorithm, along with a theorem regarding the 
  correctness of the 2Sum algorithm *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems.
From Flocq Require Import Pff2Flocq.

Section TwoSumModel.

Variable (t : type).

Definition is_finite_p (xy : ftype t * ftype t) : Prop :=
  Binary.is_finite _ _ (fst xy) = true /\ Binary.is_finite _ _ (snd xy) = true.

Definition emin := SpecFloat.emin (fprec t) (femax t).
Fact emin_le_0 : (emin <= 0)%Z. 
Proof. pose proof fprec_lb t; pose proof femax_lb t; 
unfold emin, SpecFloat.emin; lia. Qed.

Definition choice:= fun x0 : Z => negb (Z.even x0).
Fact choiceP (x : Z) : choice x = negb (choice (- (x + 1))%Z).
Proof. unfold choice; rewrite Z.even_opp, Z.even_add; 
destruct (Z.even x); auto. Qed.

Section WITHNANS.
Context {NANS: Nans}.

Definition TwoSumF (a b : ftype t) :=
let s  := BPLUS a b in
let a' := BMINUS s b in
let b' := BMINUS s a' in
let da := BMINUS a a' in
let db := BMINUS b b' in (BPLUS a b, BPLUS da db).

Definition TwoSumF_err (a b : ftype t) := snd (TwoSumF a b).
Definition TwoSumF_sum (a b : ftype t) := fst (TwoSumF a b).
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
pose proof (TwoSum_correct emin (fprec t) choice 
    (fprec_gt_one t) emin_le_0 choiceP (FT2R b) (FT2R a)) as Hc.
rewrite Rplus_comm; rewrite <- Hc; clear Hc.
pose proof generic_fmt_fexp_FLT t as Hgen; fold choice emin in Hgen.
(* invoke flocq binary op correctness theorems for rewrites *)
unfold TwoSumF_err, TwoSumF_sum, TwoSumF, fst, snd.
fold s a' b' da db; unfold s.
rewrite <- Rplus_opp, Rplus_comm, <- Rplus_assoc.
pose proof (Binary.Bplus_correct  (fprec t) (femax t) 
  (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE a b FINa FINb) as S.
pose proof (is_finite_sum_no_overflow t a b FINs) as HOV.
replace (FT2R b + FT2R a) with (FT2R a + FT2R b) by nra.
apply Rlt_bool_true in HOV; unfold FT2R in HOV; rewrite HOV in S; clear HOV; 
  destruct S as (S & _); unfold BPLUS, BINOP, FT2R; 
  rewrite Hgen in S; rewrite S; field_simplify.
pose proof (Binary.Bplus_correct  (fprec t) (femax t) 
  (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE da db FINda FINdb) as D.
pose proof (is_finite_sum_no_overflow t da db FINd) as HOV.
apply Rlt_bool_true in HOV; unfold FT2R in HOV; rewrite HOV in D; clear HOV;
  destruct D as (D & _); unfold BPLUS, BINOP, FT2R; 
  rewrite Hgen in D; rewrite D; f_equal.
rewrite Rplus_comm; f_equal.
subst db.
pose proof (Binary.Bminus_correct  (fprec t) (femax t) 
  (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE b b' FINb FINb') as DB.
pose proof (is_finite_minus_no_overflow t b b' FINdb) as HOV.
apply Rlt_bool_true in HOV; unfold FT2R in HOV; rewrite HOV in DB; clear HOV;
  destruct DB as (DB & _); unfold BMINUS, BINOP, FT2R; 
  rewrite Hgen in DB; rewrite DB; repeat f_equal.
subst b'.
pose proof (Binary.Bminus_correct  (fprec t) (femax t) 
  (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE s a' FINs FINa') as DB'.
pose proof (is_finite_minus_no_overflow t s a' FINb') as HOV.
apply Rlt_bool_true in HOV; unfold FT2R in HOV; rewrite HOV in DB'; clear HOV;
  destruct DB' as (DB' & _); unfold BMINUS, BINOP, FT2R; 
  rewrite Hgen in DB'; rewrite DB'; repeat f_equal.
{ subst s. unfold BPLUS, BINOP, FT2R; apply S. } 
{ subst a'.
  pose proof (Binary.Bminus_correct  (fprec t) (femax t) 
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE s b FINs FINb) as DA'.
  pose proof (is_finite_minus_no_overflow t s b FINa') as HOV.
  apply Rlt_bool_true in HOV; unfold FT2R in HOV; rewrite HOV in DA'; clear HOV;
    destruct DA' as (DA' & _); unfold BMINUS, BINOP, FT2R; 
    rewrite Hgen in DA'; rewrite DA'; repeat f_equal.
  { subst s. unfold BPLUS, BINOP, FT2R; apply S. } 
}
subst da.
pose proof (Binary.Bminus_correct  (fprec t) (femax t) 
  (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE a a' FINa FINa') as DA.
pose proof (is_finite_minus_no_overflow t a a' FINda) as HOV.
apply Rlt_bool_true in HOV; unfold FT2R in HOV; rewrite HOV in DA; clear HOV;
  destruct DA as (DA & _); unfold BMINUS, BINOP, FT2R; 
  rewrite Hgen in DA; rewrite DA; repeat f_equal.
{ subst a'.
  pose proof (Binary.Bminus_correct  (fprec t) (femax t) 
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE s b FINs FINb) as DA'.
  pose proof (is_finite_minus_no_overflow t s b FINa') as HOV.
  apply Rlt_bool_true in HOV; unfold FT2R in HOV; rewrite HOV in DA'; clear HOV;
    destruct DA' as (DA' & _); unfold BMINUS, BINOP, FT2R; 
    rewrite Hgen in DA'; rewrite DA'; repeat f_equal.
  { subst s. unfold BPLUS, BINOP, FT2R; apply S. } 
}
apply Binary.generic_format_B2R.
apply Binary.generic_format_B2R.
Qed.

End WITHNANS.

End TwoSumModel.