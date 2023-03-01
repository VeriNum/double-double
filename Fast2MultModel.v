(* This file contains the floating-point functional model in IEEE-754
  format of the Fast2SMult algorithm, along with a theorem regarding the 
  correctness of the Fast2SMult algorithm *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs.
From Flocq Require Import Pff2Flocq.

Section Fast2MultModel.

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

Definition Fast2Mult (a b : ftype t) :=
let m := BMULT a b in
let p := BFMA a b (BOPP m) in (m, p).

Definition Fast2Mult_err (a b : ftype t) := snd (Fast2Mult a b).
Definition Fast2Mult_mul (a b : ftype t) := fst (Fast2Mult a b).
Lemma Fast2MultModel_correct (a b : ftype t) (FIN : is_finite_p (Fast2Mult a b) ) :
  FT2R a * FT2R b = FT2R (Fast2Mult_mul a b) + FT2R (Fast2Mult_err a b).
Proof.
set (m := BMULT a b).
set (p := BFMA a b (BOPP m)).
destruct FIN as (FINm & FINp).
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

pose proof generic_fmt_fexp_FLT t as Hgen; fold choice emin in Hgen.

pose proof (Binary.Bfma_correct  (fprec t) (femax t) 
  (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan t) BinarySingleNaN.mode_NE) a b (BOPP m)
  FINa FINb FINm2 as A. 
pose proof (is_finite_fma_no_overflow t a b (BOPP m) FINp) as HOV; cbv zeta in A.
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
pose proof (is_finite_BMULT_no_overflow t a b FINm) as HOV; cbv zeta in B.
apply Rlt_bool_true in HOV; unfold FT2R, common.rounded in HOV; rewrite HOV in B; clear HOV;
  destruct B as (B & _); unfold BMULT, BINOP, FT2R.
  rewrite Hgen in B; rewrite B; clear B.

pose proof Generic_fmt.round_generic (Zaux.radix2) (FLT.FLT_exp emin (fprec t))
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

pose proof Mult_error.mult_error_FLT (Zaux.radix2) emin (fprec t)
  (Generic_fmt.Znearest choice) (FT2R a) (FT2R b) as Hc; 
unfold FT2R in Hc.
subst x1; subst x2.
apply Hc. 
apply Binary.generic_format_B2R.
apply Binary.generic_format_B2R.
intros.
admit.
subst m.
unfold BOPP.
rewrite Binary.B2R_Bopp; auto.
Admitted.

End WITHNANS.

End Fast2MultModel.