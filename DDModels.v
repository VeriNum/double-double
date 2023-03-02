(* This file contains the floating-point functional models in IEEE-754
  format for the 2Sum and Fast2Mult implementations.*)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs.

Section Format.
Context {t : type}.

Definition emin := SpecFloat.emin (fprec t) (femax t).
Fact emin_le_0 : (emin <= 0)%Z. 
Proof. pose proof @fprec_lb t; pose proof @femax_lb t; 
unfold emin, SpecFloat.emin; lia. Qed.

Definition choice:= fun x0 : Z => negb (Z.even x0).
Fact choiceP (x : Z) : choice x = negb (choice (- (x + 1))%Z).
Proof. unfold choice; rewrite Z.even_opp, Z.even_add; 
destruct (Z.even x); auto. Qed.

End Format.


Section TwoSumModel.
Context {NANS: Nans} {t : type}.

Definition TwoSumF (a b : ftype t) :=
let s  := BPLUS a b in
let a' := BMINUS s b in
let b' := BMINUS s a' in
let da := BMINUS a a' in
let db := BMINUS b b' in (BPLUS a b, BPLUS da db).

Definition TwoSumF_err (a b : ftype t) := snd (TwoSumF a b).
Definition TwoSumF_sum (a b : ftype t) := fst (TwoSumF a b).

End TwoSumModel.


Section Fast2MultModel.
Context {NANS: Nans} {t : type}.

Definition Fast2Mult (a b : ftype t) :=
let m := BMULT a b in
let p := BFMA a b (BOPP m) in (m, p).

Definition Fast2Mult_err (a b : ftype t) := snd (Fast2Mult a b).
Definition Fast2Mult_mul (a b : ftype t) := fst (Fast2Mult a b).

End Fast2MultModel.