Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics.
Require Import DDModels TwoMult_acc TwoSum_acc.
From Flocq Require Import Pff2Flocq Core.

Section AccuracyDWPlusFP.
Context {NANS: Nans} {t : type}.

Variables (a b c : ftype t).
Notation zh := (FT2R (fst (DWPlusFP a b c))).
Notation zl := (FT2R (snd (DWPlusFP a b c))).
Notation x  := (FT2R a + FT2R b).
Notation y  := (FT2R c).

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 
Notation u   := (bpow Zaux.radix2 (- fprec t)).

Definition relative_errorDWPlusFP := Rabs (((zh + zl) - (x  + y)) / (x  + y)).

Hypothesis FIN  : is_finite_p (DWPlusFP a b c). 
Hypothesis DWab : double_word a b. 

Theorem relative_errorDWPlusFP_correct : relative_errorDWPlusFP <= 2 * u ^ 2.
Proof.
Admitted.

End AccuracyDWPlusFP.

