(* This file contains basic definitions and lemmas common to all other files in 
  the repository. *)

Require Import vcfloat.VCFloat.
Require Import mathcomp.ssreflect.ssreflect.

Definition rounded (t: type) (r : R) :=
(Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
     (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) r).

Definition neg_zero {t: type} := Binary.B754_zero (fprec t) (femax t) true.

Section FinDefs.

Definition is_finite_p {t : type} {STD: is_standard t} 
  (a : ftype t * ftype t)  := is_finite (fst a) = true /\ is_finite (snd a) = true.

Definition F2Rp  {t : type} (a : ftype t * ftype t) := (FT2R (fst a), FT2R (snd a)).

End FinDefs.

Section EVars.

Definition default_rel (t : type) : R :=
  / 2 * Raux.bpow Zaux.radix2 (- fprec t + 1).

Definition default_abs  (t : type) : R :=
  / 2 * Raux.bpow Zaux.radix2 (3 - femax t - fprec t).

Fact default_rel_sep_0 (t : type) : 
  default_rel t <> 0.
Proof. 
unfold default_rel; apply Rabs_lt_pos.
rewrite Rabs_pos_eq; [apply Rmult_lt_0_compat; try nra; apply bpow_gt_0 | 
  apply Rmult_le_pos; try nra; apply bpow_ge_0].
Qed.

Fact default_rel_gt_0 (t : type)  : 
  0 < default_rel t.
Proof. 
unfold default_rel.
apply Rmult_lt_0_compat; try nra.
apply bpow_gt_0.
Qed.
 
Lemma default_rel_ge_0 (t : type)  : 
  0 <= default_rel t.
Proof. apply Rlt_le; apply default_rel_gt_0; auto. Qed.

Fact default_rel_plus_1_ge_1 (t : type)  :
1 <= 1 + default_rel t.
Proof. 
rewrite Rplus_comm. 
apply Rcomplements.Rle_minus_l; field_simplify.
apply default_rel_ge_0.
Qed.

Fact default_rel_plus_1_gt_1 (t : type)  :
1 < 1 + default_rel t.
Proof.
rewrite Rplus_comm. 
apply Rcomplements.Rlt_minus_l; field_simplify.
apply default_rel_gt_0.
Qed.

Fact default_rel_plus_1_gt_0 (t : type)  :
0 < 1 + default_rel t.
Proof.
eapply Rlt_trans with 1; [nra | ].
apply default_rel_plus_1_gt_1.
Qed.

Fact default_rel_plus_1_ge_1' (t : type) (n : nat):
1 <= (1 + default_rel t) ^ n.
Proof. 
induction n; simpl; auto; try nra.
eapply Rle_trans with (1 * 1); try nra.
apply Rmult_le_compat; try nra.
apply default_rel_plus_1_ge_1.
Qed.

Fact default_abs_gt_0 (t : type) : 
  0 < default_abs t.
Proof. 
unfold default_abs.
apply Rmult_lt_0_compat; try nra.
apply bpow_gt_0.
Qed.

Fact default_abs_ge_0 (t : type) :
  0 <= default_abs t.
Proof. apply Rlt_le; apply default_abs_gt_0; auto. Qed.

End EVars.

Section PrecFacts.
Variable (t : type).

Lemma fprec_lb :
  (2 <= fprec t)%Z.
Proof. pose proof ( fprec_gt_one t); lia. Qed.

Lemma femax_lb :
  (3 <= femax t)%Z.
Proof. 
pose proof fprec_lb;
pose proof fprec_lt_femax t; lia. 
Qed.

Fact fprec_gt_1 : 
  (1 < fprec t)%Z.
Proof. pose proof @fprec_lb ; lia. Qed.

End PrecFacts.

Section Format.
Context {t : type}.

Definition emin := SpecFloat.emin (fprec t) (femax t).
Fact emin_le_0 : (emin <= 0)%Z. 
Proof. pose proof @fprec_lb t; pose proof @femax_lb t; 
unfold emin, SpecFloat.emin; lia. Qed.

Definition choice:= fun x0 : Z => negb (Z.even x0).
Fact choiceP (x : Z) : choice x = negb (choice (- (x + 1))%Z).
Proof. unfold choice; rewrite Z.even_opp Z.even_add; 
destruct (Z.even x); auto. Qed.

End Format.

Section FmtFacts.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Notation emin := (SpecFloat.emin (fprec t) (femax t)).
Notation radix2 := Zaux.radix2.
Notation FLX_exp := FLX.FLX_exp.
Notation round := Generic_fmt.round.


Lemma generic_format_FLT_FT2R (x : ftype t) : 
Generic_fmt.generic_format radix2 fexp (FT2R x).
Proof.
rewrite <- B2R_float_of_ftype. 
apply Binary.generic_format_B2R.
Qed.

Lemma generic_format_FLX_FT2R (x : ftype t) : 
Generic_fmt.generic_format radix2 (FLX_exp (fprec t)) (FT2R x).
Proof.
rewrite <- B2R_float_of_ftype. 
eapply (@FLT.generic_format_FLX_FLT radix2 emin).
apply Binary.generic_format_B2R.
Qed.

Fact fexp_valid : Generic_fmt.Valid_exp fexp. 
Proof. apply FLT.FLT_exp_valid. apply fprec_gt_0. Qed.

End FmtFacts. 

Section RndFacts.

Fact valid_rnd_NE : Generic_fmt.Valid_rnd Round_NE.ZnearestE. 
Proof. apply Generic_fmt.valid_rnd_N. Qed. 

End RndFacts. 

Global Hint Resolve generic_format_FLT_FT2R 
                    generic_format_FLX_FT2R 
                    fexp_valid 
                    valid_rnd_NE
                    FPCore.fprec_gt_0
                    fprec_gt_1: dd_base.

