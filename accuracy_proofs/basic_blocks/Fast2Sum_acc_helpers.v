(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Helper lemmas for the accuracy and correctness proofs of the
   Fast2Sum algorithm in the FLT format.

   Layout:
     1. Zero-case helpers
     2. Correctness & double-word property
     3. FLT/FLX equivalence *)

Require Import vcfloat.VCFloat.
From Stdlib Require Import ZArith.
Require Import float_acc_lems op_defs dd_tactics.
Require Import DDModels common TwoSum_acc.
Require Import F2SumFLT F2SumFLX.
From Flocq Require Import Pff2Flocq Core.
Require Import mathcomp.ssreflect.ssreflect.

Set Bullet Behavior "Strict Subproofs".

Section FastTwoSumCorrect.

Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation FE := (FLT_exp (@emin t) (fprec t)).
Notation emin := (@common.emin t).

(* ===================================================================== *)
(* 1. Zero-case helpers                                                    *)
(* ===================================================================== *)

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
rewrite Rminus_diag;
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
rewrite Rminus_diag; apply generic_format_0.
Qed.

(* ===================================================================== *)
(* 2. Correctness & double-word property                                   *)
(* ===================================================================== *)

Variables (a b : ftype t).

Theorem FastTwoSum_correct
  (Hfin_plus : is_finite (BPLUS a b) = true)
  (Hle : Rabs (FT2R b) <= Rabs (FT2R a)) :
  FT2R (Fast2Sum_err a b) = FT2R a + FT2R b - FT2R (Fast2Sum_sum a b).
Proof.
have FIN : is_finite_p (DD.DDModels.Fast2Sum a b) :=
  conj Hfin_plus (is_finite_FastSum a b Hle Hfin_plus).
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

(* Same exactness as FastTwoSum_correct, but under the weaker Fast2Sum_cond
   disjunction (ulp b <= ulp a, or a = 0) instead of the magnitude ordering
   |b| <= |a|.  Needed at the (sh, c) Fast2Sum site of DWPlusDW, where the
   magnitude ordering is false in the cancellation regime. *)
Theorem FastTwoSum_correct_ulp (Hcond : Fast2Sum_cond a b) :
  FT2R (Fast2Sum_err a b) = FT2R a + FT2R b - FT2R (Fast2Sum_sum a b).
Proof.
destruct Hcond as [Hfin_plus Hdisj].
have FIN : is_finite_p (DD.DDModels.Fast2Sum a b) :=
  conj Hfin_plus (is_finite_FastSum_ulp a b Hdisj Hfin_plus).
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
have: Fast2Sum_correct_flt radix2 emin (fprec t) choice (FT2R a) (FT2R b).
apply F2Sum_correct_ulp_flt => //. apply (fprec_gt_one t).
rewrite /Fast2Sum_correct_flt/Fast2Sum_flt/fst/snd;
  rewrite -!B2R_float_of_ftype;
  move => H. rewrite H; f_equal.
  rewrite -!B2R_float_of_ftype in H9.
  rewrite /BPLUS/BINOP float_of_ftype_of_float => //.
Qed.

Theorem Fast2Sum_is_DW
  (Hfin_plus : is_finite (BPLUS a b) = true)
  (Hle : Rabs (FT2R b) <= Rabs (FT2R a)) :
  double_word (Fast2Sum_sum a b) (Fast2Sum_err a b).
Proof.
  rewrite /double_word FastTwoSum_correct // /Fast2Sum_sum /= /common.rounded.
unfold Fast2Sum_err, Fast2Sum_sum, DDModels.Fast2Sum, fst, snd in *.
  BPLUS_correct t a b.
by rewrite -!B2R_float_of_ftype.
Qed.

(* ===================================================================== *)
(* 3. FLT/FLX equivalence                                                  *)
(* ===================================================================== *)

Lemma FastTwoSumEq_FLT_uf1
  (FIN : is_finite_p (DD.DDModels.Fast2Sum a b)):
Rabs (FT2R a + FT2R b) < bpow radix2 (emin + fprec t - 1) ->
DD.paper_proofs.F2Sum.Fast2Sum (fprec t) choice (FT2R a) (FT2R b) = F2Rp (DD.DDModels.Fast2Sum a b).
Proof.
intros Huf.
move : FIN.
rewrite /DDModels.Fast2Sum/is_finite_p/fst/snd.
move => [] FIN1 FIN2.
have Hg1: generic_format radix2 (SpecFloat.fexp (fprec t) (femax t))
  (FT2R a + FT2R b).
  apply Plus_error.FLT_format_plus_small => //;
  try apply generic_format_FLT_FT2R.
  eapply Rle_trans. apply Rlt_le.
  apply Huf. rewrite /emin.
  apply bpow_le; lia.
have Hg2: generic_format radix2 (FLX_exp (fprec t)) (FT2R a + FT2R b).
  by apply generic_format_FLX_FLT in Hg1.
have H1: round radix2 (FLX_exp (fprec t)) (Znearest choice)
        (FT2R a + FT2R b) = (FT2R a + FT2R b) by rewrite !round_generic.
rewrite /F2Sum.Fast2Sum/Fast2Sum/F2Rp/fst/snd.
f_equal.
BPLUS_correct t a b;
   rewrite !B2R_float_of_ftype.
by rewrite !round_generic.
move: FIN2.
set (x2:= (BMINUS (BPLUS a b) a)).
subexpr_finite.
BMINUS_correct t b x2;
  rewrite !B2R_float_of_ftype.
rewrite !round_generic; try nra;
  subst x2; try field_simplify_format => //.
f_equal.
BMINUS_correct t (BPLUS a b) a;
  rewrite !B2R_float_of_ftype.
rewrite !round_generic => //; try nra.
BPLUS_correct t a b;
  rewrite !B2R_float_of_ftype.
rewrite !round_generic => //; try nra.
BPLUS_correct t a b;
  rewrite !B2R_float_of_ftype.
rewrite !round_generic => //; try nra.
field_simplify_format.

BMINUS_correct t (BPLUS a b) a;
  rewrite !B2R_float_of_ftype.
rewrite !round_generic => //; try nra.
BPLUS_correct t a b;
  rewrite !B2R_float_of_ftype.
rewrite !round_generic => //; try nra.
field_simplify_format.

BPLUS_correct t a b;
  rewrite !B2R_float_of_ftype.
rewrite !round_generic => //; try nra.
field_simplify_format.
Qed.

Lemma FastTwoSumEq_FLT_uf2
(FIN : is_finite_p (DD.DDModels.Fast2Sum a b)):
Rabs (FT2R (BPLUS a b) - FT2R a) < bpow radix2 (emin + fprec t - 1) ->
DD.paper_proofs.F2Sum.Fast2Sum (fprec t) choice (FT2R a) (FT2R b) = F2Rp (DD.DDModels.Fast2Sum a b).
Proof.
intros Huf.
case : (Rlt_dec (Rabs (FT2R a + FT2R b))
  (bpow radix2 (emin + fprec t - 1))) => Huf1.
by apply FastTwoSumEq_FLT_uf1.
apply Rnot_lt_le in Huf1.
move : FIN.
rewrite /DDModels.Fast2Sum/is_finite_p/F2Rp
  /F2Sum.Fast2Sum/Fast2Sum/fst/snd.
move => [] FIN1 FIN2.
f_equal.
BPLUS_correct t a b;
  rewrite !B2R_float_of_ftype.
rewrite round_FLT_FLX => //.

have Hg1: generic_format radix2 (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
  (round radix2 (SpecFloat.fexp (fprec t) (femax t)) ZnearestE (FT2R a + FT2R b) - FT2R a).
{ move: Huf.
BPLUS_correct t a b; rewrite !B2R_float_of_ftype //=.
move => Huf.
apply Plus_error.FLT_format_plus_small => //.
apply generic_format_round; auto with dd_base.
apply generic_format_opp;
apply generic_format_FLT_FT2R.
eapply Rle_trans. apply Rlt_le.
apply Huf. rewrite /emin.
apply bpow_le; lia. }


have Heq1 :
round radix2 (SpecFloat.fexp (fprec t) (femax t)) ZnearestE
(round radix2 (SpecFloat.fexp (fprec t) (femax t)) ZnearestE
  (FT2R a + FT2R b) - FT2R a) =
round radix2 (SpecFloat.fexp (fprec t) (femax t)) ZnearestE
  (FT2R a + FT2R b) - FT2R a.
{ by rewrite round_generic . }


have Heq2 :
round radix2 (FLX_exp (fprec t)) ZnearestE
(round radix2 (FLX_exp (fprec t)) ZnearestE
  (FT2R a + FT2R b) - FT2R a) =
round radix2 (SpecFloat.fexp (fprec t) (femax t)) ZnearestE
  (FT2R a + FT2R b) - FT2R a.
{  rewrite round_generic => //.
rewrite round_FLT_FLX => //.
apply (@generic_format_FLX_FLT radix2 emin).
by rewrite round_FLT_FLX in Hg1. }

move: FIN2.
set (x:= (BMINUS (BPLUS a b) a)).
subexpr_finite.
BMINUS_correct t b x;
  rewrite !B2R_float_of_ftype.

subst x.
BMINUS_correct t (BPLUS a b) a;
  rewrite !B2R_float_of_ftype.
BPLUS_correct t a b;
  rewrite !B2R_float_of_ftype //=.
rewrite Heq1 Heq2.

case :
(Rlt_dec
(Rabs (FT2R b - (round radix2 (SpecFloat.fexp (fprec t) (femax t))
  ZnearestE (FT2R a + FT2R b) - FT2R a)))
  (bpow radix2 (emin + fprec t - 1))) => Huf2.
{ have Hg:
generic_format radix2 (SpecFloat.fexp (fprec t) (femax t))
  (FT2R b - (round radix2 (SpecFloat.fexp (fprec t) (femax t))
  ZnearestE (FT2R a + FT2R b) - FT2R a)).
apply Plus_error.FLT_format_plus_small => //.
apply generic_format_FLT_FT2R.
apply generic_format_opp => //.
  eapply Rle_trans. apply Rlt_le. rewrite Rplus_opp.
  apply Huf2. rewrite /emin.
  apply bpow_le; lia.
rewrite round_generic.
symmetry; rewrite round_generic => //.
by eapply (@generic_format_FLX_FLT radix2 emin). }
apply Rnot_lt_le in Huf2.
symmetry; by rewrite round_FLT_FLX.
Qed.

Lemma FastTwoSumEq_FLT_uf3
  (FIN : is_finite_p (DD.DDModels.Fast2Sum a b)):
Rabs (FT2R b - FT2R (BMINUS (BPLUS a b) a)) < bpow radix2 (emin + fprec t - 1) ->
DD.paper_proofs.F2Sum.Fast2Sum (fprec t) choice (FT2R a) (FT2R b) = F2Rp (DD.DDModels.Fast2Sum a b).
Proof.
intros Huf.

case : (Rlt_dec (Rabs (FT2R a + FT2R b))
  (bpow radix2 (emin + fprec t - 1))) => Huf1.
by apply FastTwoSumEq_FLT_uf1.
apply Rnot_lt_le in Huf1.

case : (Rlt_dec (Rabs (FT2R (BPLUS a b) - FT2R a))
  (bpow radix2 (emin + fprec t - 1))) => Huf2.
by apply FastTwoSumEq_FLT_uf2.
apply Rnot_lt_le in Huf2.

move : FIN.
rewrite /DDModels.Fast2Sum/is_finite_p/F2Rp
  /F2Sum.Fast2Sum/Fast2Sum/fst/snd.
move => [] FIN1 FIN2.
f_equal.
BPLUS_correct t a b;
  rewrite !B2R_float_of_ftype.
rewrite round_FLT_FLX => //.

have Hg1: generic_format radix2 (SpecFloat.fexp (fprec t) (femax t))
  (FT2R b - FT2R (BMINUS (BPLUS a b) a)).
  apply Plus_error.FLT_format_plus_small => //;
  try apply generic_format_opp;
  try apply generic_format_FLT_FT2R.
  eapply Rle_trans. apply Rlt_le.
  apply Huf. rewrite /emin.
  apply bpow_le; lia.

move: FIN2 Hg1 Huf2 Huf.
BPLUS_correct t a b;
  rewrite !B2R_float_of_ftype.
set (x2:= (BMINUS (BPLUS a b) a)).
subexpr_finite.
BMINUS_correct t b x2;
  rewrite !B2R_float_of_ftype.
subst x2 => //=.
move => HG1 Huf2 Huf.

have Heq1 :
round radix2 (FLX_exp (fprec t)) ZnearestE
  (FT2R a + FT2R b) - FT2R a =
round radix2 (SpecFloat.fexp (fprec t) (femax t)) ZnearestE
  (FT2R a + FT2R b) - FT2R a.
{ rewrite round_FLT_FLX => //. }

have Heq2 :
round radix2 (FLX_exp (fprec t)) (Znearest choice)
  (round radix2 (FLX_exp (fprec t))
  ZnearestE (FT2R a + FT2R b) - FT2R a) =
round radix2 (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
  (round radix2 (SpecFloat.fexp (fprec t) (femax t))
  ZnearestE (FT2R a + FT2R b) - FT2R a).
{ rewrite !round_FLT_FLX => //.
 move : Huf2; rewrite round_FLT_FLX => //. }
rewrite Heq2. clear Heq2.

move: HG1.
BMINUS_correct t (BPLUS a b) a;
  rewrite !B2R_float_of_ftype.
BPLUS_correct t a b;
  rewrite !B2R_float_of_ftype => //=.
move => HG1.

rewrite round_generic .
symmetry; rewrite round_generic => //.
apply (@generic_format_FLX_FLT radix2 emin) => //.
Qed.


(* the result of the FLT format algorithm and the FLX format algorithm are
  equal, regardless of underflow. *)
Lemma FastTwoSumEq_FLT
  (FIN : is_finite_p (DD.DDModels.Fast2Sum a b)):
  DD.paper_proofs.F2Sum.Fast2Sum
      (fprec t) choice (FT2R a) (FT2R b) = F2Rp (DD.DDModels.Fast2Sum a b).
Proof.
move : FIN.
rewrite /DDModels.Fast2Sum/is_finite_p/fst/snd.
move => [] FIN1 FIN2.
case : (Rlt_dec (Rabs (FT2R a + FT2R b))
  (bpow radix2 (emin + fprec t - 1))) => Huf1.
apply FastTwoSumEq_FLT_uf1 => //.
apply Rnot_lt_le in Huf1.
case : (Rlt_dec (Rabs (FT2R b - FT2R (BMINUS (BPLUS a b) a)))
  (bpow radix2 (emin + fprec t - 1))) => Huf2.
apply FastTwoSumEq_FLT_uf3 => //.
apply Rnot_lt_le in Huf2.
case : (Rlt_dec (Rabs (FT2R (BPLUS a b) - FT2R a))
  (bpow radix2 (emin + fprec t - 1))) => Huf3.
apply FastTwoSumEq_FLT_uf2 => //.
apply Rnot_lt_le in Huf3.
rewrite /F2Sum.Fast2Sum/Fast2Sum/F2Rp/fst/snd.
f_equal.
BPLUS_correct t a b.
rewrite round_FLT_FLX => //.
  rewrite !B2R_float_of_ftype => //.
move: FIN2 Huf2.
set (x2:= (BMINUS (BPLUS a b) a)).
move => FIN2 Huf2.
BMINUS_correct t b x2;
  rewrite !B2R_float_of_ftype.
rewrite round_FLT_FLX => //.
f_equal. f_equal. subst x2.
move : FIN2. subexpr_finite.
BMINUS_correct t (BPLUS a b) a;
  rewrite !B2R_float_of_ftype.
rewrite round_FLT_FLX => //.
f_equal. f_equal.
BPLUS_correct t a b;
  rewrite !B2R_float_of_ftype.
rewrite round_FLT_FLX => //.
Qed.

End FastTwoSumCorrect.
