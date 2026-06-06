(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** This file contains accuracy proofs for double-word 
plus a (double-word, floating-point number *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common.
Require Import DWTimesFP DDModels DWord_defs Fast2Mult_acc TwoSum_acc Fast2Sum_acc DWPlus_acc.
From Flocq Require Import Pff2Flocq Core.

From Stdlib Require Import Reals.Reals.

Require Import mathcomp.ssreflect.ssreflect.

(* for choice functions : choice = fun x0 : Z => negb (Z.even x0) *)
From Stdlib Require Import Logic.FunctionalExtensionality.

Set Bullet Behavior "Strict Subproofs".

Lemma let_pair_eta {A B C} (p : A*B) (k : A -> B -> C) :
  (let '(a,b) := p in k a b) = k (fst p) (snd p).
Proof. destruct p; reflexivity. Qed.

Section CorrectDWMulFP.
  Context {NANS: Nans} {t : type} {STD: is_standard t}.

  Variables (xh xl y : ftype t).

  Hypothesis FIN : is_finite_p (DWTimesFP3 xh xl y). 

  Ltac prove_finite := 
    move: FIN;
    rewrite /DWTimesFP3/is_finite_p //=;
    move => [] //=;
    subexpr_finite => //
  .

  Fact FIN3 : is_finite (BMULT xh y) = true.
  Proof. prove_finite. Qed.

  Fact FINxh : is_finite xh = true.
  Proof. prove_finite. Qed.

  Fact FIN1 : is_finite_p (Fast2Mult xh y).
  Proof. prove_finite. Qed.

  Let sl := snd (TwoSumF xh y).

  Let cl1 := snd (Fast2Mult xh y).

  Fact FIN2 : is_finite (BFMA xl y cl1) = true.
  Proof. prove_finite. Qed.

  Let ch := fst(Fast2Mult xh y).

  Fact FINxl : is_finite xl = true.
  Proof. prove_finite. Qed.

End CorrectDWMulFP.

Section  CorrectDWMulFP'.
  Context {NANS: Nans} {t : type} {STD: is_standard t}.

  Notation emin := (common.emin (t:=t)).

  Variables (a b : ftype t).

  Hypothesis (Fast2Mult_overflow_condition : is_finite (BMULT a b) = true).
  Hypothesis (Fast2Mult_underflow_condition_strict : (FT2R a * FT2R b) <> 0 -> 
    bpow Zaux.radix2 (emin + 3 * fprec t) <= Rabs (FT2R a * FT2R b)).

  Lemma Fast2Mult_correct : DWTimesFP.Fast2Mult (fprec t) choice (FT2R a) (FT2R b) = F2Rp (Fast2Mult a b).
  Proof.
    have UF : (FT2R a * FT2R b) <> 0 -> 
      bpow Zaux.radix2 (emin + 2 * fprec t -1) <= Rabs (FT2R a * FT2R b).
    -
    move => H0.
    eapply Rle_trans; [ | apply Fast2Mult_underflow_condition_strict] => //.
    apply bpow_le. cbv [emin SpecFloat.emin].  
    pose proof femax_lb t; pose proof fprec_gt_1 t; lia.
    -
    have FIN: (is_finite_p (Fast2Mult a b)) by apply Fast2Mult_finite_if_BMULT_finite.
    destruct (Req_dec (FT2R a * FT2R b) 0).
    + 
    rewrite /DWTimesFP.Fast2Mult/Fast2Mult.
    rewrite /F2Rp/fst/snd.
    rewrite -BMULT_round_correct => //.
    destruct FIN as [_ FIN]; rewrite /Fast2Mult/snd in FIN. 
    rewrite -BFMA_round_correct /FMA => //=.
    rewrite -BOPP_binary; try left; try apply BOPP_is_finite => //=.
    rewrite Rplus_opp -BMULT_round_correct => //.
    rewrite !H !round_0 Rminus_diag !round_0; auto.
    +
    have Hgen: 
    generic_format radix2 (FLX_exp (fprec t)) 
    (FT2R a * FT2R b - round radix2 (FLX_exp (fprec t)) ZnearestE (FT2R a * FT2R b)).
    *
    rewrite -Ropp_minus_distr; apply generic_format_opp.
    apply Mult_error.mult_error_FLX; FLT_basics.
    *
    rewrite /DWTimesFP.Fast2Mult/Fast2Mult/F2Rp/fst/snd; f_equal.
    BMULT_correct t a b => //=.
    rewrite -!B2R_float_of_ftype => //=.
    rewrite (round_FLT_FLX radix2 _) !B2R_float_of_ftype => //.
    apply Fast2Mult_underflow_condition_imples => //.
    rewrite -BFMA_round_correct /FMA => //=.
    rewrite -BOPP_binary; try left; try apply BOPP_is_finite => //=.
    rewrite Rplus_opp -BMULT_round_correct => //. 
    symmetry; rewrite round_generic => //.
    symmetry; rewrite round_generic => //.
    rewrite (round_FLT_FLX radix2 emin)  => //=.
    apply Fast2Mult_underflow_condition_imples => //.
    apply format_dq; FLT_basics => //.
    apply Fast2Mult_finite_if_BMULT_finite => //.
  Qed.

End CorrectDWMulFP'.

Section CorrectDWMulFP.

Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (common.emin (t:=t)).
Notation u   := (bpow radix2 (- fprec t)).
Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).

Let ulp := (Ulp.ulp radix2 (SpecFloat.fexp (fprec t) (femax t))). 

Variables (xh xl y : ftype t).

Hypothesis  xE : double_word xh xl.

Lemma is_finite_DWTimesFP3 : 
  is_finite (fst (DWTimesFP3 xh xl y)) = true -> 
  is_finite (snd (DWTimesFP3 xh xl y)) = true.
Proof.
  rewrite /fst/snd/DWTimesFP3.
  pose proof TwoMult_is_DW xh y as H2m.
  pose proof Fast2Sum_is_DW (fst (Fast2Mult xh y)) (BFMA xl y (snd (Fast2Mult xh y))) as H2s.
  move : H2m H2s.
  rewrite /Fast2Mult_mul/Fast2Mult_err/Fast2Mult/fst/snd/Fast2Sum/double_word
    /Fast2Sum_sum/Fast2Sum_err/fst/snd/Fast2Sum.
  intros.
  set (a := (BFMA _ _ _)) in *.
  set (b := BMINUS (BPLUS _ _) _) in *.
  pose proof Binary.Bminus_correct
    (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
  BinarySingleNaN.mode_NE (float_of_ftype a) (float_of_ftype b).
Admitted.

Hypothesis FIN : is_finite_p (DWTimesFP3 xh xl y).
Hypothesis Hp3 : (3 <= fprec t)%Z.
Hypothesis TwoProdE : TwoProd = DWTimesFP.Fast2Mult (fprec t) choice.
Hypothesis DWTimesFPUnderflowHyp1: 
  bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xh * FT2R y).
Hypothesis DWTimesFPUnderflowHyp2: 
  bpow radix2 (emin + fprec t - 1) + 
  / 2 * Ulp.ulp radix2 fexp (FT2R xh * FT2R y) <= Rabs (FT2R xl * FT2R y).

Theorem DWTimesFP3_FLX_FLT  :
  DWTimesFP9 (fprec t) choice (FT2R xh) (FT2R xl) (FT2R y) = F2Rp (DWTimesFP3 xh xl y).
Proof.
have FIN1: (is_finite_p (Fast2Mult xh y)) by
apply: (FIN1 _ xl _) => //.
have FIN2 : is_finite (BFMA xl y (snd (Fast2Mult xh y))) = true by
apply: FIN2 => //.
move: FIN2. 
rewrite /Fast2Mult/fst/snd. move => FIN2.
have FIN3 : is_finite (BMULT xh y) = true by 
apply: (FIN3 _ _ _ FIN) => //.
rewrite /DWTimesFP9/DWTimesFP3.
rewrite TwoProdE Fast2Mult_correct => //.
rewrite -FastTwoSumEq_FLT /Fast2Mult/F2Rp/fst/snd.
f_equal.
rewrite -!BFMA_round_correct /FMA=> //.
rewrite Rplus_comm.
rewrite -(round_FLT_FLX radix2 emin); auto.
set u := round radix2 (FLT_exp emin (fprec t)) (Znearest choice)
           (FT2R xh * FT2R y + FT2R (BOPP (BMULT xh y))).
set v := FT2R xl * FT2R y.
apply (Rle_trans _ (Rabs v - Rabs u)).
apply Rminus_plus_le_minus.
eapply Rle_trans.
pose proof error_le_half_ulp radix2 (FLT_exp emin (fprec t))
  choice (FT2R xh * FT2R y).
subst u. rewrite round_generic. 
rewrite -BOPP_binary.
rewrite Rplus_opp -BMULT_round_correct => //.
apply Rplus_le_compat_l.
rewrite -Ropp_minus_distr Rabs_Ropp in H. 
apply H.
right; auto.
admit.
apply DWTimesFPUnderflowHyp2.
admit.
admit.
admit.

rewrite /is_finite_p/fst/snd/Fast2Sum.

admit.
Admitted. 

End CorrectDWMulFP.


(* ============================================================
   Layer-1 / Layer-2 SCAFFOLDING for DWTimesFP3 (Algorithm 9).

   These three statements are the target shape per PROOF_PATTERN.md;
   their proofs are pending and depend on completing:
     - DWTimesFP3_FLX_FLT (5 remaining admits in the section above),
     - the FLX-side error analysis already done as
       paper_proofs.DWTimesFP.DWTimesFP9_correct,
     - bridging from the paper's FLX statement to the FLT-side
       conclusion via DWTimesFP3_FLX_FLT.

   The corollary DWTimesFP_accuracy_from_cond is the Layer-2
   interface used by the VST guarded wrapper specs.
   ============================================================ *)

Section DWTimesFP_Accuracy.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation u   := (bpow Zaux.radix2 (- fprec t)).

Variables (xh xl y : ftype t).

Let zh := FT2R (fst (DWTimesFP3 xh xl y)).
Let zl := FT2R (snd (DWTimesFP3 xh xl y)).
Let xr := (FT2R xh + FT2R xl).
Let yr := FT2R y.

Definition relative_error_DWTimesFP : R :=
  Rabs (((zh + zl) - xr * yr) / (xr * yr)).

(* Load-bearing Layer-1 theorem.  Pending: bridge from
   DWTimesFP9_correct via DWTimesFP3_FLX_FLT. *)
Theorem DWTimesFP_relerr_bound :
  double_word xh xl ->
  is_finite_p (DWTimesFP3 xh xl y) ->
  (3 <= fprec t)%Z ->
  relative_error_DWTimesFP <= 2 * u ^ 2.
Proof. Admitted.

(* Layer-2 corollary: takes the cond verified at the spec interface
   (DWTimesFP_cond, defined in DDModels.v) and discharges the
   Layer-1 hypotheses.

   double_word follows from the cond's double_word_prop;
   is_finite_p is established from the cond via the (currently
   admitted) is_finite_DWTimesFP3 + finiteness of the Fast2Mult
   product; the 3 <= fprec t hypothesis must be threaded by the
   caller (it is true for Tdouble: fprec Tdouble = 53). *)
Corollary DWTimesFP_accuracy_from_cond :
  (3 <= fprec t)%Z ->
  DWTimesFP_cond xh xl y ->
  relative_error_DWTimesFP <= 2 * u ^ 2.
Proof. Admitted.

End DWTimesFP_Accuracy.
