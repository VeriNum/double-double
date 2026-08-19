(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Accuracy and representation results for [DWTimesFP3], the implementation
    model of Algorithm 9 for multiplying a double-word number by a
    floating-point number.  ADMIT-FREE.

    Notation: u = 2^(-p) is the relative rounding unit and eta = 2^emin is the
    smallest positive subnormal, the physical underflow floor.

    ============================================================================
    PUBLIC INTERFACE

      MIXED absolute/relative API (primary; holds over the whole range):
        DWTimesFP3_error_mixed        branch-aware error: purely relative
                                     (2u^2) above the TwoProd exactness
                                     threshold 2^(emin+2p-1), purely absolute
                                     (2.51*eta) below it, exact product zero
                                     when the leading product is zero
        DWTimesFP3_error_mixed_flat   its one-line consequence
                                        2u^2|P| + 2.51*eta,
                                     carrying both terms in every regime
        DWTimesFP3_double_word_mixed  output is a double word, every regime

      VST INTERFACE (end of file; what the C contract states).  The mixed
      theorems above assume is_finite_p (DWTimesFP3 ...) -- a fact about the
      RESULT, which a runtime guard cannot test -- so these Layer-2 corollaries
      derive it from the accurate-only, input-only, runtime-checkable cond:
        DWTimesFP_cond_acc            (DDModels.v) DWTimesFP_cond MINUS the
                                      underflow disjunct: double-word relation
                                      plus overflow headroom, nothing else
        DWTimesFP3_finite_acc         is_finite_p from that cond, every regime
        DWTimesFP_mixed_accuracy_from_cond_acc
                                      2u^2|P| + 2.51*eta from that cond
        DWTimesFP3_double_word_from_cond_acc
                                      output is a double word from that cond
      These are what dw_mult_fp_check discharges and dw_mult_fp9_guarded_spec
      carries.  Because no underflow premise is involved, the guard accepts the
      Fast2Mult underflow gap instead of aborting on it.

      RELATIVE API (corollaries of the mixed normal arm; needs the gap excluded,
      so it is a proof-level interface, NOT what any funspec states):
        DWTimesFP_accuracy_from_cond  relerr <= 2u^2 from DWTimesFP_cond
        DWTimesFP3_double_word        output is a double word from the cond

      Proof developments that already have decomposed hypotheses may use:
        DWTimesFP_relerr_bound        relerr <= 2u^2 from the named
                                      precondition; this is the kernel that
                                      proves the mixed theorem's normal arm
        DWTimesFP3_error_normal_arm   absolute form of that arm
        DWTimesFP_cond_no_gap         the cond forbids the nonzero gap, so
                                      under it the eta term is never paid

    Why the relative theorem is a corollary of the mixed theorem's ARM and not
    of its flat form: 2u^2|P| + 2.51*eta is strictly weaker than 2u^2|P| in the
    normal regime, so no algebra recovers the missing eta.  The arm is the
    mixed API's normal-regime content, and that is what the cond-level
    corollary invokes.  Conversely the flat form is the only one available in
    the gap, which is why weakening the guard to DWTimesFP_cond_acc means the
    exported contract must be the flat bound rather than the pure 2u^2 one.

    The Algorithm-9 underflow-floor block at the end of this file (previously
    in DWDivDW_acc.v at p >= 14, now p >= 3) is also a cross-operation proof
    interface: DWDivDW_acc consumes it for its reciprocal-refinement block.
    ============================================================================ *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common FLT_helpers.
Require Import DWTimesFP DDModels DWord_defs Fast2Mult_acc TwoSum_acc Fast2Sum_acc.
Require Import DWPlusFP_acc_helpers.
From Flocq Require Import Pff2Flocq Core.

From Stdlib Require Import Reals.Reals.

Require Import mathcomp.ssreflect.ssreflect.

(* for choice functions : choice = fun x0 : Z => negb (Z.even x0) *)
From Stdlib Require Import Logic.FunctionalExtensionality.

Set Bullet Behavior "Strict Subproofs".

(* Keep the paper's two-product folded (it is now a Definition = Fast2Mult in
   DWTimesFP); proofs expose it explicitly via DWTimesFP.TwoProdE. *)
Opaque DWTimesFP.TwoProd.
Arguments DWTimesFP.TwoProd : simpl never.


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
  (* No-underflow for the product, at threshold emin + 3*fprec.  NOTE: this is
     stronger than the TwoProd-exactness threshold emin + 2*fprec - 1 (the
     latter is derived as UF below and used for round_FLT_FLX), but the stronger
     bound is forced by Flocq's Pff2Flocq.format_dq (used at the end of this
     proof), whose section underflow hypothesis instantiates to emin + 3*fprec.
     Hence DWTimesFP3_FLX_FLT below must also assume emin + 3*fprec, which is
     STRONGER than DWTimesFP_cond's emin + 2*fprec - 1 disjunct. *)
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

(* Weak variant of Fast2Mult_correct: the FLX TwoProd equals the FLT Fast2Mult
   pair under the MINIMAL underflow threshold emin + 2*fprec - 1.  The original
   Fast2Mult_correct needs emin + 3*fprec because it discharges the product-error
   format goal with Pff's format_dq; here we use Flocq's Mult_error.mult_error_FLT
   directly, whose underflow side-condition is exactly emin + 2*fprec - 1. *)
Section CorrectDWMulFP_weak.
  Context {NANS: Nans} {t : type} {STD: is_standard t}.

  Notation emin := (common.emin (t:=t)).

  Variables (a b : ftype t).

  Hypothesis (Fast2Mult_overflow_condition : is_finite (BMULT a b) = true).
  Hypothesis (Fast2Mult_underflow_condition : (FT2R a * FT2R b) <> 0 ->
    bpow Zaux.radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R a * FT2R b)).

  Lemma Fast2Mult_correct_weak :
    DWTimesFP.Fast2Mult (fprec t) choice (FT2R a) (FT2R b) = F2Rp (Fast2Mult a b).
  Proof.
    have UF := Fast2Mult_underflow_condition.
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
    rewrite -Ropp_minus_distr; apply generic_format_opp;
      apply Mult_error.mult_error_FLT; FLT_basics => //.
    apply Fast2Mult_finite_if_BMULT_finite => //.
  Qed.

End CorrectDWMulFP_weak.

Section CorrectDWMulFP.

Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (common.emin (t:=t)).
Notation u   := (bpow radix2 (- fprec t)).
Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).

Let ulp := (Ulp.ulp radix2 (SpecFloat.fexp (fprec t) (femax t))). 

Variables (xh xl y : ftype t).

Hypothesis  xE : double_word xh xl.

(* NOTE: an earlier, underflow-free magnitude ordering |cl3| <= |ch| for the
   closing Fast2Sum (with the derived snd-output finiteness is_finite_DWTimesFP3)
   used to live here.  It is superseded by the cond-driven development in the
   DWTimesFP_Finite section below (aux_cl3_le_ch + DWTimesFP3_fst_finite /
   DWTimesFP3_snd_finite), which establishes the same finiteness from
   DWTimesFP_cond's underflow disjunction.  The standalone underflow-free form
   was unused, so it has been dropped to keep this file admit-free; the only
   delicate case it required (a subnormal product whose round-to-nearest-even
   tie collapses cl1 to 0) is avoided entirely on the cond path. *)

Hypothesis FIN : is_finite_p (DWTimesFP3 xh xl y).
Hypothesis Hp3 : (3 <= fprec t)%Z.
Hypothesis DWTimesFPUnderflowHyp1:
  bpow radix2 (emin + 3 * fprec t) <= Rabs (FT2R xh * FT2R y).
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
(* the exact product error equals FT2R (Fast2Mult_err xh y), hence representable *)
have Huf2 : FT2R xh * FT2R y <> 0 ->
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R y).
{ intros _. eapply Rle_trans; [| exact DWTimesFPUnderflowHyp1].
  apply bpow_le; pose proof fprec_lb t; lia. }
have Herr : (FT2R xh * FT2R y + FT2R (BOPP (BMULT xh y)))%R
          = FT2R (Fast2Mult_err xh y).
{ rewrite (Fast2MultModel_correct xh y FIN3 Huf2).
  rewrite -BOPP_binary; [reflexivity | right; exact FIN3]. }
rewrite Herr. apply generic_format_FLT_FT2R.
apply DWTimesFPUnderflowHyp2.
rewrite -(Rabs_Ropp u). replace (v + u)%R with (v - - u)%R by ring.
apply Rabs_triang_inv.
exact (proj2 FIN1).
exact (proj2 FIN1).

exact FIN.
Qed.

End CorrectDWMulFP.

(* Weak FLX->FLT bridge for DWTimesFP3.  Same conclusion as DWTimesFP3_FLX_FLT
   but under the MINIMAL thresholds actually needed for the algorithm to agree
   with its FLX model:
     - product threshold emin + 2*fprec - 1   (vs. emin + 3*fprec there), and
     - the low FMA argument  w = xl*y + cl1  is itself normal:
       bpow(emin+fprec-1) <= |w|              (vs. the Hyp2 form there).
   With these, every rounding inside DWTimesFP3 agrees with its FLX counterpart
   (round_FLT_FLX), so the whole computation matches DWTimesFP9.  This is the
   bridge that survives in the [emin+2*fprec-1, emin+3*fprec) product band. *)
Section CorrectDWMul_weak_bridge.

Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (common.emin (t:=t)).

Variables (xh xl y : ftype t).

Hypothesis xE : double_word xh xl.
Hypothesis FIN : is_finite_p (DWTimesFP3 xh xl y).
Hypothesis Hp3 : (3 <= fprec t)%Z.
Hypothesis Hbig :
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R y).
Hypothesis Hw :
  bpow radix2 (emin + fprec t - 1)
    <= Rabs (FT2R xl * FT2R y + FT2R (Fast2Mult_err xh y)).

Theorem DWTimesFP3_FLX_FLT_weak :
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
have Huf2 : FT2R xh * FT2R y <> 0 ->
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R y)
  by (move => _; exact Hbig).
rewrite /DWTimesFP9/DWTimesFP3.
rewrite TwoProdE Fast2Mult_correct_weak => //.
rewrite -FastTwoSumEq_FLT /Fast2Mult/F2Rp/fst/snd.
f_equal.
rewrite -!BFMA_round_correct /FMA=> //.
rewrite Rplus_comm.
rewrite -(round_FLT_FLX radix2 emin); auto.
set u := round radix2 (FLT_exp emin (fprec t)) (Znearest choice)
           (FT2R xh * FT2R y + FT2R (BOPP (BMULT xh y))).
have Herr : u = FT2R (Fast2Mult_err xh y).
{ subst u.
  rewrite (_ : (FT2R xh * FT2R y + FT2R (BOPP (BMULT xh y)))%R
             = FT2R (Fast2Mult_err xh y)).
  - apply round_generic; [apply valid_rnd_N | apply generic_format_FLT_FT2R].
  - rewrite (Fast2MultModel_correct xh y FIN3 Huf2).
    rewrite -BOPP_binary; [reflexivity | right; exact FIN3]. }
rewrite Herr; exact Hw.
exact (proj2 FIN1).
exact (proj2 FIN1).
exact FIN.
Qed.

End CorrectDWMul_weak_bridge.


(* ============================================================
   Finiteness of fst (DWTimesFP3 xh xl y) from DWTimesFP_cond.
   fst (DWTimesFP3 xh xl y) = BPLUS ch cl3, where
     ch  = Fast2Mult_mul xh y   (= BMULT xh y),
     cl3 = BFMA xl y (Fast2Mult_err xh y).
   The cond's product bound |round(xh*y)| <= Omega/4 keeps |ch| small;
   the double-word relation keeps cl3 small; together the closing
   Fast2Sum stays finite.
   ============================================================ *)
Section DWTimesFP_Finite.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin  := (@common.emin t).
Notation fexp  := (SpecFloat.fexp (fprec t) (femax t)).
Notation ulp   := (Ulp.ulp Zaux.radix2 fexp).
Notation Omega := (bpow Zaux.radix2 (femax t)).

(* Make Valid_exp resolvable for SpecFloat.fexp so Flocq's ulp/round lemmas
   (error_le_half_ulp, ulp_neq_0, round_le, ...) discharge it automatically. *)
Local Instance valid_fexp_inst : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.

(* Double-word low word is at most half an ulp of the high word (FT2R-level
   dw_ulp): xl = -(round(xh+xl) - (xh+xl)) and round(xh+xl) = xh. *)
Lemma aux_dwu (a b : ftype t) :
  double_word_prop a b -> Rabs (FT2R b) <= /2 * ulp (FT2R a).
Proof.
rewrite /double_word_prop /rounded => Hdwp.
have Hb : FT2R b =
  - (round radix2 fexp (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
       (FT2R a + FT2R b) - (FT2R a + FT2R b)) by rewrite -Hdwp; ring.
have Hu : ulp (FT2R a) =
  ulp (round radix2 fexp (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
       (FT2R a + FT2R b)) by rewrite -Hdwp.
rewrite Hb Rabs_Ropp Hu.
apply Ulp.error_le_half_ulp_round; FLT_basics.
Qed.

(* Product bound: from the rounded-product bound |round(xh*y)| <= Omega/4 in
   the cond, the real product is bounded by Omega/2. *)
Lemma aux_xhy_bnd (a b : ftype t) :
  is_finite (BMULT a b) = true ->
  Rabs (FT2R (BMULT a b)) <= /4 * Omega ->
  Rabs (FT2R a * FT2R b) <= /2 * Omega.
Proof.
move => Hfin Hb.
have HΩ : 0 < Omega by apply bpow_gt_0.
have Hr : round radix2 fexp (Znearest choice) (FT2R a * FT2R b) = FT2R (BMULT a b)
  by rewrite BMULT_round_correct.
have HFh  : generic_format radix2 fexp (/2 * Omega) by apply generic_format_half_Omega.
have HFhn : generic_format radix2 fexp (-(/2 * Omega)) by apply generic_format_opp.
have Hb2 : - (/4 * Omega) <= FT2R (BMULT a b) <= /4 * Omega
  by apply Rabs_le_inv; exact Hb.
apply Rabs_le; split.
- apply Rnot_lt_le => Hlt.
  have Hle : round radix2 fexp (Znearest choice) (FT2R a * FT2R b)
          <= round radix2 fexp (Znearest choice) (-(/2 * Omega)).
  { apply round_le;
      first [ apply FLT_exp_valid; apply fprec_gt_0 | apply valid_rnd_N | lra ]. }
  have Hrg : round radix2 fexp (Znearest choice) (-(/2 * Omega)) = -(/2 * Omega).
  { apply round_generic; first [ apply valid_rnd_N | apply HFhn ]. }
  rewrite Hrg Hr in Hle. lra.
- apply Rnot_lt_le => Hgt.
  have Hle : round radix2 fexp (Znearest choice) (/2 * Omega)
          <= round radix2 fexp (Znearest choice) (FT2R a * FT2R b).
  { apply round_le;
      first [ apply FLT_exp_valid; apply fprec_gt_0 | apply valid_rnd_N | lra ]. }
  have Hrg : round radix2 fexp (Znearest choice) (/2 * Omega) = /2 * Omega.
  { apply round_generic; first [ apply valid_rnd_N | apply HFh ]. }
  rewrite Hrg Hr in Hle. lra.
Qed.

(* From the real product bound |a*b| <= Omega/4 and finiteness of BMULT a b,
   the rounded product |round(a*b)| <= Omega/4.  This is the fragment the new
   DWTimesFP_cond leaves us to re-derive: the cond now supplies the real product
   bound directly (formerly obtained from the two factor bounds via
   sqrt_cond_facts). *)
Lemma aux_round_prod_bnd (a b : ftype t) :
  is_finite (BMULT a b) = true ->
  Rabs (FT2R a * FT2R b) <= /2 * Omega ->
  Rabs (FT2R (BMULT a b)) <= /2 * Omega.
Proof.
move => Hfin Hreal.
have HΩ : 0 < Omega by apply bpow_gt_0.
have Hfmt : generic_format radix2 fexp (/2 * Omega) by apply generic_format_half_Omega.
have Hr : round radix2 fexp (Znearest choice) (FT2R a * FT2R b) = FT2R (BMULT a b)
  by rewrite BMULT_round_correct.
have HFhn : generic_format radix2 fexp (-(/2 * Omega)) by apply generic_format_opp.
have Hb2 : - (/2 * Omega) <= FT2R a * FT2R b <= /2 * Omega
  by (apply Rabs_le_inv; exact Hreal).
apply Rabs_le; split.
- have Hlo : round radix2 fexp (Znearest choice) (-(/2 * Omega))
          <= round radix2 fexp (Znearest choice) (FT2R a * FT2R b).
  { apply round_le; first [ apply FLT_exp_valid; apply fprec_gt_0 | apply valid_rnd_N | lra ]. }
  have Hrgo : round radix2 fexp (Znearest choice) (-(/2 * Omega)) = -(/2 * Omega).
  { apply round_generic; first [ apply valid_rnd_N | apply HFhn ]. }
  rewrite Hrgo Hr in Hlo. lra.
- have Hhi : round radix2 fexp (Znearest choice) (FT2R a * FT2R b)
          <= round radix2 fexp (Znearest choice) (/2 * Omega).
  { apply round_le; first [ apply FLT_exp_valid; apply fprec_gt_0 | apply valid_rnd_N | lra ]. }
  have Hrgh : round radix2 fexp (Znearest choice) (/2 * Omega) = /2 * Omega.
  { apply round_generic; first [ apply valid_rnd_N | apply Hfmt ]. }
  rewrite Hrgh Hr in Hhi. lra.
Qed.

(* The low-word product |xl*y| is small: in the normal range the relative ulp
   bound gives |xl| <= 2^-p |xh| so |xl*y| <= 2^-p |xh*y|; in the subnormal
   range |xl| <= 1/2 bpow emin is itself tiny.  Either way |xl*y| <= Omega/4. *)
Lemma aux_xly_bnd (xh xl y : ftype t) :
  double_word_prop xh xl ->
  Rabs (FT2R xh * FT2R y) <= /2 * Omega ->
  Rabs (FT2R y) <= Omega ->
  Rabs (FT2R xl * FT2R y) <= /2 * bpow radix2 (femax t - fprec t).
Proof.
move => Hdw Hxhy Hy.
have HΩ  : 0 < Omega by apply bpow_gt_0.
have HE0 : 0 <= bpow radix2 (femax t - fprec t) by apply bpow_ge_0.
have Hdwu := aux_dwu xh xl Hdw.
have Hyp  : 0 <= Rabs (FT2R y) by apply Rabs_pos.
have Hxhp : 0 <= Rabs (FT2R xh) by apply Rabs_pos.
rewrite Rabs_mult.
rewrite Rabs_mult in Hxhy.
destruct (Rle_lt_dec (bpow radix2 (emin + fprec t - 1)) (Rabs (FT2R xh)))
  as [Hnorm | Hsub].
- (* normal range *)
  have Hrel : ulp (FT2R xh) <= Rabs (FT2R xh) * bpow radix2 (1 - fprec t)
    by apply ulp_FLT_le.
  have Hxl : Rabs (FT2R xl) <= /2 * (Rabs (FT2R xh) * bpow radix2 (1 - fprec t)).
  { eapply Rle_trans; [exact Hdwu|]. apply Rmult_le_compat_l; [lra | exact Hrel]. }
  have HB0 : 0 <= bpow radix2 (1 - fprec t) by apply bpow_ge_0.
  have HBO : bpow radix2 (1 - fprec t) * Omega = 2 * bpow radix2 (femax t - fprec t).
  { rewrite -bpow_plus.
    replace (1 - fprec t + femax t)%Z with (1 + (femax t - fprec t))%Z by lia.
    rewrite bpow_plus. have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
  nra.
- (* subnormal range *)
  have Hulpe : ulp (FT2R xh) = bpow radix2 emin.
  { apply ulp_FLT_small;
      first [ apply fprec_gt_0
            | eapply Rlt_trans; [exact Hsub | apply bpow_lt; lia] ]. }
  have Hxl : Rabs (FT2R xl) <= /2 * bpow radix2 emin by rewrite -Hulpe; exact Hdwu.
  have HEs0 : 0 <= bpow radix2 emin by apply bpow_ge_0.
  have HEsO : bpow radix2 emin * Omega <= bpow radix2 (femax t - fprec t).
  { rewrite -!bpow_plus. apply bpow_le.
    unfold common.emin, SpecFloat.emin. pose proof femax_lb t; pose proof fprec_lb t; lia. }
  nra.
Qed.

(* From the square-root-scale component bounds |a|,|b| <= bpow(femax/2-1) the
   proof bodies' legacy facts are DERIVED: |a|,|b| <= Omega/4, the real product
   |a*b| <= Omega/4, is_finite (BMULT a b), and |round(a*b)| <= Omega/4.  This
   is the multiplication analog of the addition case deriving its intermediate
   finiteness from the component bounds (see DWPlusFP_cond). *)
Lemma sqrt_cond_facts (a b : ftype t) :
  is_finite a = true -> is_finite b = true ->
  Rabs (FT2R a) <= bpow radix2 (femax t / 2 - 1) ->
  Rabs (FT2R b) <= bpow radix2 (femax t / 2 - 1) ->
  Rabs (FT2R a) <= /4 * Omega /\
  Rabs (FT2R b) <= /4 * Omega /\
  Rabs (FT2R a * FT2R b) <= /4 * Omega /\
  is_finite (BMULT a b) = true /\
  Rabs (FT2R (BMULT a b)) <= /4 * Omega.
Proof.
move => Hfa Hfb Ha Hb.
have HΩ : 0 < Omega by apply bpow_gt_0.
have Hq4 : (/4 * Omega = bpow radix2 (femax t - 2))%R.
{ have -> : Omega = (bpow radix2 (femax t - 2) * bpow radix2 2)%R
    by rewrite -bpow_plus; f_equal; lia.
  have -> : bpow radix2 2 = 4%R by reflexivity. lra. }
have Hfmt : generic_format radix2 fexp (/4 * Omega).
{ rewrite Hq4. apply Generic_fmt.generic_format_bpow.
  unfold SpecFloat.fexp, SpecFloat.emin.
  apply Z.max_lub; pose proof femax_lb t; pose proof fprec_lb t; lia. }
(* bpow(femax/2-1) <= Omega/4 *)
have Hle : bpow radix2 (femax t / 2 - 1) <= /4 * Omega.
{ rewrite Hq4. apply bpow_le.
  pose proof femax_lb t. pose proof (Z.mul_div_le (femax t) 2 ltac:(lia)). lia. }
have Ha4 : Rabs (FT2R a) <= /4 * Omega by (eapply Rle_trans; [exact Ha | exact Hle]).
have Hb4 : Rabs (FT2R b) <= /4 * Omega by (eapply Rle_trans; [exact Hb | exact Hle]).
(* real product bound |a*b| <= Omega/4 *)
have Hreal : Rabs (FT2R a * FT2R b) <= /4 * Omega.
{ rewrite Rabs_mult. eapply Rle_trans.
  - apply Rmult_le_compat;
      [apply Rabs_pos | apply Rabs_pos | exact Ha | exact Hb].
  - rewrite -bpow_plus Hq4. apply bpow_le.
    pose proof femax_lb t. pose proof (Z.mul_div_le (femax t) 2 ltac:(lia)). lia. }
have Hreal_lt : Rabs (FT2R a * FT2R b) < Omega by lra.
(* finiteness of BMULT a b *)
have HEq : bpow radix2 (femax t - fprec t) <= /4 * Omega
  by (rewrite Hq4; apply bpow_le; pose proof fprec_lb t; lia).
have Hfin : is_finite (BMULT a b) = true.
{ apply no_overflow_mult_is_finite => //.
  eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
  have Hu := ulp_below_overflow _ Hreal_lt. lra. }
(* rounded product bound |round(a*b)| <= Omega/4 *)
have Hpb : Rabs (FT2R (BMULT a b)) <= /4 * Omega.
{ have Hr : round radix2 fexp (Znearest choice) (FT2R a * FT2R b) = FT2R (BMULT a b)
    by rewrite BMULT_round_correct.
  have HFhn : generic_format radix2 fexp (-(/4 * Omega)) by apply generic_format_opp.
  have Hb2 : - (/4 * Omega) <= FT2R a * FT2R b <= /4 * Omega
    by (apply Rabs_le_inv; exact Hreal).
  apply Rabs_le; split.
  - have Hlo : round radix2 fexp (Znearest choice) (-(/4 * Omega))
            <= round radix2 fexp (Znearest choice) (FT2R a * FT2R b).
    { apply round_le; first [ apply FLT_exp_valid; apply fprec_gt_0 | apply valid_rnd_N | lra ]. }
    have Hrgo : round radix2 fexp (Znearest choice) (-(/4 * Omega)) = -(/4 * Omega).
    { apply round_generic; first [ apply valid_rnd_N | apply HFhn ]. }
    rewrite Hrgo Hr in Hlo. lra.
  - have Hhi : round radix2 fexp (Znearest choice) (FT2R a * FT2R b)
            <= round radix2 fexp (Znearest choice) (/4 * Omega).
    { apply round_le; first [ apply FLT_exp_valid; apply fprec_gt_0 | apply valid_rnd_N | lra ]. }
    have Hrgh : round radix2 fexp (Znearest choice) (/4 * Omega) = /4 * Omega.
    { apply round_generic; first [ apply valid_rnd_N | apply Hfmt ]. }
    rewrite Hrgh Hr in Hhi. lra. }
by repeat split.
Qed.

(* MAIN: BOTH components of DWTimesFP3 stay finite under the ACCURATE-ONLY cond
   DWTimesFP_cond_acc, i.e. with NO underflow hypothesis on the leading product.
   Two places in the argument used to need the underflow disjunct; neither does:

     - finiteness of cl1 = Fast2Mult_err xh y is unconditional
       (Fast2Mult_finite_unconditional): the FMA's rounded result is at most
       /2 ulp(xh*y), so it cannot overflow whatever the regime;

     - finiteness of the closing Fast2Sum's error term used to be routed through
       is_finite_FastSum_ulp, whose ulp-ordering premise comes from aux_cl3_le_ch
       and so needs a NORMAL leading product (ulp_FLT_le).  In the underflow gap
       that ordering can genuinely fail.  We take the headroom route instead
       (is_finite_FastSum_small): |cl3| <= 2^(femax-p) <= Omega/4 already bounds
       both Fast2Sum subtractions, with no ordering and hence no regime split.

   So overflow headroom -- which is all DWTimesFP_cond_acc asserts beyond the
   double-word relation -- is exactly what finiteness costs. *)
Lemma DWTimesFP3_finite_acc (xh xl y : ftype t) :
  DWTimesFP_cond_acc xh xl y ->
  is_finite_p (DWTimesFP3 xh xl y).
Proof.
intros (Hfxl & Hdwp & Hfmul & Hreal).
unfold Fast2Mult_cond_acc in Hfmul.
have [Hfxh Hfy] := BMULT_finite_e t xh y Hfmul.
have HyΩ : Rabs (FT2R y) <= Omega
  by (apply Rlt_le; exact (is_finite_no_overflow t y Hfy)).
have Hprod : Rabs (FT2R (BMULT xh y)) <= /2 * Omega
  by (apply aux_round_prod_bnd; [exact Hfmul | exact Hreal]).
have HΩ : 0 < Omega by apply bpow_gt_0.
have HE0 : 0 <= bpow radix2 (femax t - fprec t) by apply bpow_ge_0.
have HEq := @bpow_femax_fprec_le_quarter_Omega t.
(* ch = BMULT xh y : finite, bounded by Omega/2 *)
have Hfch : is_finite (Fast2Mult_mul xh y) = true.
{ unfold Fast2Mult_mul, Fast2Mult, fst. exact Hfmul. }
have Hch4 : Rabs (FT2R (Fast2Mult_mul xh y)) <= /2 * Omega.
{ unfold Fast2Mult_mul, Fast2Mult, fst. exact Hprod. }
(* cl1 = Fast2Mult_err xh y : finite, |cl1| <= 1/2 ulp(xh*y).  Finiteness of the
   error FMA needs NO underflow hypothesis: its rounded result is at most
   /2 ulp(xh*y), so it cannot overflow in any regime. *)
have Hfcl1 : is_finite (Fast2Mult_err xh y) = true.
{ destruct (Fast2Mult_finite_unconditional xh y Hfmul) as [_ H]. exact H. }
have Hcl1u : Rabs (FT2R (Fast2Mult_err xh y)) <= /2 * ulp (FT2R xh * FT2R y).
{ apply Fast2Mult_accuracy_norm; exact Hfmul. }
(* product real bound + low-product bound + cl1 in absolute terms *)
have Hxhy : Rabs (FT2R xh * FT2R y) <= /2 * Omega by exact Hreal.
have Hxhy_lt : Rabs (FT2R xh * FT2R y) < Omega by lra.
have Hxly : Rabs (FT2R xl * FT2R y) <= /2 * bpow radix2 (femax t - fprec t).
{ apply (aux_xly_bnd xh xl y); [exact Hdwp | exact Hxhy | exact HyΩ]. }
have Hcl1b : Rabs (FT2R (Fast2Mult_err xh y)) <= /2 * bpow radix2 (femax t - fprec t).
{ eapply Rle_trans; [exact Hcl1u|]. apply Rmult_le_compat_l; [lra|].
  apply ulp_below_overflow; exact Hxhy_lt. }
(* v := xl*y + cl1, small *)
have Hv : Rabs (FT2R xl * FT2R y + FT2R (Fast2Mult_err xh y))
       <= bpow radix2 (femax t - fprec t).
{ eapply Rle_trans; [apply Rabs_triang|]. lra. }
have Hv_lt : Rabs (FT2R xl * FT2R y + FT2R (Fast2Mult_err xh y)) < Omega by lra.
(* cl3 = BFMA xl y cl1 : finite *)
have Hfcl3 : is_finite (BFMA xl y (Fast2Mult_err xh y)) = true.
{ apply no_overflow_fma_is_finite => //.
  eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
  have Hu := ulp_below_overflow _ Hv_lt. lra. }
(* |cl3| <= bpow(femax-fprec): cl3 = round(v) with |v| <= bpow(femax-fprec),
   and bpow(femax-fprec) is a representable power of 2, so rounding to nearest
   cannot exceed it. *)
have Huv := ulp_below_overflow _ Hv_lt.
have HfmtB : generic_format radix2 fexp (bpow radix2 (femax t - fprec t)).
{ apply Generic_fmt.generic_format_bpow.
  unfold SpecFloat.fexp, SpecFloat.emin.
  apply Z.max_lub; pose proof femax_lb t; pose proof fprec_lb t; lia. }
have HfmtBn : generic_format radix2 fexp (-(bpow radix2 (femax t - fprec t)))
  by apply generic_format_opp.
have Hcl3b : Rabs (FT2R (BFMA xl y (Fast2Mult_err xh y)))
          <= bpow radix2 (femax t - fprec t).
{ rewrite -BFMA_round_correct; [| exact Hfcl3].
  set (v := FT2R xl * FT2R y + FT2R (Fast2Mult_err xh y)).
  have Hvb : - (bpow radix2 (femax t - fprec t)) <= v <= bpow radix2 (femax t - fprec t)
    by (apply Rabs_le_inv; exact Hv).
  apply Rabs_le; split.
  - have Hlo : round radix2 fexp (Znearest choice) (-(bpow radix2 (femax t - fprec t)))
            <= round radix2 fexp (Znearest choice) v.
    { apply round_le; first [ apply FLT_exp_valid; apply fprec_gt_0 | apply valid_rnd_N | lra ]. }
    have Hrgo : round radix2 fexp (Znearest choice) (-(bpow radix2 (femax t - fprec t)))
              = -(bpow radix2 (femax t - fprec t)).
    { apply round_generic; first [ apply valid_rnd_N | apply HfmtBn ]. }
    rewrite Hrgo in Hlo. apply Hlo.
  - have Hhi : round radix2 fexp (Znearest choice) v
            <= round radix2 fexp (Znearest choice) (bpow radix2 (femax t - fprec t)).
    { apply round_le; first [ apply FLT_exp_valid; apply fprec_gt_0 | apply valid_rnd_N | lra ]. }
    have Hrgh : round radix2 fexp (Znearest choice) (bpow radix2 (femax t - fprec t))
              = bpow radix2 (femax t - fprec t).
    { apply round_generic; first [ apply valid_rnd_N | apply HfmtB ]. }
    rewrite Hrgh in Hhi. apply Hhi. }
(* leading component: fst (DWTimesFP3) = BPLUS ch cl3.  Headroom
   /2 Omega + 3/2 bpow(femax-fprec) <= 7/8 Omega < Omega (using
   bpow(femax-fprec) <= /4 Omega at fprec >= 2). *)
have Hfst : is_finite (BPLUS (Fast2Mult_mul xh y)
                             (BFMA xl y (Fast2Mult_err xh y))) = true.
{ apply (no_overflow_sum_is_finite t _ _ Hfch Hfcl3).
  unfold Bplus_no_overflow.
  eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
  have Hsum : Rabs (FT2R (Fast2Mult_mul xh y) + FT2R (BFMA xl y (Fast2Mult_err xh y)))
           <= /2 * Omega + bpow radix2 (femax t - fprec t).
  { eapply Rle_trans; [apply Rabs_triang|]. lra. }
  have Hsum_lt : Rabs (FT2R (Fast2Mult_mul xh y) +
                       FT2R (BFMA xl y (Fast2Mult_err xh y))) < Omega by lra.
  have Hu := ulp_below_overflow _ Hsum_lt. lra. }
split.
- (* fst *)
  change (is_finite (BPLUS (Fast2Mult_mul xh y)
                           (BFMA xl y (Fast2Mult_err xh y))) = true).
  exact Hfst.
- (* snd: headroom route, no closing-Fast2Sum ordering required *)
  apply (is_finite_FastSum_small (Fast2Mult_mul xh y)
                                 (BFMA xl y (Fast2Mult_err xh y)));
    [ lra | exact Hfst ].
Qed.

(* Componentwise projections, and the original strong-cond forms retained for the
   relative (2u^2) tier and its clients: DWTimesFP_cond is strictly stronger than
   DWTimesFP_cond_acc (DDModels.DWTimesFP_cond_acc_of_cond). *)
Lemma DWTimesFP3_fst_finite_acc (xh xl y : ftype t) :
  DWTimesFP_cond_acc xh xl y ->
  is_finite (fst (DWTimesFP3 xh xl y)) = true.
Proof. move => H; exact (proj1 (DWTimesFP3_finite_acc xh xl y H)). Qed.

Lemma DWTimesFP3_snd_finite_acc (xh xl y : ftype t) :
  DWTimesFP_cond_acc xh xl y ->
  is_finite (snd (DWTimesFP3 xh xl y)) = true.
Proof. move => H; exact (proj2 (DWTimesFP3_finite_acc xh xl y H)). Qed.

Lemma DWTimesFP3_fst_finite (xh xl y : ftype t) :
  DWTimesFP_cond xh xl y ->
  is_finite (fst (DWTimesFP3 xh xl y)) = true.
Proof.
move => H.
exact (DWTimesFP3_fst_finite_acc xh xl y (DWTimesFP_cond_acc_of_cond xh xl y H)).
Qed.

(* Relative double-word bound: |xl| <= 2^-p |xh| (the low word is at most an
   ulp-step below the high word).  Subnormal xh forces xl = 0. *)
Lemma aux_dwu_rel (a b : ftype t) :
  double_word_prop a b ->
  Rabs (FT2R b) <= bpow radix2 (- fprec t) * Rabs (FT2R a).
Proof.
move => Hdw.
have Hdwu := aux_dwu a b Hdw.
have Hap : 0 <= Rabs (FT2R a) by apply Rabs_pos.
destruct (Rle_lt_dec (bpow radix2 (emin + fprec t - 1)) (Rabs (FT2R a))) as [Hn | Hs].
- have Hrel : ulp (FT2R a) <= Rabs (FT2R a) * bpow radix2 (1 - fprec t) by apply ulp_FLT_le.
  have HBe : bpow radix2 (1 - fprec t) = 2 * bpow radix2 (- fprec t).
  { have -> : (1 - fprec t = 1 + - fprec t)%Z by lia.
    rewrite bpow_plus. have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
  nra.
- have Hulpe : ulp (FT2R a) = bpow radix2 emin.
  { apply ulp_FLT_small;
      first [ apply fprec_gt_0 | eapply Rlt_trans; [exact Hs | apply bpow_lt; lia] ]. }
  have Hb0 : FT2R b = 0.
  { apply (generic_format_below_emin_eq_zero (t:=t)); [apply generic_format_FLT_FT2R|].
    rewrite Hulpe in Hdwu. have HE := bpow_gt_0 radix2 emin.
    eapply Rle_lt_trans; [exact Hdwu|]. lra. }
  rewrite Hb0 Rabs_R0.
  apply Rmult_le_pos; [apply bpow_ge_0 | exact Hap].
Qed.

(* Magnitude ordering |cl3| <= |ch| for the closing Fast2Sum, in the normal
   product regime |xh*y| >= bpow(emin+2p-1) supplied by the cond's underflow
   disjunction.  This is the FLT counterpart of the paper's F2Sum_correct_abs
   precondition inside DWTimesFP9_correct. *)
Lemma aux_cl3_le_ch (xh xl y : ftype t) :
  double_word_prop xh xl ->
  is_finite (BMULT xh y) = true ->
  is_finite (BFMA xl y (Fast2Mult_err xh y)) = true ->
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R y) ->
  Rabs (FT2R (BFMA xl y (Fast2Mult_err xh y))) <= Rabs (FT2R (Fast2Mult_mul xh y)).
Proof.
move => Hdw Hfmul Hfcl3 Hthresh.
have HApos : 0 < Rabs (FT2R xh * FT2R y)
  by (eapply Rlt_le_trans; [apply bpow_gt_0 | exact Hthresh]).
have Huf' : FT2R xh * FT2R y <> 0 ->
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R y)
  by (move => _; exact Hthresh).
have Hcl1_eq : FT2R (Fast2Mult_err xh y) = FT2R xh * FT2R y - FT2R (Fast2Mult_mul xh y)
  by (apply Fast2MultModel_correct; [exact Hfmul | exact Huf']).
have Hcl1_b : Rabs (FT2R (Fast2Mult_err xh y)) <= /2 * ulp (FT2R xh * FT2R y)
  by (apply Fast2Mult_accuracy_norm; exact Hfmul).
clear Huf'.
have Hulp_xhy : ulp (FT2R xh * FT2R y) <= Rabs (FT2R xh * FT2R y) * bpow radix2 (1 - fprec t).
{ apply ulp_FLT_le. eapply Rle_trans; [|exact Hthresh].
  apply bpow_le. unfold common.emin, SpecFloat.emin. pose proof fprec_lb t; lia. }
have Hxl_y : Rabs (FT2R xl * FT2R y) <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R y).
{ rewrite !Rabs_mult.
  have Hrel := aux_dwu_rel xh xl Hdw.
  have Hyp : 0 <= Rabs (FT2R y) by apply Rabs_pos. nra. }
have HBp : bpow radix2 (1 - fprec t) = 2 * bpow radix2 (- fprec t).
{ have -> : (1 - fprec t = 1 + - fprec t)%Z by lia.
  rewrite bpow_plus. have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
have Hbq : bpow radix2 (- fprec t) <= /4.
{ have -> : (/4 = bpow radix2 (-2))%R by (simpl; lra).
  apply bpow_le; pose proof fprec_lb t; lia. }
have HB0 : 0 <= bpow radix2 (- fprec t) by apply bpow_ge_0.
(* |cl1| <= bpow(-p) |xh*y| *)
have Hcl1Q : Rabs (FT2R (Fast2Mult_err xh y))
          <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R y).
{ eapply Rle_trans; [exact Hcl1_b|].
  eapply Rle_trans; [apply Rmult_le_compat_l; [lra | exact Hulp_xhy]|].
  rewrite HBp. apply Req_le; field. }
(* upper bound on |xl*y + cl1| *)
have Hw_ub : Rabs (FT2R xl * FT2R y + FT2R (Fast2Mult_err xh y))
          <= 2 * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R y).
{ eapply Rle_trans; [apply Rabs_triang|].
  eapply Rle_trans; [apply Rplus_le_compat; [exact Hxl_y | exact Hcl1Q]|].
  apply Req_le; ring. }
(* lower bound on |ch| *)
have Hch_lb : Rabs (FT2R xh * FT2R y) - bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R y)
           <= Rabs (FT2R (Fast2Mult_mul xh y)).
{ have Hch_e : FT2R (Fast2Mult_mul xh y) = FT2R xh * FT2R y - FT2R (Fast2Mult_err xh y)
    by (rewrite Hcl1_eq; ring).
  rewrite Hch_e.
  eapply Rle_trans; [| apply Rabs_triang_inv].
  apply Rplus_le_compat_l, Ropp_le_contravar. exact Hcl1Q. }
(* 3 bpow(-p) <= 1  (p >= 2) *)
have H3B : 3 * bpow radix2 (- fprec t) <= 1.
{ eapply Rle_trans; [apply Rmult_le_compat_l; [lra | exact Hbq] | lra]. }
(* combine: |w| <= |ch| *)
have Hwb : Rabs (FT2R xl * FT2R y + FT2R (Fast2Mult_err xh y))
        <= Rabs (FT2R (Fast2Mult_mul xh y)).
{ eapply Rle_trans; [exact Hw_ub|]. eapply Rle_trans; [| exact Hch_lb].
  apply Rminus_le.
  replace (2 * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R y) -
           (Rabs (FT2R xh * FT2R y) -
            bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R y)))
     with (- (Rabs (FT2R xh * FT2R y) * (1 - 3 * bpow radix2 (- fprec t)))) by ring.
  rewrite -Ropp_0. apply Ropp_le_contravar.
  apply Rmult_le_pos; lra. }
(* |cl3| = |round w| <= |ch| via round monotonicity into format |ch| *)
rewrite -BFMA_round_correct; [| exact Hfcl3].
apply abs_round_le_generic.
all: try exact Hwb.
all: try apply valid_rnd_N.
all: try apply generic_format_abs.
all: try exact valid_fexp_inst.
all: try apply generic_format_FLT_FT2R.
Qed.

(* Finiteness of the snd output of DWTimesFP3.  Historically this was derived
   from the cond's underflow disjunction, via the closing-Fast2Sum ulp ordering
   (ulp cl3 <= ulp ch when the leading product is normal, else ch = 0) fed to
   is_finite_FastSum_ulp.  DWTimesFP3_finite_acc above now gets it in every
   regime from overflow headroom alone, so this is just the strong-cond
   specialization.  aux_cl3_le_ch is still needed for the double-word property,
   which genuinely does depend on the ordering. *)
Lemma DWTimesFP3_snd_finite (xh xl y : ftype t) :
  DWTimesFP_cond xh xl y ->
  is_finite (snd (DWTimesFP3 xh xl y)) = true.
Proof.
move => H.
exact (DWTimesFP3_snd_finite_acc xh xl y (DWTimesFP_cond_acc_of_cond xh xl y H)).
Qed.

(* The output pair of DWTimesFP3 (Algorithm 9) is itself a double word.  The
   closing step of DWTimesFP3 is Fast2Sum ch cl3 (ch = Fast2Mult_mul xh y,
   cl3 = BFMA xl y cl1), so the double-word property reduces to Fast2Sum_is_DW.

   We first prove it from the *basic* precondition — the two Fast2Sum
   obligations on the closing arguments (finiteness of the sum and the
   magnitude ordering |cl3| <= |ch|) — and then show the operation cond
   supplies exactly those two obligations. *)

(* (1) result from the basic precondition (the closing Fast2Sum's own
   requirements): this is Fast2Sum_is_DW at the DWTimesFP3 closing site. *)
Lemma DWTimesFP3_double_word_from_pre (xh xl y : ftype t) :
  is_finite (BPLUS (Fast2Mult_mul xh y) (BFMA xl y (Fast2Mult_err xh y))) = true ->
  Rabs (FT2R (BFMA xl y (Fast2Mult_err xh y)))
    <= Rabs (FT2R (Fast2Mult_mul xh y)) ->
  double_word (fst (DWTimesFP3 xh xl y)) (snd (DWTimesFP3 xh xl y)).
Proof.
move => Hfp Hord.
exact (Fast2Sum_is_DW (Fast2Mult_mul xh y)
         (BFMA xl y (Fast2Mult_err xh y)) Hfp Hord).
Qed.

(* (2) the operation cond supplies the basic precondition:
     - finiteness              <- DWTimesFP3_fst_finite;
     - the ordering |cl3|<=|ch| <- aux_cl3_le_ch on the normal leg; on the
       cond's underflow leg (xh*y = 0) both ch and cl3 collapse to 0, so the
       ordering is 0 <= 0. *)
Lemma DWTimesFP3_double_word_pre_of_cond (xh xl y : ftype t) :
  DWTimesFP_cond xh xl y ->
  is_finite (BPLUS (Fast2Mult_mul xh y) (BFMA xl y (Fast2Mult_err xh y))) = true
  /\ Rabs (FT2R (BFMA xl y (Fast2Mult_err xh y)))
       <= Rabs (FT2R (Fast2Mult_mul xh y)).
Proof.
move => Hcond.
have Hfp : is_finite (BPLUS (Fast2Mult_mul xh y)
                            (BFMA xl y (Fast2Mult_err xh y))) = true
  by exact (DWTimesFP3_fst_finite xh xl y Hcond).
destruct (BPLUS_finite_e t (Fast2Mult_mul xh y)
            (BFMA xl y (Fast2Mult_err xh y)) Hfp) as [Hfch Hfcl3].
move: Hcond => [Hfxl [Hdwp [Hf2m Hreal]]].
have Huf := proj2 Hf2m.
have Hfmul : is_finite (BMULT xh y) = true by exact (proj1 Hf2m).
split; [ exact Hfp | ].
destruct Huf as [Hxy0 | Hthresh].
- (* underflow leg: ch = 0 and cl3 = 0, so the ordering is 0 <= 0 *)
  have Hch0 : FT2R (Fast2Mult_mul xh y) = 0.
  { unfold Fast2Mult_mul, Fast2Mult, fst.
    rewrite -BMULT_round_correct // Hxy0 round_0 //. }
  have Huf' : FT2R xh * FT2R y <> 0 ->
    bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R y)
    by (move => Hne; exfalso; exact (Hne Hxy0)).
  have Herr0 : FT2R (Fast2Mult_err xh y) = 0.
  { have Heq := Fast2MultModel_correct xh y Hfmul Huf'.
    rewrite Heq Hxy0 Hch0; ring. }
  have Hxly0 : FT2R xl * FT2R y = 0.
  { destruct (Rmult_integral _ _ Hxy0) as [Hxh0 | Hy0].
    - have Hxl0 : FT2R xl = 0 by exact (double_word_0 xh xl Hdwp Hxh0).
      rewrite Hxl0; ring.
    - rewrite Hy0; ring. }
  have Hcl30 : FT2R (BFMA xl y (Fast2Mult_err xh y)) = 0.
  { rewrite -(BFMA_round_correct t xl y (Fast2Mult_err xh y) Hfcl3).
    rewrite Herr0 Hxly0 Rplus_0_r round_0 //. }
  rewrite Hch0 Hcl30 Rabs_R0; apply Rle_refl.
- (* normal leg: the closing-Fast2Sum ordering already proven for accuracy *)
  apply aux_cl3_le_ch; [ exact Hdwp | exact Hfmul | exact Hfcl3 | exact Hthresh ].
Qed.

(* (3) cond-level corollary used by the VST guarded spec. *)
Lemma DWTimesFP3_double_word (xh xl y : ftype t) :
  DWTimesFP_cond xh xl y ->
  double_word (fst (DWTimesFP3 xh xl y)) (snd (DWTimesFP3 xh xl y)).
Proof.
move => Hcond.
have [Hfp Hord] := DWTimesFP3_double_word_pre_of_cond xh xl y Hcond.
exact (DWTimesFP3_double_word_from_pre xh xl y Hfp Hord).
Qed.

End DWTimesFP_Finite.

(* ============================================================
   Layer-1 / Layer-2 accuracy for DWTimesFP3 (Algorithm 9).

   Per PROOF_PATTERN.md.  The Layer-1 theorem DWTimesFP_relerr_bound is
   proved below by:
     - collapsing the whole double-word error to a single FLT rounding
       error  round(w) - w  (relerr_error_eq), then
     - on the normal-w leg, the FLX->FLT bridge DWTimesFP3_FLX_FLT_weak
       (minimal emin+2*fprec-1 product threshold) lifts the paper's tight
       FLX bound paper_proofs.DWTimesFP.DWTimesFP9_correct to the FLT
       conclusion; on the subnormal-w leg a direct |round(w)-w| / |xr*yr|
       bound gives < 2u^2.

   The corollary DWTimesFP_accuracy_from_cond is the Layer-2 interface
   used by the VST guarded wrapper specs.  Both carry the TwoProdE
   modeling hypothesis (TwoProd = FLX Fast2Mult), as does DWTimesFP9_correct.
   ============================================================ *)

Section DWTimesFP_Accuracy.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation u     := (bpow Zaux.radix2 (- fprec t)).
Notation fexp  := (SpecFloat.fexp (fprec t) (femax t)).
Notation eminA := (SpecFloat.emin (fprec t) (femax t)).
Notation ulp   := (Ulp.ulp Zaux.radix2 fexp).
Notation OmegaA := (bpow Zaux.radix2 (femax t)).

(* Valid_exp for SpecFloat.fexp, so Flocq's ulp/round lemmas discharge it. *)
Local Instance valid_fexp_inst_acc : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.

Variables (xh xl y : ftype t).

(* The TwoProd of the FLX model (paper_proofs.DWTimesFP) is an abstract
   Parameter; in this development it is the concrete FLX Fast2Mult.  This is the
   same modeling assumption already carried by DWTimesFP3_FLX_FLT and required by
   DWTimesFP9_correct; the C-level analog is that the compiled product realizes
   Fast2Mult. *)

Let zh := FT2R (fst (DWTimesFP3 xh xl y)).
Let zl := FT2R (snd (DWTimesFP3 xh xl y)).
Let xr := (FT2R xh + FT2R xl).
Let yr := FT2R y.

Definition relative_error_DWTimesFP : R :=
  Rabs (((zh + zl) - xr * yr) / (xr * yr)).

(* Underflow regime, straightforward part: when the exact product xr*yr is 0
   the relative error is 0 (Coq's _/0 = 0).  This is exactly the cond's
   xh*y = 0 disjunct, since FT2R xh = 0 forces FT2R xl = 0 (double_word). *)
Lemma relerr_0_of_xryr0 : xr * yr = 0 -> relative_error_DWTimesFP = 0.
Proof.
move => H. unfold relative_error_DWTimesFP. rewrite H.
rewrite /Rdiv Rinv_0 Rmult_0_r Rabs_R0 //.
Qed.

Lemma xryr0_of_prod0 :
  double_word_prop xh xl -> FT2R xh * FT2R y = 0 -> xr * yr = 0.
Proof.
move => Hdw Hxy0.
destruct (Rmult_integral _ _ Hxy0) as [Hxh0 | Hy0].
- (* FT2R xh = 0 -> FT2R xl = 0 (double_word) -> xr = 0 *)
  have Hr : rounded t (FT2R xl) = FT2R xl
    by (unfold rounded; apply round_generic;
        [ apply valid_rnd_N | apply generic_format_FLT_FT2R ]).
  have Hxl0 : FT2R xl = 0.
  { move: Hdw; rewrite /double_word_prop Hxh0 Rplus_0_l Hr.
    move => H; exact (eq_sym H). }
  unfold xr, yr. rewrite Hxh0 Hxl0. ring.
- unfold xr, yr. rewrite Hy0. ring.
Qed.

(* Converse side condition: above the TwoProd exactness threshold the exact
   product is nonzero, so a relative error is meaningful and one may divide
   by xr*yr.  Every statement in this file that converts between the relative
   and absolute forms needs exactly these three facts, so they are proved
   once here rather than inline at each use. *)
Lemma xryr_ne_0_of_big :
  double_word_prop xh xl ->
  bpow radix2 (eminA + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R y) ->
  FT2R xh * FT2R y <> 0 /\ FT2R y <> 0 /\ xr <> 0 /\ xr * yr <> 0.
Proof.
move => Hdw Hbig.
have HP0 : FT2R xh * FT2R y <> 0.
{ intro Habs. move: Hbig. rewrite Habs Rabs_R0.
  have := bpow_gt_0 radix2 (eminA + 2 * fprec t - 1). lra. }
have Hyne : FT2R y <> 0 by (intro Hy0; apply HP0; rewrite Hy0 Rmult_0_r).
have Hxrne : xr <> 0.
{ rewrite /xr => Hxr0. apply HP0.
  have Hxh0 : FT2R xh = 0.
  { move: Hdw. rewrite /double_word_prop /rounded Hxr0 round_0. by move ->. }
  rewrite Hxh0; ring. }
split; [exact HP0 | split; [exact Hyne | split; [exact Hxrne |]]].
apply Rmult_integral_contrapositive_currified; [exact Hxrne | exact Hyne].
Qed.

(* KEYSTONE: on the normal leg the whole double-word error collapses to a
   single FLT rounding error.  Since Fast2Sum is exact (zh+zl = ch+cl3) and the
   product error cl1 = xh*y - ch is representable (Fast2MultModel_correct, valid
   because |xh*y| >= bpow(emin+2p-1)), and cl3 = round(xl*y + cl1):

     (zh+zl) - xr*yr = round(w) - w,   where  w = xl*y + cl1.

   This is the foundation for both the subnormal-w bound (proved below) and the
   normal-w bound (the tight 2u^2 constant, via the FLX bridge). *)
Lemma relerr_error_eq :
  double_word_prop xh xl ->
  is_finite_p (DWTimesFP3 xh xl y) ->
  is_finite (BMULT xh y) = true ->
  bpow radix2 (eminA + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R y) ->
  let cl1 := FT2R (Fast2Mult_err xh y) in
  let w   := (FT2R xl * FT2R y + cl1)%R in
  (zh + zl - xr * yr)%R = (round radix2 fexp (Znearest choice) w - w)%R.
Proof.
move => Hdwp Hfp Hfmul Hbig cl1 w.
set ch  := Fast2Mult_mul xh y.
set cl3 := BFMA xl y (Fast2Mult_err xh y).
have Hfst : is_finite (BPLUS ch cl3) = true by exact (proj1 Hfp).
have Hfcl3 : is_finite cl3 = true
  by (destruct (BPLUS_finite_e t ch cl3 Hfst) as [_ Hf]; exact Hf).
have Hord : Rabs (FT2R cl3) <= Rabs (FT2R ch)
  by exact (aux_cl3_le_ch xh xl y Hdwp Hfmul Hfcl3 Hbig).
have Hexact : FT2R (Fast2Sum_err ch cl3)
            = FT2R ch + FT2R cl3 - FT2R (Fast2Sum_sum ch cl3)
  by exact (FastTwoSum_correct ch cl3 Hfst Hord).
have Huf' : FT2R xh * FT2R y <> 0 ->
  bpow radix2 (eminA + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R y)
  by (move => _; exact Hbig).
have Hcl1_eq : FT2R (Fast2Mult_err xh y) = FT2R xh * FT2R y - FT2R ch
  by exact (Fast2MultModel_correct xh y Hfmul Huf').
have Hcl3_eq : FT2R cl3
             = round radix2 fexp (Znearest choice) (FT2R xl * FT2R y + cl1)
  by (unfold cl1; symmetry; exact (BFMA_round_correct t xl y (Fast2Mult_err xh y) Hfcl3)).
(* zh + zl = FT2R ch + FT2R cl3 *)
have Hsum : (zh + zl)%R = (FT2R ch + FT2R cl3)%R.
{ unfold zh, zl.
  have Hfst_eq : fst (DWTimesFP3 xh xl y) = Fast2Sum_sum ch cl3 by reflexivity.
  have Hsnd_eq : snd (DWTimesFP3 xh xl y) = Fast2Sum_err ch cl3 by reflexivity.
  rewrite Hfst_eq Hsnd_eq Hexact. ring. }
rewrite Hsum Hcl3_eq.
unfold xr, yr, w, cl1.
rewrite Hcl1_eq. ring.
Qed.

(* Load-bearing Layer-1 theorem.  Carries the underflow disjunction (the same
   shape as DWTimesFP_cond's) and dispatches on it:
     - underflow leg (xh*y = 0): the exact product xr*yr is 0, so relerr = 0
       (PROVEN here via relerr_0_of_xryr0 + xryr0_of_prod0);
     - normal leg (|xh*y| >= bpow(emin+2*fprec-1)): the bridge from
       DWTimesFP9_correct via DWTimesFP3_FLX_FLT, with the FMA-underflow /
       [emin+2p-1, emin+3p) gap sub-case via a direct |abs err|/|xr*yr| bound.
   This is the regime split; the cond-level corollary below is a thin wrapper. *)
Theorem DWTimesFP_relerr_bound :
  double_word xh xl ->
  is_finite_p (DWTimesFP3 xh xl y) ->
  (3 <= fprec t)%Z ->
  (FT2R xh * FT2R y = 0 \/
   bpow Zaux.radix2 (SpecFloat.emin (fprec t) (femax t) + 2 * fprec t - 1)
   <= Rabs (FT2R xh * FT2R y)) ->
  relative_error_DWTimesFP <= 2 * u ^ 2.
Proof.
intros Hdw Hfin Hp3 Huf.
destruct Huf as [Hxy0 | Hbig].
- (* underflow regime: exact product is 0, so relerr = 0 *)
  rewrite (relerr_0_of_xryr0 (xryr0_of_prod0 Hdw Hxy0)).
  apply Rmult_le_pos; [lra | apply pow_le; apply bpow_ge_0].
- (* normal regime: |xh*y| >= bpow(emin+2*fprec-1).  The whole double-word error
     collapses (relerr_error_eq) to the single rounding error of
       w = xl*y + cl1   (cl1 = product error of xh*y),
     i.e. (zh+zl) - xr*yr = round(w) - w.  Split on whether w is normal:
       - |w| >= bpow(emin+fprec-1): every rounding agrees with the FLX model, so
         the FLX bridge (DWTimesFP3_FLX_FLT_weak) + the paper's tight bound
         (DWTimesFP9_correct) give exactly 2u^2;
       - |w| < bpow(emin+fprec-1): w is subnormal, so |round(w)-w| <= 1/2 bpow emin
         is tiny against |xr*yr| >= bpow(emin+2*fprec-1)(1-u), giving < 2u^2. *)
  have Hfmul : is_finite (BMULT xh y) = true by exact (FIN3 xh xl y Hfin).
  move: (xryr_ne_0_of_big Hdw Hbig) => [HP0 [Hyne [Hxrne Hxryrne]]].
  have Herr := relerr_error_eq Hdw Hfin Hfmul Hbig.
  cbv zeta in Herr.
  set w := (FT2R xl * FT2R y + FT2R (Fast2Mult_err xh y))%R in Herr *.
  destruct (Rlt_le_dec (Rabs w) (bpow radix2 (eminA + fprec t - 1)))
    as [Hwsub | Hwnorm].
  + (* subnormal w: tiny absolute error against a large product *)
    have Hulpw : ulp w = bpow radix2 eminA.
    { apply ulp_FLT_small;
        first [ apply fprec_gt_0
              | eapply Rlt_trans; [exact Hwsub | apply bpow_lt; lia] ]. }
    have Herror : Rabs (round radix2 fexp (Znearest choice) w - w)
                <= /2 * bpow radix2 eminA.
    { have He := @error_le_half_ulp radix2 fexp valid_fexp_inst_acc choice w.
      rewrite Hulpw in He. exact He. }
    have Hu0  : 0 <= u by apply bpow_ge_0.
    have Hbq  : u <= /4.
    { have -> : (/4 = bpow radix2 (-2))%R by (simpl; lra).
      apply bpow_le; pose proof fprec_lb t; lia. }
    have HPpos : 0 < Rabs (FT2R xh * FT2R y) by (apply Rabs_pos_lt; exact HP0).
    have Hxly : Rabs (FT2R xl * FT2R y) <= u * Rabs (FT2R xh * FT2R y).
    { rewrite !Rabs_mult -Rmult_assoc.
      apply Rmult_le_compat_r; [apply Rabs_pos | exact (aux_dwu_rel xh xl Hdw)]. }
    have Hden1 : Rabs (FT2R xh * FT2R y) * (1 - u) <= Rabs (xr * yr).
    { have Hge : Rabs (FT2R xh * FT2R y) - Rabs (FT2R xl * FT2R y)
               <= Rabs (FT2R xh * FT2R y + FT2R xl * FT2R y).
      { have H := Rabs_triang_inv (FT2R xh * FT2R y) (- (FT2R xl * FT2R y)).
        rewrite Rabs_Ropp in H.
        replace (FT2R xh * FT2R y - - (FT2R xl * FT2R y))
           with (FT2R xh * FT2R y + FT2R xl * FT2R y) in H by ring.
        exact H. }
      have Hxryr_eq : xr * yr = FT2R xh * FT2R y + FT2R xl * FT2R y
        by (rewrite /xr /yr; ring).
      rewrite Hxryr_eq. nra. }
    have Hu2pos : 0 <= 2 * u ^ 2
      by (apply Rmult_le_pos; [lra | apply pow_le; apply bpow_ge_0]).
    have HEpos : 0 < bpow radix2 eminA by apply bpow_gt_0.
    have H1u : 0 <= 1 - u by lra.
    have Hcollapse : 2 * u ^ 2 * bpow radix2 (eminA + 2 * fprec t - 1)
                   = bpow radix2 eminA.
    { have Hu2 : u ^ 2 = bpow radix2 (- (2 * fprec t)).
      { change (u ^ 2) with (u * (u * 1)).
        rewrite Rmult_1_r -bpow_plus. f_equal. lia. }
      have Hprod : bpow radix2 (- (2 * fprec t)) * bpow radix2 (eminA + 2 * fprec t - 1)
                 = bpow radix2 (eminA - 1).
      { rewrite -bpow_plus. f_equal. lia. }
      rewrite Hu2 (Rmult_assoc 2 (bpow radix2 (- (2 * fprec t)))
                               (bpow radix2 (eminA + 2 * fprec t - 1))) Hprod.
      have -> : bpow radix2 eminA = bpow radix2 (eminA - 1) * bpow radix2 1.
      { rewrite -bpow_plus. f_equal. lia. }
      have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
    have Hden : /2 * bpow radix2 eminA <= 2 * u ^ 2 * Rabs (xr * yr).
    { apply (Rle_trans _ (bpow radix2 eminA * (1 - u))).
      { nra. }
      { rewrite -Hcollapse Rmult_assoc.
        apply Rmult_le_compat_l; [exact Hu2pos |].
        eapply Rle_trans; [| exact Hden1].
        apply Rmult_le_compat_r; [exact H1u | exact Hbig]. } }
    have HfinalN : Rabs (round radix2 fexp (Znearest choice) w - w)
                <= 2 * u ^ 2 * Rabs (xr * yr)
      by (eapply Rle_trans; [exact Herror | exact Hden]).
    unfold relative_error_DWTimesFP. rewrite Herr /Rdiv Rabs_mult Rabs_inv.
    apply (Rle_trans _ ((2 * u ^ 2 * Rabs (xr * yr)) * / Rabs (xr * yr))).
    { apply Rmult_le_compat_r;
        [ apply Rlt_le, Rinv_0_lt_compat, Rabs_pos_lt; exact Hxryrne | exact HfinalN ]. }
    { rewrite Rmult_assoc Rinv_r;
        [ rewrite Rmult_1_r; apply Rle_refl
        | apply Rgt_not_eq, Rabs_pos_lt; exact Hxryrne ]. }
  + (* normal w: FLX bridge then the paper's tight 2u^2 bound *)
    have Hbridge := DWTimesFP3_FLX_FLT_weak xh xl y Hfin Hbig Hwnorm.
    have HFy : generic_format radix2 (FLX_exp (fprec t)) (FT2R y)
      by (apply (generic_format_FLX_FLT radix2 eminA (fprec t));
          apply generic_format_FLT_FT2R).
    have HDWx : DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl)
      by (apply (dw_word_DWdouble xh xl y); exact Hdw).
    (* Explicit (folded) type so the [let (zh,zl) := DWTimesFP9 ...] does not
       cascade open now that TwoProd is a Definition; this keeps DWTimesFP9
       foldable for the rewrite by Hbridge, exactly as when TwoProd was a
       Parameter. *)
    have Hpaper :
      (let (zh, zl) := DWTimesFP9 (fprec t) choice (FT2R xh) (FT2R xl) (FT2R y) in
       let xy := (FT2R xh + FT2R xl) * FT2R y in
       Rabs ((zh + zl - xy) / xy) <= 2 * u ^ 2 /\
       DWPlus.double_word (fprec t) choice zh zl)
      := @DWTimesFP9_correct (fprec t) choice eq_refl Hp3
           (FT2R xh) (FT2R xl) (FT2R y) HDWx HFy.
    rewrite Hbridge in Hpaper.
    destruct Hpaper as [Hb _].
    unfold relative_error_DWTimesFP. exact Hb.
Qed.

(* ------------------------------------------------------------------
   Layer 2: the cond-level relative bound.

   DWTimesFP_cond's job here is to supply the underflow disjunction that
   Layer 1 needs; DWTimesFP_cond_no_gap isolates that step, and is also
   what tells the whole-range theory below (DWTimesFP3_error_mixed) that
   its eta term is unreachable under the cond.
   ------------------------------------------------------------------ *)

(* The cond forbids the nonzero underflow gap.  This is literally the
   third field of DWTimesFP_cond (DDModels.v), projecting the underflow
   disjunct of Fast2Mult_cond: under the cond the leading product is
   either exactly zero or at least the TwoProd exactness threshold.  So
   the gap arm of DWTimesFP3_error_mixed is unreachable and its
   C_FP * 2^emin floor term is never paid -- which is precisely why the
   cond-level bound below is a pure 2u^2 relative bound. *)
Lemma DWTimesFP_cond_no_gap :
  DWTimesFP_cond xh xl y ->
  FT2R xh * FT2R y = 0 \/
  bpow Zaux.radix2 (eminA + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R y).
Proof. move => [_ [_ [Hf2m _]]]; exact (proj2 Hf2m). Qed.

(* Layer-2 corollary.  The cond supplies the two Layer-1 hypotheses
   (double_word_prop is convertible with double_word; is_finite_p comes
   from DWTimesFP3_fst_finite / DWTimesFP3_snd_finite), and
   DWTimesFP_cond_no_gap supplies the underflow disjunction -- i.e. it is
   the cond, via the gap-exclusion lemma, that buys the eta-free bound.
   The 3 <= fprec t hypothesis is threaded by the caller (true for
   Tdouble). *)
Corollary DWTimesFP_accuracy_from_cond :
  (3 <= fprec t)%Z ->
  DWTimesFP_cond xh xl y ->
  relative_error_DWTimesFP <= 2 * u ^ 2.
Proof.
intros Hp3 Hcond.
have Hfp : is_finite_p (DWTimesFP3 xh xl y).
{ split.
  - exact (DWTimesFP3_fst_finite xh xl y Hcond).
  - exact (DWTimesFP3_snd_finite xh xl y Hcond). }
have Hnogap := DWTimesFP_cond_no_gap Hcond.
move: Hcond => [Hfxl [Hdwp [Hf2m Hreal]]].
exact (DWTimesFP_relerr_bound Hdwp Hfp Hp3 Hnogap).
Qed.

End DWTimesFP_Accuracy.

(* ==================================================================
   WHOLE-RANGE (MIXED) ANALYSIS OF ALGORITHM 9

   Everything above assumes the leading product is either zero or at
   least the TwoProd exactness threshold 2^(emin+2p-1) -- the underflow
   disjunct of Fast2Mult_cond -- because below it the product residual
   cl1 = xh*y - ch is not representable and no relative bound can hold.
   This part removes that assumption.  In the complementary "gap" the
   error is instead governed by the physical underflow floor
   eta = 2^emin, and the two regimes assemble into the file's primary
   public result, DWTimesFP3_error_mixed, whose only hypotheses are
   p >= 3, a double-word input, and a finite output: NO cond, and in
   particular no underflow disjunct.  DWTimesFP_cond_no_gap above is the
   bridge back: under the cond the gap arm is unreachable, so the eta
   term is never paid and the pure 2u^2 bound is recovered.

   This material lives outside Section DWTimesFP_Accuracy because it is
   written with @common.emin t rather than that section's eminA notation
   (convertible, but not syntactically equal, and the fold/change steps
   below depend on the spelling).

   It previously sat in DWDivDW_acc.v behind p >= 14.  That bound was an
   artifact of the proof route, not of the mathematics -- see the two
   notes at Fast2Sum_sum_exact_of_sum_small and in the unordered arm of
   DWTimesFP3_error_floor_gap -- and everything here holds at p >= 3.
   DWDivDW_acc still consumes these lemmas for its reciprocal-refinement
   block, so they are a cross-operation proof interface as well as
   multiplication's mixed API.

   The operation-independent FLT rounding facts used below live in
   FLT_helpers.  Order below: generic Fast2Sum facts, then the Algorithm-9
   building blocks, then the gap regime, then the public assembly.
   ================================================================== *)

(* ==================================================================
   ALGORITHM-9 UNDERFLOW-FLOOR BLOCK  (whole-range / mixed API)

   Below the TwoProd exactness threshold 2^(emin+2p-1) the leading
   product's residual is not representable, so the relative analysis
   above does not apply and the error is governed by an absolute floor
   instead.  These lemmas bound that floor and assemble the two regimes
   into the file's primary public result, DWTimesFP3_error_mixed.

   They live outside Section DWTimesFP_Accuracy because they are stated
   with @common.emin t rather than that section's eminA notation (the
   two are convertible but not syntactically equal, and the fold/change
   steps below depend on the spelling).

   Previously in DWDivDW_acc.v behind a p >= 14 hypothesis, which was an
   artifact of the proof route, not of the mathematics: everything here
   holds at p >= 3.  DWDivDW_acc still consumes these lemmas, so they are
   a cross-operation proof interface as well as multiplication's mixed API.
   ================================================================== *)

(* ---------- generic Fast2Sum: exactness and closure from its sum ---------- *)

(** Runtime Fast2Sum is exact whenever the EXACT SUM still lies on the shared
    FLT/FIX lattice at exponent [emin], i.e. [|a+b| <= 2^(emin+p)].  Both
    addends are automatically multiples of [2^emin] -- [FLT_exp] is bounded
    below by [emin], so every FLT value is -- hence the only requirement is on
    the sum, and NO precision hypothesis is needed.  Above [2^(emin+p)] the
    lattice coarsens and an [eta] multiple need no longer be representable,
    which is exactly what this bound excludes. *)
Lemma Fast2Sum_sum_exact_of_sum_small {NANS : Nans} {t : type}
    {STD : is_standard t} (a b : ftype t) :
  is_finite_p (Fast2Sum a b) ->
  Rabs (FT2R a+FT2R b)<=bpow radix2 (@common.emin t+fprec t) ->
  FT2R (fst (Fast2Sum a b))+FT2R (snd (Fast2Sum a b))=
    FT2R a+FT2R b.
Proof.
move => FIN Hsumabs.
have Fa : generic_format radix2
    (SpecFloat.fexp (fprec t) (femax t)) (FT2R a)
  by apply generic_format_FLT_FT2R.
have Fb : generic_format radix2
    (SpecFloat.fexp (fprec t) (femax t)) (FT2R b)
  by apply generic_format_FLT_FT2R.
have Faf := generic_format_FIX_FLT radix2 (@common.emin t)
  (fprec t) (FT2R a) Fa.
have Fbf := generic_format_FIX_FLT radix2 (@common.emin t)
  (fprec t) (FT2R b) Fb.
have Fsumfix : generic_format radix2 (FIX_exp (@common.emin t))
    (FT2R a+FT2R b).
{ destruct (FIX_format_generic radix2 (@common.emin t) (FT2R a) Faf)
    as [fa Hfa Hefa].
  destruct (FIX_format_generic radix2 (@common.emin t) (FT2R b) Fbf)
    as [fb Hfb Hefb].
  pose fs := Float radix2 (Fnum fa+Fnum fb) (@common.emin t).
  apply generic_format_FIX.
  apply (FIX_spec radix2 (@common.emin t) (FT2R a+FT2R b) fs).
  - unfold fs, F2R. simpl.
    rewrite Hfa Hfb /F2R Hefa Hefb. rewrite plus_IZR. ring.
  - reflexivity. }
have Fsum : generic_format radix2
    (SpecFloat.fexp (fprec t) (femax t)) (FT2R a+FT2R b).
{ apply generic_format_FLT_FIX.
  - apply fprec_gt_0.
  - exact Hsumabs.
  - exact Fsumfix. }
have Fsumx : generic_format radix2 (FLX_exp (fprec t))
    (FT2R a+FT2R b).
{ apply (generic_format_FLX_FLT radix2 (@common.emin t) (fprec t)).
  exact Fsum. }
have Fax : generic_format radix2 (FLX_exp (fprec t)) (FT2R a).
{ apply (generic_format_FLX_FLT radix2 (@common.emin t) (fprec t)); exact Fa. }
have Fbx : generic_format radix2 (FLX_exp (fprec t)) (FT2R b).
{ apply (generic_format_FLX_FLT radix2 (@common.emin t) (fprec t)); exact Fb. }
have Heq := FastTwoSumEq_FLT a b FIN.
have Hsumr : round radix2 (FLX_exp (fprec t)) (Znearest choice)
    (FT2R a+FT2R b)=FT2R a+FT2R b.
{ apply round_generic; [apply valid_rnd_N|exact Fsumx]. }
have Hbr : round radix2 (FLX_exp (fprec t)) (Znearest choice)
    (FT2R b)=FT2R b.
{ apply round_generic; [apply valid_rnd_N|exact Fbx]. }
have Hpaper : F2Sum.Fast2Sum (fprec t) choice (FT2R a) (FT2R b)=
    (FT2R a+FT2R b,0).
{ unfold F2Sum.Fast2Sum, F2SumFLX.Fast2Sum.
  rewrite Hsumr.
  replace (FT2R a+FT2R b-FT2R a)%R with (FT2R b) by ring.
  rewrite Hbr.
  replace (FT2R b-FT2R b)%R with 0 by ring.
  rewrite round_0. reflexivity. }
rewrite Hpaper /F2Rp /= in Heq.
have Hh := f_equal fst Heq.
have Hl := f_equal snd Heq.
simpl in Hh, Hl. rewrite -Hh -Hl. ring.
Qed.

Lemma Fast2Sum_double_word_of_sum {NANS : Nans} {t : type}
    {STD : is_standard t} (a b : ftype t) :
  is_finite_p (Fast2Sum a b) ->
  FT2R (fst (Fast2Sum a b))+FT2R (snd (Fast2Sum a b))=
    FT2R a+FT2R b ->
  double_word_prop (fst (Fast2Sum a b)) (snd (Fast2Sum a b)).
Proof.
move => FIN Hsum.
set e := Fast2Sum a b.
fold e in Hsum.
unfold double_word_prop, rounded. fold e. rewrite Hsum.
change (FT2R (fst e)=round radix2
  (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
  (FT2R a+FT2R b)).
have Hfst : fst e=BPLUS a b by reflexivity.
rewrite Hfst. symmetry. apply BPLUS_round_correct. exact (proj1 FIN).
Qed.

(* ---------- Algorithm-9 building blocks ---------- *)

(** A compensated product loses only an underflow-floor term even when its
    exact product error is too small for the usual Fast2Mult exactness
    theorem.  Above the [emin+2p-1] threshold the sum is exact; below it the
    relative error of the low FMA is itself bounded by half a floor ulp. *)
Lemma Fast2Mult_sum_error_floor {NANS : Nans} {t : type}
    {STD : is_standard t} (a b : ftype t) :
  (3 <= fprec t)%Z -> is_finite_p (Fast2Mult a b) ->
  Rabs (FT2R (Fast2Mult_mul a b)+FT2R (Fast2Mult_err a b)-
        FT2R a*FT2R b)
    <= /2*bpow radix2 (@common.emin t).
Proof.
move => Hp3 FIN.
set x := (FT2R a*FT2R b)%R.
set ch := Fast2Mult_mul a b.
set cl := Fast2Mult_err a b.
set r := (x-FT2R ch)%R.
set u := bpow radix2 (-fprec t).
set eta := bpow radix2 (@common.emin t).
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /8.
{ unfold u. have -> : (/8:R)=bpow radix2 (-3) by (simpl;lra).
  apply bpow_le; lia. }
have Heta0 : 0 < eta by apply bpow_gt_0.
have Fch : is_finite ch=true by exact (proj1 FIN).
have Fcl : is_finite cl=true by exact (proj2 FIN).
have Hchr : FT2R ch=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) x.
{ unfold ch, Fast2Mult_mul, Fast2Mult. symmetry.
  apply BMULT_round_correct. exact Fch. }
have Hop : FT2R (BOPP ch) = -FT2R ch.
{ symmetry. apply BOPP_binary. right; exact Fch. }
have Hclr : FT2R cl=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) r.
{ unfold cl, Fast2Mult_err, Fast2Mult.
  rewrite -(BFMA_round_correct t a b (BOPP ch) Fcl) Hop.
  unfold r, x. f_equal; ring. }
destruct (Req_dec x 0) as [Hx0|Hx0].
- have Hch0 : FT2R ch=0 by rewrite Hchr Hx0 round_0.
  have Hr0 : r=0 by unfold r; rewrite Hx0 Hch0; ring.
  rewrite Hx0 Hch0 Hclr Hr0 round_0.
  rewrite Rminus_0_r Rplus_0_l Rabs_R0. nra.
- destruct (Rle_dec
    (bpow radix2 (@common.emin t+2*fprec t-1)) (Rabs x))
    as [Hbig|Hsmall].
  + have Hex := Fast2MultModel_correct a b Fch.
    specialize (Hex ltac:(move=>_;exact Hbig)).
    fold x ch cl in Hex.
    rewrite Hex. replace (FT2R ch+(x-FT2R ch)-x)%R with 0 by ring.
    rewrite Rabs_R0. nra.
  + have Hxe := round_FLT_error_rel_emin (t:=t) x.
    fold u eta in Hxe. rewrite -Hchr in Hxe.
    have Hrabs : Rabs r <= u*Rabs x+/2*eta.
    { unfold r. rewrite Rabs_minus_sym. exact Hxe. }
    have HxB : Rabs x <
        bpow radix2 (@common.emin t+2*fprec t-1)
      by apply Rnot_le_lt.
    have Hux := Rmult_lt_compat_l u _ _ Hu0 HxB.
    have Hscale : u*bpow radix2
        (@common.emin t+2*fprec t-1)=
        bpow radix2 (@common.emin t+fprec t-1).
    { unfold u. rewrite -bpow_plus. f_equal; ring. }
    rewrite Hscale in Hux.
    have Hetahalf : /2*eta = bpow radix2 (@common.emin t-1).
    { unfold eta. rewrite (bpow_plus radix2 (@common.emin t) (-1)).
      change (bpow radix2 (-1)) with (/2:R). ring. }
    have Hetasmall : /2*eta <
        bpow radix2 (@common.emin t+fprec t-1).
    { rewrite Hetahalf. apply bpow_lt. lia. }
    have Hrsmall : Rabs r <
        bpow radix2 (@common.emin t+fprec t).
      { have Hnext : bpow radix2 (@common.emin t+fprec t) =
          2*bpow radix2 (@common.emin t+fprec t-1).
      { transitivity
          (bpow radix2 (@common.emin t+fprec t-1)*bpow radix2 1).
        - rewrite -bpow_plus. f_equal; ring.
        - change (bpow radix2 1) with (2:R). ring. }
      rewrite Hnext. nra. }
    have Hre := @Ulp.error_le_half_ulp radix2
      (SpecFloat.fexp (fprec t) (femax t))
      valid_fexp_inst choice r.
    have Hulp : Ulp.ulp radix2
        (SpecFloat.fexp (fprec t) (femax t)) r=eta.
    { unfold SpecFloat.fexp, common.emin.
      apply ulp_FLT_small; [apply fprec_gt_0|exact Hrsmall]. }
    rewrite Hulp in Hre. rewrite -Hclr in Hre.
    change (Rabs (FT2R ch+FT2R cl-x) <= /2*eta).
    replace (FT2R ch+FT2R cl-x)%R with (FT2R cl-r)%R
      by (unfold r; ring).
    exact Hre.
Qed.

(** Algorithm 9's closing Fast2Sum is exact as soon as its two inputs are
    magnitude-ordered.  No precision bound, no input condition and no regime
    hypothesis is needed -- [FastTwoSum_correct] applies directly.

    This is the prerequisite for splitting the refinement block on the
    ordering: in the ordered arm the two Fast2Sum roundings of
    [DWDivDW_refinement_product_value_error_tight_floor] vanish, taking its
    floor from [2*eta] down to [eta]. *)
Lemma DWTimesFP3_sum_exact_of_ord {NANS : Nans} {t : type}
    {STD : is_standard t} (ah al b : ftype t) :
  is_finite_p (DWTimesFP3 ah al b) ->
  Rabs (FT2R (BFMA al b (Fast2Mult_err ah b))) <=
    Rabs (FT2R (Fast2Mult_mul ah b)) ->
  FT2R (fst (DWTimesFP3 ah al b)) +
  FT2R (snd (DWTimesFP3 ah al b)) =
    FT2R (Fast2Mult_mul ah b) +
    FT2R (BFMA al b (Fast2Mult_err ah b)).
Proof.
move => FIN Hord.
set ch := Fast2Mult_mul ah b.
set cl1 := Fast2Mult_err ah b.
set cl3 := BFMA al b cl1.
have Fe : is_finite_p (Fast2Sum ch cl3).
{ unfold DWTimesFP3 in FIN.
  unfold ch, cl1, cl3, Fast2Mult_mul, Fast2Mult_err, Fast2Mult in *.
  exact FIN. }
fold ch cl1 cl3 in Hord.
have Hsum := FastTwoSum_correct ch cl3 (proj1 Fe) Hord.
change (FT2R (snd (DWTimesFP3 ah al b)) =
  FT2R ch + FT2R cl3 - FT2R (fst (DWTimesFP3 ah al b))) in Hsum.
lra.
Qed.

(** If Algorithm 9's closing Fast2Sum preserves its two inputs, its returned
    pair is a double word: the high component is exactly the rounding of that
    preserved sum. *)
Lemma DWTimesFP3_double_word_of_sum {NANS : Nans} {t : type}
    {STD : is_standard t} (ah al b : ftype t) :
  is_finite_p (DWTimesFP3 ah al b) ->
  let ch := Fast2Mult_mul ah b in
  let cl3 := BFMA al b (Fast2Mult_err ah b) in
  FT2R (fst (DWTimesFP3 ah al b))+FT2R (snd (DWTimesFP3 ah al b))=
    FT2R ch+FT2R cl3 ->
  double_word_prop (fst (DWTimesFP3 ah al b))
                   (snd (DWTimesFP3 ah al b)).
Proof.
move => FIN /= Hsum.
set ch := Fast2Mult_mul ah b.
set cl3 := BFMA al b (Fast2Mult_err ah b).
set d := DWTimesFP3 ah al b.
fold d ch cl3 in Hsum.
unfold double_word_prop, rounded. fold d.
rewrite Hsum.
change (FT2R (fst d)=round radix2
  (SpecFloat.fexp (fprec t) (femax t))
  (Znearest choice) (FT2R ch+FT2R cl3)).
have Hfst : fst d=BPLUS ch cl3 by reflexivity.
rewrite Hfst. symmetry. apply BPLUS_round_correct. exact (proj1 FIN).
Qed.

(* ---------- the gap regime: below the TwoProd exactness threshold ---------- *)

(** In the gap below Fast2Mult's exactness threshold, the compensated core of
    Algorithm 9 still has a floor-only error.  This is the value before its
    closing Fast2Sum; no ordinary [u^2] term is introduced in this regime. *)
Lemma DWTimesFP_core_error_floor_gap {NANS : Nans} {t : type}
    {STD : is_standard t} (ah al b : ftype t) :
  (3 <= fprec t)%Z -> double_word_prop ah al ->
  is_finite_p (DWTimesFP3 ah al b) ->
  ~ bpow radix2 (@common.emin t+2*fprec t-1) <=
      Rabs (FT2R ah*FT2R b) ->
  let ch := Fast2Mult_mul ah b in
  let cl3 := BFMA al b (Fast2Mult_err ah b) in
  Rabs ((FT2R ch+FT2R cl3)-
        (FT2R ah+FT2R al)*FT2R b)
    <= 251/100*bpow radix2 (@common.emin t).
Proof.
move => Hp3 DWa FIN Hgap /=.
set x := (FT2R ah*FT2R b)%R.
set ch := Fast2Mult_mul ah b.
set cl1 := Fast2Mult_err ah b.
set cl3 := BFMA al b cl1.
set u := bpow radix2 (-fprec t).
set eta := bpow radix2 (@common.emin t).
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /8.
{ unfold u. have -> : (/8:R)=bpow radix2 (-3) by (simpl;lra).
  apply bpow_le; lia. }
have Heta0 : 0 < eta by apply bpow_gt_0.
have Ffast := FIN1 ah al b FIN.
have Fch : is_finite ch=true by exact (proj1 Ffast).
have Fcl1 : is_finite cl1=true by exact (proj2 Ffast).
have Fcl3 := FIN2 ah al b FIN; fold cl1 cl3 in Fcl3.
have Hdelta := Fast2Mult_sum_error_floor ah b Hp3 Ffast.
fold x ch cl1 eta in Hdelta.
have Hchr : FT2R ch=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) x.
{ unfold ch, Fast2Mult_mul, Fast2Mult. symmetry.
  apply BMULT_round_correct. exact Fch. }
have Hxe := round_FLT_error_rel_emin (t:=t) x.
fold u eta in Hxe. rewrite -Hchr in Hxe.
have Hr : Rabs (x-FT2R ch)<=u*Rabs x+/2*eta.
{ rewrite Rabs_minus_sym. exact Hxe. }
have Hcl1 : Rabs (FT2R cl1)<=
    u*Rabs x+1501/1000*eta.
{ have Htri := Rabs_triang
      (FT2R cl1-(x-FT2R ch)) (x-FT2R ch).
  replace (FT2R cl1-(x-FT2R ch)+(x-FT2R ch))%R with
      (FT2R cl1)%R in Htri by ring.
  have Heq : FT2R cl1-(x-FT2R ch)=
      FT2R ch+FT2R cl1-x by ring.
  rewrite Heq in Htri.
  eapply Rle_trans; [exact Htri|].
  eapply Rle_trans.
  - apply Rplus_le_compat; [exact Hdelta|exact Hr].
  - nra. }
have Hal := @aux_dwu_rel t STD ah al DWa.
fold u in Hal.
have Halb : Rabs (FT2R al*FT2R b)<=u*Rabs x.
{ unfold x. rewrite !Rabs_mult.
  have H := Rmult_le_compat_r (Rabs (FT2R b)) _ _
    (Rabs_pos _) Hal.
  eapply Rle_trans; [exact H|]. right; ring. }
set w := (FT2R al*FT2R b+FT2R cl1)%R.
have Hw : Rabs w<=2*u*Rabs x+1501/1000*eta.
{ unfold w. eapply Rle_trans; [apply Rabs_triang|]. nra. }
have Hcl3r : FT2R cl3=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) w.
{ unfold cl3. rewrite -(BFMA_round_correct t al b cl1 Fcl3).
  unfold w. f_equal; ring. }
have He3 := round_FLT_error_rel_emin (t:=t) w.
fold u eta in He3. rewrite -Hcl3r in He3.
have Huw := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Hw.
have Hscale : u^2*bpow radix2
    (@common.emin t+2*fprec t-1)=/2*eta.
{ replace (u^2)%R with (u*u)%R by ring.
  unfold u, eta. rewrite -bpow_plus -bpow_plus.
  replace (-fprec t+-fprec t+
      (@common.emin t+2*fprec t-1))%Z with
      (@common.emin t-1)%Z by ring.
  rewrite (bpow_plus radix2 (@common.emin t) (-1)).
  change (bpow radix2 (-1)) with (/2:R). ring. }
have HxB : Rabs x < bpow radix2
    (@common.emin t+2*fprec t-1) by apply Rnot_le_lt.
have Hu20 : 0 < u^2 by nra.
have HuB := Rmult_lt_compat_l (u^2) _ _ Hu20 HxB.
rewrite Hscale in HuB.
change (Rabs ((FT2R ch+FT2R cl3)-
  (FT2R ah+FT2R al)*FT2R b)<=251/100*eta).
have Heq : (FT2R ch+FT2R cl3)-
    (FT2R ah+FT2R al)*FT2R b =
  (FT2R ch+FT2R cl1-x)+(FT2R cl3-w) by (unfold x,w;ring).
rewrite Heq. eapply Rle_trans; [apply Rabs_triang|].
eapply Rle_trans.
- apply Rplus_le_compat; [exact Hdelta|exact He3].
- nra.
Qed.

(** Full Algorithm 9 in the Fast2Mult gap.  If the closing Fast2Sum ordering
    holds it is exact.  If it fails, the leading and low terms are both within
    six floor ulps, where their common fixed-point lattice makes Fast2Sum exact
    as well.  Thus the compensated core's [2.51] ulps are the whole cost. *)
Lemma DWTimesFP3_error_floor_gap {NANS : Nans} {t : type}
    {STD : is_standard t} (ah al b : ftype t) :
  (3 <= fprec t)%Z -> double_word_prop ah al ->
  is_finite_p (DWTimesFP3 ah al b) ->
  ~ bpow radix2 (@common.emin t+2*fprec t-1) <=
      Rabs (FT2R ah*FT2R b) ->
  Rabs ((FT2R (fst (DWTimesFP3 ah al b))+
         FT2R (snd (DWTimesFP3 ah al b)))-
        (FT2R ah+FT2R al)*FT2R b)
    <= 251/100*bpow radix2 (@common.emin t) /\
  double_word_prop (fst (DWTimesFP3 ah al b))
                   (snd (DWTimesFP3 ah al b)).
Proof.
move => Hp3 DWa FIN Hgap.
set x := (FT2R ah*FT2R b)%R.
set P := Rabs x.
set ch := Fast2Mult_mul ah b.
set cl1 := Fast2Mult_err ah b.
set cl3 := BFMA al b cl1.
set d := DWTimesFP3 ah al b.
set u := bpow radix2 (-fprec t).
set eta := bpow radix2 (@common.emin t).
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /8.
{ unfold u. have -> : (/8:R)=bpow radix2 (-3) by (simpl;lra).
  apply bpow_le; lia. }
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have Heta0 : 0 < eta by apply bpow_gt_0.
have Ffast := FIN1 ah al b FIN.
have Fch : is_finite ch=true by exact (proj1 Ffast).
have Fcl1 : is_finite cl1=true by exact (proj2 Ffast).
have Fcl3 := FIN2 ah al b FIN; fold cl1 cl3 in Fcl3.
have Hcore := DWTimesFP_core_error_floor_gap ah al b
  Hp3 DWa FIN Hgap.
fold ch cl3 eta in Hcore. cbv zeta in Hcore.
have Hdelta := Fast2Mult_sum_error_floor ah b Hp3 Ffast.
fold x ch cl1 eta in Hdelta.
have Hchr : FT2R ch=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) x.
{ unfold ch, Fast2Mult_mul, Fast2Mult. symmetry.
  apply BMULT_round_correct. exact Fch. }
have Hxe := round_FLT_error_rel_emin (t:=t) x.
fold u eta in Hxe. rewrite -Hchr in Hxe.
fold P in Hxe.
have Hr : Rabs (x-FT2R ch)<=u*P+/2*eta.
{ rewrite Rabs_minus_sym. exact Hxe. }
have Hchlo : (1-u)*P-/2*eta<=Rabs (FT2R ch).
{ have Hrev := Rabs_triang_inv x (x-FT2R ch).
  replace (x-(x-FT2R ch))%R with (FT2R ch) in Hrev by ring.
  fold P in Hrev. nra. }
have Hchup : Rabs (FT2R ch)<=(1+u)*P+/2*eta.
{ have Htri := Rabs_triang (FT2R ch-x) x.
  replace (FT2R ch-x+x)%R with (FT2R ch) in Htri by ring.
  fold P in Htri. nra. }
have Hcl1 : Rabs (FT2R cl1)<=u*P+1501/1000*eta.
{ have Htri := Rabs_triang
      (FT2R cl1-(x-FT2R ch)) (x-FT2R ch).
  replace (FT2R cl1-(x-FT2R ch)+(x-FT2R ch))%R with
      (FT2R cl1)%R in Htri by ring.
  have Heq : FT2R cl1-(x-FT2R ch)=
      FT2R ch+FT2R cl1-x by ring.
  rewrite Heq in Htri. nra. }
have Hal := @aux_dwu_rel t STD ah al DWa.
fold u in Hal.
have Halb : Rabs (FT2R al*FT2R b)<=u*P.
{ unfold P,x. rewrite !Rabs_mult.
  have H := Rmult_le_compat_r (Rabs (FT2R b)) _ _
    (Rabs_pos _) Hal.
  eapply Rle_trans; [exact H|]. right; ring. }
set w := (FT2R al*FT2R b+FT2R cl1)%R.
have Hw : Rabs w<=2*u*P+1501/1000*eta.
{ unfold w. eapply Rle_trans; [apply Rabs_triang|]. nra. }
have Hcl3r : FT2R cl3=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) w.
{ unfold cl3. rewrite -(BFMA_round_correct t al b cl1 Fcl3).
  unfold w. f_equal; ring. }
have He3 := round_FLT_error_rel_emin (t:=t) w.
fold u eta in He3. rewrite -Hcl3r in He3.
have Hcl3up : Rabs (FT2R cl3)<=
    (1+u)*(2*u*P+1501/1000*eta)+/2*eta.
{ have Htri := Rabs_triang (FT2R cl3-w) w.
  replace (FT2R cl3-w+w)%R with (FT2R cl3) in Htri by ring.
  have Huw := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Hw.
  nra. }
have Fe : is_finite_p (Fast2Sum ch cl3).
{ unfold d, DWTimesFP3 in FIN. fold ch cl1 cl3 in FIN. exact FIN. }
destruct (Rle_dec (Rabs (FT2R cl3)) (Rabs (FT2R ch)))
    as [Hord|Hnord].
- have Hsum := FastTwoSum_correct ch cl3 (proj1 Fe) Hord.
  change (FT2R (snd d)=FT2R ch+FT2R cl3-FT2R (fst d)) in Hsum.
  split.
  +
  change (Rabs ((FT2R (fst d)+FT2R (snd d))-
    (FT2R ah+FT2R al)*FT2R b)<=251/100*eta).
  rewrite Hsum.
  replace (FT2R (fst d)+(FT2R ch+FT2R cl3-FT2R (fst d))-
    (FT2R ah+FT2R al)*FT2R b)%R with
    ((FT2R ch+FT2R cl3)-(FT2R ah+FT2R al)*FT2R b)%R by ring.
  eapply Rle_trans; [exact Hcore|]. nra.
  + exact (Fast2Sum_is_DW ch cl3 (proj1 Fe) Hord).
- (* Unordered closing Fast2Sum.  |cl3| > |ch| can only happen when the
     leading product is tiny: |cl3| <= (1+u)(2uP + 1.501eta) + eta/2 while
     |ch| >= (1-u)P - eta/2, and at u <= 1/8 those cross only below
     4.5281*eta, so P < 4.6*eta.  The EXACT sum ch + cl3 is then within
     one binade of the subnormal range -- bound it through the compensated
     core error, not by the triangle inequality on |ch| and |cl3|
     separately, which would overshoot 2^(emin+3) -- and the shared
     FLT/FIX lattice at exponent emin makes Fast2Sum exact. *)
  have HuP' : u*P<=/8*P.
  { have H := Rmult_le_compat_r P _ _ HP0 Hu. nra. }
  have Hueta' : u*eta<=/8*eta.
  { have H := Rmult_le_compat_r eta _ _ (Rlt_le _ _ Heta0) Hu. nra. }
  have Hu2P : u*(u*P)<=/64*P.
  { have H := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) HuP'.
    have H2 : (/8*(u*P)<=/8*(/8*P))%R by nra.
    nra. }
  have HsmallP : P<46/10*eta.
  { apply Rnot_le_lt. move => HPbig.
    have Hcl3coarse : Rabs (FT2R cl3)<=9/32*P+22/10*eta.
    { eapply Rle_trans; [exact Hcl3up|]. nra. }
    have Hchcoarse : 7/8*P-/2*eta<=Rabs (FT2R ch).
    { eapply Rle_trans; [|exact Hchlo]. nra. }
    have Hcontra : Rabs (FT2R cl3)<=Rabs (FT2R ch) by nra.
    exact (Hnord Hcontra). }
  have Halb' : Rabs ((FT2R ah+FT2R al)*FT2R b)<=(1+u)*P.
  { replace ((FT2R ah+FT2R al)*FT2R b)%R with
        (x+FT2R al*FT2R b)%R by (unfold x; ring).
    eapply Rle_trans; [apply Rabs_triang|].
    fold P. nra. }
  have Hbig8 : 8*eta<=bpow radix2 (@common.emin t+fprec t).
  { unfold eta. have -> : (8:R)=bpow radix2 3 by (simpl;lra).
    rewrite -bpow_plus. apply bpow_le; lia. }
  have Hsumsmall : Rabs (FT2R ch+FT2R cl3)<=
      bpow radix2 (@common.emin t+fprec t).
  { have Htri2 := Rabs_triang
        ((FT2R ch+FT2R cl3)-(FT2R ah+FT2R al)*FT2R b)
        ((FT2R ah+FT2R al)*FT2R b).
    replace ((FT2R ch+FT2R cl3)-(FT2R ah+FT2R al)*FT2R b+
        (FT2R ah+FT2R al)*FT2R b)%R with (FT2R ch+FT2R cl3)%R
      in Htri2 by ring.
    have Hstep : Rabs (FT2R ch+FT2R cl3)<=251/100*eta+(1+u)*P.
    { eapply Rle_trans; [exact Htri2|].
      apply Rplus_le_compat; [exact Hcore|exact Halb']. }
    (* 2.51*eta + (1+u)*P < 2.51*eta + (9/8)*4.6*eta = 7.685*eta <= 8*eta.
       Linear in the atoms eta, P and u*P, so lra suffices. *)
    have Hstep2 : 251/100*eta+(1+u)*P<=8*eta.
    { have H1 : ((1+u)*P = P+u*P)%R by ring.
      rewrite H1. lra. }
    eapply Rle_trans; [exact Hstep|].
    eapply Rle_trans; [exact Hstep2|exact Hbig8]. }
  have Hsum := Fast2Sum_sum_exact_of_sum_small ch cl3 Fe Hsumsmall.
  fold d in Hsum.
  split.
  + change (Rabs ((FT2R (fst d)+FT2R (snd d))-
      (FT2R ah+FT2R al)*FT2R b)<=251/100*eta).
    rewrite Hsum. exact Hcore.
  + exact (DWTimesFP3_double_word_of_sum ah al b FIN Hsum).
Qed.

(* ---------- public assembly: the whole-range mixed API ---------- *)

(* Normal arm.  Above the TwoProd exactness threshold the product residual
   is representable and the entire Algorithm-9 error is relative, with no
   physical-floor contribution: this is Layer 1's DWTimesFP_relerr_bound
   cleared of its division by the exact product. *)
Lemma DWTimesFP3_error_normal_arm {NANS : Nans} {t : type}
    {STD : is_standard t} (ah al b : ftype t) :
  (3 <= fprec t)%Z -> double_word_prop ah al ->
  is_finite_p (DWTimesFP3 ah al b) ->
  bpow radix2 (@common.emin t+2*fprec t-1) <=
    Rabs (FT2R ah*FT2R b) ->
  Rabs ((FT2R (fst (DWTimesFP3 ah al b))+
         FT2R (snd (DWTimesFP3 ah al b)))-
        (FT2R ah+FT2R al)*FT2R b)
    <= 2*bpow radix2 (-fprec t)^2*
         Rabs ((FT2R ah+FT2R al)*FT2R b).
Proof.
move => Hp3 DWa FIN Hbig.
move: (xryr_ne_0_of_big ah al b DWa Hbig) => [_ [Hyne [Hxrne Hne]]].
have Hrel := DWTimesFP_relerr_bound ah al b DWa FIN Hp3 (or_intror Hbig).
unfold relative_error_DWTimesFP in Hrel.
set E := (FT2R (fst (DWTimesFP3 ah al b))+
          FT2R (snd (DWTimesFP3 ah al b))-
          (FT2R ah+FT2R al)*FT2R b)%R.
set Q := ((FT2R ah+FT2R al)*FT2R b)%R.
fold E Q in Hrel. fold Q.
have Heq : Rabs E = Rabs (E/Q)*Rabs Q.
{ rewrite -Rabs_mult. f_equal. field. exact Hne. }
rewrite Heq.
have Hmul := Rmult_le_compat_r (Rabs Q) _ _ (Rabs_pos _) Hrel.
eapply Rle_trans; [exact Hmul|]. right; ring.
Qed.

(* ------------------------------------------------------------------
   PRIMARY API: branch-aware whole-range Algorithm-9 error.

   The two arms are the two sides of Fast2Mult_cond's underflow
   disjunct (DDModels.v), so every input falls in exactly one:

     - normal arm  |xh*y| >= 2^(emin+2p-1) : purely relative, 2u^2;
     - gap arm     |xh*y| <  2^(emin+2p-1) : purely absolute, C_FP*eta
                                             with C_FP = 2.51.

   The gap arm covers the exact-zero case too (|0| is below the
   threshold), so the dichotomy is exhaustive; the third conjunct
   records the sharper fact that the exact product is then 0 as well.

   C_FP = 2.51 recomputed for p >= 3: the gap cost is
   eta/2 (Fast2Mult residual floor) + u|w| + eta/2 (cross-term floor)
   with |w| <= 2uP + 1.501eta and u^2 P < eta/2 in the gap, i.e.
   < 2eta + 1.501*u*eta <= 2.188*eta at u <= 1/8.  So 2.51 holds with
   about 0.3 eta of margin at every p >= 3.
   ------------------------------------------------------------------ *)
Theorem DWTimesFP3_error_mixed {NANS : Nans} {t : type}
    {STD : is_standard t} (xh xl y : ftype t) :
  (3 <= fprec t)%Z -> 
  double_word_prop xh xl ->
  is_finite_p (DWTimesFP3 xh xl y) ->
  (bpow radix2 (@common.emin t+2*fprec t-1) <=
     Rabs (FT2R xh*FT2R y) ->
   Rabs ((FT2R (fst (DWTimesFP3 xh xl y))+
          FT2R (snd (DWTimesFP3 xh xl y)))-
         (FT2R xh+FT2R xl)*FT2R y)
     <= 2*bpow radix2 (-fprec t)^2*
          Rabs ((FT2R xh+FT2R xl)*FT2R y)) /\
  (Rabs (FT2R xh*FT2R y) <
     bpow radix2 (@common.emin t+2*fprec t-1) ->
   Rabs ((FT2R (fst (DWTimesFP3 xh xl y))+
          FT2R (snd (DWTimesFP3 xh xl y)))-
         (FT2R xh+FT2R xl)*FT2R y)
     <= 251/100*bpow radix2 (@common.emin t)) /\
  (FT2R xh*FT2R y = 0 -> (FT2R xh+FT2R xl)*FT2R y = 0).
Proof.
move => Hp3 DWa FIN.
split; [|split].
- move => Hbig.
  exact (DWTimesFP3_error_normal_arm xh xl y Hp3 DWa FIN Hbig).
- move => Hgap.
  exact (proj1 (DWTimesFP3_error_floor_gap xh xl y
    Hp3 DWa FIN (Rlt_not_le _ _ Hgap))).
- move => Hz. exact (xryr0_of_prod0 xh xl y DWa Hz).
Qed.

(* Flat "conventional mixed" consequence: a single bound valid in every
   regime, at the cost of carrying both terms everywhere.  This is the
   form most clients want and the form DWDivDW_acc consumes.  It is a
   two-line consequence of the branch theorem -- each arm supplies one
   summand and the other is nonnegative -- rather than a second copy of
   the regime analysis. *)
Corollary DWTimesFP3_error_mixed_flat {NANS : Nans} {t : type}
    {STD : is_standard t} (ah al b : ftype t) :
  (3 <= fprec t)%Z -> double_word_prop ah al ->
  is_finite_p (DWTimesFP3 ah al b) ->
  Rabs ((FT2R (fst (DWTimesFP3 ah al b))+
         FT2R (snd (DWTimesFP3 ah al b)))-
        (FT2R ah+FT2R al)*FT2R b)
    <= 2*bpow radix2 (-fprec t)^2*
         Rabs ((FT2R ah+FT2R al)*FT2R b)+
       251/100*bpow radix2 (@common.emin t).
Proof.
move => Hp3 DWa FIN.
move: (DWTimesFP3_error_mixed ah al b Hp3 DWa FIN) => [Hnorm [Hgap _]].
have Hu2 : 0 <= 2*bpow radix2 (-fprec t)^2*
    Rabs ((FT2R ah+FT2R al)*FT2R b).
{ have := bpow_ge_0 radix2 (-fprec t).
  have := Rabs_pos ((FT2R ah+FT2R al)*FT2R b). nra. }
have Heta : 0 <= 251/100*bpow radix2 (@common.emin t).
{ have := bpow_ge_0 radix2 (@common.emin t). nra. }
destruct (Rle_or_lt (bpow radix2 (@common.emin t+2*fprec t-1))
    (Rabs (FT2R ah*FT2R b))) as [Hbig|Hsmall].
- have H := Hnorm Hbig. lra.
- have H := Hgap Hsmall. lra.
Qed.

Lemma DWTimesFP3_double_word_mixed {NANS : Nans} {t : type}
    {STD : is_standard t} (ah al b : ftype t) :
  (3 <= fprec t)%Z -> double_word_prop ah al ->
  is_finite_p (DWTimesFP3 ah al b) ->
  double_word_prop (fst (DWTimesFP3 ah al b))
                   (snd (DWTimesFP3 ah al b)).
Proof.
move => Hp3 DWa FIN.
destruct (Rle_dec
  (bpow radix2 (@common.emin t+2*fprec t-1))
  (Rabs (FT2R ah*FT2R b))) as [Hbig|Hgap].
- have Fmul := FIN3 ah al b FIN.
  have Fcl3 := FIN2 ah al b FIN.
  have Hord := aux_cl3_le_ch ah al b
    DWa Fmul Fcl3 Hbig.
  exact (DWTimesFP3_double_word_from_pre
    ah al b (proj1 FIN) Hord).
- exact (proj2 (DWTimesFP3_error_floor_gap ah al b
    Hp3 DWa FIN Hgap)).
Qed.

(* ------------------------------------------------------------------
   PUBLIC VST INTERFACE (Layer 2): the whole-range mixed bound from the
   runtime-checkable accurate-only cond DWTimesFP_cond_acc (DDModels.v).

   This is the pair of results carried by the exported funspec
   dw_mult_fp9_guarded_spec and discharged by the runtime guard
   dw_mult_fp_check.  The two corollaries just close the last gap between
   the mixed API above and the guard: the mixed theorems ASSUME
   is_finite_p (DWTimesFP3 ...), a property of the computed result, while a
   guard can only test its inputs -- so finiteness is DERIVED here from
   DWTimesFP3_finite_acc, whose only real content is overflow headroom.

   No underflow disjunct appears anywhere in this interface: unlike the
   relative (2u^2) tier, it holds in the Fast2Mult underflow gap, which is
   precisely why the guard need not -- and no longer does -- reject it.
   ------------------------------------------------------------------ *)

(* The absolute Algorithm-9 error, the quantity the mixed API bounds.
   Companion to relative_error_DWTimesFP of the relative tier. *)
Definition absolute_error_DWTimesFP {NANS : Nans} {t : type}
    {STD : is_standard t} (xh xl y : ftype t) : R :=
  Rabs ((FT2R (fst (DWTimesFP3 xh xl y)) +
         FT2R (snd (DWTimesFP3 xh xl y))) -
        (FT2R xh + FT2R xl) * FT2R y).

Corollary DWTimesFP_mixed_accuracy_from_cond_acc {NANS : Nans} {t : type}
    {STD : is_standard t} (xh xl y : ftype t) :
  (3 <= fprec t)%Z ->
  DWTimesFP_cond_acc xh xl y ->
  absolute_error_DWTimesFP xh xl y
    <= 2 * bpow radix2 (- fprec t) ^ 2 *
         Rabs ((FT2R xh + FT2R xl) * FT2R y) +
       251/100 * bpow radix2 (@common.emin t).
Proof.
move => Hp3 Hcond.
have FIN := DWTimesFP3_finite_acc xh xl y Hcond.
have DWa : double_word_prop xh xl by (move: Hcond => [_ [H _]]; exact H).
exact (DWTimesFP3_error_mixed_flat xh xl y Hp3 DWa FIN).
Qed.

Corollary DWTimesFP3_double_word_from_cond_acc {NANS : Nans} {t : type}
    {STD : is_standard t} (xh xl y : ftype t) :
  (3 <= fprec t)%Z ->
  DWTimesFP_cond_acc xh xl y ->
  double_word_prop (fst (DWTimesFP3 xh xl y))
                   (snd (DWTimesFP3 xh xl y)).
Proof.
move => Hp3 Hcond.
have FIN := DWTimesFP3_finite_acc xh xl y Hcond.
have DWa : double_word_prop xh xl by (move: Hcond => [_ [H _]]; exact H).
exact (DWTimesFP3_double_word_mixed xh xl y Hp3 DWa FIN).
Qed.
