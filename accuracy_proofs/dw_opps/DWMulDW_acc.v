(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** This file contains accuracy proofs for the multiplication of two
    double-word numbers: the algorithm DWTimesDW3 (Algorithm 12), which is the
    functional model of the C routine dw_mult_dw12 (dd_lib/dw_mult_dw.c).

    ============================================================================
    Mirrors the section layout of DWMulFP_acc.v (the DW x FP accuracy proof).
    ADMIT-FREE.  Proven results (all depend only on the standard Flocq/Coq
    axioms):
      - finiteness from DWTimesDW_cond: DWTimesDW3_fst_finite / _snd_finite;
      - the error identity relerr_error_eq: (zh+zl) - xr*yr = e0+e1+e2+e3;
      - the FLX->FLT bridge DWTimesDW3_FLX_FLT (op-by-op round_FLT_FLX under the
        per-intermediate normality hypotheses; lifts DWTimesDW.DWTimesDW12);
      - the Layer-1 accuracy DWTimesDW_relerr_bound and its Layer-2 corollary
        DWTimesDW_accuracy_from_cond, at the (loose but self-contained) constant
        relerr <= 32*u^2, proved directly via aux_eta_bnd (no bridge needed).

    Correspondences with the DW x FP template:
      - 4 inputs (xh xl yh yl) instead of 3;  y -> double word (yh, yl);
      - the FLT model DWTimesDW3 has five rounded ops
          Fast2Mult xh yh ; BMULT xl yl ; BFMA xh yl _ ; BFMA xl yh _ ; BPLUS _ _
        then a closing Fast2Sum  (vs. two ops for DW x FP);
      - the paper's tight bound is 4*u^2
          (DWTimesDW.DWTimesDW12_correct : Rabs ((zh+zl-xy)/xy) < 4*(u*u));
        it is recoverable on the normal regime via the bridge (see the NOTE at
        the end of Section DWTimesDW_Accuracy), but the full-regime FLT bound
        here is the direct 32*u^2 (the underflow band is genuinely looser);
      - the FLX/paper model is DWTimesDW.DWTimesDW12 (paper_proofs/DWTimesDW.v).
    ============================================================================ *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common.
Require Import DWTimesFP DWTimesDW DDModels DWord_defs Fast2Mult_acc TwoSum_acc Fast2Sum_acc.
Require Import DWPlusFP_acc_helpers.
From Flocq Require Import Pff2Flocq Core.

From Stdlib Require Import Reals.Reals.

Require Import mathcomp.ssreflect.ssreflect.

(* for choice functions : choice = fun x0 : Z => negb (Z.even x0) *)
From Stdlib Require Import Logic.FunctionalExtensionality.

Set Bullet Behavior "Strict Subproofs".

(* Keep the paper's two-product folded; proofs expose it via TwoProdE. *)
Opaque DWTimesFP.TwoProd.
Arguments DWTimesFP.TwoProd : simpl never.


Lemma let_pair_eta {A B C} (p : A*B) (k : A -> B -> C) :
  (let '(a,b) := p in k a b) = k (fst p) (snd p).
Proof. destruct p; reflexivity. Qed.

(* No-overflow of an FMA implies finiteness (converse of
   is_finite_fma_no_overflow); mirrors no_overflow_sum_is_finite for BPLUS.
   Re-declared file-local (as in DWMulFP_acc.v). *)
Lemma no_overflow_fma_is_finite {NANS: Nans} {t : type} {STD: is_standard t} :
  forall (a b c : ftype t),
  is_finite a = true -> is_finite b = true -> is_finite c = true ->
  Rabs (rounded t (FT2R a * FT2R b + FT2R c)) < bpow Zaux.radix2 (femax t) ->
  is_finite (BFMA a b c) = true.
Proof.
  intros a b c Ha Hb Hc Hov.
  rewrite !is_finite_Binary in Ha, Hb, Hc.
  rewrite is_finite_Binary /BFMA float_of_ftype_of_float.
  pose proof (Binary.Bfma_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan (fprec t) (femax t) (fprec_gt_one t))
    BinarySingleNaN.mode_NE (float_of_ftype a) (float_of_ftype b) (float_of_ftype c)
    Ha Hb Hc) as H.
  cbv zeta in H.
  rewrite !B2R_float_of_ftype in H.
  unfold rounded in Hov.
  apply Rlt_bool_true in Hov.
  rewrite Hov in H.
  destruct H as (_ & HF & _).
  exact HF.
Qed.

(* No-overflow of a product implies finiteness (BMULT analog of the FMA lemma
   above).  Needed for tl0 = BMULT xl yl, whose finiteness DWTimesDW_cond does
   not supply directly. *)
Lemma no_overflow_mult_is_finite {NANS: Nans} {t : type} {STD: is_standard t} :
  forall (a b : ftype t),
  is_finite a = true -> is_finite b = true ->
  Rabs (rounded t (FT2R a * FT2R b)) < bpow Zaux.radix2 (femax t) ->
  is_finite (BMULT a b) = true.
Proof.
  intros a b Ha Hb Hov.
  rewrite !is_finite_Binary in Ha, Hb.
  rewrite is_finite_Binary /BMULT/BINOP float_of_ftype_of_float.
  pose proof (Binary.Bmult_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (mult_nan (fprec t) (femax t) (fprec_gt_one t))
    BinarySingleNaN.mode_NE (float_of_ftype a) (float_of_ftype b)) as H.
  cbv zeta in H.
  rewrite !B2R_float_of_ftype in H.
  unfold rounded in Hov.
  apply Rlt_bool_true in Hov.
  rewrite Hov in H.
  destruct H as (_ & HF & _).
  rewrite HF Ha Hb //.
Qed.


(* ============================================================
   Section 1: extract per-operation finiteness from
   FIN : is_finite_p (DWTimesDW3 xh xl yh yl).
   ============================================================ *)
Section CorrectDWMulDW.
  Context {NANS: Nans} {t : type} {STD: is_standard t}.

  Variables (xh xl yh yl : ftype t).

  Hypothesis FIN : is_finite_p (DWTimesDW3 xh xl yh yl).

  (* fst (DWTimesDW3 xh xl yh yl) reduces to
       BPLUS (BMULT xh yh) (BPLUS (Fast2Mult_err xh yh)
                                  (BFMA xl yh (BFMA xh yl (BMULT xl yl)))).
     One pass of BPLUS/BFMA finite-elimination exposes every subterm's
     finiteness; each FIN* fact then closes by [exact]/[split]. *)
  Ltac prove_finite :=
    let Hf := fresh "Hf" in
    have Hf := proj1 FIN;
    change (is_finite (BPLUS (BMULT xh yh)
              (BPLUS (Fast2Mult_err xh yh)
                     (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) = true) in Hf;
    destruct (BPLUS_finite_e t _ _ Hf) as [Hmul Hrest];
    destruct (BPLUS_finite_e t _ _ Hrest) as [Hcl1 Hcl2];
    destruct (BFMA_finite_e t _ _ _ Hcl2) as [Hxl [Hyh Htl1]];
    destruct (BFMA_finite_e t _ _ _ Htl1) as [Hxh [Hyl Htl0]];
    first [ exact Hxh | exact Hxl | exact Hyh | exact Hyl
          | exact Hmul | exact Htl0 | exact Htl1 | exact Hcl2 | exact Hrest
          | split; [ exact Hmul | exact Hcl1 ] ].

  Fact FINxh : is_finite xh = true.
  Proof. prove_finite. Qed.

  Fact FINxl : is_finite xl = true.
  Proof. prove_finite. Qed.

  Fact FINyh : is_finite yh = true.
  Proof. prove_finite. Qed.

  Fact FINyl : is_finite yl = true.
  Proof. prove_finite. Qed.

  (* ch = fst (Fast2Mult xh yh) = BMULT xh yh *)
  Fact FINmul : is_finite (BMULT xh yh) = true.
  Proof. prove_finite. Qed.

  Fact FIN1 : is_finite_p (Fast2Mult xh yh).
  Proof. prove_finite. Qed.

  Let cl1 := snd (Fast2Mult xh yh).
  Let tl0 := BMULT xl yl.
  Let tl1 := BFMA xh yl tl0.
  Let cl2 := BFMA xl yh tl1.
  Let cl3 := BPLUS cl1 cl2.

  Fact FINtl0 : is_finite tl0 = true.
  Proof. prove_finite. Qed.

  Fact FINtl1 : is_finite tl1 = true.
  Proof. prove_finite. Qed.

  Fact FINcl2 : is_finite cl2 = true.
  Proof. prove_finite. Qed.

  Fact FINcl3 : is_finite cl3 = true.
  Proof. prove_finite. Qed.

End CorrectDWMulDW.


(* ============================================================
   Section 2: FLX TwoProd = FLT Fast2Mult, for the high product (xh, yh).
   Identical in content to DWMulFP_acc.v's Fast2Mult_correct (concerns a
   two-FP product only, no DW specifics).
   ============================================================ *)
Section CorrectDWMulDW'.
  Context {NANS: Nans} {t : type} {STD: is_standard t}.

  Notation emin := (common.emin (t:=t)).

  Variables (a b : ftype t).

  Hypothesis (Fast2Mult_overflow_condition : is_finite (BMULT a b) = true).
  Hypothesis (Fast2Mult_underflow_condition_strict : (FT2R a * FT2R b) <> 0 ->
    bpow Zaux.radix2 (emin + 3 * fprec t) <= Rabs (FT2R a * FT2R b)).

  Lemma Fast2Mult_correct :
    DWTimesFP.Fast2Mult (fprec t) choice (FT2R a) (FT2R b) = F2Rp (Fast2Mult a b).
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

End CorrectDWMulDW'.

(* Weak variant under the minimal underflow threshold emin + 2*fprec - 1. *)
Section CorrectDWMulDW_weak.
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

End CorrectDWMulDW_weak.


(* ============================================================
   Section 3: the load-bearing FLX -> FLT bridge for DWTimesDW3.
     DWTimesDW.DWTimesDW12 (fprec t) choice (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl)
       = F2Rp (DWTimesDW3 xh xl yh yl).
   Analog of DWMulFP_acc.v's DWTimesFP3_FLX_FLT: each of the five rounded ops
   agrees with its FLX counterpart (round_FLT_FLX + representability), and the
   closing Fast2Sum is exact via the magnitude ordering |cl3| <= |ch|.
   ============================================================ *)
Section CorrectDWMulDW_bridge.

Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (common.emin (t:=t)).
Notation u   := (bpow radix2 (- fprec t)).
Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).

Let ulp := (Ulp.ulp radix2 (SpecFloat.fexp (fprec t) (femax t))).

Variables (xh xl yh yl : ftype t).

Hypothesis FIN : is_finite_p (DWTimesDW3 xh xl yh yl).
(* Normal-regime hypotheses: every rounding argument of DWTimesDW3 is normal
   (>= bpow(emin+fprec-1)), so each FLT rounding equals its FLX counterpart
   (round_FLT_FLX).  Nprod is the two-product threshold for Fast2Mult_correct. *)
Hypothesis Nprod : bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh).
Hypothesis N0 : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xl * FT2R yl).
Hypothesis N1 : bpow radix2 (emin + fprec t - 1)
             <= Rabs (FT2R xh * FT2R yl + FT2R (BMULT xl yl)).
Hypothesis N2 : bpow radix2 (emin + fprec t - 1)
             <= Rabs (FT2R (BFMA xh yl (BMULT xl yl)) + FT2R xl * FT2R yh).
Hypothesis N3 : bpow radix2 (emin + fprec t - 1)
             <= Rabs (FT2R (Fast2Mult_err xh yh)
                      + FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))).

Theorem DWTimesDW3_FLX_FLT :
  DWTimesDW.DWTimesDW12 (fprec t) choice
    (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl)
    = F2Rp (DWTimesDW3 xh xl yh yl).
Proof.
have Hfmul := FINmul xh xl yh yl FIN.
have Hftl0 := FINtl0 xh xl yh yl FIN.
have Hftl1 := FINtl1 xh xl yh yl FIN.
have Hfcl2 := FINcl2 xh xl yh yl FIN.
have Hfcl3 := FINcl3 xh xl yh yl FIN.
have Nprod' : FT2R xh * FT2R yh <> 0 ->
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh)
  by (move => _; exact Nprod).
(* the four layer equalities: FLX round = FT2R of the FLT op *)
have H0 : round radix2 (FLX_exp (fprec t)) (Znearest choice) (FT2R xl * FT2R yl)
        = FT2R (BMULT xl yl).
{ rewrite -(round_FLT_FLX radix2 emin (fprec t) (Znearest choice) (FT2R xl * FT2R yl) N0).
  exact (BMULT_round_correct t xl yl Hftl0). }
have H1 : round radix2 (FLX_exp (fprec t)) (Znearest choice)
              (FT2R xh * FT2R yl + FT2R (BMULT xl yl))
        = FT2R (BFMA xh yl (BMULT xl yl)).
{ rewrite -(round_FLT_FLX radix2 emin (fprec t) (Znearest choice) _ N1).
  exact (BFMA_round_correct t xh yl (BMULT xl yl) Hftl1). }
have H2 : round radix2 (FLX_exp (fprec t)) (Znearest choice)
              (FT2R (BFMA xh yl (BMULT xl yl)) + FT2R xl * FT2R yh)
        = FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))).
{ rewrite -(round_FLT_FLX radix2 emin (fprec t) (Znearest choice) _ N2).
  rewrite Rplus_comm.
  exact (BFMA_round_correct t xl yh (BFMA xh yl (BMULT xl yl)) Hfcl2). }
have H3 : round radix2 (FLX_exp (fprec t)) (Znearest choice)
              (FT2R (Fast2Mult_err xh yh)
               + FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))
        = FT2R (BPLUS (Fast2Mult_err xh yh)
                      (BFMA xl yh (BFMA xh yl (BMULT xl yl)))).
{ rewrite -(round_FLT_FLX radix2 emin (fprec t) (Znearest choice) _ N3).
  exact (BPLUS_round_correct t (Fast2Mult_err xh yh)
           (BFMA xl yh (BFMA xh yl (BMULT xl yl))) Hfcl3). }
(* assemble: bridge the product and closing Fast2Sum, then peel the four rounds *)
rewrite /DWTimesDW.DWTimesDW12 DWTimesFP.TwoProdE.
rewrite (Fast2Mult_correct_weak xh yh Hfmul Nprod').
rewrite /F2Rp /Fast2Mult_err /Fast2Mult_mul /Fast2Mult /fst /snd.
cbv zeta.
rewrite H0 H1 H2 H3.
rewrite (FastTwoSumEq_FLT (Fast2Mult_mul xh yh)
          (BPLUS (Fast2Mult_err xh yh)
                 (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) FIN).
reflexivity.
Qed.

End CorrectDWMulDW_bridge.


(* ============================================================
   Section 4: finiteness of DWTimesDW3 from DWTimesDW_cond.
     fst (DWTimesDW3 xh xl yh yl) = BPLUS ch cl3, where
       ch  = Fast2Mult_mul xh yh   (= BMULT xh yh),
       cl3 = BPLUS (Fast2Mult_err xh yh) (BFMA xl yh (BFMA xh yl (BMULT xl yl))).
   The cond's product bound |round(xh*yh)| <= Omega/4 keeps |ch| small; the two
   double-word relations keep cl3 small; the closing Fast2Sum stays finite.
   ============================================================ *)
Section DWTimesDW_Finite.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin  := (@common.emin t).
Notation fexp  := (SpecFloat.fexp (fprec t) (femax t)).
Notation ulp   := (Ulp.ulp Zaux.radix2 fexp).
Notation Omega := (bpow Zaux.radix2 (femax t)).

Local Instance valid_fexp_inst : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.

(* --- Generic auxiliary bounds (identical to DWMulFP_acc.v) --- *)

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

Lemma aux_format_half_Omega : generic_format radix2 fexp (/2 * Omega).
Proof.
have -> : (/2 * Omega = bpow radix2 (femax t - 1))%R.
{ have -> : Omega = (bpow radix2 (femax t - 1) * bpow radix2 1)%R
    by rewrite -bpow_plus; f_equal; lia.
  have -> : bpow radix2 1 = 2%R by reflexivity.
  lra. }
apply Generic_fmt.generic_format_bpow.
unfold SpecFloat.fexp, SpecFloat.emin.
apply Z.max_lub; pose proof femax_lb t; pose proof fprec_lb t; lia.
Qed.

Lemma aux_xhy_bnd (a b : ftype t) :
  is_finite (BMULT a b) = true ->
  Rabs (FT2R (BMULT a b)) <= /4 * Omega ->
  Rabs (FT2R a * FT2R b) <= /2 * Omega.
Proof.
move => Hfin Hb.
have HΩ : 0 < Omega by apply bpow_gt_0.
have Hr : round radix2 fexp (Znearest choice) (FT2R a * FT2R b) = FT2R (BMULT a b)
  by rewrite BMULT_round_correct.
have HFh  : generic_format radix2 fexp (/2 * Omega) by apply aux_format_half_Omega.
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

Lemma aux_round_ub (v : R) :
  Rabs (round radix2 fexp (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) v)
    <= Rabs v + /2 * ulp v.
Proof.
have He := @Ulp.error_le_half_ulp radix2 fexp valid_fexp_inst choice v.
have Hb : Rabs (round radix2 fexp (Znearest choice) v) <= Rabs v + /2 * ulp v.
{ replace (round radix2 fexp (Znearest choice) v)
     with ((round radix2 fexp (Znearest choice) v - v) + v) at 1 by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rplus_comm. apply Rplus_le_compat_l. exact He. }
exact Hb.
Qed.

Lemma aux_ulp_real (v : R) :
  Rabs v < Omega -> ulp v <= bpow radix2 (femax t - fprec t).
Proof.
move => Hlt. destruct (Req_dec v 0) as [Hv0 | Hv0].
- rewrite Hv0.
  change (Ulp.ulp radix2 (SpecFloat.fexp (fprec t) (femax t)) 0) with
    (Ulp.ulp radix2 (FLT.FLT_exp (3 - femax t - fprec t) (fprec t)) 0).
  rewrite FLT.ulp_FLT_0. apply bpow_le. pose proof femax_lb t; pose proof fprec_lb t; lia.
- rewrite (Ulp.ulp_neq_0 radix2 fexp _ Hv0). apply bpow_le.
  have Hmag : (mag radix2 v <= femax t)%Z
    by apply (mag_le_bpow radix2 v (femax t) Hv0 Hlt).
  unfold cexp, SpecFloat.fexp, SpecFloat.emin.
  apply Z.max_lub; pose proof femax_lb t; pose proof fprec_lb t; lia.
Qed.

Lemma aux_format_small_0 (x : R) :
  generic_format radix2 fexp x -> Rabs x < bpow radix2 emin -> x = 0.
Proof.
move => Hf Hlt. destruct (Req_dec x 0) as [Hx0 | Hx0]; [exact Hx0|].
exfalso.
have Hule : ulp x <= Rabs x.
{ apply Ulp.ulp_le_abs; first [ exact Hx0 | exact Hf ]. }
have Hge : bpow radix2 emin <= ulp x.
{ rewrite (Ulp.ulp_neq_0 radix2 fexp _ Hx0). apply bpow_le.
  unfold cexp, SpecFloat.fexp, SpecFloat.emin. apply Z.le_max_r. }
lra.
Qed.

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
  { apply aux_format_small_0; [apply generic_format_FLT_FT2R|].
    rewrite Hulpe in Hdwu. have HE := bpow_gt_0 radix2 emin.
    eapply Rle_lt_trans; [exact Hdwu|]. lra. }
  rewrite Hb0 Rabs_R0.
  apply Rmult_le_pos; [apply bpow_ge_0 | exact Hap].
Qed.

(* ulp is at most a relative step plus the subnormal floor: a universal bound
   used to keep the extra DW x DW rounding-error terms small. *)
Lemma aux_ulp_rel_emin (v : R) :
  ulp v <= 2 * bpow radix2 (- fprec t) * Rabs v + bpow radix2 emin.
Proof.
have HE0 : 0 <= bpow radix2 emin by apply bpow_ge_0.
have Hvp : 0 <= Rabs v by apply Rabs_pos.
have Hu0 : 0 <= bpow radix2 (- fprec t) by apply bpow_ge_0.
destruct (Rle_lt_dec (bpow radix2 (emin + fprec t - 1)) (Rabs v)) as [Hn | Hs].
- have Hle : ulp v <= Rabs v * bpow radix2 (1 - fprec t) by apply ulp_FLT_le.
  have HBe : bpow radix2 (1 - fprec t) = 2 * bpow radix2 (- fprec t).
  { have -> : (1 - fprec t = 1 + - fprec t)%Z by lia.
    rewrite bpow_plus. have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
  rewrite HBe in Hle. nra.
- have Heq : ulp v = bpow radix2 emin.
  { apply ulp_FLT_small;
      first [ apply fprec_gt_0 | eapply Rlt_trans; [exact Hs | apply bpow_lt; lia] ]. }
  rewrite Heq. nra.
Qed.

(* |round v| <= |v|(1+u) + 1/2 bpow emin. *)
Lemma aux_round_rel (v : R) :
  Rabs (round radix2 fexp (Znearest choice) v)
    <= Rabs v * (1 + bpow radix2 (- fprec t)) + /2 * bpow radix2 emin.
Proof.
eapply Rle_trans; [apply aux_round_ub|].
have Hulp := aux_ulp_rel_emin v.
nra.
Qed.

(* Monotone form: from an upper bound c on |v|, bound |round v|. *)
Lemma aux_round_step (v c : R) :
  Rabs v <= c ->
  Rabs (round radix2 fexp (Znearest choice) v)
    <= c * (1 + bpow radix2 (- fprec t)) + /2 * bpow radix2 emin.
Proof.
move => Hv.
eapply Rle_trans; [apply aux_round_rel|].
have Hu0 : 0 <= bpow radix2 (- fprec t) by apply bpow_ge_0.
have := Rabs_pos v.
nra.
Qed.

(* --- DW x DW-specific term bounds (new; the extra products / FMAs) --- *)

(* |xh*yl| and |xl*yh| are ~u-small relative to |xh*yh| (one low word each);
   |xl*yl| is ~u^2-small (both low words).  Each stays well under Omega. *)
Lemma aux_xhyl_bnd (xh xl yh yl : ftype t) :
  double_word_prop yh yl ->
  Rabs (FT2R xh * FT2R yh) <= /2 * Omega ->
  Rabs (FT2R xh * FT2R yl) <= /2 * bpow radix2 (femax t - fprec t).
Proof.
move => Hdwy Hxhy.
have Hrel := aux_dwu_rel yh yl Hdwy.
have Hxhp : 0 <= Rabs (FT2R xh) by apply Rabs_pos.
have HB0 : 0 <= bpow radix2 (- fprec t) by apply bpow_ge_0.
have HuO : /2 * bpow radix2 (femax t - fprec t)
         = bpow radix2 (- fprec t) * (/2 * Omega).
{ rewrite (_ : bpow radix2 (femax t - fprec t)
             = bpow radix2 (- fprec t) * Omega);
    [ring | rewrite -bpow_plus; f_equal; lia]. }
rewrite Rabs_mult HuO.
rewrite Rabs_mult in Hxhy.
eapply Rle_trans; [apply Rmult_le_compat_l; [exact Hxhp | exact Hrel]|].
nra.
Qed.

Lemma aux_xlyh_bnd (xh xl yh yl : ftype t) :
  double_word_prop xh xl ->
  Rabs (FT2R xh * FT2R yh) <= /2 * Omega ->
  Rabs (FT2R xl * FT2R yh) <= /2 * bpow radix2 (femax t - fprec t).
Proof.
move => Hdwx Hxhy.
have Hrel := aux_dwu_rel xh xl Hdwx.
have Hyhp : 0 <= Rabs (FT2R yh) by apply Rabs_pos.
have HB0 : 0 <= bpow radix2 (- fprec t) by apply bpow_ge_0.
have HuO : /2 * bpow radix2 (femax t - fprec t)
         = bpow radix2 (- fprec t) * (/2 * Omega).
{ rewrite (_ : bpow radix2 (femax t - fprec t)
             = bpow radix2 (- fprec t) * Omega);
    [ring | rewrite -bpow_plus; f_equal; lia]. }
rewrite Rabs_mult HuO.
rewrite Rabs_mult in Hxhy.
eapply Rle_trans; [apply Rmult_le_compat_r; [exact Hyhp | exact Hrel]|].
nra.
Qed.

Lemma aux_xlyl_bnd (xh xl yh yl : ftype t) :
  double_word_prop xh xl ->
  double_word_prop yh yl ->
  Rabs (FT2R xh * FT2R yh) <= /2 * Omega ->
  Rabs (FT2R xl * FT2R yl) <= /2 * bpow radix2 (femax t - fprec t).
Proof.
move => Hdwx Hdwy Hxhy.
have Hrelx := aux_dwu_rel xh xl Hdwx.
have Hrely := aux_dwu_rel yh yl Hdwy.
have Hxlp : 0 <= Rabs (FT2R xl) by apply Rabs_pos.
have Hylp : 0 <= Rabs (FT2R yl) by apply Rabs_pos.
have Hyhp : 0 <= Rabs (FT2R yh) by apply Rabs_pos.
have HB0 : 0 <= bpow radix2 (- fprec t) by apply bpow_ge_0.
have Hu1 : bpow radix2 (- fprec t) <= 1.
{ have -> : (1 = bpow radix2 0)%R by reflexivity. apply bpow_le; pose proof fprec_lb t; lia. }
have HuO : /2 * bpow radix2 (femax t - fprec t)
         = bpow radix2 (- fprec t) * (/2 * Omega).
{ rewrite (_ : bpow radix2 (femax t - fprec t)
             = bpow radix2 (- fprec t) * Omega);
    [ring | rewrite -bpow_plus; f_equal; lia]. }
rewrite Rabs_mult HuO.
rewrite Rabs_mult in Hxhy.
have Hxhp : 0 <= Rabs (FT2R xh) by apply Rabs_pos.
have Hstep : Rabs (FT2R xl) * Rabs (FT2R yl)
          <= (bpow radix2 (- fprec t) * Rabs (FT2R xh))
             * (bpow radix2 (- fprec t) * Rabs (FT2R yh)).
{ apply Rmult_le_compat; [exact Hxlp | exact Hylp | exact Hrelx | exact Hrely]. }
eapply Rle_trans; [exact Hstep|].
have Hre : (bpow radix2 (- fprec t) * Rabs (FT2R xh))
           * (bpow radix2 (- fprec t) * Rabs (FT2R yh))
         = bpow radix2 (- fprec t)
           * (bpow radix2 (- fprec t) * (Rabs (FT2R xh) * Rabs (FT2R yh))) by ring.
rewrite Hre.
apply Rmult_le_compat_l; [exact HB0|].
have HRxy : 0 <= Rabs (FT2R xh) * Rabs (FT2R yh) by apply Rmult_le_pos.
nra.
Qed.

(* Magnitude ordering |cl3| <= |ch| for the closing Fast2Sum, in the normal
   product regime |xh*yh| >= bpow(emin+2p-1).  Everything scales with the
   product P = |xh*yh|: the low words give |cl1|,|xh*yl|,|xl*yh| <= u*P and
   |xl*yl| <= u^2*P, so accumulating the four roundings keeps |cl3| <= 6u*P,
   which is <= (1-u)*P <= |ch| once 7u <= 1 (fprec >= 3). *)
Lemma aux_cl3_le_ch (xh xl yh yl : ftype t) :
  (3 <= fprec t)%Z ->
  double_word_prop xh xl ->
  double_word_prop yh yl ->
  is_finite (BMULT xh yh) = true ->
  is_finite (BPLUS (Fast2Mult_err xh yh)
                   (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) = true ->
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh) ->
  Rabs (FT2R (BPLUS (Fast2Mult_err xh yh)
                    (BFMA xl yh (BFMA xh yl (BMULT xl yl)))))
    <= Rabs (FT2R (Fast2Mult_mul xh yh)).
Proof.
move => Hp3 Hdwx Hdwy Hfmul Hfsum Hthresh.
(* basic quantities *)
have HP0 : 0 < Rabs (FT2R xh * FT2R yh)
  by (eapply Rlt_le_trans; [apply bpow_gt_0 | exact Hthresh]).
have Hu0 : 0 < bpow radix2 (- fprec t) by apply bpow_gt_0.
have Hule : bpow radix2 (- fprec t) <= /8.
{ have -> : (/8 = bpow radix2 (-3))%R by (simpl; lra). apply bpow_le; lia. }
have H1u : 1 + bpow radix2 (- fprec t) <= 9/8 by lra.
have HuP0 : 0 <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)
  by (apply Rmult_le_pos; [lra | apply Rabs_pos]).
have Hu2P0 : 0 <= bpow radix2 (- fprec t) * bpow radix2 (- fprec t)
                    * Rabs (FT2R xh * FT2R yh)
  by (repeat apply Rmult_le_pos; try lra; apply Rabs_pos).
(* u^2 P <= /8 (u P) *)
have Huu : bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)
        <= /8 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)).
{ have -> : bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)
          = bpow radix2 (- fprec t) * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh))
    by ring.
  apply Rmult_le_compat_r; [exact HuP0 | exact Hule]. }
(* the subnormal floor is tiny: E <= 2 u^2 P *)
have HEP : bpow radix2 emin
        <= 2 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t))
             * Rabs (FT2R xh * FT2R yh).
{ have Hle : bpow radix2 (emin - 1)
          <= bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
  { eapply Rle_trans;
      [| apply Rmult_le_compat_l; [apply Rmult_le_pos; apply bpow_ge_0 | exact Hthresh]].
    rewrite -!bpow_plus. apply bpow_le. lia. }
  have -> : bpow radix2 emin = 2 * bpow radix2 (emin - 1).
  { have H1 : bpow radix2 emin = bpow radix2 (emin - 1) * bpow radix2 1
      by (rewrite -bpow_plus; f_equal; lia).
    rewrite H1. have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
  lra. }
(* subterm finiteness *)
destruct (BPLUS_finite_e t _ _ Hfsum) as [Hfcl1 Hfcl2].
destruct (BFMA_finite_e t xl yh (BFMA xh yl (BMULT xl yl)) Hfcl2) as [_ [_ Hftl1]].
destruct (BFMA_finite_e t xh yl (BMULT xl yl) Hftl1) as [_ [_ Hftl0]].
have Huf' : FT2R xh * FT2R yh <> 0 ->
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh)
  by (move => _; exact Hthresh).
(* |cl1| <= u P and |ch| >= P - u P *)
have Hcl1u : Rabs (FT2R (Fast2Mult_err xh yh)) <= /2 * ulp (FT2R xh * FT2R yh)
  by (apply Fast2Mult_accuracy_norm; exact Hfmul).
have Hulpxhyh : ulp (FT2R xh * FT2R yh)
             <= Rabs (FT2R xh * FT2R yh) * bpow radix2 (1 - fprec t).
{ apply ulp_FLT_le. eapply Rle_trans; [| exact Hthresh]. apply bpow_le.
  unfold common.emin, SpecFloat.emin. pose proof fprec_lb t; lia. }
have HBp : bpow radix2 (1 - fprec t) = 2 * bpow radix2 (- fprec t).
{ have -> : (1 - fprec t = 1 + - fprec t)%Z by lia.
  rewrite bpow_plus. have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
have Hcl1 : Rabs (FT2R (Fast2Mult_err xh yh))
         <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
{ rewrite HBp in Hulpxhyh. nra. }
have Hcl1_eq : FT2R (Fast2Mult_err xh yh) = FT2R xh * FT2R yh - FT2R (Fast2Mult_mul xh yh)
  by (apply Fast2MultModel_correct; [exact Hfmul | exact Huf']).
have Hch_lb : Rabs (FT2R xh * FT2R yh) - bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)
           <= Rabs (FT2R (Fast2Mult_mul xh yh)).
{ have Hche : FT2R (Fast2Mult_mul xh yh) = FT2R xh * FT2R yh - FT2R (Fast2Mult_err xh yh)
    by (rewrite Hcl1_eq; ring).
  rewrite Hche.
  eapply Rle_trans; [| apply Rabs_triang_inv].
  have := Hcl1. lra. }
(* the three products (relative bounds) *)
have Hxhyl : Rabs (FT2R xh * FT2R yl)
          <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
{ have Hyl := aux_dwu_rel yh yl Hdwy.
  rewrite !Rabs_mult. have Hxhp : 0 <= Rabs (FT2R xh) by apply Rabs_pos. nra. }
have Hxlyh : Rabs (FT2R xl * FT2R yh)
          <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
{ have Hxl := aux_dwu_rel xh xl Hdwx.
  rewrite !Rabs_mult. have Hyhp : 0 <= Rabs (FT2R yh) by apply Rabs_pos. nra. }
have Hxlyl : Rabs (FT2R xl * FT2R yl)
          <= bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
{ have Hxl := aux_dwu_rel xh xl Hdwx.
  have Hyl := aux_dwu_rel yh yl Hdwy.
  rewrite !Rabs_mult.
  have Hxlp : 0 <= Rabs (FT2R xl) by apply Rabs_pos.
  have Hylp : 0 <= Rabs (FT2R yl) by apply Rabs_pos.
  have Hstep : Rabs (FT2R xl) * Rabs (FT2R yl)
            <= (bpow radix2 (- fprec t) * Rabs (FT2R xh))
               * (bpow radix2 (- fprec t) * Rabs (FT2R yh))
    by (apply Rmult_le_compat; [exact Hxlp | exact Hylp | exact Hxl | exact Hyl]).
  eapply Rle_trans; [exact Hstep|]. apply Req_le; ring. }
(* |tl0| <= u P *)
have Htl0 : Rabs (FT2R (BMULT xl yl))
         <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
{ rewrite -BMULT_round_correct; [| exact Hftl0].
  eapply Rle_trans; [ apply (aux_round_step _ _ Hxlyl) |].
  have Hm := Rmult_le_compat_l _ _ _ Hu2P0 H1u. lra. }
(* |tl1| <= 3 u P *)
have Harg1 : Rabs (FT2R xh * FT2R yl + FT2R (BMULT xl yl))
          <= 2 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh))
  by (eapply Rle_trans; [apply Rabs_triang|]; lra).
have Htl1 : Rabs (FT2R (BFMA xh yl (BMULT xl yl)))
         <= 3 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)).
{ rewrite -BFMA_round_correct; [| exact Hftl1].
  eapply Rle_trans; [ apply (aux_round_step _ _ Harg1) |].
  have Hc0 : 0 <= 2 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)) by lra.
  have Hm := Rmult_le_compat_l _ _ _ Hc0 H1u. lra. }
(* |cl2| <= 5 u P *)
have Harg2 : Rabs (FT2R xl * FT2R yh + FT2R (BFMA xh yl (BMULT xl yl)))
          <= 4 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh))
  by (eapply Rle_trans; [apply Rabs_triang|]; lra).
have Hcl2 : Rabs (FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))
         <= 5 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)).
{ rewrite -BFMA_round_correct; [| exact Hfcl2].
  eapply Rle_trans; [ apply (aux_round_step _ _ Harg2) |].
  have Hc0 : 0 <= 4 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)) by lra.
  have Hm := Rmult_le_compat_l _ _ _ Hc0 H1u. lra. }
(* |cl1 + cl2| <= 6 u P <= (1-u) P <= |ch| *)
have Hw : Rabs (FT2R (Fast2Mult_err xh yh)
                + FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))
       <= Rabs (FT2R (Fast2Mult_mul xh yh)).
{ eapply Rle_trans; [apply Rabs_triang|].
  eapply Rle_trans; [apply Rplus_le_compat; [exact Hcl1 | exact Hcl2]|].
  eapply Rle_trans; [| exact Hch_lb]. nra. }
rewrite -BPLUS_round_correct; [| exact Hfsum].
apply abs_round_le_generic.
all: try exact Hw.
all: try apply valid_rnd_N.
all: try apply generic_format_abs.
all: try exact valid_fexp_inst.
all: try apply generic_format_FLT_FT2R.
Qed.

(* Per-term rounding-error bound: |round v - v| <= c*u + 1/2 bpow emin when |v|<=c. *)
Lemma aux_err_step (v c : R) :
  Rabs v <= c ->
  Rabs (round radix2 fexp (Znearest choice) v - v)
    <= c * bpow radix2 (- fprec t) + /2 * bpow radix2 emin.
Proof.
move => Hv.
have He := @Ulp.error_le_half_ulp radix2 fexp valid_fexp_inst choice v.
have Hu := aux_ulp_rel_emin v.
have Hvp := Rabs_pos v.
have Hu0 : 0 <= bpow radix2 (- fprec t) by apply bpow_ge_0.
nra.
Qed.

(* Sharper per-term error bound: the relative term and the subnormal floor are a
   MAX, not a sum.  In the normal range ulp v = 2u|v| so the error is <= u|v| <= uc
   with no floor; in the subnormal range the error is <= 1/2 bpow emin and the
   relative term is smaller.  This lets aux_eta_bnd ABSORB the four 1/2 bpow emin
   floors into the u^2 P scale rather than adding them, dropping |eta| from ~11 to
   ~7.5 u^2 P. *)
Lemma aux_err_step2 (v c : R) :
  Rabs v <= c ->
  Rabs (round radix2 fexp (Znearest choice) v - v)
    <= Rmax (c * bpow radix2 (- fprec t)) (/2 * bpow radix2 emin).
Proof.
move => Hv.
have He := @Ulp.error_le_half_ulp radix2 fexp valid_fexp_inst choice v.
have Hvp := Rabs_pos v.
have Hu0 : 0 <= bpow radix2 (- fprec t) by apply bpow_ge_0.
destruct (Rle_lt_dec (bpow radix2 (emin + fprec t - 1)) (Rabs v)) as [Hn | Hs].
- (* normal: 1/2 ulp v <= u|v| <= u c *)
  have Hle : ulp v <= Rabs v * bpow radix2 (1 - fprec t) by apply ulp_FLT_le.
  have HBe : bpow radix2 (1 - fprec t) = 2 * bpow radix2 (- fprec t).
  { have -> : (1 - fprec t = 1 + - fprec t)%Z by lia.
    rewrite bpow_plus. have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
  rewrite HBe in Hle.
  eapply Rle_trans; [exact He|]. eapply Rle_trans; [| apply Rmax_l]. nra.
- (* subnormal: ulp v = bpow emin *)
  have Heq : ulp v = bpow radix2 emin.
  { apply ulp_FLT_small;
      first [ apply fprec_gt_0 | eapply Rlt_trans; [exact Hs | apply bpow_lt; lia] ]. }
  eapply Rle_trans; [exact He|]. rewrite Heq. apply Rmax_r.
Qed.

(* Aggregate error bound for the underflow leg: |e0+e1+e2+e3| <= 15/2 u^2 P.  Uses
   the floor-ABSORBING chain (aux_err_step2 gives each error as a MAX of relative
   term and subnormal floor, not a sum): magnitudes |tl0|<=2u^2P, |tl1|<=uP+4u^2P,
   |cl2|<=2uP+7u^2P (leading coeffs 1,2,3 on uP), each error e_i <= u*|arg_i| for
   i>=1 (floor absorbed) and e0<=u^2P.  Sum = 7 u^2 P + 13 u^3 P <= 15/2 u^2 P via
   u <= 1/32 (from 5 <= fprec t).  The floors are no longer additive. *)
Lemma aux_eta_bnd (xh xl yh yl : ftype t) :
  (5 <= fprec t)%Z ->
  double_word_prop xh xl -> double_word_prop yh yl ->
  is_finite (BMULT xh yh) = true ->
  is_finite (BMULT xl yl) = true ->
  is_finite (BFMA xh yl (BMULT xl yl)) = true ->
  is_finite (BFMA xl yh (BFMA xh yl (BMULT xl yl))) = true ->
  is_finite (BPLUS (Fast2Mult_err xh yh)
                   (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) = true ->
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh) ->
  Rabs ((FT2R (BMULT xl yl) - FT2R xl * FT2R yl)
        + (FT2R (BFMA xh yl (BMULT xl yl))
           - (FT2R xh * FT2R yl + FT2R (BMULT xl yl)))
        + (FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))
           - (FT2R xl * FT2R yh + FT2R (BFMA xh yl (BMULT xl yl))))
        + (FT2R (BPLUS (Fast2Mult_err xh yh)
                       (BFMA xl yh (BFMA xh yl (BMULT xl yl))))
           - (FT2R (Fast2Mult_err xh yh)
              + FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))))
    <= 15/2 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t))
          * Rabs (FT2R xh * FT2R yh).
Proof.
move => Hp5 Hdwx Hdwy Hfmul Hftl0 Hftl1 Hfcl2 Hfsum Hthresh.
have HP0 : 0 < Rabs (FT2R xh * FT2R yh)
  by (eapply Rlt_le_trans; [apply bpow_gt_0 | exact Hthresh]).
have Hu0 : 0 < bpow radix2 (- fprec t) by apply bpow_gt_0.
have Hule : bpow radix2 (- fprec t) <= /32.
{ have -> : (/32 = bpow radix2 (-5))%R by (simpl; lra). apply bpow_le; lia. }
have H1u : 1 + bpow radix2 (- fprec t) <= 9/8 by lra.
have HuP0 : 0 <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)
  by (apply Rmult_le_pos; [lra | apply Rabs_pos]).
have Hu2P0 : 0 <= bpow radix2 (- fprec t) * bpow radix2 (- fprec t)
                    * Rabs (FT2R xh * FT2R yh)
  by (repeat apply Rmult_le_pos; try lra; apply Rabs_pos).
have Huu : bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)
        <= /8 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)).
{ have -> : bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)
          = bpow radix2 (- fprec t) * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh))
    by ring.
  apply Rmult_le_compat_r; [exact HuP0 |]. have := Hule; lra. }
have HEP : bpow radix2 emin
        <= 2 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t))
             * Rabs (FT2R xh * FT2R yh).
{ have Hle : bpow radix2 (emin - 1)
          <= bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
  { eapply Rle_trans;
      [| apply Rmult_le_compat_l; [apply Rmult_le_pos; apply bpow_ge_0 | exact Hthresh]].
    rewrite -!bpow_plus. apply bpow_le. lia. }
  have -> : bpow radix2 emin = 2 * bpow radix2 (emin - 1).
  { have H1 : bpow radix2 emin = bpow radix2 (emin - 1) * bpow radix2 1
      by (rewrite -bpow_plus; f_equal; lia).
    rewrite H1. have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
  lra. }
have Huf' : FT2R xh * FT2R yh <> 0 ->
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh)
  by (move => _; exact Hthresh).
(* argument-magnitude chain (copied from aux_cl3_le_ch) *)
have Hcl1u : Rabs (FT2R (Fast2Mult_err xh yh)) <= /2 * ulp (FT2R xh * FT2R yh)
  by (apply Fast2Mult_accuracy_norm; exact Hfmul).
have Hulpxhyh : ulp (FT2R xh * FT2R yh)
             <= Rabs (FT2R xh * FT2R yh) * bpow radix2 (1 - fprec t).
{ apply ulp_FLT_le. eapply Rle_trans; [| exact Hthresh]. apply bpow_le.
  unfold common.emin, SpecFloat.emin. pose proof fprec_lb t; lia. }
have HBp : bpow radix2 (1 - fprec t) = 2 * bpow radix2 (- fprec t).
{ have -> : (1 - fprec t = 1 + - fprec t)%Z by lia.
  rewrite bpow_plus. have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
have Hcl1 : Rabs (FT2R (Fast2Mult_err xh yh))
         <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
{ rewrite HBp in Hulpxhyh. nra. }
have Hxhyl : Rabs (FT2R xh * FT2R yl)
          <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
{ have Hyl := aux_dwu_rel yh yl Hdwy.
  rewrite !Rabs_mult. have Hxhp : 0 <= Rabs (FT2R xh) by apply Rabs_pos. nra. }
have Hxlyh : Rabs (FT2R xl * FT2R yh)
          <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
{ have Hxl := aux_dwu_rel xh xl Hdwx.
  rewrite !Rabs_mult. have Hyhp : 0 <= Rabs (FT2R yh) by apply Rabs_pos. nra. }
have Hxlyl : Rabs (FT2R xl * FT2R yl)
          <= bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
{ have Hxl := aux_dwu_rel xh xl Hdwx.
  have Hyl := aux_dwu_rel yh yl Hdwy.
  rewrite !Rabs_mult.
  have Hxlp : 0 <= Rabs (FT2R xl) by apply Rabs_pos.
  have Hylp : 0 <= Rabs (FT2R yl) by apply Rabs_pos.
  have Hstep : Rabs (FT2R xl) * Rabs (FT2R yl)
            <= (bpow radix2 (- fprec t) * Rabs (FT2R xh))
               * (bpow radix2 (- fprec t) * Rabs (FT2R yh))
    by (apply Rmult_le_compat; [exact Hxlp | exact Hylp | exact Hxl | exact Hyl]).
  eapply Rle_trans; [exact Hstep|]. apply Req_le; ring. }
(* Floor-absorbing chain.  Each rounding error is bounded by a MAX (aux_err_step2),
   and each intermediate magnitude by |arg| + error (triangle); so the four
   1/2 bpow emin floors are ABSORBED into the u^2 P scale instead of added.  Leading
   coefficients on uP stay 1,2,3; the u^2 P corrections shrink (2,4,7).  Order:
   compute each error e_i first, then the magnitude it feeds. *)
(* e0, then |tl0| <= 2 u^2 P *)
have He0 : Rabs (FT2R (BMULT xl yl) - FT2R xl * FT2R yl)
        <= bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
{ rewrite -BMULT_round_correct; [| exact Hftl0].
  eapply Rle_trans; [ apply (aux_err_step2 _ _ Hxlyl) |].
  apply Rmax_lub; [ have := Hu2P0; have := Hule; nra | have := HEP; lra ]. }
have Htl0 : Rabs (FT2R (BMULT xl yl))
         <= 2 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)).
{ have Hsplit : FT2R (BMULT xl yl)
             = FT2R xl * FT2R yl + (FT2R (BMULT xl yl) - FT2R xl * FT2R yl) by ring.
  rewrite {1}Hsplit. eapply Rle_trans; [apply Rabs_triang|].
  have := Hxlyl. have := He0. lra. }
(* |arg1| <= uP + 2 u^2 P, e1, then |tl1| <= uP + 4 u^2 P *)
have Harg1 : Rabs (FT2R xh * FT2R yl + FT2R (BMULT xl yl))
          <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)
           + 2 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)).
{ eapply Rle_trans; [apply Rabs_triang|]. have := Hxhyl. have := Htl0. lra. }
have He1 : Rabs (FT2R (BFMA xh yl (BMULT xl yl))
                 - (FT2R xh * FT2R yl + FT2R (BMULT xl yl)))
        <= (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)
            + 2 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)))
             * bpow radix2 (- fprec t).
{ rewrite -BFMA_round_correct; [| exact Hftl1].
  eapply Rle_trans; [ apply (aux_err_step2 _ _ Harg1) |].
  apply Rmax_lub; [ apply Rle_refl
                  | have := HuP0; have := Hu2P0; have := HEP; have := Hule; nra ]. }
have Htl1 : Rabs (FT2R (BFMA xh yl (BMULT xl yl)))
         <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)
          + 4 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)).
{ have Hsplit : FT2R (BFMA xh yl (BMULT xl yl))
             = (FT2R xh * FT2R yl + FT2R (BMULT xl yl))
               + (FT2R (BFMA xh yl (BMULT xl yl))
                  - (FT2R xh * FT2R yl + FT2R (BMULT xl yl))) by ring.
  rewrite {1}Hsplit. eapply Rle_trans; [apply Rabs_triang|].
  have := Harg1. have := He1. have := Hu2P0. have := Hule. nra. }
(* |arg2| <= 2uP + 4 u^2 P, e2, then |cl2| <= 2uP + 7 u^2 P *)
have Harg2 : Rabs (FT2R xl * FT2R yh + FT2R (BFMA xh yl (BMULT xl yl)))
          <= 2 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh))
           + 4 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)).
{ eapply Rle_trans; [apply Rabs_triang|]. have := Hxlyh. have := Htl1. lra. }
have He2 : Rabs (FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))
                 - (FT2R xl * FT2R yh + FT2R (BFMA xh yl (BMULT xl yl))))
        <= (2 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh))
            + 4 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)))
             * bpow radix2 (- fprec t).
{ rewrite -BFMA_round_correct; [| exact Hfcl2].
  eapply Rle_trans; [ apply (aux_err_step2 _ _ Harg2) |].
  apply Rmax_lub; [ apply Rle_refl
                  | have := HuP0; have := Hu2P0; have := HEP; have := Hule; nra ]. }
have Hcl2 : Rabs (FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))
         <= 2 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh))
          + 7 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)).
{ have Hsplit : FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))
             = (FT2R xl * FT2R yh + FT2R (BFMA xh yl (BMULT xl yl)))
               + (FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))
                  - (FT2R xl * FT2R yh + FT2R (BFMA xh yl (BMULT xl yl)))) by ring.
  rewrite {1}Hsplit. eapply Rle_trans; [apply Rabs_triang|].
  have := Harg2. have := He2. have := Hu2P0. have := Hule. nra. }
(* |arg3| <= 3uP + 7 u^2 P, e3 *)
have Harg3 : Rabs (FT2R (Fast2Mult_err xh yh)
                   + FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))
          <= 3 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh))
           + 7 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)).
{ eapply Rle_trans; [apply Rabs_triang|]. have := Hcl1. have := Hcl2. lra. }
have He3 : Rabs (FT2R (BPLUS (Fast2Mult_err xh yh)
                             (BFMA xl yh (BFMA xh yl (BMULT xl yl))))
                 - (FT2R (Fast2Mult_err xh yh)
                    + FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))))
        <= (3 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh))
            + 7 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)))
             * bpow radix2 (- fprec t).
{ rewrite -BPLUS_round_correct; [| exact Hfsum].
  eapply Rle_trans; [ apply (aux_err_step2 _ _ Harg3) |].
  apply Rmax_lub; [ apply Rle_refl
                  | have := HuP0; have := Hu2P0; have := HEP; have := Hule; nra ]. }
(* triangle over the four terms, then combine numerically:
   sum <= u^2 P + (uP+2u^2P)u + (2uP+4u^2P)u + (3uP+7u^2P)u = 7 u^2 P + 13 u^3 P;
   with u <= 1/32, 13 u^3 P <= 13/32 u^2 P < 1/2 u^2 P, so sum <= 15/2 u^2 P. *)
eapply Rle_trans.
- eapply Rle_trans; [apply Rabs_triang|]. apply Rplus_le_compat; [| exact He3].
  eapply Rle_trans; [apply Rabs_triang|]. apply Rplus_le_compat; [| exact He2].
  eapply Rle_trans; [apply Rabs_triang|]. apply Rplus_le_compat; [exact He0 | exact He1].
- have := HuP0. have := Hu2P0. have := HEP. have := Hule. nra.
Qed.

(* /4 * Omega = bpow(femax-2) is representable. *)
Lemma aux_format_quarter_Omega : generic_format radix2 fexp (/4 * Omega).
Proof.
have -> : (/4 * Omega = bpow radix2 (femax t - 2))%R.
{ have -> : Omega = (bpow radix2 (femax t - 2) * bpow radix2 2)%R
    by rewrite -bpow_plus; f_equal; lia.
  have -> : bpow radix2 2 = 4%R by reflexivity. lra. }
apply Generic_fmt.generic_format_bpow.
unfold SpecFloat.fexp, SpecFloat.emin.
apply Z.max_lub; pose proof femax_lb t; pose proof fprec_lb t; lia.
Qed.

(* The cond's factor bounds |xh|,|yh| <= bpow(femax/2-1) give the product bound
   |xh*yh| <= Omega/4 (from which product finiteness and the rounded-product
   bound follow), replacing DWTimesDW_cond's former explicit product fields. *)
Lemma aux_factor_prod (a b : ftype t) :
  Rabs (FT2R a) <= bpow radix2 (femax t / 2 - 1) ->
  Rabs (FT2R b) <= bpow radix2 (femax t / 2 - 1) ->
  Rabs (FT2R a * FT2R b) <= /4 * Omega.
Proof.
move => Ha Hb.
have Hdm : (2 * (femax t / 2) <= femax t)%Z.
{ pose proof (Z.div_mod (femax t) 2 ltac:(lia));
  pose proof (Z.mod_pos_bound (femax t) 2 ltac:(lia)); lia. }
rewrite Rabs_mult.
eapply Rle_trans.
{ apply Rmult_le_compat; try apply Rabs_pos; [exact Ha | exact Hb]. }
rewrite -bpow_plus.
have -> : (/4 * Omega = bpow radix2 (femax t - 2))%R.
{ have -> : Omega = (bpow radix2 (femax t - 2) * bpow radix2 2)%R
    by rewrite -bpow_plus; f_equal; lia.
  have -> : bpow radix2 2 = 4%R by reflexivity. lra. }
apply bpow_le. lia.
Qed.

Lemma aux_factor_finite (a b : ftype t) :
  is_finite a = true -> is_finite b = true ->
  Rabs (FT2R a * FT2R b) <= /4 * Omega ->
  is_finite (BMULT a b) = true.
Proof.
move => Ha Hb Hp.
have HΩ : 0 < Omega by apply bpow_gt_0.
have HEq : bpow radix2 (femax t - fprec t) <= /4 * Omega.
{ have -> : (/4 * Omega = bpow radix2 (femax t - 2))%R.
  { have -> : Omega = (bpow radix2 (femax t - 2) * bpow radix2 2)%R
      by rewrite -bpow_plus; f_equal; lia.
    have -> : bpow radix2 2 = 4%R by reflexivity. lra. }
  apply bpow_le; pose proof fprec_lb t; lia. }
apply no_overflow_mult_is_finite => //.
eapply Rle_lt_trans; [apply aux_round_ub|].
have Hlt : Rabs (FT2R a * FT2R b) < Omega by lra.
have Hu := aux_ulp_real _ Hlt. lra.
Qed.

Lemma aux_factor_round_bnd (a b : ftype t) :
  is_finite (BMULT a b) = true ->
  Rabs (FT2R a * FT2R b) <= /4 * Omega ->
  Rabs (FT2R (BMULT a b)) <= /4 * Omega.
Proof.
move => Hfin Hp.
rewrite -BMULT_round_correct; [| exact Hfin].
apply abs_round_le_generic.
all: try exact Hp.
all: try apply valid_rnd_N.
all: try exact valid_fexp_inst.
all: try apply aux_format_quarter_Omega.
Qed.

(* The weakened DWTimesDW_cond bounds the real product by /2*Omega; since
   /2*Omega is representable (aux_format_half_Omega), the rounded product stays
   <= /2*Omega.  Same structure as aux_factor_round_bnd, larger representable
   bound. *)
Lemma aux_round_half_bnd (a b : ftype t) :
  is_finite (BMULT a b) = true ->
  Rabs (FT2R a * FT2R b) <= /2 * Omega ->
  Rabs (FT2R (BMULT a b)) <= /2 * Omega.
Proof.
move => Hfin Hp.
rewrite -BMULT_round_correct; [| exact Hfin].
apply abs_round_le_generic.
all: try exact Hp.
all: try apply valid_rnd_N.
all: try exact valid_fexp_inst.
all: try apply aux_format_half_Omega.
Qed.

(* MAIN: the closing Fast2Sum of DWTimesDW3 stays finite under the cond. *)
Lemma DWTimesDW3_fst_finite (xh xl yh yl : ftype t) :
  (4 <= fprec t)%Z ->
  DWTimesDW_cond xh xl yh yl ->
  is_finite (fst (DWTimesDW3 xh xl yh yl)) = true.
Proof.
intros Hp4 (Hfxl & Hfyl & Hdwx & Hdwy & Hf2m & Hxhy4).
have Hp3 : (3 <= fprec t)%Z by lia.
have Huf := proj2 Hf2m.
have Hfmul : is_finite (BMULT xh yh) = true by exact (proj1 Hf2m).
have [Hfxh Hfyh] := BMULT_finite_e t xh yh Hfmul.
(* the cond now bounds the real product by /2*Omega; the rounded product then
   stays <= /2*Omega (representable bound, RN monotone) *)
have Hprod : Rabs (FT2R (BMULT xh yh)) <= /2 * Omega
  by (apply aux_round_half_bnd; [exact Hfmul | exact Hxhy4]).
have HΩ : 0 < Omega by apply bpow_gt_0.
have HE0 : 0 <= bpow radix2 (femax t - fprec t) by apply bpow_ge_0.
have HEq : bpow radix2 (femax t - fprec t) <= /4 * Omega.
{ have -> : (/4 * Omega = bpow radix2 (femax t - 2))%R.
  { have -> : Omega = (bpow radix2 (femax t - 2) * bpow radix2 2)%R
      by rewrite -bpow_plus; f_equal; lia.
    have -> : bpow radix2 2 = 4%R by reflexivity. lra. }
  apply bpow_le; pose proof fprec_lb t; lia. }
(* tighter: bpow(femax-fprec) = u*Omega <= Omega/16 (fprec >= 4) *)
have Hbu : bpow radix2 (femax t - fprec t) = bpow radix2 (- fprec t) * Omega
  by (rewrite -bpow_plus; f_equal; lia).
have Hu16 : bpow radix2 (- fprec t) <= /16.
{ have -> : (/16 = bpow radix2 (-4))%R by (simpl; lra).
  apply bpow_le; lia. }
have HE16 : bpow radix2 (femax t - fprec t) <= /16 * Omega.
{ rewrite Hbu. have := bpow_ge_0 radix2 (- fprec t). nra. }
(* ch = BMULT xh yh : finite, bounded by Omega/2 *)
have Hfch : is_finite (Fast2Mult_mul xh yh) = true.
{ unfold Fast2Mult_mul, Fast2Mult, fst. exact Hfmul. }
have Hch4 : Rabs (FT2R (Fast2Mult_mul xh yh)) <= /2 * Omega.
{ unfold Fast2Mult_mul, Fast2Mult, fst. exact Hprod. }
have Huf' : FT2R xh * FT2R yh <> 0 ->
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh).
{ intro Hne. destruct Huf as [H | H]; [contradiction | exact H]. }
(* cl1 = Fast2Mult_err xh yh : finite, |cl1| <= 1/2 bpow(femax-fprec) *)
have Hfcl1 : is_finite (Fast2Mult_err xh yh) = true.
{ destruct (Fast2Mult_finite_if_BMULT_finite xh yh Huf' Hfmul) as [_ H]. exact H. }
have Hcl1u : Rabs (FT2R (Fast2Mult_err xh yh)) <= /2 * ulp (FT2R xh * FT2R yh).
{ apply Fast2Mult_accuracy_norm; exact Hfmul. }
have Hxhy : Rabs (FT2R xh * FT2R yh) <= /2 * Omega
  by (eapply Rle_trans; [exact Hxhy4|]; lra).
have Hxhy_lt : Rabs (FT2R xh * FT2R yh) < Omega by lra.
have Hcl1b : Rabs (FT2R (Fast2Mult_err xh yh)) <= /2 * bpow radix2 (femax t - fprec t).
{ eapply Rle_trans; [exact Hcl1u|]. apply Rmult_le_compat_l; [lra|].
  apply aux_ulp_real; exact Hxhy_lt. }
(* the three extra products, each <= 1/2 bpow(femax-fprec) *)
have Hxlyl : Rabs (FT2R xl * FT2R yl) <= /2 * bpow radix2 (femax t - fprec t)
  by (apply (aux_xlyl_bnd xh xl yh yl); [exact Hdwx | exact Hdwy | exact Hxhy]).
have Hxhyl : Rabs (FT2R xh * FT2R yl) <= /2 * bpow radix2 (femax t - fprec t)
  by (apply (aux_xhyl_bnd xh xl yh yl); [exact Hdwy | exact Hxhy]).
have Hxlyh : Rabs (FT2R xl * FT2R yh) <= /2 * bpow radix2 (femax t - fprec t)
  by (apply (aux_xlyh_bnd xh xl yh yl); [exact Hdwx | exact Hxhy]).
(* tl0 = BMULT xl yl : finite, |tl0| <= bpow(femax-fprec) *)
have Hxlyl_lt : Rabs (FT2R xl * FT2R yl) < Omega by lra.
have Hftl0 : is_finite (BMULT xl yl) = true.
{ apply no_overflow_mult_is_finite => //.
  eapply Rle_lt_trans; [apply aux_round_ub|].
  have Hu := aux_ulp_real _ Hxlyl_lt. lra. }
have Htl0b : Rabs (FT2R (BMULT xl yl)) <= bpow radix2 (femax t - fprec t).
{ rewrite -BMULT_round_correct; [| exact Hftl0].
  eapply Rle_trans; [apply aux_round_ub|].
  have Hu := aux_ulp_real _ Hxlyl_lt. lra. }
(* tl1 = BFMA xh yl tl0 : finite, |tl1| <= 2 bpow(femax-fprec) *)
have Harg1 : Rabs (FT2R xh * FT2R yl + FT2R (BMULT xl yl))
          <= 3/2 * bpow radix2 (femax t - fprec t)
  by (eapply Rle_trans; [apply Rabs_triang|]; lra).
have Harg1_lt : Rabs (FT2R xh * FT2R yl + FT2R (BMULT xl yl)) < Omega
  by (eapply Rle_lt_trans; [exact Harg1|]; lra).
have Hftl1 : is_finite (BFMA xh yl (BMULT xl yl)) = true.
{ apply no_overflow_fma_is_finite => //.
  eapply Rle_lt_trans; [apply aux_round_ub|].
  have Hu := aux_ulp_real _ Harg1_lt. lra. }
have Htl1b : Rabs (FT2R (BFMA xh yl (BMULT xl yl))) <= 2 * bpow radix2 (femax t - fprec t).
{ rewrite -BFMA_round_correct; [| exact Hftl1].
  eapply Rle_trans; [apply aux_round_ub|].
  have Hu := aux_ulp_real _ Harg1_lt. lra. }
(* cl2 = BFMA xl yh tl1 : finite, |cl2| <= 3 bpow(femax-fprec) *)
have Harg2 : Rabs (FT2R xl * FT2R yh + FT2R (BFMA xh yl (BMULT xl yl)))
          <= 5/2 * bpow radix2 (femax t - fprec t)
  by (eapply Rle_trans; [apply Rabs_triang|]; lra).
have Harg2_lt : Rabs (FT2R xl * FT2R yh + FT2R (BFMA xh yl (BMULT xl yl))) < Omega
  by (eapply Rle_lt_trans; [exact Harg2|]; lra).
have Hfcl2 : is_finite (BFMA xl yh (BFMA xh yl (BMULT xl yl))) = true.
{ apply no_overflow_fma_is_finite => //.
  eapply Rle_lt_trans; [apply aux_round_ub|].
  have Hu := aux_ulp_real _ Harg2_lt. lra. }
have Hcl2b : Rabs (FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))
          <= 3 * bpow radix2 (femax t - fprec t).
{ rewrite -BFMA_round_correct; [| exact Hfcl2].
  eapply Rle_trans; [apply aux_round_ub|].
  have Hu := aux_ulp_real _ Harg2_lt. lra. }
(* cl3 = BPLUS cl1 cl2 : finite, |cl3| <= 4 bpow(femax-fprec) *)
have Hcl3_arg : Rabs (FT2R (Fast2Mult_err xh yh)
                      + FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))
             <= 7/2 * bpow radix2 (femax t - fprec t)
  by (eapply Rle_trans; [apply Rabs_triang|]; lra).
have Hcl3_arg_lt :
  Rabs (FT2R (Fast2Mult_err xh yh) + FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) < Omega
  by (eapply Rle_lt_trans; [exact Hcl3_arg|]; lra).
have Hfcl3 : is_finite (BPLUS (Fast2Mult_err xh yh)
                              (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) = true.
{ apply (no_overflow_sum_is_finite t _ _ Hfcl1 Hfcl2).
  unfold Bplus_no_overflow.
  eapply Rle_lt_trans; [apply aux_round_ub|].
  have Hu := aux_ulp_real _ Hcl3_arg_lt. lra. }
have Hcl3b : Rabs (FT2R (BPLUS (Fast2Mult_err xh yh)
                               (BFMA xl yh (BFMA xh yl (BMULT xl yl)))))
          <= 4 * bpow radix2 (femax t - fprec t).
{ rewrite -BPLUS_round_correct; [| exact Hfcl3].
  eapply Rle_trans; [apply aux_round_ub|].
  have Hu := aux_ulp_real _ Hcl3_arg_lt. lra. }
(* final: fst (DWTimesDW3) = BPLUS ch cl3, no overflow *)
change (is_finite (BPLUS (Fast2Mult_mul xh yh)
                    (BPLUS (Fast2Mult_err xh yh)
                           (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) = true).
apply (no_overflow_sum_is_finite t _ _ Hfch Hfcl3).
unfold Bplus_no_overflow.
(* fprec >= 4 gives 4*bpow(femax-fprec) = 4*2^-fprec*Omega <= /4*Omega, so with
   ch <= /2*Omega the sum stays <= 3/4*Omega and the closing round is < Omega. *)
have H4 : 4 * bpow radix2 (femax t - fprec t) <= /4 * Omega by (rewrite Hbu; nra).
have Hsum : Rabs (FT2R (Fast2Mult_mul xh yh)
                  + FT2R (BPLUS (Fast2Mult_err xh yh)
                                (BFMA xl yh (BFMA xh yl (BMULT xl yl)))))
         <= 3/4 * Omega.
{ eapply Rle_trans; [apply Rabs_triang|]. lra. }
have Hsum_lt : Rabs (FT2R (Fast2Mult_mul xh yh)
                     + FT2R (BPLUS (Fast2Mult_err xh yh)
                                   (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) < Omega
  by (eapply Rle_lt_trans; [exact Hsum|]; lra).
eapply Rle_lt_trans; [apply aux_round_ub|].
have Hu := aux_ulp_real _ Hsum_lt. lra.
Qed.

(* Finiteness of the snd output from the cond, via the closing Fast2Sum
   ulp-ordering precondition (ch = 0 when xh*yh = 0, else aux_cl3_le_ch). *)
Lemma DWTimesDW3_snd_finite (xh xl yh yl : ftype t) :
  (4 <= fprec t)%Z ->
  DWTimesDW_cond xh xl yh yl ->
  is_finite (snd (DWTimesDW3 xh xl yh yl)) = true.
Proof.
move => Hp4 Hcond.
have Hp3 : (3 <= fprec t)%Z by lia.
have Hfp : is_finite (BPLUS (Fast2Mult_mul xh yh)
                            (BPLUS (Fast2Mult_err xh yh)
                                   (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) = true
  by exact (DWTimesDW3_fst_finite xh xl yh yl Hp4 Hcond).
destruct (BPLUS_finite_e t _ _ Hfp) as [Hfch Hfcl3].
move: Hcond => [Hfxl [Hfyl [Hdwx [Hdwy [Hf2m Hxhy4]]]]].
have Huf := proj2 Hf2m.
have Hfmul : is_finite (BMULT xh yh) = true by exact (proj1 Hf2m).
have Hord : ulp (FT2R (BPLUS (Fast2Mult_err xh yh)
                             (BFMA xl yh (BFMA xh yl (BMULT xl yl)))))
         <= ulp (FT2R (Fast2Mult_mul xh yh))
         \/ FT2R (Fast2Mult_mul xh yh) = 0.
{ destruct Huf as [Hxy0 | Hthresh].
  - right. unfold Fast2Mult_mul, Fast2Mult, fst.
    rewrite -BMULT_round_correct // Hxy0 round_0 //.
  - left. apply Ulp.ulp_le; FLT_basics.
    apply aux_cl3_le_ch;
      [ exact Hp3 | exact Hdwx | exact Hdwy | exact Hfmul | exact Hfcl3 | exact Hthresh ]. }
apply (is_finite_FastSum_ulp (Fast2Mult_mul xh yh)
         (BPLUS (Fast2Mult_err xh yh)
                (BFMA xl yh (BFMA xh yl (BMULT xl yl))))); [exact Hord | exact Hfp].
Qed.

(* The output pair of DWTimesDW3 (Algorithm 12) is itself a double word.  The
   closing step is Fast2Sum ch cl3 (ch = Fast2Mult_mul xh yh,
   cl3 = BPLUS cl1 (BFMA xl yh (BFMA xh yl (BMULT xl yl)))), so the double-word
   property reduces to Fast2Sum_is_DW.  Its two obligations both hold under
   DWTimesDW_cond:
     - is_finite (BPLUS ch cl3)   <- DWTimesDW3_fst_finite;
     - |cl3| <= |ch|              <- aux_cl3_le_ch on the normal leg; on the
       cond's underflow leg (xh*yh = 0) ch = 0 and every cross-product term of
       cl3 vanishes (via the double_word relations), so cl3 = 0 and the ordering
       is 0 <= 0. *)
(* We first prove it from the *basic* precondition — the two Fast2Sum
   obligations on the closing arguments (finiteness of the sum and the
   magnitude ordering |cl3| <= |ch|) — and then show the operation cond
   supplies exactly those two obligations. *)

(* (1) result from the basic precondition (the closing Fast2Sum's own
   requirements): this is Fast2Sum_is_DW at the DWTimesDW3 closing site. *)
Lemma DWTimesDW3_double_word_from_pre (xh xl yh yl : ftype t) :
  is_finite (BPLUS (Fast2Mult_mul xh yh)
                   (BPLUS (Fast2Mult_err xh yh)
                          (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) = true ->
  Rabs (FT2R (BPLUS (Fast2Mult_err xh yh)
                    (BFMA xl yh (BFMA xh yl (BMULT xl yl)))))
    <= Rabs (FT2R (Fast2Mult_mul xh yh)) ->
  double_word (fst (DWTimesDW3 xh xl yh yl)) (snd (DWTimesDW3 xh xl yh yl)).
Proof.
move => Hfp Hord.
exact (Fast2Sum_is_DW (Fast2Mult_mul xh yh)
         (BPLUS (Fast2Mult_err xh yh)
                (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) Hfp Hord).
Qed.

(* (2) the operation cond supplies the basic precondition:
     - finiteness              <- DWTimesDW3_fst_finite;
     - the ordering |cl3|<=|ch| <- aux_cl3_le_ch on the normal leg; on the
       cond's underflow leg (xh*yh = 0) ch = 0 and every cross-product term of
       cl3 vanishes (via the double_word relations), so cl3 = 0. *)
Lemma DWTimesDW3_double_word_pre_of_cond (xh xl yh yl : ftype t) :
  (4 <= fprec t)%Z ->
  DWTimesDW_cond xh xl yh yl ->
  is_finite (BPLUS (Fast2Mult_mul xh yh)
                   (BPLUS (Fast2Mult_err xh yh)
                          (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) = true
  /\ Rabs (FT2R (BPLUS (Fast2Mult_err xh yh)
                       (BFMA xl yh (BFMA xh yl (BMULT xl yl)))))
       <= Rabs (FT2R (Fast2Mult_mul xh yh)).
Proof.
move => Hp4 Hcond.
have Hp3 : (3 <= fprec t)%Z by lia.
have Hfp : is_finite (BPLUS (Fast2Mult_mul xh yh)
                            (BPLUS (Fast2Mult_err xh yh)
                                   (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) = true
  by exact (DWTimesDW3_fst_finite xh xl yh yl Hp4 Hcond).
destruct (BPLUS_finite_e t _ _ Hfp) as [Hfch Hfcl3].
move: Hcond => [Hfxl [Hfyl [Hdwx [Hdwy [Hf2m Hxhy4]]]]].
have Huf := proj2 Hf2m.
have Hfmul : is_finite (BMULT xh yh) = true by exact (proj1 Hf2m).
split; [ exact Hfp | ].
destruct Huf as [Hxy0 | Hthresh].
- (* underflow leg: ch = 0 and cl3 = 0 *)
  have Hch0 : FT2R (Fast2Mult_mul xh yh) = 0.
  { unfold Fast2Mult_mul, Fast2Mult, fst.
    rewrite -BMULT_round_correct // Hxy0 round_0 //. }
  have Huf' : FT2R xh * FT2R yh <> 0 ->
    bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh)
    by (move => Hne; exfalso; exact (Hne Hxy0)).
  have Herr0 : FT2R (Fast2Mult_err xh yh) = 0.
  { have Heq := Fast2MultModel_correct xh yh Hfmul Huf'.
    rewrite Heq Hxy0 Hch0; ring. }
  (* all three cross products vanish in the underflow leg *)
  have Hzeros : FT2R xl * FT2R yl = 0 /\ FT2R xh * FT2R yl = 0
             /\ FT2R xl * FT2R yh = 0.
  { destruct (Rmult_integral _ _ Hxy0) as [Hxh0 | Hyh0].
    - have Hxl0 : FT2R xl = 0 by exact (double_word_0 xh xl Hdwx Hxh0).
      repeat split; rewrite ?Hxl0 ?Hxh0; ring.
    - have Hyl0 : FT2R yl = 0 by exact (double_word_0 yh yl Hdwy Hyh0).
      repeat split; rewrite ?Hyl0 ?Hyh0; ring. }
  destruct Hzeros as [Hxlyl0 [Hxhyl0 Hxlyh0]].
  (* finiteness of the nested product/accumulation nodes *)
  destruct (BPLUS_finite_e t (Fast2Mult_err xh yh)
              (BFMA xl yh (BFMA xh yl (BMULT xl yl))) Hfcl3) as [Hferr Hfcl2].
  destruct (BFMA_finite_e t xl yh (BFMA xh yl (BMULT xl yl)) Hfcl2)
    as [_ [_ Hftl1]].
  destruct (BFMA_finite_e t xh yl (BMULT xl yl) Hftl1) as [_ [_ Hftl0]].
  have Htl0_0 : FT2R (BMULT xl yl) = 0
    by (rewrite -(BMULT_round_correct t xl yl Hftl0) Hxlyl0 round_0 //).
  have Htl1_0 : FT2R (BFMA xh yl (BMULT xl yl)) = 0
    by (rewrite -(BFMA_round_correct t xh yl (BMULT xl yl) Hftl1)
                Hxhyl0 Htl0_0 Rplus_0_r round_0 //).
  have Hcl2_0 : FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))) = 0
    by (rewrite -(BFMA_round_correct t xl yh (BFMA xh yl (BMULT xl yl)) Hfcl2)
                Hxlyh0 Htl1_0 Rplus_0_r round_0 //).
  have Hcl3_0 : FT2R (BPLUS (Fast2Mult_err xh yh)
                           (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) = 0
    by (rewrite -(BPLUS_round_correct t (Fast2Mult_err xh yh)
                    (BFMA xl yh (BFMA xh yl (BMULT xl yl))) Hfcl3)
                Herr0 Hcl2_0 Rplus_0_r round_0 //).
  rewrite Hch0 Hcl3_0 Rabs_R0; apply Rle_refl.
- (* normal leg: the closing-Fast2Sum ordering already proven for accuracy *)
  apply aux_cl3_le_ch;
    [ exact Hp3 | exact Hdwx | exact Hdwy | exact Hfmul | exact Hfcl3
    | exact Hthresh ].
Qed.

(* (3) cond-level corollary used by the VST guarded spec. *)
Lemma DWTimesDW3_double_word (xh xl yh yl : ftype t) :
  (4 <= fprec t)%Z ->
  DWTimesDW_cond xh xl yh yl ->
  double_word (fst (DWTimesDW3 xh xl yh yl)) (snd (DWTimesDW3 xh xl yh yl)).
Proof.
move => Hp4 Hcond.
have [Hfp Hord] := DWTimesDW3_double_word_pre_of_cond xh xl yh yl Hp4 Hcond.
exact (DWTimesDW3_double_word_from_pre xh xl yh yl Hfp Hord).
Qed.

End DWTimesDW_Finite.


(* ============================================================
   Section 5: Layer-1 / Layer-2 accuracy for DWTimesDW3 (Algorithm 12).

   The Layer-1 theorem DWTimesDW_relerr_bound is to be proved by:
     - the underflow leg (xh*yh = 0): the exact product xr*yr is 0, so
       relerr = 0 (relerr_0_of_xryr0 + xryr0_of_prod0);
     - the normal leg: the FLX->FLT bridge DWTimesDW3_FLX_FLT(_weak) lifts the
       paper's tight FLX bound DWTimesDW.DWTimesDW12_correct (< 4*(u*u)) to the
       FLT conclusion.
   The corollary DWTimesDW_accuracy_from_cond is the Layer-2 interface used by
   the VST guarded wrapper spec (verif_proofs/verif_dw_mult_dw.v).
   ============================================================ *)
Section DWTimesDW_Accuracy.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation u      := (bpow Zaux.radix2 (- fprec t)).
Notation fexp   := (SpecFloat.fexp (fprec t) (femax t)).
Notation eminA  := (SpecFloat.emin (fprec t) (femax t)).
Notation ulp    := (Ulp.ulp Zaux.radix2 fexp).
Notation OmegaA := (bpow Zaux.radix2 (femax t)).

Local Instance valid_fexp_inst_acc : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.

Variables (xh xl yh yl : ftype t).

Let zh := FT2R (fst (DWTimesDW3 xh xl yh yl)).
Let zl := FT2R (snd (DWTimesDW3 xh xl yh yl)).
Let xr := (FT2R xh + FT2R xl).
Let yr := (FT2R yh + FT2R yl).

Definition relative_error_DWTimesDW : R :=
  Rabs (((zh + zl) - xr * yr) / (xr * yr)).

(* When the exact product xr*yr is 0 the relative error is 0 (Coq's _/0 = 0). *)
Lemma relerr_0_of_xryr0 : xr * yr = 0 -> relative_error_DWTimesDW = 0.
Proof.
move => H. unfold relative_error_DWTimesDW. rewrite H.
rewrite /Rdiv Rinv_0 Rmult_0_r Rabs_R0 //.
Qed.

(* xh*yh = 0 forces xr*yr = 0: FT2R xh = 0 -> FT2R xl = 0 (double_word), and
   symmetrically for yh, yl. *)
Lemma xryr0_of_prod0 :
  double_word_prop xh xl ->
  double_word_prop yh yl ->
  FT2R xh * FT2R yh = 0 -> xr * yr = 0.
Proof.
move => Hdwx Hdwy Hxy0.
destruct (Rmult_integral _ _ Hxy0) as [Hxh0 | Hyh0].
- have Hr : rounded t (FT2R xl) = FT2R xl
    by (unfold rounded; apply round_generic;
        [ apply valid_rnd_N | apply generic_format_FLT_FT2R ]).
  have Hxl0 : FT2R xl = 0.
  { move: Hdwx; rewrite /double_word_prop Hxh0 Rplus_0_l Hr.
    move => H; exact (eq_sym H). }
  unfold xr, yr. rewrite Hxh0 Hxl0. ring.
- have Hr : rounded t (FT2R yl) = FT2R yl
    by (unfold rounded; apply round_generic;
        [ apply valid_rnd_N | apply generic_format_FLT_FT2R ]).
  have Hyl0 : FT2R yl = 0.
  { move: Hdwy; rewrite /double_word_prop Hyh0 Rplus_0_l Hr.
    move => H; exact (eq_sym H). }
  unfold xr, yr. rewrite Hyh0 Hyl0. ring.
Qed.

(* KEYSTONE (DW analog of FP relerr_error_eq): the whole double-word error is the
   sum of the four FLT rounding errors e0..e3.  Fast2Sum is exact (aux_cl3_le_ch),
   the product error cl1 is representable (Fast2MultModel_correct), and each
   intermediate is round(arg); the identity then telescopes by [ring].  Mirrors
   paper DWTimesDW.v:4960-4968. *)
Lemma relerr_error_eq :
  (3 <= fprec t)%Z ->
  double_word_prop xh xl ->
  double_word_prop yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  is_finite (BMULT xh yh) = true ->
  bpow radix2 (eminA + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh) ->
  (zh + zl - xr * yr)%R
  = ((FT2R (BMULT xl yl) - FT2R xl * FT2R yl)
     + (FT2R (BFMA xh yl (BMULT xl yl))
        - (FT2R xh * FT2R yl + FT2R (BMULT xl yl)))
     + (FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))
        - (FT2R xl * FT2R yh + FT2R (BFMA xh yl (BMULT xl yl))))
     + (FT2R (BPLUS (Fast2Mult_err xh yh)
                    (BFMA xl yh (BFMA xh yl (BMULT xl yl))))
        - (FT2R (Fast2Mult_err xh yh)
           + FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))))%R.
Proof.
move => Hp3 Hdwx Hdwy Hfp Hfmul Hbig.
set ch  := Fast2Mult_mul xh yh.
set cl2 := BFMA xl yh (BFMA xh yl (BMULT xl yl)).
set cl3 := BPLUS (Fast2Mult_err xh yh) cl2.
have Hfst : is_finite (BPLUS ch cl3) = true by exact (proj1 Hfp).
have Hfcl3 : is_finite cl3 = true
  by (destruct (BPLUS_finite_e t ch cl3 Hfst) as [_ Hf]; exact Hf).
have Hord : Rabs (FT2R cl3) <= Rabs (FT2R ch)
  by exact (aux_cl3_le_ch xh xl yh yl Hp3 Hdwx Hdwy Hfmul Hfcl3 Hbig).
have Hexact : FT2R (Fast2Sum_err ch cl3)
            = FT2R ch + FT2R cl3 - FT2R (Fast2Sum_sum ch cl3)
  by exact (FastTwoSum_correct ch cl3 Hfst Hord).
have Huf' : FT2R xh * FT2R yh <> 0 ->
  bpow radix2 (eminA + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh)
  by (move => _; exact Hbig).
have Hch_eq : FT2R ch = FT2R xh * FT2R yh - FT2R (Fast2Mult_err xh yh).
{ have H := Fast2MultModel_correct xh yh Hfmul Huf'. rewrite -/ch in H. lra. }
have Hsum : (zh + zl)%R = (FT2R ch + FT2R cl3)%R.
{ unfold zh, zl.
  have Hfst_eq : fst (DWTimesDW3 xh xl yh yl) = Fast2Sum_sum ch cl3 by reflexivity.
  have Hsnd_eq : snd (DWTimesDW3 xh xl yh yl) = Fast2Sum_err ch cl3 by reflexivity.
  rewrite Hfst_eq Hsnd_eq Hexact. ring. }
rewrite Hsum Hch_eq. unfold xr, yr, cl3, cl2. ring.
Qed.

(* Load-bearing Layer-1 theorem.  Carries the underflow disjunction (same shape
   as DWTimesDW_cond's) and dispatches on it.  Bound is 4*u^2 (the paper proves
   the strict < 4*(u*u); we state the non-strict form here). *)
Theorem DWTimesDW_relerr_bound :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  (FT2R xh * FT2R yh = 0 \/
   bpow Zaux.radix2 (SpecFloat.emin (fprec t) (femax t) + 2 * fprec t - 1)
   <= Rabs (FT2R xh * FT2R yh)) ->
  relative_error_DWTimesDW <= 8 * u ^ 2.
Proof.
intros Hdw Hdwy Hfin Hp5 Huf.
have Hp3 : (3 <= fprec t)%Z by lia.
have Hdwp : double_word_prop xh xl := Hdw.
have Hdwyp : double_word_prop yh yl := Hdwy.
destruct Huf as [Hxy0 | Hbig].
- (* zero product: relerr = 0 *)
  rewrite (relerr_0_of_xryr0 (xryr0_of_prod0 Hdwp Hdwyp Hxy0)).
  apply Rmult_le_pos; [lra | apply pow_le; apply bpow_ge_0].
- (* nonzero leg: uniform direct bound *)
  have Hfmul : is_finite (BMULT xh yh) = true by exact (FINmul xh xl yh yl Hfin).
  have Hftl0 : is_finite (BMULT xl yl) = true by exact (FINtl0 xh xl yh yl Hfin).
  have Hftl1 : is_finite (BFMA xh yl (BMULT xl yl)) = true
    by exact (FINtl1 xh xl yh yl Hfin).
  have Hfcl2 : is_finite (BFMA xl yh (BFMA xh yl (BMULT xl yl))) = true
    by exact (FINcl2 xh xl yh yl Hfin).
  have Hfcl3 : is_finite (BPLUS (Fast2Mult_err xh yh)
                                (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) = true
    by exact (FINcl3 xh xl yh yl Hfin).
  have Herr := relerr_error_eq Hp3 Hdwp Hdwyp Hfin Hfmul Hbig.
  have Heta := aux_eta_bnd xh xl yh yl Hp5 Hdwp Hdwyp Hfmul Hftl0 Hftl1 Hfcl2 Hfcl3 Hbig.
  have HPpos : 0 < Rabs (FT2R xh * FT2R yh)
    by (eapply Rlt_le_trans; [apply bpow_gt_0 | exact Hbig]).
  have Hu0 : 0 < bpow radix2 (- fprec t) by apply bpow_gt_0.
  have Hule : bpow radix2 (- fprec t) <= /8.
  { have -> : (/8 = bpow radix2 (-3))%R by (simpl; lra). apply bpow_le; lia. }
  have Hxl : Rabs (FT2R xl) <= bpow radix2 (- fprec t) * Rabs (FT2R xh)
    by (apply aux_dwu_rel; exact Hdwp).
  have Hyl : Rabs (FT2R yl) <= bpow radix2 (- fprec t) * Rabs (FT2R yh)
    by (apply aux_dwu_rel; exact Hdwyp).
  (* |xr| >= (1-u)|xh|, |yr| >= (1-u)|yh| *)
  have Hxr : (1 - bpow radix2 (- fprec t)) * Rabs (FT2R xh) <= Rabs xr.
  { have Ht := Rabs_triang_inv (FT2R xh) (- FT2R xl).
    rewrite Rabs_Ropp in Ht.
    have He : (FT2R xh - - FT2R xl = FT2R xh + FT2R xl)%R by ring.
    rewrite He in Ht. unfold xr.
    eapply Rle_trans; [| exact Ht].
    have Hexp : ((1 - bpow radix2 (- fprec t)) * Rabs (FT2R xh)
              = Rabs (FT2R xh) - bpow radix2 (- fprec t) * Rabs (FT2R xh))%R by ring.
    rewrite Hexp. apply Rplus_le_compat_l, Ropp_le_contravar. exact Hxl. }
  have Hyr : (1 - bpow radix2 (- fprec t)) * Rabs (FT2R yh) <= Rabs yr.
  { have Ht := Rabs_triang_inv (FT2R yh) (- FT2R yl).
    rewrite Rabs_Ropp in Ht.
    have He : (FT2R yh - - FT2R yl = FT2R yh + FT2R yl)%R by ring.
    rewrite He in Ht. unfold yr.
    eapply Rle_trans; [| exact Ht].
    have Hexp : ((1 - bpow radix2 (- fprec t)) * Rabs (FT2R yh)
              = Rabs (FT2R yh) - bpow radix2 (- fprec t) * Rabs (FT2R yh))%R by ring.
    rewrite Hexp. apply Rplus_le_compat_l, Ropp_le_contravar. exact Hyl. }
  have H1u0 : 0 <= 1 - bpow radix2 (- fprec t) by lra.
  have Hxhp : 0 <= Rabs (FT2R xh) by apply Rabs_pos.
  have Hyhp : 0 <= Rabs (FT2R yh) by apply Rabs_pos.
  have Hden : (1 - bpow radix2 (- fprec t)) ^ 2 * Rabs (FT2R xh * FT2R yh)
           <= Rabs (xr * yr).
  { rewrite (Rabs_mult xr yr) (Rabs_mult (FT2R xh) (FT2R yh)).
    eapply Rle_trans; [| apply Rmult_le_compat;
        [ apply Rmult_le_pos; [exact H1u0 | exact Hxhp]
        | apply Rmult_le_pos; [exact H1u0 | exact Hyhp]
        | exact Hxr | exact Hyr ]].
    apply Req_le; ring. }
  have Hdenpos : 0 < Rabs (xr * yr).
  { eapply Rlt_le_trans; [| exact Hden].
    apply Rmult_lt_0_compat; [nra | exact HPpos]. }
  have Hxryrne : xr * yr <> 0.
  { intro H0. rewrite H0 Rabs_R0 in Hdenpos. lra. }
  unfold relative_error_DWTimesDW. rewrite Herr /Rdiv Rabs_mult Rabs_inv.
  apply (Rle_trans _ ((15/2 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t))
                          * Rabs (FT2R xh * FT2R yh)) * / Rabs (xr * yr))).
  { apply Rmult_le_compat_r;
      [ apply Rlt_le, Rinv_0_lt_compat; exact Hdenpos | exact Heta ]. }
  apply (Rmult_le_reg_r (Rabs (xr * yr))); [exact Hdenpos|].
  rewrite Rmult_assoc Rinv_l; [| apply Rgt_not_eq; exact Hdenpos].
  rewrite Rmult_1_r.
  eapply Rle_trans;
    [| apply Rmult_le_compat_l;
       [ apply Rmult_le_pos; [lra | apply pow_le; apply bpow_ge_0] | exact Hden ]].
  have Hu2 : bpow radix2 (- fprec t) ^ 2
           = bpow radix2 (- fprec t) * bpow radix2 (- fprec t) by (simpl; ring).
  rewrite Hu2.
  have Hu32 : bpow radix2 (- fprec t) <= /32.
  { have -> : (/32 = bpow radix2 (-5))%R by (simpl; lra). apply bpow_le; lia. }
  have Hfac : 15/2 <= 8 * (1 - bpow radix2 (- fprec t)) ^ 2.
  { have H1 := Hu32. nra. }
  have HuuP : 0 <= bpow radix2 (- fprec t) * bpow radix2 (- fprec t)
                  * Rabs (FT2R xh * FT2R yh).
  { apply Rmult_le_pos; [ apply Rmult_le_pos; apply Rlt_le; exact Hu0 | apply Rabs_pos ]. }
  nra.
Qed.

(* Layer-2 corollary: a thin wrapper over DWTimesDW_relerr_bound.  Pulls the
   Layer-1 hypotheses out of DWTimesDW_cond (verified at the spec interface):
     - double_word          <- the cond's double_word_prop (convertible);
     - is_finite_p          <- DWTimesDW3_fst_finite / DWTimesDW3_snd_finite;
     - the underflow disjunction is passed through verbatim.
   The 5 <= fprec t hypothesis is threaded by the caller (true for Tdouble). *)
Corollary DWTimesDW_accuracy_from_cond :
  (5 <= fprec t)%Z ->
  DWTimesDW_cond xh xl yh yl ->
  relative_error_DWTimesDW <= 8 * u ^ 2.
Proof.
intros Hp5 Hcond.
have Hp3 : (3 <= fprec t)%Z by lia.
have Hp4 : (4 <= fprec t)%Z by lia.
have Hfp : is_finite_p (DWTimesDW3 xh xl yh yl).
{ split; [ exact (DWTimesDW3_fst_finite xh xl yh yl Hp4 Hcond)
         | exact (DWTimesDW3_snd_finite xh xl yh yl Hp4 Hcond) ]. }
move: Hcond => [Hfxl [Hfyl [Hdwx [Hdwy [Hf2m Hxhy4]]]]].
have Huf := proj2 Hf2m.
exact (DWTimesDW_relerr_bound Hdwx Hdwy Hfp Hp5 Huf).
Qed.

(* Tight normal-regime accuracy (the paper's constant).  Under the
   per-intermediate normality hypotheses (Nprod, N0..N3, exactly those of the
   bridge DWTimesDW3_FLX_FLT), the FLX->FLT bridge lifts the paper's tight FLX
   bound DWTimesDW.DWTimesDW12_correct (< 4*(u*u)) to the FLT result, recovering
   4*u^2 where the direct 32*u^2 bound above is loose. *)
Theorem DWTimesDW_relerr_normal :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  bpow radix2 (eminA + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh) ->
  bpow radix2 (eminA + fprec t - 1) <= Rabs (FT2R xl * FT2R yl) ->
  bpow radix2 (eminA + fprec t - 1)
    <= Rabs (FT2R xh * FT2R yl + FT2R (BMULT xl yl)) ->
  bpow radix2 (eminA + fprec t - 1)
    <= Rabs (FT2R (BFMA xh yl (BMULT xl yl)) + FT2R xl * FT2R yh) ->
  bpow radix2 (eminA + fprec t - 1)
    <= Rabs (FT2R (Fast2Mult_err xh yh)
             + FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) ->
  relative_error_DWTimesDW <= 4 * u ^ 2.
Proof.
move => Hdw Hdwy Hfin Hp5 Nprod N0 N1 N2 N3.
(* the FLX->FLT bridge: DWTimesDW12 (FLX) = F2Rp (DWTimesDW3) (FLT) *)
have Hbridge := DWTimesDW3_FLX_FLT xh xl yh yl Hfin Nprod N0 N1 N2 N3.
(* lift both DW inputs to the paper's DWPlus.double_word predicate *)
have HDWx : DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl)
  by (apply (dw_word_DWdouble xh xl xh); exact Hdw).
have HDWy : DWPlus.double_word (fprec t) choice (FT2R yh) (FT2R yl)
  by (apply (dw_word_DWdouble yh yl yh); exact Hdwy).
(* the paper's tight FLX bound (< 4*(u*u)) specialized to our inputs.  The
   explicit type annotation keeps DWTimesDW12 FOLDED (Coq would otherwise unfold
   it through Fast2Sum to a pair, breaking the [rewrite Hbridge] below) -- the
   same idiom as DWMulFP_acc.v's normal-leg use of DWTimesFP9_correct. *)
have Hpaper :
  (let (zh, zl) := DWTimesDW.DWTimesDW12 (fprec t) choice
                     (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl) in
   let xy := (FT2R xh + FT2R xl) * (FT2R yh + FT2R yl) in
   Rabs ((zh + zl - xy) / xy)
     < 4 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t)))
  := @DWTimesDW.DWTimesDW12_correct (fprec t) (fprec_gt_one t) choice choiceP Hp5
       (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl) HDWx HDWy.
(* rewrite the bridge into the (still-folded) FLX result, reduce F2Rp to the
   literal FLT pair, and read off the bound *)
rewrite Hbridge /F2Rp /= in Hpaper.
unfold relative_error_DWTimesDW, zh, zl, xr, yr.
have Hu2 : (4 * bpow radix2 (- fprec t) ^ 2
          = 4 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t)))%R by (simpl; ring).
rewrite Hu2.
apply Rlt_le. exact Hpaper.
Qed.

End DWTimesDW_Accuracy.
