(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Accuracy and representation results for [DWTimesFP3] (Algorithm 9).

    Public results:
    - [DWTimesFP_relative_accuracy]: the pure [2u^2] relative bound under
      [DWTimesFP_relative_error_input_cond];
    - [DWTimesFP_mixed_guarantee_from_cond]: the whole-range
      [2u^2|P| + 2.51 eta] bound and output closure under
      [DWTimesFP_mixed_cond];
    - [DWTimesFP_mixed_guarantee_from_safe_input_cond]: the same bundle after
      an input-only sufficient condition establishes result finiteness.

    The proof has three parts: a minimal FLX/FLT model bridge, finiteness from
    overflow headroom, and separate relative and whole-range analyses. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common FLT_helpers.
Require Import DWTimesFP DDConds DWord_defs Fast2Mult_acc TwoSum_acc Fast2Sum_acc.
Require Import DW_acc_lemmas.
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


Section DWTimesFP_ResultFacts.
  Context {NANS: Nans} {t : type} {STD: is_standard t}.

  Variables (xh xl y : ftype t).

  Hypothesis FIN : is_finite_p (DWTimesFP3 xh xl y). 

  Ltac prove_finite := 
    move: FIN;
    rewrite /DWTimesFP3/is_finite_p //=;
    move => [] //=;
    subexpr_finite => //
  .

  Fact DWTimesFP3_mul_finite : is_finite (BMULT xh y) = true.
  Proof. prove_finite. Qed.

  Fact DWTimesFP3_xh_finite : is_finite xh = true.
  Proof. prove_finite. Qed.

  Fact DWTimesFP3_fast2mult_finite : is_finite_p (Fast2Mult xh y).
  Proof. prove_finite. Qed.

  Let cl1 := snd (Fast2Mult xh y).

  Fact DWTimesFP3_correction_finite : is_finite (BFMA xl y cl1) = true.
  Proof. prove_finite. Qed.

  Fact DWTimesFP3_xl_finite : is_finite xl = true.
  Proof. prove_finite. Qed.

End DWTimesFP_ResultFacts.

(* The paper's FLX TwoProd agrees with the runtime FLT Fast2Mult at the
   exact-reconstruction threshold [emin + 2p - 1]. *)
Section Fast2Mult_FLX_Bridge.
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

End Fast2Mult_FLX_Bridge.

(* FLX/FLT bridge for DWTimesFP3 under the minimal thresholds needed for the
   algorithm to agree with its FLX model:
     - product threshold emin + 2*fprec - 1   (vs. emin + 3*fprec there), and
     - the low FMA argument  w = xl*y + cl1  is itself normal:
       bpow(emin+fprec-1) <= |w|              (vs. the Hyp2 form there).
   With these, every rounding inside DWTimesFP3 agrees with its FLX counterpart
   (round_FLT_FLX), so the whole computation matches DWTimesFP9.  This is the
   bridge that survives in the [emin+2*fprec-1, emin+3*fprec) product band. *)
Section DWTimesFP_FLX_Bridge.

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
have Ffast : is_finite_p (Fast2Mult xh y) by
  apply: (DWTimesFP3_fast2mult_finite _ xl _) => //.
have Fcorr : is_finite (BFMA xl y (snd (Fast2Mult xh y))) = true by
  apply: DWTimesFP3_correction_finite => //.
move: Fcorr.
rewrite /Fast2Mult/fst/snd. move => Fcorr.
have Fmul : is_finite (BMULT xh y) = true by
  apply: (DWTimesFP3_mul_finite _ _ _ FIN) => //.
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
  - rewrite (Fast2MultModel_correct xh y Fmul Huf2).
    rewrite -BOPP_binary; [reflexivity | right; exact Fmul]. }
rewrite Herr; exact Hw.
exact (proj2 Ffast).
exact (proj2 Ffast).
exact FIN.
Qed.

End DWTimesFP_FLX_Bridge.


(* ============================================================
   Finiteness of fst (DWTimesFP3 xh xl y) from DWTimesFP_relative_error_input_cond.
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

(* Rounding preserves the representable product headroom bound. *)
Local Lemma aux_round_prod_bnd (a b : ftype t) :
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
Local Lemma aux_xly_bnd (xh xl y : ftype t) :
  double_word_prop xh xl ->
  Rabs (FT2R xh * FT2R y) <= /2 * Omega ->
  Rabs (FT2R y) <= Omega ->
  Rabs (FT2R xl * FT2R y) <= /2 * bpow radix2 (femax t - fprec t).
Proof.
move => Hdw Hxhy Hy.
have HΩ  : 0 < Omega by apply bpow_gt_0.
have HE0 : 0 <= bpow radix2 (femax t - fprec t) by apply bpow_ge_0.
have Hdwu := dw_low_le_half_ulp xh xl Hdw.
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

(* Product headroom and the input double-word relation keep every intermediate
   finite; no underflow premise is required. *)
Local Lemma DWTimesFP3_finite_from_safe_input_cond (xh xl y : ftype t) :
  DWTimesFP_mixed_safe_input_cond xh xl y ->
  is_finite_p (DWTimesFP3 xh xl y).
Proof.
intros (Hfxl & Hdwp & Hfmul & Hreal).
unfold Fast2Mult_acc_only_cond in Hfmul.
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

(* Magnitude ordering |cl3| <= |ch| for the closing Fast2Sum, in the normal
   product regime |xh*y| >= bpow(emin+2p-1) supplied by the cond's underflow
   disjunction.  This is the FLT counterpart of the paper's F2Sum_correct_abs
   precondition inside DWTimesFP9_correct. *)
Local Lemma aux_cl3_le_ch (xh xl y : ftype t) :
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
  have Hrel := @dw_low_le_u_high t STD xh xl Hdw.
  rewrite -Rmult_assoc.
  apply Rmult_le_compat_r; [apply Rabs_pos | exact Hrel]. }
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

(** Closing Fast2Sum obligations imply output double-word closure. *)
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

End DWTimesFP_Finite.

(** Relative accuracy.  The proof collapses the double-word error to the
    rounding error of the correction term.  It then treats normal and
    subnormal corrections separately. *)

Section DWTimesFP_Accuracy.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation u     := (bpow Zaux.radix2 (- fprec t)).
Notation fexp  := (SpecFloat.fexp (fprec t) (femax t)).
Notation eminA := (SpecFloat.emin (fprec t) (femax t)).
Notation ulp   := (Ulp.ulp Zaux.radix2 fexp).

(* Valid_exp for SpecFloat.fexp, so Flocq's ulp/round lemmas discharge it. *)
Local Instance valid_fexp_inst_acc : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.

Variables (xh xl y : ftype t).

Let zh := FT2R (fst (DWTimesFP3 xh xl y)).
Let zl := FT2R (snd (DWTimesFP3 xh xl y)).
Let xr := (FT2R xh + FT2R xl).
Let yr := FT2R y.

Definition relative_error_DWTimesFP : R :=
  Rabs (((zh + zl) - xr * yr) / (xr * yr)).

(* Underflow regime, straightforward part: when the exact product xr*yr is 0
   the relative error is 0 (Coq's _/0 = 0).  This is exactly the cond's
   xh*y = 0 disjunct, since FT2R xh = 0 forces FT2R xl = 0 (double_word). *)
Local Lemma relerr_0_of_xryr0 : xr * yr = 0 -> relative_error_DWTimesFP = 0.
Proof.
move => H. unfold relative_error_DWTimesFP. rewrite H.
rewrite /Rdiv Rinv_0 Rmult_0_r Rabs_R0 //.
Qed.

Local Lemma xryr0_of_prod0 :
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
Local Lemma xryr_ne_0_of_big :
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
Local Lemma relerr_error_eq :
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

(* The local core carries the underflow disjunction and dispatches on it:
     - underflow leg (xh*y = 0): the exact product xr*yr is 0, so relerr = 0
       (PROVEN here via relerr_0_of_xryr0 + xryr0_of_prod0);
     - normal leg (|xh*y| >= bpow(emin+2*fprec-1)): the bridge from
       DWTimesFP9_correct via DWTimesFP3_FLX_FLT, with the FMA-underflow /
       [emin+2p-1, emin+3p) gap sub-case via a direct |abs err|/|xr*yr| bound. *)
Local Lemma DWTimesFP_relative_accuracy_core :
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
  have Hfmul : is_finite (BMULT xh y) = true
    by exact (DWTimesFP3_mul_finite xh xl y Hfin).
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
      apply Rmult_le_compat_r;
        [apply Rabs_pos | exact (@dw_low_le_u_high t STD xh xl Hdw)]. }
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

(* The cond forbids the nonzero underflow gap.  This is literally the
   third field of DWTimesFP_relative_error_input_cond (DDConds.v), projecting the underflow
   disjunct of Fast2Mult_exact_cond: under the cond the leading product is
   either exactly zero or at least the TwoProd exactness threshold, which is
   precisely why the theorem below has no physical-floor term. *)
Local Lemma DWTimesFP_cond_no_gap :
  DWTimesFP_relative_error_input_cond xh xl y ->
  FT2R xh * FT2R y = 0 \/
  bpow Zaux.radix2 (eminA + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R y).
Proof. move => [_ [_ [Hf2m _]]]; exact (proj2 Hf2m). Qed.

(** Pure relative error bound.  The input condition excludes the nonzero
    underflow gap, while its safe-input consequence establishes finiteness. *)
Theorem DWTimesFP_relative_accuracy :
  (3 <= fprec t)%Z ->
  DWTimesFP_relative_error_input_cond xh xl y ->
  relative_error_DWTimesFP <= 2 * u ^ 2.
Proof.
intros Hp3 Hcond.
have Hsafe :=
  DWTimesFP_mixed_safe_input_cond_of_relative_error_input_cond
    xh xl y Hcond.
have Hfp := DWTimesFP3_finite_from_safe_input_cond xh xl y Hsafe.
have Hnogap := DWTimesFP_cond_no_gap Hcond.
move: Hcond => [Hfxl [Hdwp [Hf2m Hreal]]].
exact (DWTimesFP_relative_accuracy_core Hdwp Hfp Hp3 Hnogap).
Qed.

End DWTimesFP_Accuracy.

(** Whole-range mixed accuracy.  Below the TwoProd exactness threshold
    [2^(emin+2p-1)], the product residual need not be representable; the
    absolute [eta] term accounts for that underflow regime. *)

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
Local Lemma DWTimesFP3_double_word_of_sum {NANS : Nans} {t : type}
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
Local Lemma DWTimesFP_core_error_floor_gap {NANS : Nans} {t : type}
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
have Ffast := DWTimesFP3_fast2mult_finite ah al b FIN.
have Fch : is_finite ch=true by exact (proj1 Ffast).
have Fcl1 : is_finite cl1=true by exact (proj2 Ffast).
have Fcl3 := DWTimesFP3_correction_finite ah al b FIN; fold cl1 cl3 in Fcl3.
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
have Hal := @dw_low_le_u_high t STD ah al DWa.
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
Local Lemma DWTimesFP3_error_floor_gap {NANS : Nans} {t : type}
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
have Ffast := DWTimesFP3_fast2mult_finite ah al b FIN.
have Fch : is_finite ch=true by exact (proj1 Ffast).
have Fcl1 : is_finite cl1=true by exact (proj2 Ffast).
have Fcl3 := DWTimesFP3_correction_finite ah al b FIN; fold cl1 cl3 in Fcl3.
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
have Hal := @dw_low_le_u_high t STD ah al DWa.
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
   physical-floor contribution: this is the local relative-accuracy core
   cleared of its division by the exact product. *)
Local Lemma DWTimesFP3_error_normal_arm {NANS : Nans} {t : type}
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
have Hrel := DWTimesFP_relative_accuracy_core ah al b DWa FIN Hp3 (or_intror Hbig).
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

(* The public whole-range result bundles the conventional mixed bound with
   output closure.  The single local core below performs the only normal/gap
   split used to establish that bundle. *)
Definition DWTimesFP_mixed_guarantee {NANS : Nans} {t : type}
    {STD : is_standard t} (xh xl y : ftype t) : Prop :=
  let '(zh, zl) := DWTimesFP3 xh xl y in
  Rabs
    (FT2R zh + FT2R zl - (FT2R xh + FT2R xl) * FT2R y)
    <= 2 * bpow Zaux.radix2 (- fprec t) ^ 2 *
         Rabs ((FT2R xh + FT2R xl) * FT2R y) +
       251 / 100 * bpow Zaux.radix2 (@common.emin t) /\
  double_word_prop zh zl.

Local Lemma DWTimesFP_mixed_guarantee_core {NANS : Nans} {t : type}
    {STD : is_standard t} (xh xl y : ftype t) :
  (3 <= fprec t)%Z ->
  double_word_prop xh xl ->
  is_finite_p (DWTimesFP3 xh xl y) ->
  DWTimesFP_mixed_guarantee xh xl y.
Proof.
move => Hp3 DWa FIN.
destruct (Rle_dec
  (bpow radix2 (@common.emin t + 2*fprec t - 1))
  (Rabs (FT2R xh * FT2R y))) as [Hbig | Hgap].
- have Hnormal := DWTimesFP3_error_normal_arm xh xl y Hp3 DWa FIN Hbig.
  have Heta : 0 <= 251/100*bpow radix2 (@common.emin t).
  { have := bpow_ge_0 radix2 (@common.emin t). nra. }
  have Hacc :
    Rabs ((FT2R (fst (DWTimesFP3 xh xl y)) +
           FT2R (snd (DWTimesFP3 xh xl y))) -
          (FT2R xh + FT2R xl) * FT2R y)
    <= 2*bpow radix2 (-fprec t)^2 *
         Rabs ((FT2R xh + FT2R xl) * FT2R y) +
       251/100*bpow radix2 (@common.emin t) by lra.
  have Fmul := DWTimesFP3_mul_finite xh xl y FIN.
  have Fcl3 := DWTimesFP3_correction_finite xh xl y FIN.
  have Hord := aux_cl3_le_ch xh xl y DWa Fmul Fcl3 Hbig.
  have Hdw : double_word_prop (fst (DWTimesFP3 xh xl y))
      (snd (DWTimesFP3 xh xl y))
    by exact (DWTimesFP3_double_word_from_pre
      xh xl y (proj1 FIN) Hord).
  unfold DWTimesFP_mixed_guarantee.
  revert Hacc Hdw.
  destruct (DWTimesFP3 xh xl y) as [zh zl].
  cbn [fst snd]. intros Hacc Hdw. exact (conj Hacc Hdw).
- have [Hfloor Hdw] := DWTimesFP3_error_floor_gap
    xh xl y Hp3 DWa FIN Hgap.
  have Hu2 : 0 <= 2*bpow radix2 (-fprec t)^2 *
      Rabs ((FT2R xh + FT2R xl) * FT2R y).
  { have := bpow_ge_0 radix2 (-fprec t).
    have := Rabs_pos ((FT2R xh + FT2R xl) * FT2R y). nra. }
  have Hacc :
    Rabs ((FT2R (fst (DWTimesFP3 xh xl y)) +
           FT2R (snd (DWTimesFP3 xh xl y))) -
          (FT2R xh + FT2R xl) * FT2R y)
    <= 2*bpow radix2 (-fprec t)^2 *
         Rabs ((FT2R xh + FT2R xl) * FT2R y) +
       251/100*bpow radix2 (@common.emin t) by lra.
  unfold DWTimesFP_mixed_guarantee.
  revert Hacc Hdw.
  destruct (DWTimesFP3 xh xl y) as [zh zl].
  cbn [fst snd]. intros Hacc Hdw. exact (conj Hacc Hdw).
Qed.

(* ------------------------------------------------------------------
   PUBLIC WHOLE-RANGE INTERFACE.

   DWTimesFP_mixed_cond contains exactly the input double-word property and
   finiteness of the computed pair.  From it, the theorem below proves the
   bundled mixed bound and output closure.
   A caller using only pre-operation checks may instead establish
   DWTimesFP_mixed_safe_input_cond, derive mixed_cond via result finiteness,
   and obtain the same bundle.  No underflow disjunct is needed in either
   route, so both cover the Fast2Mult underflow gap.
   ------------------------------------------------------------------ *)

Lemma DWTimesFP_mixed_cond_of_safe_input_cond {NANS : Nans} {t : type}
    {STD : is_standard t} (xh xl y : ftype t) :
  DWTimesFP_mixed_safe_input_cond xh xl y ->
  DWTimesFP_mixed_cond xh xl y.
Proof.
move => Hsafe.
have Hfin := DWTimesFP3_finite_from_safe_input_cond xh xl y Hsafe.
move: Hsafe => [_ [Hdw _]].
unfold DWTimesFP_mixed_cond, DWTimesFP_mixed_input_cond,
       DWTimesFP_result_finite.
exact (conj Hdw Hfin).
Qed.

Theorem DWTimesFP_mixed_guarantee_from_cond
    {NANS : Nans} {t : type} {STD : is_standard t}
    (xh xl y : ftype t) :
  (3 <= fprec t)%Z ->
  DWTimesFP_mixed_cond xh xl y ->
  DWTimesFP_mixed_guarantee xh xl y.
Proof.
move => Hp3 [DWa FIN].
exact (DWTimesFP_mixed_guarantee_core xh xl y Hp3 DWa FIN).
Qed.

Theorem DWTimesFP_mixed_guarantee_from_safe_input_cond
    {NANS : Nans} {t : type} {STD : is_standard t}
    (xh xl y : ftype t) :
  (3 <= fprec t)%Z ->
  DWTimesFP_mixed_safe_input_cond xh xl y ->
  DWTimesFP_mixed_guarantee xh xl y.
Proof.
intros Hp3 Hsafe.
apply DWTimesFP_mixed_guarantee_from_cond; [exact Hp3 |].
exact (DWTimesFP_mixed_cond_of_safe_input_cond xh xl y Hsafe).
Qed.

Lemma DWTimesFP_inputs_finite_of_result_finite {NANS : Nans} {t : type}
    {STD : is_standard t} (xh xl y : ftype t) :
  DWTimesFP_result_finite xh xl y ->
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite y = true.
Proof.
unfold DWTimesFP_result_finite.
move => Hfin.
have [Hfxh Hfy] := BMULT_finite_e t xh y
  (DWTimesFP3_mul_finite xh xl y Hfin).
exact (conj Hfxh (conj (DWTimesFP3_xl_finite xh xl y Hfin) Hfy)).
Qed.
