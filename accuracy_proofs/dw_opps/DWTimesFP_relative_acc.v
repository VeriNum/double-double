(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Relative accuracy results for [DWTimesFP]. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common FLT_helpers.
Require Import DWTimesFP DDConds DWord_defs Fast2Mult_acc TwoSum_acc Fast2Sum_acc.
Require Import DW_acc_lemmas.
From Flocq Require Import Pff2Flocq Core.

From Stdlib Require Import Reals.Reals.

Require Import mathcomp.ssreflect.ssreflect.

From Stdlib Require Import Logic.FunctionalExtensionality.

Set Bullet Behavior "Strict Subproofs".

Opaque DWTimesFP.TwoProd.
Arguments DWTimesFP.TwoProd : simpl never.

Section DWTimesFP_ResultFacts.
  Context {NANS: Nans} {t : type} {STD: is_standard t}.

  Variables (xh xl y : ftype t).

  Hypothesis FIN : is_finite_p (DWTimesFP xh xl y).

  Ltac prove_finite :=
    move: FIN;
    rewrite /DWTimesFP/is_finite_p //=;
    move => [] //=;
    subexpr_finite => //
  .

  Fact DWTimesFP_mul_finite : is_finite (BMULT xh y) = true.
  Proof. prove_finite. Qed.

  Fact DWTimesFP_xh_finite : is_finite xh = true.
  Proof. prove_finite. Qed.

  Fact DWTimesFP_fast2mult_finite : is_finite_p (Fast2Mult xh y).
  Proof. prove_finite. Qed.

  Let cl1 := snd (Fast2Mult xh y).

  Fact DWTimesFP_correction_finite : is_finite (BFMA xl y cl1) = true.
  Proof. prove_finite. Qed.

  Fact DWTimesFP_xl_finite : is_finite xl = true.
  Proof. prove_finite. Qed.

End DWTimesFP_ResultFacts.

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

Section DWTimesFP_FLX_Bridge.

Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (common.emin (t:=t)).

Variables (xh xl y : ftype t).

Hypothesis xE : double_word xh xl.
Hypothesis FIN : is_finite_p (DWTimesFP xh xl y).
Hypothesis Hp3 : (3 <= fprec t)%Z.
Hypothesis Hbig :
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R y).
Hypothesis Hw :
  bpow radix2 (emin + fprec t - 1)
    <= Rabs (FT2R xl * FT2R y + FT2R (Fast2Mult_err xh y)).

Theorem DWTimesFP_FLX_FLT_weak :
  DWTimesFP9 (fprec t) choice (FT2R xh) (FT2R xl) (FT2R y) = F2Rp (DWTimesFP xh xl y).
Proof.
have Ffast : is_finite_p (Fast2Mult xh y) by
  apply: (DWTimesFP_fast2mult_finite _ xl _) => //.
have Fcorr : is_finite (BFMA xl y (snd (Fast2Mult xh y))) = true by
  apply: DWTimesFP_correction_finite => //.
move: Fcorr.
rewrite /Fast2Mult/fst/snd. move => Fcorr.
have Fmul : is_finite (BMULT xh y) = true by
  apply: (DWTimesFP_mul_finite _ _ _ FIN) => //.
have Huf2 : FT2R xh * FT2R y <> 0 ->
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R y)
  by (move => _; exact Hbig).
rewrite /DWTimesFP9/DWTimesFP.
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

Section DWTimesFP_Finite.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin  := (@common.emin t).
Notation fexp  := (SpecFloat.fexp (fprec t) (femax t)).
Notation ulp   := (Ulp.ulp Zaux.radix2 fexp).
Notation Omega := (bpow Zaux.radix2 (femax t)).

Local Instance valid_fexp_inst : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.

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
-
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
-
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

Lemma DWTimesFP_finite_post_cond_from_strong_precond (xh xl y : ftype t) :
  DWTimesFP_strong_precond xh xl y ->
  is_finite_p (DWTimesFP xh xl y).
Proof.
intros (Hfxl & Hdwp & Hfmul & Hreal).
have [Hfxh Hfy] := BMULT_finite_e t xh y Hfmul.
have HyΩ : Rabs (FT2R y) <= Omega
  by (apply Rlt_le; exact (is_finite_no_overflow t y Hfy)).
have Hprod : Rabs (FT2R (BMULT xh y)) <= /2 * Omega
  by (apply aux_round_prod_bnd; [exact Hfmul | exact Hreal]).
have HΩ : 0 < Omega by apply bpow_gt_0.
have HE0 : 0 <= bpow radix2 (femax t - fprec t) by apply bpow_ge_0.
have HEq := @bpow_femax_fprec_le_quarter_Omega t.

have Hfch : is_finite (Fast2Mult_mul xh y) = true.
{ unfold Fast2Mult_mul, Fast2Mult, fst. exact Hfmul. }
have Hch4 : Rabs (FT2R (Fast2Mult_mul xh y)) <= /2 * Omega.
{ unfold Fast2Mult_mul, Fast2Mult, fst. exact Hprod. }

have Hfcl1 : is_finite (Fast2Mult_err xh y) = true.
{ destruct (Fast2Mult_finite_unconditional xh y Hfmul) as [_ H]. exact H. }
have Hcl1u : Rabs (FT2R (Fast2Mult_err xh y)) <= /2 * ulp (FT2R xh * FT2R y).
{ apply Fast2Mult_accuracy_norm; exact Hfmul. }

have Hxhy : Rabs (FT2R xh * FT2R y) <= /2 * Omega by exact Hreal.
have Hxhy_lt : Rabs (FT2R xh * FT2R y) < Omega by lra.
have Hxly : Rabs (FT2R xl * FT2R y) <= /2 * bpow radix2 (femax t - fprec t).
{ apply (aux_xly_bnd xh xl y); [exact Hdwp | exact Hxhy | exact HyΩ]. }
have Hcl1b : Rabs (FT2R (Fast2Mult_err xh y)) <= /2 * bpow radix2 (femax t - fprec t).
{ eapply Rle_trans; [exact Hcl1u|]. apply Rmult_le_compat_l; [lra|].
  apply ulp_below_overflow; exact Hxhy_lt. }

have Hv : Rabs (FT2R xl * FT2R y + FT2R (Fast2Mult_err xh y))
       <= bpow radix2 (femax t - fprec t).
{ eapply Rle_trans; [apply Rabs_triang|]. lra. }
have Hv_lt : Rabs (FT2R xl * FT2R y + FT2R (Fast2Mult_err xh y)) < Omega by lra.

have Hfcl3 : is_finite (BFMA xl y (Fast2Mult_err xh y)) = true.
{ apply no_overflow_fma_is_finite => //.
  eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
  have Hu := ulp_below_overflow _ Hv_lt. lra. }

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
-
  change (is_finite (BPLUS (Fast2Mult_mul xh y)
                           (BFMA xl y (Fast2Mult_err xh y))) = true).
  exact Hfst.
-
  apply (is_finite_FastSum_small (Fast2Mult_mul xh y)
                                 (BFMA xl y (Fast2Mult_err xh y)));
    [ lra | exact Hfst ].
Qed.

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

have Hcl1Q : Rabs (FT2R (Fast2Mult_err xh y))
          <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R y).
{ eapply Rle_trans; [exact Hcl1_b|].
  eapply Rle_trans; [apply Rmult_le_compat_l; [lra | exact Hulp_xhy]|].
  rewrite HBp. apply Req_le; field. }

have Hw_ub : Rabs (FT2R xl * FT2R y + FT2R (Fast2Mult_err xh y))
          <= 2 * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R y).
{ eapply Rle_trans; [apply Rabs_triang|].
  eapply Rle_trans; [apply Rplus_le_compat; [exact Hxl_y | exact Hcl1Q]|].
  apply Req_le; ring. }

have Hch_lb : Rabs (FT2R xh * FT2R y) - bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R y)
           <= Rabs (FT2R (Fast2Mult_mul xh y)).
{ have Hch_e : FT2R (Fast2Mult_mul xh y) = FT2R xh * FT2R y - FT2R (Fast2Mult_err xh y)
    by (rewrite Hcl1_eq; ring).
  rewrite Hch_e.
  eapply Rle_trans; [| apply Rabs_triang_inv].
  apply Rplus_le_compat_l, Ropp_le_contravar. exact Hcl1Q. }

have H3B : 3 * bpow radix2 (- fprec t) <= 1.
{ eapply Rle_trans; [apply Rmult_le_compat_l; [lra | exact Hbq] | lra]. }

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

rewrite -BFMA_round_correct; [| exact Hfcl3].
apply abs_round_le_generic.
all: try exact Hwb.
all: try apply valid_rnd_N.
all: try apply generic_format_abs.
all: try exact valid_fexp_inst.
all: try apply generic_format_FLT_FT2R.
Qed.

Lemma DWTimesFP_double_word_from_pre (xh xl y : ftype t) :
  is_finite (BPLUS (Fast2Mult_mul xh y) (BFMA xl y (Fast2Mult_err xh y))) = true ->
  Rabs (FT2R (BFMA xl y (Fast2Mult_err xh y)))
    <= Rabs (FT2R (Fast2Mult_mul xh y)) ->
  double_word (fst (DWTimesFP xh xl y)) (snd (DWTimesFP xh xl y)).
Proof.
move => Hfp Hord.
exact (Fast2Sum_is_DW (Fast2Mult_mul xh y)
         (BFMA xl y (Fast2Mult_err xh y)) Hfp Hord).
Qed.

End DWTimesFP_Finite.

Section DWTimesFP_Accuracy.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation u     := (bpow Zaux.radix2 (- fprec t)).
Notation fexp  := (SpecFloat.fexp (fprec t) (femax t)).
Notation eminA := (SpecFloat.emin (fprec t) (femax t)).
Notation ulp   := (Ulp.ulp Zaux.radix2 fexp).

Local Instance valid_fexp_inst_acc : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.

Variables (xh xl y : ftype t).

Let zh := FT2R (fst (DWTimesFP xh xl y)).
Let zl := FT2R (snd (DWTimesFP xh xl y)).
Let xr := (FT2R xh + FT2R xl).
Let yr := FT2R y.

Definition relative_error_DWTimesFP : R :=
  Rabs (((zh + zl) - xr * yr) / (xr * yr)).

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
-
  have Hr : rounded t (FT2R xl) = FT2R xl
    by (unfold rounded; apply round_generic;
        [ apply valid_rnd_N | apply generic_format_FLT_FT2R ]).
  have Hxl0 : FT2R xl = 0.
  { move: Hdw; rewrite /double_word_prop Hxh0 Rplus_0_l Hr.
    move => H; exact (eq_sym H). }
  unfold xr, yr. rewrite Hxh0 Hxl0. ring.
- unfold xr, yr. rewrite Hy0. ring.
Qed.

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

Local Lemma relerr_error_eq :
  double_word_prop xh xl ->
  is_finite_p (DWTimesFP xh xl y) ->
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

have Hsum : (zh + zl)%R = (FT2R ch + FT2R cl3)%R.
{ unfold zh, zl.
  have Hfst_eq : fst (DWTimesFP xh xl y) = Fast2Sum_sum ch cl3 by reflexivity.
  have Hsnd_eq : snd (DWTimesFP xh xl y) = Fast2Sum_err ch cl3 by reflexivity.
  rewrite Hfst_eq Hsnd_eq Hexact. ring. }
rewrite Hsum Hcl3_eq.
unfold xr, yr, w, cl1.
rewrite Hcl1_eq. ring.
Qed.

Lemma DWTimesFP_relative_accuracy_core :
  double_word xh xl ->
  is_finite_p (DWTimesFP xh xl y) ->
  (3 <= fprec t)%Z ->
  (FT2R xh * FT2R y = 0 \/
   bpow Zaux.radix2 (SpecFloat.emin (fprec t) (femax t) + 2 * fprec t - 1)
   <= Rabs (FT2R xh * FT2R y)) ->
  relative_error_DWTimesFP <= 2 * u ^ 2.
Proof.
intros Hdw Hfin Hp3 Huf.
destruct Huf as [Hxy0 | Hbig].
-
  rewrite (relerr_0_of_xryr0 (xryr0_of_prod0 Hdw Hxy0)).
  apply Rmult_le_pos; [lra | apply pow_le; apply bpow_ge_0].
-

  have Hfmul : is_finite (BMULT xh y) = true
    by exact (DWTimesFP_mul_finite xh xl y Hfin).
  move: (xryr_ne_0_of_big Hdw Hbig) => [HP0 [Hyne [Hxrne Hxryrne]]].
  have Herr := relerr_error_eq Hdw Hfin Hfmul Hbig.
  cbv zeta in Herr.
  set w := (FT2R xl * FT2R y + FT2R (Fast2Mult_err xh y))%R in Herr *.
  destruct (Rlt_le_dec (Rabs w) (bpow radix2 (eminA + fprec t - 1)))
    as [Hwsub | Hwnorm].
  +
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
  +
    have Hbridge := DWTimesFP_FLX_FLT_weak xh xl y Hfin Hbig Hwnorm.
    have HFy : generic_format radix2 (FLX_exp (fprec t)) (FT2R y)
      by (apply (generic_format_FLX_FLT radix2 eminA (fprec t));
          apply generic_format_FLT_FT2R).
    have HDWx : DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl)
      by (apply (dw_word_DWdouble xh xl y); exact Hdw).

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

Local Lemma DWTimesFP_cond_no_gap :
  DWTimesFP_relative_precond xh xl y ->
  FT2R xh * FT2R y = 0 \/
  bpow Zaux.radix2 (eminA + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R y).
Proof. move => [_ [_ [Hf2m _]]]; exact (proj2 Hf2m). Qed.

(** Bounds the relative error of [DWTimesFP]. *)
Theorem DWTimesFP_relative_accuracy :
  (3 <= fprec t)%Z ->
  DWTimesFP_relative_precond xh xl y ->
  relative_error_DWTimesFP <= 2 * u ^ 2.
Proof.
intros Hp3 Hcond.
have Hsafe :=
  DWTimesFP_strong_precond_of_relative_precond
    xh xl y Hcond.
have Hfp := DWTimesFP_finite_post_cond_from_strong_precond xh xl y Hsafe.
have Hnogap := DWTimesFP_cond_no_gap Hcond.
move: Hcond => [Hfxl [Hdwp [Hf2m Hreal]]].
exact (DWTimesFP_relative_accuracy_core Hdwp Hfp Hp3 Hnogap).
Qed.

End DWTimesFP_Accuracy.
