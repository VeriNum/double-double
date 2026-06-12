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

(* No-overflow of an FMA implies finiteness (the converse of
   is_finite_fma_no_overflow), mirroring no_overflow_sum_is_finite for BPLUS.
   Same statement/proof as LAProof.accuracy_proofs.float_acc_lems
   .is_finite_fma_no_overflow'; kept local since LAProof is not a dependency. *)
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

Section CorrectDWMulFP.

Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (common.emin (t:=t)).
Notation u   := (bpow radix2 (- fprec t)).
Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).

Let ulp := (Ulp.ulp radix2 (SpecFloat.fexp (fprec t) (femax t))). 

Variables (xh xl y : ftype t).

Hypothesis  xE : double_word xh xl.

(* Magnitude ordering for the final Fast2Sum of DWTimesFP3 (ch <> 0): the low
   term cl3 = BFMA xl y (Fast2Mult_err xh y) is no larger than the high product
   ch = Fast2Mult_mul xh y.  This is the FLT-level counterpart of the |b| <= |a|
   precondition the paper feeds to F2Sum_correct_abs inside DWTimesFP9_correct
   (paper_proofs/DWTimesFP.v); it is the multiplication analog of
   DWPlusDW_vh_w_disjunction.

   Sketch (not underflow-dependent): cl3 = round(xl*y + cl1) with
   |cl1| <= 1/2 ulp(xh*y) (product rounding error) and |xl| <= 1/2 ulp(xh)
   (double_word).  For xh normal, ulp(xh) <= 2^{1-p}|xh| gives
   |xl*y| <= 2^{-p}|xh*y|, so |xl*y + cl1| <= |ch| and round monotonicity gives
   the bound; for xh subnormal, |xl| <= 1/2 ulp(xh) forces xl = 0 and the bound
   still holds. *)
Lemma DWTimesFP3_cl3_le_ch :
  is_finite (BPLUS (Fast2Mult_mul xh y) (BFMA xl y (Fast2Mult_err xh y))) = true ->
  FT2R (Fast2Mult_mul xh y) <> 0 ->
  Rabs (FT2R (BFMA xl y (Fast2Mult_err xh y)))
    <= Rabs (FT2R (Fast2Mult_mul xh y)).
Proof. Admitted.

(* The final step of DWTimesFP3 is Fast2Sum ch cl3, so finiteness of the snd
   output follows from is_finite_FastSum_ulp: the Fast2Sum ulp-ordering
   precondition  ulp cl3 <= ulp ch \/ ch = 0  is discharged by the magnitude
   ordering above (ulp_le) on the ch <> 0 branch, and trivially on ch = 0. *)
Lemma is_finite_DWTimesFP3 :
  is_finite (fst (DWTimesFP3 xh xl y)) = true ->
  is_finite (snd (DWTimesFP3 xh xl y)) = true.
Proof.
  move => Hfin.
  apply (is_finite_FastSum_ulp (Fast2Mult_mul xh y)
                               (BFMA xl y (Fast2Mult_err xh y))); [| exact Hfin].
  destruct (Req_dec (FT2R (Fast2Mult_mul xh y)) 0) as [Hch0 | Hch0];
    [by right | left].
  apply Ulp.ulp_le;
    first [ apply FLT.FLT_exp_valid; apply fprec_gt_0
          | apply FLT_exp_monotone
          | exact (DWTimesFP3_cl3_le_ch Hfin Hch0) ].
Qed.

Hypothesis FIN : is_finite_p (DWTimesFP3 xh xl y).
Hypothesis Hp3 : (3 <= fprec t)%Z.
Hypothesis TwoProdE : TwoProd = DWTimesFP.Fast2Mult (fprec t) choice.
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

(* |bpow(femax-1)| = /2 Omega, a power of 2, is in format. *)
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

(* The low-word product |xl*y| is small: in the normal range the relative ulp
   bound gives |xl| <= 2^-p |xh| so |xl*y| <= 2^-p |xh*y|; in the subnormal
   range |xl| <= 1/2 bpow emin is itself tiny.  Either way |xl*y| <= Omega/4. *)
Lemma aux_xly_bnd (xh xl y : ftype t) :
  double_word_prop xh xl ->
  Rabs (FT2R xh * FT2R y) <= /2 * Omega ->
  Rabs (FT2R y) <= /4 * Omega ->
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
  have HEsO : bpow radix2 emin * Omega <= 4 * bpow radix2 (femax t - fprec t).
  { have -> : (4 = bpow radix2 2)%R by reflexivity.
    rewrite -!bpow_plus. apply bpow_le.
    unfold common.emin, SpecFloat.emin. pose proof femax_lb t; pose proof fprec_lb t; lia. }
  nra.
Qed.

(* A rounded value is at most |v| + 1/2 ulp(v) in magnitude. *)
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

(* ulp of any real below the overflow threshold is at most bpow(femax-fprec). *)
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

(* MAIN: the closing Fast2Sum of DWTimesFP3 stays finite under the cond. *)
Lemma DWTimesFP3_fst_finite (xh xl y : ftype t) :
  DWTimesFP_cond xh xl y ->
  is_finite (fst (DWTimesFP3 xh xl y)) = true.
Proof.
intros (Hfxh & Hfxl & Hfy & Hdwp & Hfmul & Huf & Hxh4 & Hy4 & Hprod).
have HΩ : 0 < Omega by apply bpow_gt_0.
have HE0 : 0 <= bpow radix2 (femax t - fprec t) by apply bpow_ge_0.
have HEq : bpow radix2 (femax t - fprec t) <= /4 * Omega.
{ have -> : (/4 * Omega = bpow radix2 (femax t - 2))%R.
  { have -> : Omega = (bpow radix2 (femax t - 2) * bpow radix2 2)%R
      by rewrite -bpow_plus; f_equal; lia.
    have -> : bpow radix2 2 = 4%R by reflexivity. lra. }
  apply bpow_le; pose proof fprec_lb t; lia. }
(* ch = BMULT xh y : finite, bounded by Omega/4 *)
have Hfch : is_finite (Fast2Mult_mul xh y) = true.
{ unfold Fast2Mult_mul, Fast2Mult, fst. exact Hfmul. }
have Hch4 : Rabs (FT2R (Fast2Mult_mul xh y)) <= /4 * Omega.
{ unfold Fast2Mult_mul, Fast2Mult, fst. exact Hprod. }
(* underflow side-condition shared by Fast2Mult lemmas *)
have Huf' : FT2R xh * FT2R y <> 0 ->
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R y).
{ intro Hne. destruct Huf as [H | H]; [contradiction | exact H]. }
(* cl1 = Fast2Mult_err xh y : finite, |cl1| <= 1/2 ulp(xh*y) *)
have Hfcl1 : is_finite (Fast2Mult_err xh y) = true.
{ destruct (Fast2Mult_finite_if_BMULT_finite xh y Huf' Hfmul) as [_ H]. exact H. }
have Hcl1u : Rabs (FT2R (Fast2Mult_err xh y)) <= /2 * ulp (FT2R xh * FT2R y).
{ apply Fast2Mult_accuracy_norm; [exact Hfmul | exact Huf']. }
(* product real bound + low-product bound + cl1 in absolute terms *)
have Hxhy : Rabs (FT2R xh * FT2R y) <= /2 * Omega.
{ apply (aux_xhy_bnd xh y); [exact Hfmul | exact Hprod]. }
have Hxhy_lt : Rabs (FT2R xh * FT2R y) < Omega by lra.
have Hxly : Rabs (FT2R xl * FT2R y) <= /2 * bpow radix2 (femax t - fprec t).
{ apply (aux_xly_bnd xh xl y); [exact Hdwp | exact Hxhy | exact Hy4]. }
have Hcl1b : Rabs (FT2R (Fast2Mult_err xh y)) <= /2 * bpow radix2 (femax t - fprec t).
{ eapply Rle_trans; [exact Hcl1u|]. apply Rmult_le_compat_l; [lra|].
  apply aux_ulp_real; exact Hxhy_lt. }
(* v := xl*y + cl1, small *)
have Hv : Rabs (FT2R xl * FT2R y + FT2R (Fast2Mult_err xh y))
       <= bpow radix2 (femax t - fprec t).
{ eapply Rle_trans; [apply Rabs_triang|]. lra. }
have Hv_lt : Rabs (FT2R xl * FT2R y + FT2R (Fast2Mult_err xh y)) < Omega by lra.
(* cl3 = BFMA xl y cl1 : finite *)
have Hfcl3 : is_finite (BFMA xl y (Fast2Mult_err xh y)) = true.
{ apply no_overflow_fma_is_finite => //.
  eapply Rle_lt_trans; [apply aux_round_ub|].
  have Hu := aux_ulp_real _ Hv_lt. lra. }
(* |cl3| <= Omega/2 *)
have Hcl3b : Rabs (FT2R (BFMA xl y (Fast2Mult_err xh y))) <= /2 * Omega.
{ rewrite -BFMA_round_correct.
  - eapply Rle_trans; [apply aux_round_ub|].
    have Hu := aux_ulp_real _ Hv_lt. lra.
  - exact Hfcl3. }
(* final: fst (DWTimesFP3) = BPLUS ch cl3, no overflow *)
change (is_finite (BPLUS (Fast2Mult_mul xh y) (BFMA xl y (Fast2Mult_err xh y))) = true).
apply (no_overflow_sum_is_finite t _ _ Hfch Hfcl3).
unfold Bplus_no_overflow.
eapply Rle_lt_trans; [apply aux_round_ub|].
have Hsum : Rabs (FT2R (Fast2Mult_mul xh y) + FT2R (BFMA xl y (Fast2Mult_err xh y)))
         <= /4 * Omega + /2 * Omega.
{ eapply Rle_trans; [apply Rabs_triang|]. lra. }
have Hsum_lt : Rabs (FT2R (Fast2Mult_mul xh y) + FT2R (BFMA xl y (Fast2Mult_err xh y))) < Omega
  by lra.
have Hu := aux_ulp_real _ Hsum_lt. lra.
Qed.

(* A format value below the smallest subnormal bpow(emin) must be 0. *)
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
  { apply aux_format_small_0; [apply generic_format_FLT_FT2R|].
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
  by (apply Fast2Mult_accuracy_norm; [exact Hfmul | exact Huf']).
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

(* Finiteness of the snd output of DWTimesFP3 from the cond: the closing
   Fast2Sum precondition (ulp cl3 <= ulp ch, or ch = 0) is discharged from the
   cond's underflow disjunction — ch = 0 when xh*y = 0, else the magnitude
   ordering aux_cl3_le_ch lifted to ulp. *)
Lemma DWTimesFP3_snd_finite (xh xl y : ftype t) :
  DWTimesFP_cond xh xl y ->
  is_finite (snd (DWTimesFP3 xh xl y)) = true.
Proof.
move => Hcond.
have Hfp : is_finite (BPLUS (Fast2Mult_mul xh y) (BFMA xl y (Fast2Mult_err xh y))) = true
  by exact (DWTimesFP3_fst_finite xh xl y Hcond).
destruct (BPLUS_finite_e t (Fast2Mult_mul xh y) (BFMA xl y (Fast2Mult_err xh y)) Hfp)
  as [Hfch Hfcl3].
move: Hcond => [Hfxh [Hfxl [Hfy [Hdwp [Hfmul [Huf [Hxh4 [Hy4 Hprod]]]]]]]].
have Hord : ulp (FT2R (BFMA xl y (Fast2Mult_err xh y)))
         <= ulp (FT2R (Fast2Mult_mul xh y))
         \/ FT2R (Fast2Mult_mul xh y) = 0.
{ destruct Huf as [Hxy0 | Hthresh].
  - right. unfold Fast2Mult_mul, Fast2Mult, fst.
    rewrite -BMULT_round_correct // Hxy0 round_0 //.
  - left. apply Ulp.ulp_le; FLT_basics.
    apply aux_cl3_le_ch; [ exact Hdwp | exact Hfmul | exact Hfcl3 | exact Hthresh ]. }
apply (is_finite_FastSum_ulp (Fast2Mult_mul xh y)
                             (BFMA xl y (Fast2Mult_err xh y))); [exact Hord | exact Hfp].
Qed.

End DWTimesFP_Finite.

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

Notation u     := (bpow Zaux.radix2 (- fprec t)).
Notation fexp  := (SpecFloat.fexp (fprec t) (femax t)).
Notation eminA := (SpecFloat.emin (fprec t) (femax t)).
Notation ulp   := (Ulp.ulp Zaux.radix2 fexp).
Notation OmegaA := (bpow Zaux.radix2 (femax t)).

(* Valid_exp for SpecFloat.fexp, so Flocq's ulp/round lemmas discharge it. *)
Local Instance valid_fexp_inst : Generic_fmt.Valid_exp fexp.
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
  by (unfold cl1; symmetry; exact (BFMA_round_correct xl y (Fast2Mult_err xh y) Hfcl3)).
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
- (* normal regime: |xh*y| >= bpow(emin+2*fprec-1); via the FLX->FLT bridge
     (DWTimesFP3_FLX_FLT) + DWTimesFP9_correct, with the FMA-underflow sub-case
     handled by a direct |abs error| / |xr*yr| bound. *)
  admit.
Admitted.

(* Layer-2 corollary: a thin wrapper over DWTimesFP_relerr_bound.  It pulls
   the three Layer-1 hypotheses out of the cond verified at the spec interface
   (DWTimesFP_cond, defined in DDModels.v):
     - double_word           <- the cond's double_word_prop (convertible);
     - is_finite_p           <- DWTimesFP3_fst_finite / DWTimesFP3_snd_finite;
     - the underflow disjunction is passed through verbatim.
   The 3 <= fprec t hypothesis is threaded by the caller (true for Tdouble). *)
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
move: Hcond => [Hfxh [Hfxl [Hfy [Hdwp [Hfmul [Huf [Hxh4 [Hy4 Hprod]]]]]]]].
exact (DWTimesFP_relerr_bound Hdwp Hfp Hp3 Huf).
Qed.

End DWTimesFP_Accuracy.
