(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs common dd_tactics FLT_helpers.
Require Import DDConds.
Require Export Fast2Mult_acc_helpers.
From Flocq Require Import Pff2Flocq Core.
Require Import mathcomp.ssreflect.ssreflect.

Set Bullet Behavior "Strict Subproofs".

Section FastTwoMultAcc.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (@common.emin t).
Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))).
Notation u   := (bpow Zaux.radix2 (- fprec t)).

Variables (a b : ftype t).

Hypothesis (Fast2Mult_overflow_condition : is_finite (BMULT a b) = true).

Theorem Fast2Mult_accuracy_norm:
    Rabs (FT2R (Fast2Mult_err a b))  <= /2 * ulp (FT2R a * FT2R b).
Proof.

  have FIN := Fast2Mult_finite_unconditional a b Fast2Mult_overflow_condition.
  destruct FIN as (FINs & FINd).
  set (ab := FT2R a * FT2R b) in *.

  unfold Fast2Mult_err, Fast2Mult, snd in FINd |- *.
  rewrite -(BFMA_round_correct t a b (BOPP (BMULT a b)) FINd).
  rewrite -(BOPP_binary t (BMULT a b)); [ | right; exact Fast2Mult_overflow_condition ].
  fold ab; rewrite -(BMULT_round_correct t a b Fast2Mult_overflow_condition).
  fold ab.
  set (rab := round Zaux.radix2 (FLT_exp emin (fprec t)) (Znearest choice) ab).
  set (d := ab + - rab).

  have Hd : Rabs d <= /2 * ulp ab.
  { rewrite /d /rab.
    have -> : (ab + - round Zaux.radix2 (FLT_exp emin (fprec t)) (Znearest choice) ab)
       = - (round Zaux.radix2 (FLT_exp emin (fprec t)) (Znearest choice) ab - ab) by ring.
    rewrite Rabs_Ropp.
    apply (error_le_half_ulp Zaux.radix2 (FLT_exp emin (fprec t)) choice ab). }

  destruct (Req_dec ab 0) as [Hab0 | Hab0].
  { rewrite /d /rab Hab0 round_0 Ropp_0 Rplus_0_r round_0 Rabs_R0.
    have Hge := ulp_ge_0 Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) 0. lra. }

  set (c := cexp Zaux.radix2 (FLT_exp emin (fprec t)) ab).
  have Hulp : /2 * ulp ab = bpow Zaux.radix2 (c - 1).
  { rewrite (ulp_neq_0 _ _ _ Hab0). fold c.
    have Hstep : bpow Zaux.radix2 c = bpow Zaux.radix2 (c - 1) * bpow Zaux.radix2 1
      by rewrite -bpow_plus; f_equal; lia.
    rewrite Hstep bpow_1 /=. lra. }
  rewrite Hulp. rewrite Hulp in Hd.

  destruct (Z.le_gt_cases emin (c - 1)) as [Hle | Hgt].
  -
    apply abs_round_le_generic; [ FLT_basics | FLT_basics | | exact Hd ].
    apply generic_format_bpow. cbv [FLT_exp].
    revert Hle. cbv [emin SpecFloat.emin].
    pose proof (fprec_gt_0 t) as Hp; red in Hp. lia.
  -

    have Hc : (c = emin)%Z.
    { have Hcge : (emin <= c)%Z by rewrite /c /cexp /FLT_exp; lia.
      lia. }

    rewrite -round_NE_abs.
    apply Rle_trans with
      (round Zaux.radix2 (FLT_exp emin (fprec t)) (Znearest choice)
             (bpow Zaux.radix2 (emin - 1))).
    { apply round_le; [ FLT_basics | FLT_basics | ].
      eapply Rle_trans; [ apply Hd | apply bpow_le; lia ]. }

    have Hround0 :
      round Zaux.radix2 (FLT_exp emin (fprec t)) (Znearest choice)
        (bpow Zaux.radix2 (emin - 1)) = 0.
    { unfold round, scaled_mantissa, cexp, F2R; simpl.
      have Hmag : mag Zaux.radix2 (bpow Zaux.radix2 (emin - 1)) = emin :> Z
        by rewrite mag_bpow; f_equal; lia.
      rewrite Hmag.
      have Hfe : FLT_exp emin (fprec t) emin = emin.
      { cbv [FLT_exp]. pose proof (fprec_gt_0 t) as Hp; red in Hp. lia. }
      rewrite Hfe.
      have Hsm : (bpow Zaux.radix2 (emin - 1) * bpow Zaux.radix2 (- emin))%R = /2.
      { rewrite -bpow_plus.
        have -> : (emin - 1 + - emin = -1)%Z by lia.
        rewrite /bpow /=. lra. }
      rewrite Hsm.
      have Hzn : Znearest choice (/2) = 0%Z.
      { unfold Znearest.
        have Hf : Zfloor (/2) = 0%Z.
        { apply Zfloor_imp. rewrite /=. lra. }
        rewrite Hf. rewrite Rminus_0_r.
        rewrite Rcompare_Eq; [ | reflexivity ].
        rewrite /choice /=. reflexivity. }
      rewrite Hzn /=. lra. }
    rewrite Hround0. apply bpow_ge_0.
Qed.

End FastTwoMultAcc.

Section FastTwoMultFloor.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

(** Even below the exact reconstruction threshold, the compensated product
    loses at most half a physical underflow ulp. *)
Lemma Fast2Mult_sum_error_floor (a b : ftype t) :
  (3 <= fprec t)%Z ->
  is_finite_p (Fast2Mult a b) ->
  Rabs (FT2R (Fast2Mult_mul a b) + FT2R (Fast2Mult_err a b) -
        FT2R a * FT2R b) <=
    /2 * bpow radix2 (@common.emin t).
Proof.
move => Hp3 FIN.
set x := (FT2R a * FT2R b)%R.
set ch := Fast2Mult_mul a b.
set cl := Fast2Mult_err a b.
set r := (x - FT2R ch)%R.
set u := bpow radix2 (- fprec t).
set eta := bpow radix2 (@common.emin t).
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /8.
{ unfold u. have -> : (/8:R) = bpow radix2 (-3) by (simpl; lra).
  apply bpow_le; lia. }
have Heta0 : 0 < eta by apply bpow_gt_0.
have Fch : is_finite ch = true by exact (proj1 FIN).
have Fcl : is_finite cl = true by exact (proj2 FIN).
have Hchr : FT2R ch = round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) x.
{ unfold ch, Fast2Mult_mul, Fast2Mult. symmetry.
  apply BMULT_round_correct. exact Fch. }
have Hop : FT2R (BOPP ch) = - FT2R ch.
{ symmetry. apply BOPP_binary. right; exact Fch. }
have Hclr : FT2R cl = round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) r.
{ unfold cl, Fast2Mult_err, Fast2Mult.
  rewrite -(BFMA_round_correct t a b (BOPP ch) Fcl) Hop.
  unfold r, x. f_equal; ring. }
destruct (Req_dec x 0) as [Hx0 | Hx0].
- have Hch0 : FT2R ch = 0 by rewrite Hchr Hx0 round_0.
  have Hr0 : r = 0 by unfold r; rewrite Hx0 Hch0; ring.
  rewrite Hx0 Hch0 Hclr Hr0 round_0.
  rewrite Rminus_0_r Rplus_0_l Rabs_R0. nra.
- destruct (Rle_dec
    (bpow radix2 (@common.emin t + 2 * fprec t - 1)) (Rabs x))
    as [Hbig | Hsmall].
  + have Hex := Fast2MultModel_correct a b Fch.
    specialize (Hex ltac:(move => _; exact Hbig)).
    fold x ch cl in Hex.
    rewrite Hex. replace (FT2R ch + (x - FT2R ch) - x)%R with 0 by ring.
    rewrite Rabs_R0. nra.
  + have Hxe := round_FLT_error_rel_emin (t:=t) x.
    fold u eta in Hxe. rewrite -Hchr in Hxe.
    have Hrabs : Rabs r <= u * Rabs x + /2 * eta.
    { unfold r. rewrite Rabs_minus_sym. exact Hxe. }
    have HxB : Rabs x <
        bpow radix2 (@common.emin t + 2 * fprec t - 1)
      by apply Rnot_le_lt.
    have Hux := Rmult_lt_compat_l u _ _ Hu0 HxB.
    have Hscale : u * bpow radix2
        (@common.emin t + 2 * fprec t - 1) =
        bpow radix2 (@common.emin t + fprec t - 1).
    { unfold u. rewrite -bpow_plus. f_equal; ring. }
    rewrite Hscale in Hux.
    have Hetahalf : /2 * eta = bpow radix2 (@common.emin t - 1).
    { unfold eta. rewrite (bpow_plus radix2 (@common.emin t) (-1)).
      change (bpow radix2 (-1)) with (/2:R). ring. }
    have Hetasmall : /2 * eta <
        bpow radix2 (@common.emin t + fprec t - 1).
    { rewrite Hetahalf. apply bpow_lt. lia. }
    have Hrsmall : Rabs r < bpow radix2 (@common.emin t + fprec t).
    { have Hnext : bpow radix2 (@common.emin t + fprec t) =
          2 * bpow radix2 (@common.emin t + fprec t - 1).
      { transitivity
          (bpow radix2 (@common.emin t + fprec t - 1) * bpow radix2 1).
        - rewrite -bpow_plus. f_equal; ring.
        - change (bpow radix2 1) with (2:R). ring. }
      rewrite Hnext. nra. }
    have Hvalid : Generic_fmt.Valid_exp
        (SpecFloat.fexp (fprec t) (femax t)).
    { apply FLT.FLT_exp_valid, fprec_gt_0. }
    have Hre := @Ulp.error_le_half_ulp radix2
      (SpecFloat.fexp (fprec t) (femax t)) Hvalid choice r.
    have Hulp : Ulp.ulp radix2
        (SpecFloat.fexp (fprec t) (femax t)) r = eta.
    { unfold SpecFloat.fexp, common.emin.
      apply ulp_FLT_small; [apply fprec_gt_0 | exact Hrsmall]. }
    rewrite Hulp in Hre. rewrite -Hclr in Hre.
    change (Rabs (FT2R ch + FT2R cl - x) <= /2 * eta).
    replace (FT2R ch + FT2R cl - x)%R with (FT2R cl - r)%R
      by (unfold r; ring).
    exact Hre.
Qed.

End FastTwoMultFloor.

Section FastTwoMultCheckImplies.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))).

Variables (a b : ftype t).

Corollary Fast2Mult_accuracy_from_exact_cond :
  Fast2Mult_exact_cond a b ->
  Rabs (FT2R (Fast2Mult_err a b)) <= /2 * ulp (FT2R a * FT2R b).
Proof.
  intros [Hfin _].
  now apply Fast2Mult_accuracy_norm.
Qed.

Corollary Fast2Mult_correct_from_exact_cond :
  Fast2Mult_exact_cond a b ->
  FT2R (Fast2Mult_mul a b) + FT2R (Fast2Mult_err a b) = FT2R a * FT2R b
  /\ double_word_prop (Fast2Mult_mul a b) (Fast2Mult_err a b).
Proof.
  intros [Hfin Huf].
  have Huf' : (FT2R a * FT2R b <> 0 ->
    bpow Zaux.radix2 (@common.emin t + 2 * fprec t - 1) <= Rabs (FT2R a * FT2R b)).
  { intros Hne. destruct Huf as [H | H].
    - exfalso; apply Hne; exact H.
    - exact H. }
  split.
  - have HE := Fast2MultModel_correct a b Hfin Huf'.
    unfold Fast2Mult_mul, Fast2Mult_err in *. rewrite HE. ring.
  - have HDW := TwoMult_is_DW a b Hfin Huf'.
    unfold double_word_prop. unfold double_word in *. exact HDW.
Qed.

End FastTwoMultCheckImplies.
