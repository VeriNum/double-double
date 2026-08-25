(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Final accuracy results for the Fast2Mult algorithm in the FLT format.
   Helper lemmas live in Fast2Mult_acc_helpers.v. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs common dd_tactics.
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
  (* Accuracy follows from finiteness alone (no underflow condition).
     The error term is fl(a*b - fl(a*b)) = round d, with d = ab - round ab,
     |d| <= /2 ulp(ab) = bpow(cexp ab - 1).  Rounding d cannot exceed that
     bound: if cexp ab - 1 >= emin then bpow(cexp ab - 1) is representable and
     round fixes it; otherwise cexp ab = emin, d lies at/below the midpoint
     bpow(emin-1) of the smallest normal number and rounds to 0. *)
  have FIN := Fast2Mult_finite_unconditional a b Fast2Mult_overflow_condition.
  destruct FIN as (FINs & FINd).
  set (ab := FT2R a * FT2R b) in *.
  (* Rewrite the error term to round d. *)
  unfold Fast2Mult_err, Fast2Mult, snd in FINd |- *.
  rewrite -(BFMA_round_correct t a b (BOPP (BMULT a b)) FINd).
  rewrite -(BOPP_binary t (BMULT a b)); [ | right; exact Fast2Mult_overflow_condition ].
  fold ab; rewrite -(BMULT_round_correct t a b Fast2Mult_overflow_condition).
  fold ab.
  set (rab := round Zaux.radix2 (FLT_exp emin (fprec t)) (Znearest choice) ab).
  set (d := ab + - rab).
  (* |d| <= /2 ulp(ab). *)
  have Hd : Rabs d <= /2 * ulp ab.
  { rewrite /d /rab.
    have -> : (ab + - round Zaux.radix2 (FLT_exp emin (fprec t)) (Znearest choice) ab)
       = - (round Zaux.radix2 (FLT_exp emin (fprec t)) (Znearest choice) ab - ab) by ring.
    rewrite Rabs_Ropp.
    apply (error_le_half_ulp Zaux.radix2 (FLT_exp emin (fprec t)) choice ab). }
  (* handle ab = 0 separately. *)
  destruct (Req_dec ab 0) as [Hab0 | Hab0].
  { rewrite /d /rab Hab0 round_0 Ropp_0 Rplus_0_r round_0 Rabs_R0.
    have Hge := ulp_ge_0 Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) 0. lra. }
  (* ab <> 0 : /2 ulp ab = bpow (cexp ab - 1). *)
  set (c := cexp Zaux.radix2 (FLT_exp emin (fprec t)) ab).
  have Hulp : /2 * ulp ab = bpow Zaux.radix2 (c - 1).
  { rewrite (ulp_neq_0 _ _ _ Hab0). fold c.
    have Hstep : bpow Zaux.radix2 c = bpow Zaux.radix2 (c - 1) * bpow Zaux.radix2 1
      by rewrite -bpow_plus; f_equal; lia.
    rewrite Hstep bpow_1 /=. lra. }
  rewrite Hulp. rewrite Hulp in Hd.
  (* Goal: Rabs (round d) <= bpow (c - 1). *)
  destruct (Z.le_gt_cases emin (c - 1)) as [Hle | Hgt].
  - (* bpow (c-1) is representable; round fixes it. *)
    apply abs_round_le_generic; [ FLT_basics | FLT_basics | | exact Hd ].
    apply generic_format_bpow. cbv [FLT_exp].
    revert Hle. cbv [emin SpecFloat.emin].
    pose proof (fprec_gt_0 t) as Hp; red in Hp. lia.
  - (* c = emin: |d| <= bpow(emin-1) (the exact midpoint), which
       round-to-nearest-even sends to 0. *)
    have Hc : (c = emin)%Z.
    { have Hcge : (emin <= c)%Z by rewrite /c /cexp /FLT_exp; lia.
      lia. }
    (* Reduce to round-monotonicity: |round d| = round|d| <= round(bpow(emin-1)). *)
    rewrite -round_NE_abs.
    apply Rle_trans with
      (round Zaux.radix2 (FLT_exp emin (fprec t)) (Znearest choice)
             (bpow Zaux.radix2 (emin - 1))).
    { apply round_le; [ FLT_basics | FLT_basics | ].
      eapply Rle_trans; [ apply Hd | apply bpow_le; lia ]. }
    (* round(bpow(emin-1)) = 0 by direct computation (ties-to-even at the
       midpoint bpow(emin-1) = (0 + bpow emin)/2 picks the even neighbour 0). *)
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

Section FastTwoMultCheckImplies.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))).

Variables (a b : ftype t).

(* Fast2Mult_exact_cond is the single pre-condition shared with the verif spec
   (fast2_mult_check_spec at Tdouble). *)
Corollary Fast2Mult_accuracy_from_exact_cond :
  Fast2Mult_exact_cond a b ->
  Rabs (FT2R (Fast2Mult_err a b)) <= /2 * ulp (FT2R a * FT2R b).
Proof.
  intros [Hfin _].
  now apply Fast2Mult_accuracy_norm.
Qed.

(* The accuracy bound needs ONLY overflow-safety (finiteness of the rounded
   product): Fast2Mult_acc_only_cond = is_finite (BMULT a b) = true. *)
Corollary Fast2Mult_accuracy_from_acc_only_cond :
  Fast2Mult_acc_only_cond a b ->
  Rabs (FT2R (Fast2Mult_err a b)) <= /2 * ulp (FT2R a * FT2R b).
Proof.
  unfold Fast2Mult_acc_only_cond; intros Hfin.
  now apply Fast2Mult_accuracy_norm.
Qed.

(* Exact reconstruction and the double-word property need the full condition:
   both a finite rounded product and the underflow disjunct. *)
(* Stated as a Prop-level conjunction (/\) using double_word_prop, so it is
   usable in VST PROP clauses.  double_word_prop is definitionally the same
   equality as double_word (just : Prop instead of : Type), so the equality
   from TwoMult_is_DW closes the double_word_prop goal. *)
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
