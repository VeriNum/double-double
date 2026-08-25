(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Helper lemmas for the accuracy and correctness proofs of the
   TwoSum and Fast2Sum algorithms in the FLT format.

   Layout:
     1. No-overflow lemmas
     2. Finiteness propagation
     3. Real-arithmetic helper
     4. Correctness & equivalence *)

Require Import vcfloat.VCFloat.
From Stdlib Require Import ZArith.
Require Import float_acc_lems op_defs dd_tactics FLT_helpers.
Require Import DWPlus DDConds common.
Require Import F2SumFLT F2SumFLX.
From Flocq Require Import Pff2Flocq Core.
Require Import mathcomp.ssreflect.ssreflect.

Set Bullet Behavior "Strict Subproofs".

Section TwoSumCorrect.

Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Notation emin := (@common.emin t).
Notation rnd  := (round radix2 fexp (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)).
Notation Omega  := (bpow radix2 (femax t)).
Notation BMINUS := (@FPCore.BMINUS NANS t STD).
Notation BPLUS  := (@FPCore.BPLUS  NANS t STD).

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))).

(* ===================================================================== *)
(* 1. No-overflow lemmas                                                   *)
(* ===================================================================== *)

(* Generic ulp ceiling: a finite float's ulp cannot exceed 2^(femax - p), since
   its magnitude is below the overflow threshold.  This is just
   FLT_helpers.ulp_below_overflow composed with is_finite_no_overflow; it is
   hoisted here because no_overflow_2Sum_a_ulp and is_finite_TwoSum each used to
   carry a verbatim inline copy of the same 18-line argument. *)
Lemma ulp_le_top (x : ftype t) :
  is_finite x = true -> ulp (FT2R x) <= bpow radix2 (femax t - fprec t).
Proof.
  move => Hx. apply ulp_below_overflow; apply is_finite_no_overflow => //.
Qed.

Lemma no_overflow_2Sum_a (a b : ftype t):
  Rabs (FT2R b) <= Rabs (FT2R a) ->
  is_finite (BPLUS a b) = true ->
  Rabs (rnd (FT2R (BPLUS a b) - FT2R a)) < Omega .
Proof.
  move => Hab Hfin.
  destruct (BPLUS_finite_e t a b Hfin) as [Hfina  Hfinb].
  have Hfinlt : Rabs (FT2R a) < Omega by (apply is_finite_no_overflow).
  suff: Rabs (rnd (FT2R (BPLUS a b) - FT2R a)) <= Rabs (FT2R a).
  move => Ha.
  eapply Rle_lt_trans; [apply Ha |] => //.
  ++
  destruct (Rlt_dec 0 (FT2R a)) as [Hgt | Hle].
  **
  apply Rlt_le in Hgt.
  move : Hab.
  rewrite (Rabs_pos_eq (FT2R a)) => //.
  move => Hab.
  rewrite -round_NE_abs.
  eapply Rle_trans with (round radix2 fexp ZnearestE (FT2R a)).
  ---
  apply round_le; FLT_basics.
  apply Rabs_le.
  apply Rabs_le_inv in Hab.
  rewrite -BPLUS_round_correct => //.
  suff: 0 <= FT2R a + FT2R b <= 2 * FT2R a; [| destruct Hab; split; nra].
  +++
  move => H1.
  destruct H1 as [H1 H2].
  fold emin.
  eapply (round_le radix2 fexp (Znearest choice)) in H1, H2.
  rewrite round_0 in H1.
  split; apply Rcomplements.Rle_minus_l; [field_simplify|] => //.
  eapply Rle_trans; [apply H2|].
  rewrite round_generic; [ nra |replace 2 with (bpow radix2 1)] => //.
  rewrite Rmult_comm.
  apply Mult_error.mult_bpow_pos_exact_FLT => //.
  rewrite -B2R_float_of_ftype; apply Binary.generic_format_B2R.
  ---
  rewrite round_generic;
  rewrite -B2R_float_of_ftype; [nra| apply Binary.generic_format_B2R].
  **
  apply Rnot_lt_le in Hle.
  move : Hab.
  rewrite (Rabs_left1 (FT2R a)) => //.
  move => Hab.
  rewrite -round_NE_abs.
  eapply Rle_trans with (round radix2 fexp ZnearestE (- FT2R a)).
  ---
  apply round_le; FLT_basics.
  apply Rabs_le.
  apply Rabs_le_inv in Hab.
  rewrite -BPLUS_round_correct => //.
  suff: 2 * FT2R a <= FT2R a + FT2R b <= 0; [| destruct Hab; split; nra].
  +++
  move => H1.
  destruct H1 as [H1 H2].
  fold emin.
  eapply (round_le radix2 fexp (Znearest choice)) in H1, H2.
  rewrite round_0 in H2.
  split; apply Rcomplements.Rle_minus_l; [|field_simplify] => //.
  ***
  eapply Rle_trans; [| apply H1].
  rewrite round_generic; [ nra |replace 2 with (bpow radix2 1)] => //.
  rewrite Rmult_comm.
  apply Mult_error.mult_bpow_pos_exact_FLT => //.
  rewrite -B2R_float_of_ftype; apply Binary.generic_format_B2R.
  ---
  rewrite round_generic; [ nra |replace 2 with (bpow radix2 1)] => //.
  apply generic_format_opp.
  rewrite -B2R_float_of_ftype; apply Binary.generic_format_B2R.
Qed.

(* No-overflow of the first Fast2Sum step under the Fast2Sum_cond disjunction
   (ulp ordering, or a = 0).  The magnitude version (no_overflow_2Sum_a) bounds
   |rnd(s-a)| <= |a|, which FAILS under mere ulp ordering.  Instead we use that
   under ulp b <= ulp a the step is exact (z = s - a), then bound
   |s - a| <= |b| + (1/2) ulp(s)
   <= (Omega - bpow(femax-fprec)) + (1/2) bpow(femax-fprec) < Omega.
   The a = 0 disjunct is handled directly (rnd(s - 0) = s). *)
Lemma no_overflow_2Sum_a_ulp (a b : ftype t):
  ulp (FT2R b) <= ulp (FT2R a) \/ FT2R a = 0 ->
  is_finite (BPLUS a b) = true ->
  Rabs (rnd (FT2R (BPLUS a b) - FT2R a)) < Omega .
Proof.
  move => Hor Hfin.
  destruct (BPLUS_finite_e t a b Hfin) as [Hfina Hfinb].
  (* a = 0 : rnd(s - 0) = rnd s = s, |s| < Omega *)
  destruct (Req_dec (FT2R a) 0) as [Ha0 | Ha0].
  { rewrite Ha0 Rminus_0_r round_generic; FLT_basics.
    by apply is_finite_no_overflow. }
  (* b = 0 : s = rnd(a + 0) = a, rnd(s - a) = rnd 0 = 0 *)
  destruct (Req_dec (FT2R b) 0) as [Hb0 | Hb0].
  { have HrA : rnd (FT2R a) = FT2R a by rewrite round_generic; FLT_basics.
    rewrite -BPLUS_round_correct // Hb0 Rplus_0_r HrA Rminus_diag round_0 Rabs_R0.
    apply bpow_gt_0. }
  (* both nonzero: the a = 0 disjunct is excluded, so the ulp ordering holds *)
  have Hulp : ulp (FT2R b) <= ulp (FT2R a)
    by case: Hor => [//| Ha00]; case: (Ha0 Ha00).
  (* ulp ordering -> cexp ordering -> exactness *)
  have Hce : (cexp radix2 fexp (FT2R b) <= cexp radix2 fexp (FT2R a))%Z.
  { apply (le_bpow radix2).
    rewrite -(Ulp.ulp_neq_0 radix2 fexp (FT2R a) Ha0).
    rewrite -(Ulp.ulp_neq_0 radix2 fexp (FT2R b) Hb0).
    exact Hulp. }
  have Hex : rnd (FT2R (BPLUS a b) - FT2R a) = (FT2R (BPLUS a b) - FT2R a)%R.
  { rewrite -BPLUS_round_correct //.
    apply F2Sum_sma_exact_cexp_flt; first [ exact Hce | FLT_basics => // ]. }
  rewrite Hex.
  (* error bound: |s - (a + b)| <= /2 ulp(s) *)
  have Herr : Rabs (FT2R (BPLUS a b) - (FT2R a + FT2R b))
              <= /2 * ulp (FT2R (BPLUS a b)).
  { rewrite -!BPLUS_round_correct //. apply Ulp.error_le_half_ulp_round; FLT_basics. }
  (* ulp bound *)
  have Hulps : ulp (FT2R (BPLUS a b)) <= bpow radix2 (femax t - fprec t)
    by apply ulp_le_top.
  (* |b| <= pred Omega = Omega - bpow(femax - fprec) *)
  have Hbmax : Rabs (FT2R b)
               <= bpow radix2 (femax t) - bpow radix2 (femax t - fprec t).
  { have He : (SpecFloat.fexp (fprec t) (femax t) (femax t) = femax t - fprec t)%Z.
    { unfold SpecFloat.fexp, SpecFloat.emin.
      apply Z.max_l. pose proof femax_lb t. pose proof fprec_lb t. lia. }
    have Hr : (bpow radix2 (femax t) - bpow radix2 (femax t - fprec t))%R
              = Ulp.pred radix2 fexp Omega.
    { rewrite Ulp.pred_bpow He //. }
    rewrite Hr.
    apply Ulp.pred_ge_gt;
      first [ apply FLT.FLT_exp_valid; apply fprec_gt_0
            | apply Generic_fmt.generic_format_abs;
                first [ apply FLT.FLT_exp_valid; apply fprec_gt_0
                      | apply generic_format_FLT_FT2R ]
            | apply Generic_fmt.generic_format_bpow;
                unfold SpecFloat.fexp, SpecFloat.emin;
                apply Z.max_lub; pose proof femax_lb t; pose proof fprec_lb t; lia
            | apply is_finite_no_overflow => // ]. }
  (* triangle: |s - a| <= |b| + /2 ulp(s) *)
  eapply Rle_lt_trans.
  { replace (FT2R (BPLUS a b) - FT2R a)%R
      with (FT2R b + (FT2R (BPLUS a b) - (FT2R a + FT2R b)))%R by ring.
    eapply Rle_trans; [apply Rabs_triang|].
    apply Rplus_le_compat_l. exact Herr. }
  (* arithmetic close *)
  have Hpos : 0 < bpow radix2 (femax t - fprec t) by apply bpow_gt_0.
  eapply Rle_lt_trans.
  { apply Rplus_le_compat; [exact Hbmax|].
    apply Rmult_le_compat_l; [lra | exact Hulps]. }
  lra.
Qed.

(* No-overflow of the first Fast2Sum step from pure magnitude headroom on the
   SECOND argument -- no ordering hypothesis of any kind.

   The two lemmas above both need an ordering because they bound the step
   argument through |a|.  That is unnecessary: since
     s - a = b + (s - (a + b)),   s = BPLUS a b,
   the step argument is controlled by |b| plus the rounding error of the sum,
     |s - a| <= |b| + /2 ulp(s),
   and NOT by |s| + |a|.  So a bound on |b| alone suffices.  This is the route
   needed in the Fast2Mult underflow gap, where neither the magnitude ordering
   |b| <= |a| nor the ulp ordering ulp b <= ulp a is available.

   The stated conclusion is the sharp Omega/2, which callers need in order to
   chain into the second Fast2Sum step (see is_finite_FastSum_small):
     |b| <= Omega/4, ulp(_) <= bpow (femax - fprec) <= Omega/4
     ==> |s - a| <= Omega/4 + Omega/8 = 3/8 Omega
     ==> |rnd (s - a)| <= 3/8 Omega + Omega/8 = Omega/2. *)
Lemma round_2Sum_a_bnd_small (a b : ftype t):
  Rabs (FT2R b) <= /4 * Omega ->
  is_finite (BPLUS a b) = true ->
  Rabs (rnd (FT2R (BPLUS a b) - FT2R a)) <= /2 * Omega .
Proof.
  move => Hb Hfin.
  have HO  : 0 < Omega by apply bpow_gt_0.
  have HB0 : 0 < bpow radix2 (femax t - fprec t) by apply bpow_gt_0.
  have HB4 := @bpow_femax_fprec_le_quarter_Omega t.
  (* rounding error of the sum, and the generic ulp ceiling *)
  have Herr : Rabs (FT2R (BPLUS a b) - (FT2R a + FT2R b))
              <= /2 * ulp (FT2R (BPLUS a b)).
  { rewrite -!BPLUS_round_correct //. apply Ulp.error_le_half_ulp_round; FLT_basics. }
  have Hulps : ulp (FT2R (BPLUS a b)) <= bpow radix2 (femax t - fprec t)
    by (apply ulp_below_overflow; apply is_finite_no_overflow => //).
  (* |s - a| <= |b| + /2 ulp(s) *)
  have Hsa : Rabs (FT2R (BPLUS a b) - FT2R a)
             <= /4 * Omega + /2 * bpow radix2 (femax t - fprec t).
  { replace (FT2R (BPLUS a b) - FT2R a)%R
      with (FT2R b + (FT2R (BPLUS a b) - (FT2R a + FT2R b)))%R by ring.
    eapply Rle_trans; [apply Rabs_triang|]. lra. }
  (* rounding the step costs at most another /2 ulp *)
  eapply Rle_trans; [apply round_abs_le_abs_plus_half_ulp|].
  have Hu2 : ulp (FT2R (BPLUS a b) - FT2R a) <= bpow radix2 (femax t - fprec t)
    by (apply ulp_below_overflow; lra).
  lra.
Qed.

Lemma no_overflow_2Sum_b_1 (a b : ftype t) :
  Rabs (FT2R a) <= Rabs (FT2R b) ->
  is_finite (BPLUS a b) = true ->
  Rabs (rnd (FT2R (BPLUS a b) - FT2R b)) < Omega.
Proof.
  move=> Hab Hfin.
  rewrite BPLUS_comm => //.
  apply (no_overflow_2Sum_a b a) => //.
  apply BPLUS_fin_symm => //.
Qed.

Lemma no_overflow_2Sum_b_2 (a b : ftype t):
  is_finite (BMINUS a b) = true ->
  is_finite (BPLUS a b) = true ->
  Rabs (FT2R b) <= Rabs (FT2R a) ->
  Rabs (rnd (FT2R (BPLUS a b) - FT2R b)) < Omega.
Proof.
  move => Hfin_minus Hfin_plus Hba.
  (* No overflow of +/- *)
  have Habov_plus : Rabs (FT2R (BPLUS a b)) < Omega by
  rewrite -BPLUS_round_correct //;
  apply (@is_finite_sum_no_overflow t NANS STD a b Hfin_plus).
  have Habov_minus : Rabs (FT2R (BMINUS a b)) < Omega by
  rewrite -BMINUS_round_correct //;
  apply (@is_finite_minus_no_overflow t NANS STD a b Hfin_minus).
  (* Extract finiteness of a,b from finiteness of a+b *)
  destruct (BPLUS_finite_e t a b Hfin_plus) as [Hfina  Hfinb].
  have Hfinlta : Rabs (FT2R a) < Omega by (apply is_finite_no_overflow).
  have Hfinltb : Rabs (FT2R b) < Omega by (apply is_finite_no_overflow).
  (* Cases on sign a *) destruct (Rle_dec 0 (FT2R a)) as [Hapos | Haneg].
  - (* 0 <= a *)
  (* Cases on sign b *) destruct (Rle_dec 0 (FT2R b)) as [Hbpos | Hbneg].
  + (* 0 <= b *)
  suff: FT2R (BPLUS a b) - FT2R a <= FT2R (BPLUS a b) - FT2R b <= FT2R (BPLUS a b).
  move => Hs; destruct Hs as [Hs1 Hs2].
  apply (round_le radix2 fexp
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)) in Hs1, Hs2.
  apply Rabs_lt; split.
  eapply Rlt_le_trans; [| apply Hs1].
  apply Rabs_def2.
  rewrite BPLUS_comm => //.
  apply (no_overflow_2Sum_b_1 b a) => //; apply BPLUS_fin_symm => //.
  eapply Rle_lt_trans; [apply Hs2| ].
  rewrite round_generic; FLT_basics.
  apply Rabs_def2 => //.
  suff: - FT2R a <= - FT2R b <= 0; [nra|].
  apply Rabs_pos_eq in Hapos.
  rewrite Hapos in Hba;
  apply Rabs_le_inv in Hba; nra.
  + (* b <= 0 *)
  move/Rnot_le_lt: Hbneg => Hbneg.
  suff: - FT2R b <= FT2R (BPLUS a b) - FT2R b <= FT2R a - FT2R b.
  move => Hs; destruct Hs as [Hs1 Hs2].
  apply (round_le radix2 fexp
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)) in Hs1, Hs2.
  apply Rabs_lt; split.
  eapply Rlt_le_trans; [| apply Hs1].
  apply Rabs_def2.
  rewrite round_NE_opp Rabs_Ropp.
  rewrite round_generic; FLT_basics => //.
  eapply Rle_lt_trans; [apply Hs2 | ].
  apply Rabs_def2 => //.
  rewrite -BMINUS_round_correct in Habov_minus => //.
  suff: 0 <= FT2R (BPLUS a b) <= FT2R a; [nra |].
  rewrite -(round_generic radix2 fexp
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) (FT2R a)); FLT_basics.
  rewrite -BPLUS_round_correct => //.
  rewrite -(round_0 radix2 fexp
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)).
  split; apply round_le; FLT_basics; [|nra].
  apply Rabs_pos_eq in Hapos.
  rewrite Hapos in Hba.
  rewrite Rabs_left in Hba => //; nra.
  - (* a <= 0 *)
  move/Rnot_le_lt: Haneg => Haneg.
  (* Cases on sign b *) destruct (Rle_dec 0 (FT2R b)) as [Hbpos | Hbneg].
  + (* 0 <= b *)
  suff: FT2R a - FT2R b <= FT2R (BPLUS a b) - FT2R b <= - FT2R b.
  move => Hs; destruct Hs as [Hs1 Hs2].
  apply (round_le radix2 fexp
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)) in Hs1, Hs2.
  apply Rabs_lt; split.
  eapply Rlt_le_trans; [| apply Hs1].
  apply Rabs_def2.
  rewrite -BMINUS_round_correct in Habov_minus => //.
  eapply Rle_lt_trans; [apply Hs2 | ].
  apply Rabs_def2 => //.
  rewrite round_NE_opp Rabs_Ropp.
  rewrite round_generic; FLT_basics => //.
  suff: FT2R a <= FT2R (BPLUS a b) <= 0; [ nra| ].
  rewrite -(round_generic radix2 fexp
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) (FT2R a)); FLT_basics.
  rewrite -BPLUS_round_correct => //.
  split; [apply round_le; FLT_basics; nra | ].
  rewrite -(round_0 radix2 fexp
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)).
  apply round_le; FLT_basics.
  apply Rabs_pos_eq in Hbpos.
  rewrite Hbpos in Hba.
  rewrite Rabs_left in Hba => //; nra.
  +
  move/Rnot_le_lt: Hbneg => Hbneg.
  suff: FT2R (BPLUS a b) <= FT2R (BPLUS a b) - FT2R b <= FT2R (BPLUS a b) - FT2R a.
  move => Hs; destruct Hs as [Hs1 Hs2].
  apply (round_le radix2 fexp
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)) in Hs1, Hs2.
  apply Rabs_lt; split.
  eapply Rlt_le_trans; [| apply Hs1].
  apply Rabs_def2.
  rewrite round_generic; FLT_basics => //.
  eapply Rle_lt_trans; [apply Hs2| ].
  rewrite BPLUS_comm => //.
  apply Rabs_def2 => //.
  apply (no_overflow_2Sum_b_1 b a) => //; apply BPLUS_fin_symm => //.
  suff: 0 <= - FT2R b <= - FT2R a; [nra|].
  rewrite !Rabs_left in Hba => //; nra.
Qed.

Lemma no_overflow_2Sum_b (a b : ftype t):
  is_finite (BMINUS a b) = true ->
  is_finite (BPLUS a b) = true ->
  Rabs (rnd (FT2R (BPLUS a b) - FT2R b)) < Omega.
Proof.
  move=> Hfin1 Hfin2.
  destruct (Rle_dec  (Rabs (FT2R b)) (Rabs (FT2R a))).
  + (* |b| <= |a| *)
  apply no_overflow_2Sum_b_2 => //.
  + (* |a| <= |b| *)
  apply no_overflow_2Sum_b_1 => //; nra.
Qed.

(* ===================================================================== *)
(* 2. Finiteness propagation                                               *)
(* ===================================================================== *)

Lemma is_finite_2Sum_a (a b : ftype t) :
  Rabs (FT2R b) <= Rabs (FT2R a) ->
  is_finite (BPLUS a b) = true ->
  is_finite (BMINUS (BPLUS a b) a) = true.
Proof.
  move=> Hab Hfin.
  apply no_overflow_minus_is_finite => //.
  destruct (BPLUS_finite_e t a b Hfin) as [Hfina  _] => //.
  apply no_overflow_2Sum_a => //.
Qed.

Lemma is_finite_FastSum (a b : ftype t):
  Rabs (FT2R b) <= Rabs (FT2R a) ->
  is_finite (BPLUS a b) = true -> is_finite (snd (DDModels.Fast2Sum a b)) = true .
Proof.
  move => Hab.
  rewrite /DDModels.Fast2Sum/fst/snd.
  move => Hfin.
  destruct (BPLUS_finite_e t a b Hfin) as [Hfina  Hfinb].
  have Hfinlt : Rabs (FT2R a) < Omega by (apply is_finite_no_overflow).
  suff: is_finite (BMINUS (BPLUS a b) a) = true.
  -
  move => Hfin1.
  suff: Rabs (rnd (FT2R b - FT2R (BMINUS (BPLUS a b) a))) < Omega.
  +
  move => Hbnd.
  rewrite !is_finite_Binary in Hfin1, Hfinb.
  rewrite -!B2R_float_of_ftype in Hbnd.
  pose proof Binary.Bminus_correct (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t)
  (plus_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE
  (float_of_ftype b) (float_of_ftype (BMINUS (BPLUS a b) a)) Hfinb Hfin1 as Hc.
  apply Rlt_bool_true in Hbnd; rewrite Hbnd in Hc; clear Hbnd.
  destruct Hc as [_ [HB _]].
  move: HB; rewrite /BMINUS/BINOP !is_finite_Binary !float_of_ftype_of_float => //.
  +
  suff: Rabs (rnd (FT2R (BPLUS a b) - FT2R a)) < Omega; [|apply (is_finite_minus_no_overflow t) => //].
  move => Hbnd.
  rewrite -BMINUS_round_correct; [|apply no_overflow_minus_is_finite => //].
  suff: (Fast2Sum_correct_flt radix2 emin (fprec t) choice (FT2R a) (FT2R b));
  [|apply F2Sum_correct_abs_flt; FLT_basics => //=].
  rewrite /Fast2Sum_correct_flt/fst/snd/Fast2Sum_flt; move => H2sflt.
  rewrite -BPLUS_round_correct => //.
  rewrite H2sflt; clear H2sflt.
  rewrite -Ropp_minus_distr Rabs_Ropp.
  eapply Rle_lt_trans.
  apply Plus_error.plus_error_le_l; FLT_basics.
  exact Hfinlt.
  - apply is_finite_2Sum_a => //.
Qed.

(* Same finiteness result as is_finite_FastSum, but under the Fast2Sum_cond
   disjunction (ulp ordering ulp b <= ulp a, or a = 0) instead of the magnitude
   ordering |b| <= |a|.  This is exactly the shape DWPlusDW_vh_w_disjunction (and
   Fast2Sum_cond) produce, so it can be forwarded directly.  The chain mirrors
   is_finite_FastSum: no_overflow_2Sum_a_ulp for the no-overflow steps and
   F2Sum_correct_ulp_flt for the error-term correctness. *)
Lemma is_finite_FastSum_ulp (a b : ftype t):
  ulp (FT2R b) <= ulp (FT2R a) \/ FT2R a = 0 ->
  is_finite (BPLUS a b) = true -> is_finite (snd (DDModels.Fast2Sum a b)) = true .
Proof.
  move => Hab.
  rewrite /DDModels.Fast2Sum/fst/snd.
  move => Hfin.
  destruct (BPLUS_finite_e t a b Hfin) as [Hfina  Hfinb].
  have Hfinlt : Rabs (FT2R a) < Omega by (apply is_finite_no_overflow).
  suff: is_finite (BMINUS (BPLUS a b) a) = true.
  -
  move => Hfin1.
  suff: Rabs (rnd (FT2R b - FT2R (BMINUS (BPLUS a b) a))) < Omega.
  +
  move => Hbnd.
  rewrite !is_finite_Binary in Hfin1, Hfinb.
  rewrite -!B2R_float_of_ftype in Hbnd.
  pose proof Binary.Bminus_correct (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t)
  (plus_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE
  (float_of_ftype b) (float_of_ftype (BMINUS (BPLUS a b) a)) Hfinb Hfin1 as Hc.
  apply Rlt_bool_true in Hbnd; rewrite Hbnd in Hc; clear Hbnd.
  destruct Hc as [_ [HB _]].
  move: HB; rewrite /BMINUS/BINOP !is_finite_Binary !float_of_ftype_of_float => //.
  +
  suff: Rabs (rnd (FT2R (BPLUS a b) - FT2R a)) < Omega; [|apply (is_finite_minus_no_overflow t) => //].
  move => Hbnd.
  rewrite -BMINUS_round_correct; [|apply no_overflow_minus_is_finite => //].
  suff: (Fast2Sum_correct_flt radix2 emin (fprec t) choice (FT2R a) (FT2R b));
  [|apply F2Sum_correct_ulp_flt; first [ exact Hab | FLT_basics => // ]].
  rewrite /Fast2Sum_correct_flt/fst/snd/Fast2Sum_flt; move => H2sflt.
  rewrite -BPLUS_round_correct => //.
  rewrite H2sflt; clear H2sflt.
  rewrite -Ropp_minus_distr Rabs_Ropp.
  eapply Rle_lt_trans.
  apply Plus_error.plus_error_le_l; FLT_basics.
  exact Hfinlt.
  -
  suff: Rabs (rnd (FT2R (BPLUS a b) - FT2R a)) < Omega.
  --
  move => Hbnd.
  rewrite !is_finite_Binary in Hfin, Hfina.
  rewrite -!B2R_float_of_ftype in Hbnd.
  pose proof Binary.Bminus_correct (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t)
  (plus_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE
  (float_of_ftype (BPLUS a b)) (float_of_ftype a) Hfin Hfina as Hc.
  apply Rlt_bool_true in Hbnd; rewrite Hbnd in Hc; clear Hbnd.
  destruct Hc as [_ [HB _]].
  move: HB; rewrite /BMINUS/BINOP !is_finite_Binary !float_of_ftype_of_float => //.
  --
  apply no_overflow_2Sum_a_ulp => //.
Qed.

(* Same finiteness result as is_finite_FastSum / is_finite_FastSum_ulp, but from
   pure magnitude headroom on the second argument instead of from an ordering.
   |b| <= Omega/4 is enough for BOTH Fast2Sum steps:

     z = BMINUS s a : |rnd (s - a)| <= Omega/2      (round_2Sum_a_bnd_small)
     t = BMINUS b z : |b - z| <= Omega/4 + Omega/2 = 3/4 Omega, so
                      |rnd (b - z)| <= 3/4 Omega + Omega/8 = 7/8 Omega < Omega.

   Unlike its two siblings this route says nothing about the VALUE of the error
   term -- Fast2Sum need not be exact here -- only that it is finite.  That is
   exactly what is wanted in the Fast2Mult underflow gap, where the closing
   Fast2Sum of DWTimesFP3 may be unordered: the value is then recovered
   separately from the shared FLT/FIX lattice (see
   DWMulFP_acc.Fast2Sum_sum_exact_of_sum_small). *)
Lemma is_finite_FastSum_small (a b : ftype t):
  Rabs (FT2R b) <= /4 * Omega ->
  is_finite (BPLUS a b) = true ->
  is_finite (snd (DDModels.Fast2Sum a b)) = true .
Proof.
  move => Hb Hfin.
  rewrite /DDModels.Fast2Sum/fst/snd.
  destruct (BPLUS_finite_e t a b Hfin) as [Hfina Hfinb].
  have HO  : 0 < Omega by apply bpow_gt_0.
  have HB0 : 0 < bpow radix2 (femax t - fprec t) by apply bpow_gt_0.
  have HB4 := @bpow_femax_fprec_le_quarter_Omega t.
  (* first step: z = BMINUS s a is finite, with |z| <= Omega/2 *)
  have Hstep1 := round_2Sum_a_bnd_small a b Hb Hfin.
  have Hfinz : is_finite (BMINUS (BPLUS a b) a) = true.
  { apply no_overflow_minus_is_finite => //. unfold Bminus_no_overflow. lra. }
  have Hzb : Rabs (FT2R (BMINUS (BPLUS a b) a)) <= /2 * Omega
    by (rewrite -BMINUS_round_correct //; exact Hstep1).
  (* second step: |b - z| <= 3/4 Omega, so its rounding stays below Omega *)
  have Hd : Rabs (FT2R b - FT2R (BMINUS (BPLUS a b) a)) <= /4 * Omega + /2 * Omega.
  { replace (FT2R b - FT2R (BMINUS (BPLUS a b) a))%R
      with (FT2R b + - FT2R (BMINUS (BPLUS a b) a))%R by ring.
    eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_Ropp. lra. }
  have Hnov2 : Rabs (rnd (FT2R b - FT2R (BMINUS (BPLUS a b) a))) < Omega.
  { eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
    have Hu : ulp (FT2R b - FT2R (BMINUS (BPLUS a b) a))
              <= bpow radix2 (femax t - fprec t)
      by (apply ulp_below_overflow; lra).
    lra. }
  apply no_overflow_minus_is_finite => //.
Qed.

Lemma is_finite_2Sum_b (a b : ftype t):
  is_finite (BMINUS a b) = true ->
  is_finite (BPLUS a b) = true ->
  is_finite (BMINUS (BPLUS a b) b) = true.
Proof.
  move=> Hfin1 Hfin2.
  apply no_overflow_minus_is_finite => //.
  destruct (BPLUS_finite_e t a b Hfin2) as [_  Hfinb] => //.
  apply no_overflow_2Sum_b => //.
Qed.

Lemma is_finite_2Sum_right_aux (a b : ftype t):
  is_finite (BMINUS a b) = true ->
  is_finite (BPLUS a b) = true ->
  Rabs (FT2R b) < pred radix2 fexp Omega ->
  Rabs (rnd (FT2R (BPLUS a b) - FT2R (BMINUS (BPLUS a b) b))) < Omega.
Proof.
  move => Hfin_minus Hfin_plus HbFmax.
  have Ha'_fin : is_finite (BMINUS (BPLUS a b) b) = true by
    apply is_finite_2Sum_b => //.
  have Habov_plus : Rabs (FT2R (BPLUS a b)) < Omega by
    rewrite -BPLUS_round_correct //;
    apply (@is_finite_sum_no_overflow t NANS STD a b Hfin_plus).
  have Habov_minus : Rabs (FT2R (BMINUS a b)) < Omega by
    rewrite -BMINUS_round_correct //;
    apply (@is_finite_minus_no_overflow t NANS STD a b Hfin_minus).
  destruct (BPLUS_finite_e t a b Hfin_plus) as [Hfina Hfinb].
  have Hfinlta : Rabs (FT2R a) < Omega by apply is_finite_no_overflow.
  have Hfinltb : Rabs (FT2R b) < Omega by apply is_finite_no_overflow.
  (* pred(Omega) setup — Valid_exp fexp must be discharged explicitly *)
  have HOmega_ne0 : Omega <> 0 by apply Rgt_not_eq, bpow_gt_0.
  have HpredO_lt : pred radix2 fexp Omega < Omega.
  { apply Ulp.pred_lt_id;
    try (apply FLT.FLT_exp_valid; apply fprec_gt_0); exact HOmega_ne0. }
  have HFOmega : generic_format radix2 fexp Omega.
  { apply Generic_fmt.generic_format_bpow.
    unfold SpecFloat.fexp, SpecFloat.emin.
    pose proof fprec_lb t; pose proof femax_lb t; lia. }
  have HFpredO : generic_format radix2 fexp (pred radix2 fexp Omega).
  { apply Ulp.generic_format_pred;
    try (apply FLT.FLT_exp_valid; apply fprec_gt_0); exact HFOmega. }
  have HFb_abs : generic_format radix2 fexp (Rabs (FT2R b)).
  { apply Generic_fmt.generic_format_abs.
    rewrite -B2R_float_of_ftype; apply Binary.generic_format_B2R. }
  have Hsucc_le : Ulp.succ radix2 fexp (Rabs (FT2R b)) <= pred radix2 fexp Omega.
  { apply Ulp.succ_le_lt;
    try (apply FLT.FLT_exp_valid; apply fprec_gt_0);
    try exact HFb_abs; try exact HFpredO; exact HbFmax. }
  have Hsucc_eq : Ulp.succ radix2 fexp (Rabs (FT2R b)) =
                  Rabs (FT2R b) + ulp (Rabs (FT2R b)).
  { apply Ulp.succ_eq_pos;
    try (apply FLT.FLT_exp_valid; apply fprec_gt_0); apply Rabs_pos. }
  (* Case split on sign of a, then sign of b *)
  destruct (Rle_dec 0 (FT2R a)) as [Hapos | Haneg].
  - destruct (Rle_dec 0 (FT2R b)) as [Hbpos | Hbneg].
    + (* Case a >= 0, b >= 0: sandwich 0 <= v <= s *)
      suff: 0 <= FT2R (BPLUS a b) - FT2R (BMINUS (BPLUS a b) b) <=
            FT2R (BPLUS a b).
      { move => [Hlo Hhi].
        apply (round_le radix2 fexp
          (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)) in Hlo, Hhi.
        apply Rabs_lt; split.
        - rewrite round_0 in Hlo.
          apply (Rlt_le_trans _ 0); [| apply Hlo].
          apply Ropp_lt_gt_0_contravar, bpow_gt_0.
        - apply (Rle_lt_trans _ (rnd (FT2R (BPLUS a b)))); [apply Hhi |].
          rewrite round_generic; [apply Rabs_def2 => // | FLT_basics]. }
      split.
      * have H1 : FT2R (BMINUS (BPLUS a b) b) <= FT2R (BPLUS a b).
        { rewrite -BMINUS_round_correct => //.
          eapply Rle_trans with
            (round Zaux.radix2 fexp (Znearest choice) (FT2R (BPLUS a b))).
          - apply round_le; FLT_basics; lra.
          - rewrite round_generic; [lra | FLT_basics]. }
        lra.
      * have Hge : FT2R b <= FT2R (BPLUS a b).
        { rewrite -BPLUS_round_correct => //.
          eapply Rle_trans with
            (round Zaux.radix2 fexp (Znearest choice) (FT2R b)).
          - rewrite round_generic; [lra | FLT_basics].
          - apply round_le; FLT_basics; lra. }
        have H1 : 0 <= FT2R (BMINUS (BPLUS a b) b).
        { rewrite -BMINUS_round_correct => //.
          eapply Rle_trans with (round Zaux.radix2 fexp (Znearest choice) 0).
          - rewrite round_0; lra.
          - apply round_le; FLT_basics; lra. }
        lra.
    + (* Case a >= 0, b < 0 *)
      move/Rnot_le_lt: Hbneg => Hbneg.
      destruct (Rle_dec (Rabs (FT2R b)) (Rabs (FT2R a))) as [Hba | Hba].
      * (* |b| <= |a|: sandwich -fl(a-b) <= v <= 0 *)
        have HbA : Rabs (FT2R b) = -FT2R b by (apply Rabs_left; lra).
        have HaA : Rabs (FT2R a) = FT2R a by (apply Rabs_pos_eq; lra).
        (* s >= 0: a >= |b|, a+b >= 0 *)
        have Hs_ge_0 : 0 <= FT2R (BPLUS a b).
        { rewrite -BPLUS_round_correct => //.
          eapply Rle_trans with (round radix2 fexp (Znearest choice) 0).
          - rewrite round_0; lra.
          - apply round_le; FLT_basics; lra. }
        (* s <= a: b <= 0 *)
        have Hs_le_a : FT2R (BPLUS a b) <= FT2R a.
        { rewrite -BPLUS_round_correct => //.
          eapply Rle_trans with (round radix2 fexp (Znearest choice) (FT2R a)).
          - apply round_le; FLT_basics; lra.
          - rewrite round_generic; [lra | FLT_basics]. }
        (* a' >= s: sb = s-b >= s since b < 0 *)
        have Ha'_ge_s : FT2R (BPLUS a b) <= FT2R (BMINUS (BPLUS a b) b).
        { rewrite -BMINUS_round_correct => //.
          eapply Rle_trans with
            (round radix2 fexp (Znearest choice) (FT2R (BPLUS a b))).
          - rewrite round_generic; [lra | FLT_basics].
          - apply round_le; FLT_basics; lra. }
        (* a' <= fl(a-b): s <= a so s-b <= a-b *)
        have Ha'_le : FT2R (BMINUS (BPLUS a b) b) <= FT2R (BMINUS a b).
        { rewrite -BMINUS_round_correct => //.
          rewrite -(BMINUS_round_correct _ _ _ Hfin_minus).
          apply round_le; FLT_basics; lra. }
        suff: - FT2R (BMINUS a b) <=
              FT2R (BPLUS a b) - FT2R (BMINUS (BPLUS a b) b) <= 0.
        { move => [Hlo Hhi].
          apply (round_le radix2 fexp
            (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)) in Hlo, Hhi.
          apply Rabs_lt; split.
          - apply (Rlt_le_trans _ (rnd (- FT2R (BMINUS a b)))).
            + rewrite round_generic.
              * apply Ropp_lt_contravar.
                apply (Rle_lt_trans _ (Rabs (FT2R (BMINUS a b)))).
                -- apply Rle_abs.
                -- exact Habov_minus.
              * apply generic_format_opp; FLT_basics.
            + exact Hlo.
          - rewrite round_0 in Hhi.
            exact (Rle_lt_trans _ 0 _ Hhi (bpow_gt_0 radix2 (femax t))). }
        split; lra.
      * (* |a| < |b|: epsilon bound *)
        apply Rnot_le_lt in Hba.
        have HbA : Rabs (FT2R b) = -FT2R b by (apply Rabs_left; lra).
        have HaA : Rabs (FT2R a) = FT2R a by (apply Rabs_pos_eq; lra).
        (* s <= 0: |a| < |b|, a+b < 0 *)
        have Hs_le_0 : FT2R (BPLUS a b) <= 0.
        { rewrite -BPLUS_round_correct => //.
          eapply Rle_trans with (round radix2 fexp (Znearest choice) 0).
          - apply round_le; FLT_basics; lra.
          - rewrite round_0; lra. }
        (* s >= b: a >= 0 *)
        have Hs_ge_b : FT2R b <= FT2R (BPLUS a b).
        { rewrite -BPLUS_round_correct => //.
          eapply Rle_trans with (round radix2 fexp (Znearest choice) (FT2R b)).
          - rewrite round_generic; [lra | FLT_basics].
          - apply round_le; FLT_basics; lra. }
        (* sb = s - b in [0, Rabs(FT2R b)] *)
        have Hsb_pos : 0 <= FT2R (BPLUS a b) - FT2R b by lra.
        have Hsb_le : FT2R (BPLUS a b) - FT2R b <= Rabs (FT2R b) by lra.
        (* a' = round(sb); rounding error bound *)
        have Ha'_eq : FT2R (BMINUS (BPLUS a b) b) =
                      round radix2 fexp (Znearest choice)
                        (FT2R (BPLUS a b) - FT2R b)
          by (symmetry; apply BMINUS_round_correct => //).
        have Herr1 : Rabs (round radix2 fexp (Znearest choice)
                             (FT2R (BPLUS a b) - FT2R b) -
                           (FT2R (BPLUS a b) - FT2R b)) <=
                     /2 * ulp (FT2R (BPLUS a b) - FT2R b).
        { apply Ulp.error_le_half_ulp;
          try (apply FLT.FLT_exp_valid; apply fprec_gt_0);
          apply Generic_fmt.valid_rnd_N. }
        have Hulp_le1 : ulp (FT2R (BPLUS a b) - FT2R b) <= ulp (Rabs (FT2R b)).
        { apply Ulp.ulp_le_pos; FLT_basics; [exact Hsb_pos | exact Hsb_le]. }
        (* a' >= 0: sb >= 0 so round(sb) >= 0 *)
        have Ha'_ge_0 : 0 <= FT2R (BMINUS (BPLUS a b) b).
        { rewrite Ha'_eq.
          eapply Rle_trans with (round radix2 fexp (Znearest choice) 0).
          - rewrite round_0; lra.
          - apply round_le; FLT_basics; lra. }
        have Hv_le_0 : FT2R (BPLUS a b) - FT2R (BMINUS (BPLUS a b) b) <= 0 by lra.
        (* |v| = -v = round(sb) - FT2R(BPLUS a b)
               = (sb + err) - (sb + FT2R b) = -FT2R b + err <= Rabs(FT2R b) + ulp(|b|) *)
        have Habs_v1 : Rabs (FT2R (BPLUS a b) - FT2R (BMINUS (BPLUS a b) b)) <=
                       pred radix2 fexp Omega.
        { have Hulp_nn : 0 <= ulp (Rabs (FT2R b)) by apply Ulp.ulp_ge_0.
          have Hsucc_bd : Rabs (FT2R b) + ulp (Rabs (FT2R b)) <= pred radix2 fexp Omega
            by (rewrite -Hsucc_eq; exact Hsucc_le).
          have Herr_le : round radix2 fexp (Znearest choice)
                           (FT2R (BPLUS a b) - FT2R b) -
                         (FT2R (BPLUS a b) - FT2R b) <= /2 * ulp (Rabs (FT2R b)).
          { apply (Rle_trans _ (Rabs (round radix2 fexp (Znearest choice)
                                        (FT2R (BPLUS a b) - FT2R b) -
                                      (FT2R (BPLUS a b) - FT2R b)))).
            - apply Rle_abs.
            - apply (Rle_trans _ (/2 * ulp (FT2R (BPLUS a b) - FT2R b))).
              + exact Herr1.
              + apply Rmult_le_compat_l; lra. }
          rewrite (Rabs_left1 _ Hv_le_0) Ha'_eq.
          lra. }
        apply (Rle_lt_trans _ (pred radix2 fexp Omega)).
        { apply Generic_fmt.abs_round_le_generic;
          try FLT_basics;
          try apply BinarySingleNaN.valid_rnd_round_mode;
          try exact HFpredO;
          exact Habs_v1. }
        exact HpredO_lt.
  - move/Rnot_le_lt: Haneg => Haneg.
    destruct (Rle_dec 0 (FT2R b)) as [Hbpos | Hbneg].
    + (* Case a < 0, b >= 0: symmetric to a >= 0, b < 0 *)
      destruct (Rle_dec (Rabs (FT2R b)) (Rabs (FT2R a))) as [Hba | Hba].
      * (* |b| <= |a|: sandwich 0 <= v <= -fl(a-b) *)
        have HbA : Rabs (FT2R b) = FT2R b by (apply Rabs_pos_eq; lra).
        have HaA : Rabs (FT2R a) = -FT2R a by (apply Rabs_left; lra).
        (* s <= 0: |b| <= |a|, a+b <= 0 *)
        have Hs_le_0 : FT2R (BPLUS a b) <= 0.
        { rewrite -BPLUS_round_correct => //.
          eapply Rle_trans with (round radix2 fexp (Znearest choice) 0).
          - apply round_le; FLT_basics; lra.
          - rewrite round_0; lra. }
        (* s >= a: b >= 0 *)
        have Hs_ge_a : FT2R a <= FT2R (BPLUS a b).
        { rewrite -BPLUS_round_correct => //.
          eapply Rle_trans with (round radix2 fexp (Znearest choice) (FT2R a)).
          - rewrite round_generic; [lra | FLT_basics].
          - apply round_le; FLT_basics; lra. }
        (* a' <= s: sb = s-b <= s since b >= 0 *)
        have Ha'_le_s : FT2R (BMINUS (BPLUS a b) b) <= FT2R (BPLUS a b).
        { rewrite -BMINUS_round_correct => //.
          eapply Rle_trans with
            (round radix2 fexp (Znearest choice) (FT2R (BPLUS a b))).
          - apply round_le; FLT_basics; lra.
          - rewrite round_generic; [lra | FLT_basics]. }
        (* a' >= fl(a-b): s >= a so s-b >= a-b *)
        have Ha'_ge : FT2R (BMINUS a b) <= FT2R (BMINUS (BPLUS a b) b).
        { rewrite -(BMINUS_round_correct _ _ _ Hfin_minus).
          rewrite -BMINUS_round_correct => //.
          apply round_le; FLT_basics; lra. }
        suff: 0 <=
              FT2R (BPLUS a b) - FT2R (BMINUS (BPLUS a b) b) <=
              - FT2R (BMINUS a b).
        { move => [Hlo Hhi].
          apply (round_le radix2 fexp
            (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)) in Hlo, Hhi.
          apply Rabs_lt; split.
          - rewrite round_0 in Hlo.
            apply (Rlt_le_trans _ 0); [| apply Hlo].
            apply Ropp_lt_gt_0_contravar, bpow_gt_0.
          - apply (Rle_lt_trans _ (rnd (- FT2R (BMINUS a b)))).
            + exact Hhi.
            + rewrite round_generic.
              * apply (Rle_lt_trans _ (Rabs (FT2R (BMINUS a b)))).
                -- rewrite <- Rabs_Ropp; apply Rle_abs.
                -- exact Habov_minus.
              * apply generic_format_opp; FLT_basics. }
        split; lra.
      * (* |a| < |b|: epsilon bound *)
        apply Rnot_le_lt in Hba.
        have HbA : Rabs (FT2R b) = FT2R b by (apply Rabs_pos_eq; lra).
        have HaA : Rabs (FT2R a) = -FT2R a by (apply Rabs_left; lra).
        (* s >= 0: |a| < |b|, a+b > 0 *)
        have Hs_ge_0 : 0 <= FT2R (BPLUS a b).
        { rewrite -BPLUS_round_correct => //.
          eapply Rle_trans with (round radix2 fexp (Znearest choice) 0).
          - rewrite round_0; lra.
          - apply round_le; FLT_basics; lra. }
        (* s <= b: a <= 0 *)
        have Hs_le_b : FT2R (BPLUS a b) <= FT2R b.
        { rewrite -BPLUS_round_correct => //.
          eapply Rle_trans with (round radix2 fexp (Znearest choice) (FT2R b)).
          - apply round_le; FLT_basics; lra.
          - rewrite round_generic; [lra | FLT_basics]. }
        (* sb = s - b in [-Rabs(FT2R b), 0] *)
        have Hsb_neg : FT2R (BPLUS a b) - FT2R b <= 0 by lra.
        have Hsb_abs : Rabs (FT2R (BPLUS a b) - FT2R b) <= Rabs (FT2R b).
        { rewrite (Rabs_left1 _ Hsb_neg) Rabs_pos_eq; lra. }
        have Ha'_eq2 : FT2R (BMINUS (BPLUS a b) b) =
                       round radix2 fexp (Znearest choice)
                         (FT2R (BPLUS a b) - FT2R b)
          by (symmetry; apply BMINUS_round_correct => //).
        have Herr2 : Rabs (round radix2 fexp (Znearest choice)
                             (FT2R (BPLUS a b) - FT2R b) -
                           (FT2R (BPLUS a b) - FT2R b)) <=
                     /2 * ulp (FT2R (BPLUS a b) - FT2R b).
        { apply Ulp.error_le_half_ulp;
          try (apply FLT.FLT_exp_valid; apply fprec_gt_0);
          apply Generic_fmt.valid_rnd_N. }
        have Hulp_le2 : ulp (FT2R (BPLUS a b) - FT2R b) <= ulp (Rabs (FT2R b)).
        { apply Ulp.ulp_le; FLT_basics;
          rewrite (Rabs_pos_eq _ (Rabs_pos _)); exact Hsb_abs. }
        have Heps2_neg : - (/2 * ulp (Rabs (FT2R b))) <=
                         round radix2 fexp (Znearest choice)
                           (FT2R (BPLUS a b) - FT2R b) -
                         (FT2R (BPLUS a b) - FT2R b).
        { apply (Rle_trans _ (- Rabs (round radix2 fexp (Znearest choice)
                                        (FT2R (BPLUS a b) - FT2R b) -
                                      (FT2R (BPLUS a b) - FT2R b)))).
          - have Hbd : Rabs (round radix2 fexp (Znearest choice)
                               (FT2R (BPLUS a b) - FT2R b) -
                             (FT2R (BPLUS a b) - FT2R b)) <=
                       /2 * ulp (Rabs (FT2R b)).
            { eapply Rle_trans; [exact Herr2 |].
              apply Rmult_le_compat_l; [lra | exact Hulp_le2]. }
            lra.
          - apply Ropp_le_cancel; rewrite Ropp_involutive;
            rewrite <- Rabs_Ropp; apply Rle_abs. }
        (* a' <= 0: sb <= 0 so round(sb) <= 0 *)
        have Ha'_le_0 : FT2R (BMINUS (BPLUS a b) b) <= 0.
        { rewrite Ha'_eq2.
          eapply Rle_trans with (round radix2 fexp (Znearest choice) 0).
          - apply round_le; FLT_basics; lra.
          - rewrite round_0; lra. }
        have Hv_ge_0 : 0 <= FT2R (BPLUS a b) - FT2R (BMINUS (BPLUS a b) b) by lra.
        (* |v| <= pred(Omega) via epsilon bound *)
        have Habs_v2 : Rabs (FT2R (BPLUS a b) - FT2R (BMINUS (BPLUS a b) b)) <=
                       pred radix2 fexp Omega.
        { rewrite (Rabs_pos_eq _ Hv_ge_0) Ha'_eq2.
          have Hulp_nn : 0 <= ulp (Rabs (FT2R b)) by apply Ulp.ulp_ge_0.
          have Hsucc_bd : Rabs (FT2R b) + ulp (Rabs (FT2R b)) <= pred radix2 fexp Omega
            by (rewrite -Hsucc_eq; exact Hsucc_le).
          lra. }
        apply (Rle_lt_trans _ (pred radix2 fexp Omega)).
        { apply Generic_fmt.abs_round_le_generic;
          try FLT_basics;
          try apply BinarySingleNaN.valid_rnd_round_mode;
          try exact HFpredO;
          exact Habs_v2. }
        exact HpredO_lt.
    + (* Case a < 0, b < 0: sandwich s <= v <= 0 *)
      move/Rnot_le_lt: Hbneg => Hbneg.
      suff: FT2R (BPLUS a b) <=
            FT2R (BPLUS a b) - FT2R (BMINUS (BPLUS a b) b) <= 0.
      { move => [Hlo Hhi].
        apply (round_le radix2 fexp
          (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)) in Hlo, Hhi.
        apply Rabs_lt; split.
        - apply (Rlt_le_trans _ (rnd (FT2R (BPLUS a b)))); [| apply Hlo].
          rewrite round_generic; [apply Rabs_def2 => // | FLT_basics].
        - rewrite round_0 in Hhi.
          apply (Rle_lt_trans _ 0); [apply Hhi |].
          apply bpow_gt_0. }
      split.
      * have Hb_rnd : round radix2 fexp (Znearest choice) (FT2R b) = FT2R b
          by apply round_generic; FLT_basics.
        have Hs_le_b : FT2R (BPLUS a b) <= FT2R b.
        { have Hle : round radix2 fexp (Znearest choice) (FT2R a + FT2R b) <=
                     round radix2 fexp (Znearest choice) (FT2R b)
            by (apply round_le; FLT_basics; lra).
          rewrite BPLUS_round_correct in Hle => //.
          rewrite Hb_rnd in Hle; lra. }
        have Ha'_le0 : round radix2 fexp (Znearest choice)
                         (FT2R (BPLUS a b) - FT2R b) <= 0.
        { have Hle : round radix2 fexp (Znearest choice) (FT2R (BPLUS a b) - FT2R b) <=
                     round radix2 fexp (Znearest choice) 0
            by (apply round_le; FLT_basics; lra).
          rewrite round_0 in Hle; lra. }
        have HB : FT2R (BMINUS (BPLUS a b) b) =
                  round radix2 fexp (Znearest choice) (FT2R (BPLUS a b) - FT2R b)
          by (symmetry; apply BMINUS_round_correct => //).
        lra.
      * have Hs_rnd : round radix2 fexp (Znearest choice)
                        (FT2R (BPLUS a b)) = FT2R (BPLUS a b)
          by apply round_generic; FLT_basics.
        have Hs_le_a' : round radix2 fexp (Znearest choice) (FT2R (BPLUS a b)) <=
                        round radix2 fexp (Znearest choice) (FT2R (BPLUS a b) - FT2R b)
          by (apply round_le; FLT_basics; lra).
        have HB : FT2R (BMINUS (BPLUS a b) b) =
                  round radix2 fexp (Znearest choice) (FT2R (BPLUS a b) - FT2R b)
          by (symmetry; apply BMINUS_round_correct => //).
        lra.
Qed.

Lemma is_finite_TwoSum (a b : ftype t):
  is_finite (BPLUS a b) = true ->
  is_finite (BMINUS a b) = true ->
  Rabs (FT2R b) < pred radix2 fexp Omega ->
  is_finite (TwoSumF_err a b) = true.
Proof.
move => Hfin_plus Hfin_minus HbFmax.
rewrite /TwoSumF_err /TwoSumF /snd.
destruct (BPLUS_finite_e t a b Hfin_plus) as [Hfina Hfinb].
set s  := BPLUS a b.
set a' := BMINUS s b.
set b' := BMINUS s a'.
set da := BMINUS a a'.
set db := BMINUS b b'.
(* a' is finite *)
have Ha'_fin : is_finite a' = true.
{ change a' with (BMINUS (BPLUS a b) b).
  apply is_finite_2Sum_b; [exact Hfin_minus | exact Hfin_plus]. }
(* b' is finite via is_finite_2Sum_right_aux *)
have Hb'_ov : Rabs (rnd (FT2R s - FT2R a')) < Omega.
{ change s with (BPLUS a b). change a' with (BMINUS (BPLUS a b) b).
  apply is_finite_2Sum_right_aux; [exact Hfin_minus | exact Hfin_plus | exact HbFmax]. }
have Hb'_fin : is_finite b' = true.
{ apply no_overflow_minus_is_finite.
  - change s with (BPLUS a b). exact Hfin_plus.
  - exact Ha'_fin.
  - exact Hb'_ov. }
(* ulp bound helper *)
have Hulp_le := ulp_le_top.
(* generic_format for bpow(femax t - fprec t) *)
have HFbp : generic_format radix2 fexp (bpow radix2 (femax t - fprec t)).
{ apply Generic_fmt.generic_format_bpow.
  unfold fexp, SpecFloat.fexp, SpecFloat.emin.
  apply Z.max_lub; pose proof femax_lb t; pose proof fprec_lb t; lia. }
(* generic_format for bpow(femax t - fprec t + 1) *)
have HFbp1 : generic_format radix2 fexp (bpow radix2 (femax t - fprec t + 1)).
{ apply Generic_fmt.generic_format_bpow.
  unfold fexp, SpecFloat.fexp, SpecFloat.emin.
  apply Z.max_lub; pose proof femax_lb t; pose proof fprec_lb t; lia. }
(* bpow(femax t - fprec t + 1) < Omega *)
have Hbp1_lt : bpow radix2 (femax t - fprec t + 1) < Omega.
{ apply bpow_lt; pose proof fprec_lb t; lia. }
(* ulp bounds for specific floats *)
have Hulp_s  : ulp (FT2R s)  <= bpow radix2 (femax t - fprec t).
{ change s with (BPLUS a b). apply Hulp_le; exact Hfin_plus. }
have Hulp_a' : ulp (FT2R a') <= bpow radix2 (femax t - fprec t).
{ apply Hulp_le; exact Ha'_fin. }
have Hulp_b' : ulp (FT2R b') <= bpow radix2 (femax t - fprec t).
{ apply Hulp_le; exact Hb'_fin. }
(* error bounds via error_le_half_ulp_round *)
have Heps1 : Rabs (FT2R s - (FT2R a + FT2R b)) <= /2 * ulp (FT2R s).
{ change s with (BPLUS a b). rewrite -BPLUS_round_correct => //.
  apply Ulp.error_le_half_ulp_round; FLT_basics. }
have Heps2 : Rabs (FT2R a' - (FT2R s - FT2R b)) <= /2 * ulp (FT2R a').
{ change a' with (BMINUS s b).
  rewrite -BMINUS_round_correct => //.
  apply Ulp.error_le_half_ulp_round; FLT_basics. }
have Heps3 : Rabs (FT2R b' - (FT2R s - FT2R a')) <= /2 * ulp (FT2R b').
{ change b' with (BMINUS s a').
  rewrite -BMINUS_round_correct => //.
  apply Ulp.error_le_half_ulp_round; FLT_basics. }
(* |a - a'| <= bpow(femax t - fprec t) *)
have Ha_a'_bnd : Rabs (FT2R a - FT2R a') <= bpow radix2 (femax t - fprec t).
{ have Halg : FT2R a - FT2R a' =
      -((FT2R s - (FT2R a + FT2R b)) + (FT2R a' - (FT2R s - FT2R b))) by ring.
  rewrite Halg Rabs_Ropp.
  apply (Rle_trans _ (Rabs (FT2R s - (FT2R a + FT2R b)) + Rabs (FT2R a' - (FT2R s - FT2R b)))).
  - apply Rabs_triang.
  - lra. }
(* da finite *)
have Hda_ov_lt : Rabs (rnd (FT2R a - FT2R a')) < Omega.
{ apply (Rle_lt_trans _ (bpow radix2 (femax t - fprec t))).
  - apply Generic_fmt.abs_round_le_generic;
    [FLT_basics | apply BinarySingleNaN.valid_rnd_round_mode | exact HFbp | exact Ha_a'_bnd].
  - apply bpow_lt; pose proof fprec_lb t; lia. }
have Hda_fin : is_finite da = true.
{ apply no_overflow_minus_is_finite;
  [exact Hfina | exact Ha'_fin | exact Hda_ov_lt]. }
(* |FT2R da| <= bpow(femax t - fprec t) *)
have Hda_bnd : Rabs (FT2R da) <= bpow radix2 (femax t - fprec t).
{ change da with (BMINUS a a'). rewrite -BMINUS_round_correct => //.
  apply Generic_fmt.abs_round_le_generic;
  [FLT_basics | apply valid_rnd_N | exact HFbp | exact Ha_a'_bnd]. }
(* |b - b'| <= bpow(femax t - fprec t) *)
have Hb_b'_bnd : Rabs (FT2R b - FT2R b') <= bpow radix2 (femax t - fprec t).
{ have Halg : FT2R b - FT2R b' =
      (FT2R a' - (FT2R s - FT2R b)) + (-(FT2R b' - (FT2R s - FT2R a'))) by ring.
  rewrite Halg.
  apply (Rle_trans _ (Rabs (FT2R a' - (FT2R s - FT2R b)) + Rabs (-(FT2R b' - (FT2R s - FT2R a'))))).
  - apply Rabs_triang.
  - rewrite Rabs_Ropp. lra. }
(* db finite *)
have Hdb_ov_lt : Rabs (rnd (FT2R b - FT2R b')) < Omega.
{ apply (Rle_lt_trans _ (bpow radix2 (femax t - fprec t))).
  - apply Generic_fmt.abs_round_le_generic;
    [FLT_basics | apply BinarySingleNaN.valid_rnd_round_mode | exact HFbp | exact Hb_b'_bnd].
  - apply bpow_lt; pose proof fprec_lb t; lia. }
have Hdb_fin : is_finite db = true.
{ apply no_overflow_minus_is_finite;
  [exact Hfinb | exact Hb'_fin | exact Hdb_ov_lt]. }
(* |FT2R db| <= bpow(femax t - fprec t) *)
have Hdb_bnd : Rabs (FT2R db) <= bpow radix2 (femax t - fprec t).
{ change db with (BMINUS b b'). rewrite -BMINUS_round_correct => //.
  apply Generic_fmt.abs_round_le_generic;
  [FLT_basics | apply valid_rnd_N | exact HFbp | exact Hb_b'_bnd]. }
(* BPLUS da db is finite *)
apply no_overflow_sum_is_finite; [exact Hda_fin | exact Hdb_fin |].
rewrite /Bplus_no_overflow.
apply (Rle_lt_trans _ (bpow radix2 (femax t - fprec t + 1))); [| exact Hbp1_lt].
apply Generic_fmt.abs_round_le_generic;
  [FLT_basics | apply BinarySingleNaN.valid_rnd_round_mode | exact HFbp1 |].
apply (Rle_trans _ (Rabs (FT2R da) + Rabs (FT2R db)));
  [apply Rabs_triang |].
have Hbp1 : bpow radix2 (femax t - fprec t + 1) =
            bpow radix2 (femax t - fprec t) + bpow radix2 (femax t - fprec t).
{ rewrite bpow_plus_1. simpl. lra. }
lra.
Qed.

(* ===================================================================== *)
(* 3. Real-arithmetic helper                                               *)
(* ===================================================================== *)

Theorem round_plus_ge_ulp :
  forall (x y : ftype t),
  rounded t (FT2R x + FT2R y) <> 0%R ->
  (ulp (FT2R x /IZR radix2) <= Rabs (rounded t (FT2R x + FT2R y)))%R.
Proof with auto with typeclass_instances.
intros.
have HGy: generic_format radix2 fexp (FT2R y) by
  rewrite -B2R_float_of_ftype; apply Binary.generic_format_B2R.
have HGx: generic_format radix2 fexp (FT2R x) by
  rewrite -B2R_float_of_ftype; apply Binary.generic_format_B2R.
case (Req_dec (FT2R x) 0); intros Zx.
{ rewrite Zx Rplus_0_l.
rewrite /rounded round_generic => //.
unfold Rdiv; rewrite Rmult_0_l.
rewrite HGy.
unfold F2R; simpl; rewrite Rabs_mult.
rewrite (Rabs_pos_eq (bpow radix2 _)); [ |apply bpow_ge_0].
case (Z.eq_dec (Ztrunc (scaled_mantissa radix2 fexp (FT2R y))) 0); intros Hm.
contradict H.
rewrite Zx HGy Hm; unfold F2R; simpl.
rewrite Rplus_0_l Rmult_0_l.
apply round_0...
apply Rle_trans with (1*bpow radix2 (cexp radix2 fexp (FT2R y)))%R.
rewrite Rmult_1_l.
rewrite -ulp_neq_0...
apply: ulp_ge_ulp_0.
intros K; apply Hm.
rewrite K scaled_mantissa_0.
apply Ztrunc_IZR.
apply Rmult_le_compat_r.
apply bpow_ge_0.
rewrite <- abs_IZR.
apply IZR_le.
apply (Zlt_le_succ 0).
by apply Z.abs_pos. }
destruct (Plus_error.round_plus_F2R radix2 fexp
 (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) (FT2R x) (FT2R y)
  HGx HGy Zx) as (m,Hm).
case (Z.eq_dec m 0); intros Zm.
contradict H.
rewrite /rounded  Hm Zm.
apply F2R_0.
rewrite /rounded Hm -F2R_Zabs.
rewrite ulp_neq_0.
rewrite -(Rmult_1_l (bpow radix2 _)).
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply IZR_le.
apply (Zlt_le_succ 0).
now apply Z.abs_pos.
apply Rmult_integral_contrapositive_currified with (1 := Zx).
apply Rinv_neq_0_compat.
apply Rgt_not_eq, radix_pos.
Qed.

(* ===================================================================== *)
(* 4. Correctness & equivalence                                            *)
(* ===================================================================== *)

Lemma TwoSumF_eq (xh y: ftype t):
FT2R xh + FT2R y = 0 ->
is_finite_p (TwoSumF xh y) ->
F2Rp (TwoSumF xh y) = (0,0).
Proof.
move => H. rewrite /F2Rp/TwoSumF/is_finite_p/fst/snd.
move => [] FIN1 FIN2.
set (a:= (BMINUS xh (BMINUS (BPLUS xh y) y))) in *.
set (b:= (BMINUS y (BMINUS (BPLUS xh y) (BMINUS (BPLUS xh y) y)))) in *.
BPLUS_correct t a b.
clear H5; subst a b.
set (c:= (BMINUS (BPLUS xh y) y)) in *.
rewrite -is_finite_Binary in H3.
BMINUS_correct t xh c. clear H7; subst c.
set (d:= (BMINUS (BPLUS xh y) (BMINUS (BPLUS xh y) y))) in *.
rewrite -is_finite_Binary in H4.
rewrite !B2R_float_of_ftype.
BMINUS_correct t y d; clear H9; subst d.
set (a:= BPLUS xh y) in *.
set (b:= (BMINUS a y)) in *.
rewrite -is_finite_Binary in H8.
BMINUS_correct t a b; clear H11; subst b.
rewrite -is_finite_Binary in H10.
rewrite !B2R_float_of_ftype.
BMINUS_correct t a y; clear H13; subst a.
rewrite -is_finite_Binary in H11.
rewrite !B2R_float_of_ftype.
BPLUS_correct t xh y; clear H15.
rewrite H round_0
  !Rminus_0_l round_NE_opp Ropp_involutive.
f_equal.
rewrite -(round_0 radix2 fexp
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)).
f_equal.
apply Rplus_opp_r_uniq in H.
rewrite !B2R_float_of_ftype.
rewrite H !round_NE_opp Ropp_involutive.
rewrite -Rcomplements.Ropp_plus_minus_distr
  round_NE_opp !Rplus_opp .
apply Rminus_diag_eq; f_equal.
symmetry; rewrite round_generic => //.
apply generic_format_round.
apply Binary.fexp_correct, fprec_gt_0.
apply valid_rnd_N.
Qed.

Variables (a b : ftype t).

Hypothesis (FIN : is_finite_p (TwoSumF a b)).

Theorem TwoSumF_correct :
  FT2R (TwoSumF_err a b) = FT2R a + FT2R b - FT2R (TwoSumF_sum a b).
Proof.
have FINs : is_finite (BPLUS a b) = true := proj1 FIN.
have FINd : is_finite (TwoSumF_err a b) = true := proj2 FIN.
set (s  := BPLUS a b).
set (a' := BMINUS s b).
set (b' := BMINUS s a').
set (da := BMINUS a a').
set (db := BMINUS b b').
(* use TwoSum correct from Flocq, not double-double paper *)
have Hc := @Flocq.Pff.Pff2Flocq.TwoSum_correct emin (fprec t) choice
    (fprec_gt_one t) emin_le_0 choiceP (FT2R b) (FT2R a).
rewrite Rplus_comm; rewrite <- Hc; clear Hc; rewrite_format.
(* algebra *)
rewrite <- Rplus_opp, Rplus_comm, <- Rplus_assoc.
replace (FT2R b + FT2R a) with (FT2R a + FT2R b) by nra.
(* rewrites from correctness theorems *)
unfold TwoSumF_err, TwoSumF_sum, TwoSumF, fst, snd in *.
BPLUS_correct t a b; rewrite !B2R_float_of_ftype; field_simplify.
fold s a' b' da db in FINd; fold s a' b' da db.
BPLUS_correct t da db.
rewrite Rplus_comm; repeat f_equal.
{ subst db; rewrite -is_finite_Binary in H6.
  BMINUS_correct t b b'.
  subst b' s; rewrite -is_finite_Binary in H9.
  BMINUS_correct t (BPLUS a b) a'.
  unfold BPLUS, BINOP. rewrite FT2R_ftype_of_float H4.
  repeat f_equal; try rewrite B2R_float_of_ftype => //.
  subst a'; rewrite -is_finite_Binary in H12.
  BMINUS_correct t (BPLUS a b) b.
  unfold BPLUS, BINOP. rewrite FT2R_ftype_of_float H4.
  repeat f_equal; try rewrite B2R_float_of_ftype => //. }
{ subst da; rewrite -is_finite_Binary in H5.
  BMINUS_correct t a a'.
  subst a' s; rewrite -is_finite_Binary in H9.
  BMINUS_correct t (BPLUS a b) b.
  unfold BPLUS, BINOP. rewrite FT2R_ftype_of_float H4.
  repeat f_equal; try rewrite B2R_float_of_ftype => //. }
all: rewrite -B2R_float_of_ftype; apply Binary.generic_format_B2R.
Qed.

Theorem TwoSumF_error :
  exists del,
  FT2R (TwoSumF_err a b) = (FT2R a + FT2R b) * del /\
  Rabs del <= /2 * bpow radix2(-fprec t + 1).
Proof.
have FINs : is_finite (BPLUS a b) = true := proj1 FIN.
rewrite TwoSumF_correct.
rewrite /TwoSumF_sum/TwoSumF/fst/snd.
destruct (BPLUS_accurate' t a b FINs) as (del & A & B).
rewrite B; exists (-del); split; [field_simplify; nra|].
rewrite Rabs_Ropp.
refine (Rle_trans _ _ _ A _ ).
now apply Req_le; rewrite /default_rel.
Qed.

Theorem TwoSum_is_DW:
  double_word (TwoSumF_sum a b) (TwoSumF_err a b).
Proof.
  rewrite /double_word TwoSumF_correct // /TwoSumF_sum /= /common.rounded.
have FINm : is_finite (BPLUS a b) = true := proj1 FIN.
unfold TwoSumF_err, TwoSumF_sum, TwoSumF, fst, snd in *.
  BPLUS_correct t a b.
by rewrite !B2R_float_of_ftype.
Qed.

Lemma TwoSumEq_no_underflow
(HU1 : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R a + FT2R b)):
TwoSum (fprec t) choice (FT2R a) (FT2R b) = F2Rp (TwoSumF a b).
Proof.
move : FIN. move => [].
pose proof round_FLT_FLX radix2 emin.
have Heq1 : TwoSum (fprec t) choice (FT2R a) (FT2R b) =
  (TwoSum_sum (fprec t) choice (FT2R a) (FT2R b), TwoSum_err (fprec t) choice (FT2R a) (FT2R b)).
{ simpl; auto. }
rewrite Heq1.
have Heq2 : TwoSumF a b =
  (TwoSumF_sum a b, TwoSumF_err a b).
{ simpl; auto. }
rewrite Heq2 /F2Rp.
clear Heq1 Heq2.
move => FIN1 FIN2 /=.
have Heq :
TwoSum_sum (fprec t) choice (FT2R a) (FT2R b) = FT2R (TwoSumF_sum a b).
{ move: FIN1. rewrite /TwoSum_sum/TwoSumF_sum/F2Rp/fst/snd/=. move => FIN1.
BPLUS_correct t a b; field_simplify. rewrite H => //. rewrite !B2R_float_of_ftype => //. }
f_equal => //.
rewrite TwoSumF_correct DWPlus.TwoSum_correct => //. f_equal => //.
apply fprec_gt_one.
all: (apply ( @generic_format_FLX_FLT radix2 emin);
rewrite -B2R_float_of_ftype;
apply Binary.generic_format_B2R).
Qed.

(* results of FLT and FLX algorithms are equal regardless of underflow *)
Lemma TwoSumEq_FLT :
TwoSum (fprec t) choice (FT2R a) (FT2R b) = F2Rp (TwoSumF a b).
Proof.
destruct FIN as (FINA & FINB).
rewrite /TwoSumF_err/TwoSumF/snd in FINB.
rewrite /TwoSumF/TwoSum/F2Rp/fst/snd.
destruct (Rlt_or_le (Rabs (FT2R a + FT2R b)) (bpow radix2 (emin + fprec t - 1)) ) as
   [BND | BND].
{ have A : generic_format radix2 (FLT_exp emin (fprec t)) (FT2R a + FT2R b).
  { apply Plus_error.FLT_format_plus_small;
    try rewrite -B2R_float_of_ftype;
    try apply (Binary.generic_format_B2R (fprec t) (femax t)).
    apply (fprec_gt_0 t). apply Rlt_le.
    try rewrite -FT2R_ftype_of_float ftype_of_float_of_ftype.
    refine (Rlt_le_trans _ _ _ BND _).
    apply bpow_le; fold emin; lia. }
rewrite !(BPLUS_UF_exact t a b) => //. f_equal.
rewrite round_generic => //.
by apply (generic_format_FLX_FLT _ emin).
set (f1:= (BMINUS a (BMINUS (BPLUS a b) b))) in *.
set (f2:= (BMINUS b (BMINUS (BPLUS a b)
  (BMINUS (BPLUS a b) b)))) in *.
BPLUS_correct t f1 f2; subst f1 f2; clear H4.
set (f3:= (BMINUS (BPLUS a b) b)) in *.
rewrite -is_finite_Binary in H2.
BMINUS_correct t a f3; subst f3; clear H6.
set (f4:= (BPLUS a b)) in *.
rewrite -is_finite_Binary in H5.
BMINUS_correct t f4 b; subst f4; clear H8.
set (f5:= (BMINUS (BPLUS a b)
  (BMINUS (BPLUS a b) b))) in *.
rewrite -is_finite_Binary in H3.
 rewrite -!FT2R_ftype_of_float !ftype_of_float_of_ftype.
BMINUS_correct t b f5; subst f5; clear H10.
set (f4:= (BPLUS a b)) in *.
set (f6:= (BMINUS f4 b)) in *.
rewrite -is_finite_Binary in H9.
BMINUS_correct t f4 f6; subst f6; clear H12.
rewrite -is_finite_Binary in H11.
BMINUS_correct t f4 b; subst f4; clear H14.
 rewrite -!FT2R_ftype_of_float !ftype_of_float_of_ftype.
rewrite !(BPLUS_UF_exact t a b) => //.
rewrite -!B2R_float_of_ftype.
rewrite -!B2R_float_of_ftype in A.
rewrite !round_generic => //;
match goal with |- context [generic_format _ _ ?A] =>
    try field_simplify A end;
(try apply: Binary.generic_format_B2R;
try apply (generic_format_FLX_FLT _ emin);
try apply: Binary.generic_format_B2R;
try apply: generic_format_0) => //. }
by apply TwoSumEq_no_underflow.
Qed.

End TwoSumCorrect.
