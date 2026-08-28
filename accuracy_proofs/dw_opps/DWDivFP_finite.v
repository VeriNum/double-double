(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Precision-independent finiteness of [DWDivFP3] under the public safe-input
    bounds.  The normal and subnormal quotient ranges are proved separately. *)

Require Import vcfloat.VCFloat.
Require Import common float_acc_lems op_defs DDModels DDConds DWord_defs FLT_helpers.
Require Import DW_acc_lemmas.
Require Import DD.accuracy_proofs.dw_opps.DWDivFP_relative_acc.
Require Import DD.accuracy_proofs.basic_blocks.Fast2Mult_acc.
Require Import DD.accuracy_proofs.basic_blocks.TwoSum_acc_helpers.
From Flocq Require Import Pff2Flocq Core Relative Mult_error Div_sqrt_error FLT Sterbenz Plus_error.
Require Import mathcomp.ssreflect.ssreflect.

Set Bullet Behavior "Strict Subproofs".

Section DWDivFPFinite.
Context {NANS : Nans} {t : type} {STD : is_standard t}.

Notation emin := (@common.emin t).
Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Notation Omega := (bpow radix2 (femax t)).
Notation u := (bpow radix2 (- fprec t)).
Notation ulp := (Ulp.ulp radix2 fexp).

Local Instance valid_fexp_finite : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.

Local Lemma Omega_ge_8 : 8 <= Omega.
Proof.
have -> : (8 = bpow radix2 3)%R by reflexivity.
apply bpow_le. pose proof (fprec_lb t). pose proof (fprec_lt_femax t). lia.
Qed.

Local Lemma u_le_quarter : u <= /4.
Proof.
have -> : (/4 = bpow radix2 (-2))%R by (simpl; lra).
apply bpow_le. pose proof (fprec_lb t). lia.
Qed.

Local Lemma eta_le_Omega_32 : bpow radix2 emin <= /32 * Omega.
Proof.
have He : emin = (3 - femax t - fprec t)%Z by
  (unfold common.emin, SpecFloat.emin; lia).
rewrite He.
have -> : (/32 * Omega = bpow radix2 (femax t - 5))%R.
{ have -> : (/32:R) = bpow radix2 (-5) by (simpl; lra).
  rewrite -bpow_plus. f_equal; lia. }
apply bpow_le. pose proof (fprec_lb t). pose proof (fprec_lt_femax t). lia.
Qed.

Local Lemma half_ulp_below_half (v : R) :
  Rabs v < /2 * Omega -> /2 * ulp v <= /16 * Omega.
Proof.
move => Hv.
have Hhalf : /2 * Omega = bpow radix2 (femax t - 1).
{ have -> : (/2:R) = bpow radix2 (-1) by (simpl; lra).
  rewrite -bpow_plus. f_equal; lia. }
have Hu : ulp v <= bpow radix2 (femax t - 1 - fprec t).
{ destruct (Req_dec v 0) as [-> | Hv0].
  - change (ulp 0) with
      (Ulp.ulp radix2 (FLT.FLT_exp (3 - femax t - fprec t) (fprec t)) 0).
    rewrite FLT.ulp_FLT_0. apply bpow_le.
    pose proof (fprec_lb t). pose proof (fprec_lt_femax t). lia.
  - rewrite (Ulp.ulp_neq_0 radix2 fexp _ Hv0). apply bpow_le.
    have Hmag : (mag radix2 v <= femax t - 1)%Z.
    { apply (mag_le_bpow radix2 v (femax t - 1) Hv0).
      rewrite -Hhalf. exact Hv. }
    unfold cexp, SpecFloat.fexp, SpecFloat.emin.
    apply Z.max_lub; pose proof (fprec_lb t);
      pose proof (fprec_lt_femax t); lia. }
have Hb : bpow radix2 (femax t - 1 - fprec t) <= /8 * Omega.
{ have -> : (/8 * Omega = bpow radix2 (femax t - 3))%R.
  { have -> : (/8:R) = bpow radix2 (-3) by (simpl; lra).
    rewrite -bpow_plus. f_equal; lia. }
  apply bpow_le. pose proof (fprec_lb t). lia. }
have HO : 0 <= Omega by apply bpow_ge_0.
lra.
Qed.

Local Lemma half_ulp_below_quarter (v : R) :
  Rabs v < /4 * Omega -> /2 * ulp v <= /32 * Omega.
Proof.
move => Hv.
have Hquarter : /4 * Omega = bpow radix2 (femax t - 2).
{ symmetry. apply bpow_femax_minus_two. }
have Hu : ulp v <= bpow radix2 (femax t - 2 - fprec t).
{ destruct (Req_dec v 0) as [-> | Hv0].
  - change (ulp 0) with
      (Ulp.ulp radix2 (FLT.FLT_exp (3 - femax t - fprec t) (fprec t)) 0).
    rewrite FLT.ulp_FLT_0. apply bpow_le.
    pose proof (fprec_lb t). pose proof (fprec_lt_femax t). lia.
  - rewrite (Ulp.ulp_neq_0 radix2 fexp _ Hv0). apply bpow_le.
    have Hmag : (mag radix2 v <= femax t - 2)%Z.
    { apply (mag_le_bpow radix2 v (femax t - 2) Hv0).
      rewrite -Hquarter. exact Hv. }
    unfold cexp, SpecFloat.fexp, SpecFloat.emin.
    apply Z.max_lub; pose proof (fprec_lb t);
      pose proof (fprec_lt_femax t); lia. }
have Hb : bpow radix2 (femax t - 2 - fprec t) <= /16 * Omega.
{ have -> : (/16 * Omega = bpow radix2 (femax t - 4))%R.
  { have -> : (/16:R) = bpow radix2 (-4) by (simpl; lra).
    rewrite -bpow_plus. f_equal; lia. }
  apply bpow_le. pose proof (fprec_lb t). lia. }
have HO : 0 <= Omega by apply bpow_ge_0.
lra.
Qed.

Local Lemma half_ulp_below_overflow (v : R) :
  Rabs v < Omega -> /2 * ulp v <= /8 * Omega.
Proof.
move => Hv.
have Hu := ulp_below_overflow v Hv.
have Hb : bpow radix2 (femax t - fprec t) <= /4 * Omega
  by apply bpow_femax_fprec_le_quarter_Omega.
have HO : 0 <= Omega by apply bpow_ge_0.
lra.
Qed.

Local Lemma round_abs_le_bpow (k : Z) (v : R) :
  (emin <= k)%Z -> Rabs v <= bpow radix2 k ->
  Rabs (round radix2 fexp (Znearest choice) v) <= bpow radix2 k.
Proof.
move => Hk Hv.
apply abs_round_le_generic.
- exact valid_fexp_finite.
- apply valid_rnd_N.
- apply Generic_fmt.generic_format_bpow.
  unfold fexp, SpecFloat.fexp. apply Z.max_lub.
  + pose proof (fprec_lb t). lia.
  + unfold emin, common.emin. exact Hk.
- exact Hv.
Qed.

Local Lemma round_abs_le_quarter_Omega (v : R) :
  Rabs v <= /4 * Omega ->
  Rabs (round radix2 fexp (Znearest choice) v) <= /4 * Omega.
Proof.
move => Hv.
rewrite -(@bpow_femax_minus_two t) in Hv.
rewrite -(@bpow_femax_minus_two t).
apply round_abs_le_bpow.
- unfold common.emin, SpecFloat.emin.
  pose proof (fprec_lt_femax t).
  pose proof (fprec_lb t). lia.
- exact Hv.
Qed.

Lemma DWDivFP_result_finite_subnormal (xh xl y : ftype t) :
  DWDivFP_mixed_safe_input_cond xh xl y ->
  FT2R xh <> 0 ->
  Rabs (FT2R xh / FT2R y) < bpow radix2 (emin + fprec t - 1) ->
  is_finite_p (DWDivFP3 xh xl y).
Proof.
intros (Hfxh & Hfxl & Hfy & Hdwp & Hfth & Hxhb & Hqub & Hxhlb)
  Hxhne Hsub.
destruct Hxhlb as [Hxh0 | Hxhlb]; [contradiction |].
have Hp2 := fprec_lb t.
have HO := Omega_ge_8.
have HOp : 0 < Omega by apply bpow_gt_0.
have Hu := u_le_quarter.
have Hu0 : 0 <= u by apply bpow_ge_0.
have Hx4 : Rabs (FT2R xh) <= /4 * Omega.
{ rewrite -(@bpow_femax_minus_two t). exact Hxhb. }
have Hyne : FT2R y <> 0
  by exact (DWDivFP_denom_nonzero_from_finite xh y Hfy Hfth).
have Hylt : Rabs (FT2R y) < Omega.
{ rewrite -B2R_float_of_ftype. apply Binary.abs_B2R_lt_emax. }
have HEY : bpow radix2 emin * Rabs (FT2R y) <= 2.
{ have HE : 0 < bpow radix2 emin by apply bpow_gt_0.
  have Hstep : bpow radix2 emin * Rabs (FT2R y)
             <= bpow radix2 emin * Omega by nra.
  have Hprod : bpow radix2 emin * Omega = bpow radix2 (3 - fprec t).
  { rewrite -bpow_plus. f_equal.
    unfold emin, common.emin, SpecFloat.emin. lia. }
  have Hb : bpow radix2 (3 - fprec t) <= 2.
  { change 2 with (bpow radix2 1). apply bpow_le; lia. }
  lra. }
have Hulpq : ulp (FT2R xh / FT2R y) = bpow radix2 emin.
{ apply ulp_FLT_small; [apply fprec_gt_0 |].
  eapply Rlt_le_trans; [exact Hsub |]. apply bpow_le.
  unfold emin, common.emin. lia. }
have Hthclose :
  Rabs (FT2R (BDIV xh y) - FT2R xh / FT2R y) <= /2 * bpow radix2 emin.
{ rewrite -(BDIV_round_correct t xh y Hyne Hfth) -Hulpq.
  exact (@error_le_half_ulp radix2 fexp valid_fexp_finite choice
           (FT2R xh / FT2R y)). }
have HAX :
  Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh) <= 1.
{ have Hid : FT2R (BDIV xh y) * FT2R y - FT2R xh
           = (FT2R (BDIV xh y) - FT2R xh / FT2R y) * FT2R y
      by (field; exact Hyne).
  rewrite Hid Rabs_mult.
  have Hm := Rmult_le_compat_r (Rabs (FT2R y)) _ _ (Rabs_pos _) Hthclose.
  nra. }
have HA : Rabs (FT2R (BDIV xh y) * FT2R y) <= 3/8 * Omega.
{ have Hle : Rabs (FT2R (BDIV xh y) * FT2R y)
           <= Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh) +
              Rabs (FT2R xh).
  { have Heq : FT2R (BDIV xh y) * FT2R y =
        (FT2R (BDIV xh y) * FT2R y - FT2R xh) + FT2R xh by ring.
    rewrite {1}Heq. apply Rabs_triang. }
  nra. }
have HAlt : Rabs (FT2R (BDIV xh y) * FT2R y) < /2 * Omega by nra.
have Hpiherr :
  Rabs (FT2R (BMULT (BDIV xh y) y) -
        FT2R (BDIV xh y) * FT2R y) <= /16 * Omega.
{ have Fpih : is_finite (BMULT (BDIV xh y) y) = true.
  { apply no_overflow_mult_is_finite; [exact Hfth | exact Hfy |].
    eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp |].
    have Hulp := half_ulp_below_half _ HAlt. nra. }
  rewrite -(BMULT_round_correct t _ _ Fpih).
  eapply Rle_trans.
  - exact (@error_le_half_ulp radix2 fexp valid_fexp_finite choice
             (FT2R (BDIV xh y) * FT2R y)).
  - exact (half_ulp_below_half _ HAlt). }
have Fpih : is_finite (BMULT (BDIV xh y) y) = true.
{ apply no_overflow_mult_is_finite; [exact Hfth | exact Hfy |].
  eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp |].
  have Hulp := half_ulp_below_half _ HAlt. nra. }
have Fpil : is_finite (Fast2Mult_err (BDIV xh y) y) = true.
{ exact (proj2 (Fast2Mult_finite_unconditional (BDIV xh y) y Fpih)). }
have Hpil : Rabs (FT2R (Fast2Mult_err (BDIV xh y) y)) <= /16 * Omega.
{ eapply Rle_trans.
  - exact (Fast2Mult_accuracy_norm (BDIV xh y) y Fpih).
  - exact (half_ulp_below_half _ HAlt). }
have Hdharg :
  Rabs (FT2R xh - FT2R (BMULT (BDIV xh y) y)) <= 3/16 * Omega.
{ have HAX' : Rabs (FT2R xh - FT2R (BDIV xh y) * FT2R y) <= 1.
  { rewrite Rabs_minus_sym. exact HAX. }
  have Hpiherr' : Rabs (FT2R (BDIV xh y) * FT2R y -
                          FT2R (BMULT (BDIV xh y) y)) <= /16 * Omega.
  { rewrite Rabs_minus_sym. exact Hpiherr. }
  have Hsplit : FT2R xh - FT2R (BMULT (BDIV xh y) y)
              = (FT2R xh - FT2R (BDIV xh y) * FT2R y) +
                (FT2R (BDIV xh y) * FT2R y -
                 FT2R (BMULT (BDIV xh y) y)) by ring.
  rewrite Hsplit. eapply Rle_trans; [apply Rabs_triang |].
  eapply Rle_trans; [apply Rplus_le_compat; [exact HAX' | exact Hpiherr'] |].
  nra. }
have Fdh : is_finite (BMINUS xh (BMULT (BDIV xh y) y)) = true.
{ apply no_overflow_minus_is_finite; [exact Hfxh | exact Fpih |].
  red. eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp |].
  have Hlt : Rabs (FT2R xh - FT2R (BMULT (BDIV xh y) y)) < /4 * Omega
    by (eapply Rle_lt_trans; [exact Hdharg |]; nra).
  have Hulp := half_ulp_below_quarter _ Hlt. nra. }
have Hdh :
  Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y))) <= 7/32 * Omega.
{ rewrite -(BMINUS_round_correct t _ _ Fdh).
  eapply Rle_trans; [apply round_abs_le_abs_plus_half_ulp |].
  have Hlt : Rabs (FT2R xh - FT2R (BMULT (BDIV xh y) y)) < /4 * Omega
    by (eapply Rle_lt_trans; [exact Hdharg |]; nra).
  have Hulp := half_ulp_below_quarter _ Hlt. nra. }
have Hdtarg :
  Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y)) -
        FT2R (Fast2Mult_err (BDIV xh y) y)) <= 9/32 * Omega.
{ eapply Rle_trans; [unfold Rminus; apply Rabs_triang |].
  rewrite Rabs_Ropp. nra. }
have Fdt : is_finite (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                             (Fast2Mult_err (BDIV xh y) y)) = true.
{ apply no_overflow_minus_is_finite; [exact Fdh | exact Fpil |].
  red. eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp |].
  have Hlt : Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y)) -
                  FT2R (Fast2Mult_err (BDIV xh y) y)) < /2 * Omega
    by (eapply Rle_lt_trans; [exact Hdtarg |]; nra).
  have Hulp := half_ulp_below_half _ Hlt. nra. }
have Hdt :
  Rabs (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                     (Fast2Mult_err (BDIV xh y) y))) <= 11/32 * Omega.
{ rewrite -(BMINUS_round_correct t _ _ Fdt).
  eapply Rle_trans; [apply round_abs_le_abs_plus_half_ulp |].
  have Hlt : Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y)) -
                  FT2R (Fast2Mult_err (BDIV xh y) y)) < /2 * Omega
    by (eapply Rle_lt_trans; [exact Hdtarg |]; nra).
  have Hulp := half_ulp_below_half _ Hlt. nra. }
have Hxl : Rabs (FT2R xl) <= /16 * Omega.
{ have Hlow := @DW_acc_lemmas.dw_low_le_u_high t STD xh xl Hdwp.
  have HX0 := Rabs_pos (FT2R xh).
  nra. }
have Hdarg :
  Rabs (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                     (Fast2Mult_err (BDIV xh y) y)) + FT2R xl)
    <= 13/32 * Omega.
{ eapply Rle_trans; [apply Rabs_triang |]. nra. }
have Fd : is_finite (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                  (Fast2Mult_err (BDIV xh y) y)) xl) = true.
{ apply no_overflow_sum_is_finite; [exact Fdt | exact Hfxl |].
  red. eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp |].
  have Hlt : Rabs (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                     (Fast2Mult_err (BDIV xh y) y)) + FT2R xl) < /2 * Omega
    by (eapply Rle_lt_trans; [exact Hdarg |]; nra).
  have Hulp := half_ulp_below_half _ Hlt. nra. }
have Hd :
  Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                            (Fast2Mult_err (BDIV xh y) y)) xl)) <= 15/32 * Omega.
{ rewrite -(BPLUS_round_correct t _ _ Fd).
  eapply Rle_trans; [apply round_abs_le_abs_plus_half_ulp |].
  have Hlt : Rabs (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                     (Fast2Mult_err (BDIV xh y) y)) + FT2R xl) < /2 * Omega
    by (eapply Rle_lt_trans; [exact Hdarg |]; nra).
  have Hulp := half_ulp_below_half _ Hlt. nra. }
have Hy8 : 8 <= Rabs (FT2R y).
{ have HY : 0 < Rabs (FT2R y) by (apply Rabs_pos_lt; exact Hyne).
  have Hsplit : Rabs (FT2R xh) =
      Rabs (FT2R xh / FT2R y) * Rabs (FT2R y)
    by (rewrite -Rabs_mult; f_equal; field; exact Hyne).
  have H1 : bpow radix2 (emin + 2 * fprec t)
       < bpow radix2 (emin + fprec t - 1) * Rabs (FT2R y).
  { eapply Rle_lt_trans; [exact Hxhlb |].
    rewrite Hsplit. apply Rmult_lt_compat_r; assumption. }
  have Heq : bpow radix2 (emin + 2 * fprec t) =
      bpow radix2 (emin + fprec t - 1) * bpow radix2 (fprec t + 1)
    by (rewrite -bpow_plus; f_equal; lia).
  have HB8 : 8 <= bpow radix2 (fprec t + 1).
  { change 8 with (bpow radix2 3). apply bpow_le; lia. }
  rewrite Heq in H1.
  have HBp := bpow_gt_0 radix2 (emin + fprec t - 1).
  apply (Rle_trans _ (bpow radix2 (fprec t + 1))); [exact HB8 |].
  apply (Rmult_le_reg_l (bpow radix2 (emin + fprec t - 1))); [exact HBp |].
  exact (Rlt_le _ _ H1). }
have Hdy :
  Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                            (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
    <= /8 * Rabs (FT2R (BPLUS
      (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
              (Fast2Mult_err (BDIV xh y) y)) xl)).
{ rewrite /Rdiv Rabs_mult Rabs_inv.
  have HYp : 0 < Rabs (FT2R y) by lra.
  have Hinv : / Rabs (FT2R y) <= /8 by apply Rinv_le_contravar; lra.
  rewrite (Rmult_comm (/8)).
  apply Rmult_le_compat_l; [apply Rabs_pos | exact Hinv]. }
have Hdy8 :
  Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                            (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
    <= /8 * Omega by nra.
have Ftl : is_finite (BDIV (BPLUS
    (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
            (Fast2Mult_err (BDIV xh y) y)) xl) y) = true.
{ apply no_overflow_div_is_finite; [exact Fd | exact Hyne |].
  eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp |].
  have Hdylt : Rabs (FT2R (BPLUS
      (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
              (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y) < /4 * Omega
    by (eapply Rle_lt_trans; [exact Hdy8 |]; nra).
  have Hulp := half_ulp_below_quarter _ Hdylt. nra. }
have Htl : Rabs (FT2R (BDIV (BPLUS
    (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
            (Fast2Mult_err (BDIV xh y) y)) xl) y)) <= /8 * Omega.
{ rewrite -(BDIV_round_correct t _ y Hyne Ftl).
  have Heq8 : bpow radix2 (femax t - 3) = /8 * Omega.
  { have -> : (/8:R) = bpow radix2 (-3) by (simpl; lra).
    rewrite -bpow_plus. f_equal; lia. }
  rewrite -Heq8.
  apply round_abs_le_bpow.
  - unfold emin, common.emin, SpecFloat.emin.
    pose proof (fprec_lb t). pose proof (fprec_lt_femax t). lia.
  - rewrite Heq8. exact Hdy8. }
have Hq16 : Rabs (FT2R xh / FT2R y) <= /16 * Omega.
{ eapply Rlt_le; eapply Rlt_le_trans; [exact Hsub |].
  have -> : /16 * Omega = bpow radix2 (femax t - 4).
  { have -> : (/16:R) = bpow radix2 (-4) by (simpl; lra).
    rewrite -bpow_plus. f_equal; lia. }
  apply bpow_le. unfold emin, common.emin, SpecFloat.emin.
  pose proof (fprec_lb t). pose proof (fprec_lt_femax t). lia. }
have Hth : Rabs (FT2R (BDIV xh y)) <= /16 * Omega.
{ rewrite -(BDIV_round_correct t xh y Hyne Hfth).
  have Heq16 : bpow radix2 (femax t - 4) = /16 * Omega.
  { have -> : (/16:R) = bpow radix2 (-4) by (simpl; lra).
    rewrite -bpow_plus. f_equal; lia. }
  rewrite -Heq16.
  apply round_abs_le_bpow.
  - unfold emin, common.emin, SpecFloat.emin.
    pose proof (fprec_lb t). pose proof (fprec_lt_femax t). lia.
  - rewrite Heq16. exact Hq16. }
have Hsum : Rabs (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS
    (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
            (Fast2Mult_err (BDIV xh y) y)) xl) y)) <= 3/16 * Omega.
{ eapply Rle_trans; [apply Rabs_triang |]. nra. }
have Ffst : is_finite (BPLUS (BDIV xh y) (BDIV (BPLUS
    (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
            (Fast2Mult_err (BDIV xh y) y)) xl) y)) = true.
{ apply no_overflow_sum_is_finite; [exact Hfth | exact Ftl |].
  red. eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp |].
  have Hsumlt : Rabs (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS
      (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
              (Fast2Mult_err (BDIV xh y) y)) xl) y)) < /4 * Omega
    by (eapply Rle_lt_trans; [exact Hsum |]; nra).
  have Hulp := half_ulp_below_quarter _ Hsumlt. nra. }
unfold DWDivFP3, Fast2Mult_err, Fast2Mult, Fast2Sum.
cbn [fst snd]. split; [exact Ffst |].
apply is_finite_FastSum_small.
- eapply Rle_trans; [exact Htl |]. nra.
- exact Ffst.
Qed.

Lemma DWDivFP_result_finite_normal (xh xl y : ftype t) :
  DWDivFP_mixed_safe_input_cond xh xl y ->
  FT2R xh <> 0 ->
  bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xh / FT2R y) ->
  is_finite_p (DWDivFP3 xh xl y).
Proof.
intros (Hfxh & Hfxl & Hfy & Hdwp & Hfth & Hxhb & Hqub & Hxhlb)
  Hxhne Hnorm.
destruct Hxhlb as [Hxh0 | Hxhlb]; [contradiction |].
have Hp2 := fprec_lb t.
have HO := Omega_ge_8.
have HOp : 0 < Omega by apply bpow_gt_0.
have Hu := u_le_quarter.
have Hu0 : 0 <= u by apply bpow_ge_0.
have Hx0 : 0 <= Rabs (FT2R xh) by apply Rabs_pos.
have Hx4 : Rabs (FT2R xh) <= /4 * Omega.
{ rewrite -(@bpow_femax_minus_two t). exact Hxhb. }
have Hq4 : Rabs (FT2R xh / FT2R y) <= /4 * Omega.
{ rewrite -(@bpow_femax_minus_two t). exact Hqub. }
have Hyne : FT2R y <> 0
  by exact (DWDivFP_denom_nonzero_from_finite xh y Hfy Hfth).
have HAX :
  Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh)
    <= Rabs (FT2R xh) * u
  by exact (thy_residual xh y Hfth Hyne Hnorm).
have HW : Rabs (FT2R xh) * u <= /16 * Omega.
{ apply Rle_trans with (/4 * Omega * u).
  - apply Rmult_le_compat_r; [exact Hu0 | exact Hx4].
  - nra. }
have HA : Rabs (FT2R (BDIV xh y) * FT2R y) <= 5/16 * Omega.
{ have Hle : Rabs (FT2R (BDIV xh y) * FT2R y)
      <= Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh) + Rabs (FT2R xh).
  { have Heq : FT2R (BDIV xh y) * FT2R y =
      (FT2R (BDIV xh y) * FT2R y - FT2R xh) + FT2R xh by ring.
    rewrite {1}Heq. apply Rabs_triang. }
  nra. }
have HAlt : Rabs (FT2R (BDIV xh y) * FT2R y) < /2 * Omega by nra.
have Fpih : is_finite (BMULT (BDIV xh y) y) = true.
{ apply no_overflow_mult_is_finite; [exact Hfth | exact Hfy |].
  eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp |].
  have Hulp := half_ulp_below_half _ HAlt. nra. }
have Hpiherr :
  Rabs (FT2R (BMULT (BDIV xh y) y) -
        FT2R (BDIV xh y) * FT2R y) <= /16 * Omega.
{ rewrite -(BMULT_round_correct t _ _ Fpih).
  eapply Rle_trans.
  - exact (@error_le_half_ulp radix2 fexp valid_fexp_finite choice
             (FT2R (BDIV xh y) * FT2R y)).
  - exact (half_ulp_below_half _ HAlt). }
have Fpil : is_finite (Fast2Mult_err (BDIV xh y) y) = true
  by exact (proj2 (Fast2Mult_finite_unconditional (BDIV xh y) y Fpih)).
have Hpil : Rabs (FT2R (Fast2Mult_err (BDIV xh y) y)) <= /16 * Omega.
{ eapply Rle_trans.
  - exact (Fast2Mult_accuracy_norm (BDIV xh y) y Fpih).
  - exact (half_ulp_below_half _ HAlt). }
have Hdharg :
  Rabs (FT2R xh - FT2R (BMULT (BDIV xh y) y)) <= /8 * Omega.
{ have HAX' : Rabs (FT2R xh - FT2R (BDIV xh y) * FT2R y)
       <= Rabs (FT2R xh) * u by (rewrite Rabs_minus_sym; exact HAX).
  have Hpiherr' : Rabs (FT2R (BDIV xh y) * FT2R y -
                          FT2R (BMULT (BDIV xh y) y)) <= /16 * Omega
    by (rewrite Rabs_minus_sym; exact Hpiherr).
  have Heq : FT2R xh - FT2R (BMULT (BDIV xh y) y) =
      (FT2R xh - FT2R (BDIV xh y) * FT2R y) +
      (FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y)) by ring.
  rewrite Heq. eapply Rle_trans; [apply Rabs_triang |]. nra. }
have Fdh : is_finite (BMINUS xh (BMULT (BDIV xh y) y)) = true.
{ apply no_overflow_minus_is_finite; [exact Hfxh | exact Fpih |].
  red. eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp |].
  have Hlt : Rabs (FT2R xh - FT2R (BMULT (BDIV xh y) y)) < /4 * Omega
    by (eapply Rle_lt_trans; [exact Hdharg |]; nra).
  have Hulp := half_ulp_below_quarter _ Hlt. nra. }

(* The normal quotient and product nodes agree with their FLX roundings. *)
have INTERNAL : DWDivFP_internal_input_cond xh xl y.
{ repeat split; assumption. }
have UFprod := cond_UF_prod_internal xh xl y INTERNAL Hnorm.
have Hth_bridge : round radix2 (FLX_exp (fprec t)) (Znearest choice)
      (FT2R xh / FT2R y) = FT2R (BDIV xh y).
{ rewrite -(BDIV_round_correct t xh y Hyne Hfth).
  by rewrite round_FLT_FLX. }
have Hpair := DWMulFP_relative_acc.Fast2Mult_correct_weak
  (BDIV xh y) y Fpih (fun _ => UFprod).
have Hpih_bridge : round radix2 (FLX_exp (fprec t)) (Znearest choice)
      (FT2R (BDIV xh y) * FT2R y) = FT2R (BMULT (BDIV xh y) y).
{ have H := f_equal (@fst R R) Hpair.
  rewrite /DWTimesFP.Fast2Mult /F2Rp /Fast2Mult /= in H. exact H. }
have Hpil_bridge : round radix2 (FLX_exp (fprec t)) (Znearest choice)
      (FT2R (BDIV xh y) * FT2R y -
       round radix2 (FLX_exp (fprec t)) (Znearest choice)
         (FT2R (BDIV xh y) * FT2R y)) =
      FT2R (Fast2Mult_err (BDIV xh y) y).
{ have H := f_equal (@snd R R) Hpair.
  rewrite /DWTimesFP.Fast2Mult /F2Rp /= in H. exact H. }
have Hprod : FT2R (BMULT (BDIV xh y) y) +
             FT2R (Fast2Mult_err (BDIV xh y) y) =
             FT2R (BDIV xh y) * FT2R y.
{ rewrite -Hpih_bridge -Hpil_bridge.
  have Hg : generic_format radix2 (FLX_exp (fprec t))
      (FT2R (BDIV xh y) * FT2R y -
       round radix2 (FLX_exp (fprec t)) (Znearest choice)
         (FT2R (BDIV xh y) * FT2R y)).
  { rewrite -Ropp_minus_distr; apply generic_format_opp.
    apply (mult_error_FLX radix2 (fprec t) (Znearest choice));
      [apply (generic_format_FLX_FLT radix2 emin (fprec t)), generic_format_FLT_FT2R
      |apply (generic_format_FLX_FLT radix2 emin (fprec t)), generic_format_FLT_FT2R]. }
  rewrite (round_generic radix2 (FLX_exp (fprec t)) (Znearest choice) _ Hg).
  ring. }

(* A sharp nearest-rounding estimate gives the Sterbenz factor even at p=2. *)
set e := (u / (1 + u))%R.
have Huro : Relative.u_ro radix2 (fprec t) = u.
{ unfold Relative.u_ro.
  have Hb : bpow radix2 (- fprec t + 1) = 2 * u.
  { replace (- fprec t + 1)%Z with (1 + - fprec t)%Z by lia.
    rewrite bpow_plus. change (bpow radix2 1) with 2. ring. }
  rewrite Hb. field. }
have He0 : 0 <= e.
{ unfold e. apply Rmult_le_pos; [exact Hu0 |].
  apply Rlt_le, Rinv_0_lt_compat. nra. }
have He5 : e <= /5.
{ unfold e, Rdiv.
  apply (Rmult_le_reg_r (1 + u)); [nra |].
  rewrite Rmult_assoc Rinv_l; [rewrite Rmult_1_r | nra].
  nra. }
have Hrel1 : Rabs (FT2R (BDIV xh y) - FT2R xh / FT2R y)
             <= e * Rabs (FT2R xh / FT2R y).
{ rewrite -Hth_bridge. unfold e.
  have H := Relative.relative_error_N_FLX' radix2 (fprec t)
           (fprec_gt_0 t) choice (FT2R xh / FT2R y).
  rewrite Huro in H. exact H. }
have HthyX : Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh)
             <= e * Rabs (FT2R xh).
{ have Hid : FT2R (BDIV xh y) * FT2R y - FT2R xh =
      (FT2R (BDIV xh y) - FT2R xh / FT2R y) * FT2R y
      by (field; exact Hyne).
  rewrite Hid Rabs_mult.
  eapply Rle_trans; [apply Rmult_le_compat_r; [apply Rabs_pos | exact Hrel1] |].
  have Heq : Rabs (FT2R xh / FT2R y) * Rabs (FT2R y) = Rabs (FT2R xh)
    by (rewrite -Rabs_mult; f_equal; field; exact Hyne).
  rewrite Rmult_assoc Heq. apply Rle_refl. }
have HAe : Rabs (FT2R (BDIV xh y) * FT2R y)
           <= (1 + e) * Rabs (FT2R xh).
{ have Hle : Rabs (FT2R (BDIV xh y) * FT2R y) <=
      Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh) + Rabs (FT2R xh).
  { have Hid : FT2R (BDIV xh y) * FT2R y =
      (FT2R (BDIV xh y) * FT2R y - FT2R xh) + FT2R xh by ring.
    rewrite {1}Hid. apply Rabs_triang. }
  nra. }
have Hrel2 : Rabs (FT2R (BMULT (BDIV xh y) y) -
                         FT2R (BDIV xh y) * FT2R y)
             <= e * Rabs (FT2R (BDIV xh y) * FT2R y).
{ rewrite -Hpih_bridge. unfold e.
  have H := Relative.relative_error_N_FLX' radix2 (fprec t)
           (fprec_gt_0 t) choice (FT2R (BDIV xh y) * FT2R y).
  rewrite Huro in H. exact (H NANS STD). }
have Hpihclose : Rabs (FT2R (BMULT (BDIV xh y) y) - FT2R xh)
                 <= /2 * Rabs (FT2R xh).
{ have Htri : Rabs (FT2R (BMULT (BDIV xh y) y) - FT2R xh) <=
      Rabs (FT2R (BMULT (BDIV xh y) y) -
            FT2R (BDIV xh y) * FT2R y) +
      Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh).
  { have Hid : FT2R (BMULT (BDIV xh y) y) - FT2R xh =
      (FT2R (BMULT (BDIV xh y) y) - FT2R (BDIV xh y) * FT2R y) +
      (FT2R (BDIV xh y) * FT2R y - FT2R xh) by ring.
    rewrite Hid. apply Rabs_triang. }
  eapply Rle_trans; [exact Htri |].
  have Hstep : Rabs (FT2R (BMULT (BDIV xh y) y) -
                     FT2R (BDIV xh y) * FT2R y)
      <= e * ((1 + e) * Rabs (FT2R xh)).
  { eapply Rle_trans; [exact Hrel2 |].
    apply Rmult_le_compat_l; [exact He0 | exact HAe]. }
  eapply Rle_trans; [apply Rplus_le_compat; [exact Hstep | exact HthyX] |].
  have Hcoef : e * (1 + e) + e <= /2 by nra.
  replace (e * ((1 + e) * Rabs (FT2R xh)) +
           e * Rabs (FT2R xh))
    with ((e * (1 + e) + e) * Rabs (FT2R xh)) by ring.
  apply Rmult_le_compat_r; [apply Rabs_pos | exact Hcoef]. }
have Hdh_exact : FT2R xh - FT2R (BMULT (BDIV xh y) y) =
                 FT2R (BMINUS xh (BMULT (BDIV xh y) y)).
{ have FX : generic_format radix2 fexp (FT2R xh)
    by apply generic_format_FLT_FT2R.
  have FP : generic_format radix2 fexp (FT2R (BMULT (BDIV xh y) y))
    by apply generic_format_FLT_FT2R.
  have Hg : generic_format radix2 fexp
      (FT2R xh - FT2R (BMULT (BDIV xh y) y)).
  { have HXP := Rabs_le_inv _ _ Hpihclose.
    destruct (Rcase_abs (FT2R xh)) as [HXn | HXp].
    - have HrX : Rabs (FT2R xh) = - FT2R xh by rewrite Rabs_left.
      rewrite HrX in HXP.
      have Hopp : FT2R xh - FT2R (BMULT (BDIV xh y) y) =
          - ((-FT2R xh) - (-FT2R (BMULT (BDIV xh y) y))) by ring.
      rewrite Hopp. apply generic_format_opp.
      apply (Sterbenz.sterbenz radix2 fexp);
        [apply generic_format_opp; exact FX
        |apply generic_format_opp; exact FP
        |lra].
    - have HrX : Rabs (FT2R xh) = FT2R xh by rewrite Rabs_pos_eq; lra.
      rewrite HrX in HXP. apply (Sterbenz.sterbenz radix2 fexp);
        [exact FX | exact FP | lra]. }
  rewrite -(BMINUS_round_correct t _ _ Fdh).
  symmetry. apply round_generic; [apply valid_rnd_N | exact Hg]. }
have Hdtarg_exact :
  FT2R (BMINUS xh (BMULT (BDIV xh y) y)) -
  FT2R (Fast2Mult_err (BDIV xh y) y) =
  FT2R xh - FT2R (BDIV xh y) * FT2R y
  by (rewrite -Hdh_exact -Hprod; ring).
have Hdtarg : Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y)) -
                          FT2R (Fast2Mult_err (BDIV xh y) y)) <= /16 * Omega
  by (rewrite Hdtarg_exact Rabs_minus_sym;
      exact (Rle_trans _ _ _ HAX HW)).
have Fdt : is_finite (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                             (Fast2Mult_err (BDIV xh y) y)) = true.
{ apply no_overflow_minus_is_finite; [exact Fdh | exact Fpil |].
  red. eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp |].
  have Hlt : Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y)) -
                         FT2R (Fast2Mult_err (BDIV xh y) y)) < /4 * Omega
    by (eapply Rle_lt_trans; [exact Hdtarg |]; nra).
  have Hulp := half_ulp_below_quarter _ Hlt. nra. }
have Hdt_exact :
  FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                (Fast2Mult_err (BDIV xh y) y)) =
  FT2R xh - FT2R (BDIV xh y) * FT2R y.
{ rewrite -Hdtarg_exact.
  rewrite -(BMINUS_round_correct t _ _ Fdt).
  apply round_generic; [apply valid_rnd_N |].
  destruct (Rle_lt_dec (bpow radix2 (emin + fprec t - 1))
              (Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y)) -
                     FT2R (Fast2Mult_err (BDIV xh y) y)))) as [Hbig | Hsmall].
  - apply generic_format_FLT_FLX; [exact Hbig |].
    rewrite Hdtarg_exact -Hth_bridge.
    apply (div_error_FLX radix2 (fprec t) (Znearest choice)
             (FT2R xh) (FT2R y));
      apply (generic_format_FLX_FLT radix2 emin (fprec t)),
            generic_format_FLT_FT2R.
  - have Fdhf : generic_format radix2 fexp
        (FT2R (BMINUS xh (BMULT (BDIV xh y) y)))
      by apply generic_format_FLT_FT2R.
    have Fpilf : generic_format radix2 fexp
        (FT2R (Fast2Mult_err (BDIV xh y) y))
      by apply generic_format_FLT_FT2R.
    replace (FT2R (BMINUS xh (BMULT (BDIV xh y) y)) -
             FT2R (Fast2Mult_err (BDIV xh y) y))
      with (FT2R (BMINUS xh (BMULT (BDIV xh y) y)) +
            -FT2R (Fast2Mult_err (BDIV xh y) y)) by ring.
    apply FLT_format_plus_small;
      [apply fprec_gt_0 | exact Fdhf | apply generic_format_opp; exact Fpilf |].
    apply Rlt_le. eapply Rlt_trans.
    + replace (FT2R (BMINUS xh (BMULT (BDIV xh y) y)) +
               - FT2R (Fast2Mult_err (BDIV xh y) y))
        with (FT2R (BMINUS xh (BMULT (BDIV xh y) y)) -
              FT2R (Fast2Mult_err (BDIV xh y) y)) by ring.
      exact Hsmall.
    + apply bpow_lt. unfold emin, common.emin. lia. }
have Hdt : Rabs (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                              (Fast2Mult_err (BDIV xh y) y)))
           <= Rabs (FT2R xh) * u
  by (rewrite Hdt_exact Rabs_minus_sym; exact HAX).
have Hxl : Rabs (FT2R xl) <= Rabs (FT2R xh) * u
  by (rewrite Rmult_comm; exact (@DW_acc_lemmas.dw_low_le_u_high t STD xh xl Hdwp)).
have Hdarg : Rabs (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                (Fast2Mult_err (BDIV xh y) y)) + FT2R xl)
             <= 2 * (Rabs (FT2R xh) * u).
{ eapply Rle_trans; [apply Rabs_triang |]. nra. }
have Hdarg8 : Rabs (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                 (Fast2Mult_err (BDIV xh y) y)) + FT2R xl)
              <= /8 * Omega by nra.
have Fd : is_finite (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                  (Fast2Mult_err (BDIV xh y) y)) xl) = true.
{ apply no_overflow_sum_is_finite; [exact Fdt | exact Hfxl |].
  red. eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp |].
  have Hlt : Rabs (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                (Fast2Mult_err (BDIV xh y) y)) + FT2R xl)
             < /4 * Omega by (eapply Rle_lt_trans; [exact Hdarg8 |]; nra).
  have Hulp := half_ulp_below_quarter _ Hlt. nra. }
have HE_X16 : bpow radix2 emin <= /16 * Rabs (FT2R xh).
{ have H16 : 16 * bpow radix2 emin <= bpow radix2 (emin + 2 * fprec t).
  { have H16b : 16 <= bpow radix2 (2 * fprec t).
    { change 16 with (bpow radix2 4). apply bpow_le; lia. }
    rewrite bpow_plus. have HE0 := bpow_ge_0 radix2 emin. nra. }
  have H16X : 16 * bpow radix2 emin <= Rabs (FT2R xh).
  { eapply Rle_trans; [exact H16 |]. exact Hxhlb. }
  lra. }
have Hd : Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                    (Fast2Mult_err (BDIV xh y) y)) xl))
          <= 21/32 * Rabs (FT2R xh).
{ rewrite -(BPLUS_round_correct t _ _ Fd).
  eapply Rle_trans; [apply (@round_ub_emin t) |].
  have HB0 := Rabs_pos (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                    (Fast2Mult_err (BDIV xh y) y)) + FT2R xl).
  have Hmul := Rmult_le_compat_r u _ _ Hu0 Hdarg.
  have HW0 : 0 <= Rabs (FT2R xh) * u by nra.
  have Hmulu : 2 * (Rabs (FT2R xh) * u) * u
             <= /2 * (Rabs (FT2R xh) * u).
  { replace (/2 * (Rabs (FT2R xh) * u))
      with ((2 * (Rabs (FT2R xh) * u)) * /4) by field.
    apply Rmult_le_compat_l; [nra | exact Hu]. }
  have HWX : Rabs (FT2R xh) * u <= /4 * Rabs (FT2R xh).
  { rewrite (Rmult_comm (/4)).
    apply Rmult_le_compat_l; [exact Hx0 | exact Hu]. }
  lra. }
have Hdy : Rabs (FT2R (BPLUS
      (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
              (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
    <= 21/32 * Rabs (FT2R xh / FT2R y).
{ rewrite /Rdiv !Rabs_mult Rabs_inv.
  rewrite -Rmult_assoc.
  apply Rmult_le_compat_r;
    [apply Rlt_le, Rinv_0_lt_compat, Rabs_pos_lt; exact Hyne | exact Hd]. }
have Hdy4 : Rabs (FT2R (BPLUS
      (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
              (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y) <= /4 * Omega
  by nra.
have Ftl : is_finite (BDIV (BPLUS
    (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
            (Fast2Mult_err (BDIV xh y) y)) xl) y) = true.
{ apply no_overflow_div_is_finite; [exact Fd | exact Hyne |].
  eapply Rle_lt_trans; [apply round_abs_le_quarter_Omega; exact Hdy4 |].
  nra. }
have Htl : Rabs (FT2R (BDIV (BPLUS
    (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
            (Fast2Mult_err (BDIV xh y) y)) xl) y)) <= /4 * Omega.
{ rewrite -(BDIV_round_correct t _ y Hyne Ftl).
  apply round_abs_le_quarter_Omega. exact Hdy4. }
have Hth : Rabs (FT2R (BDIV xh y)) <= /4 * Omega.
{ rewrite -(BDIV_round_correct t xh y Hyne Hfth).
  apply round_abs_le_quarter_Omega. exact Hq4. }
have Hsum : Rabs (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS
    (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
            (Fast2Mult_err (BDIV xh y) y)) xl) y)) <= /2 * Omega.
{ eapply Rle_trans; [apply Rabs_triang |]. nra. }
have Ffst : is_finite (BPLUS (BDIV xh y) (BDIV (BPLUS
    (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
            (Fast2Mult_err (BDIV xh y) y)) xl) y)) = true.
{ apply no_overflow_sum_is_finite; [exact Hfth | exact Ftl |].
  red. eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp |].
  have Hsumlt : Rabs (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS
      (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
              (Fast2Mult_err (BDIV xh y) y)) xl) y)) < Omega by nra.
  have Hulp := half_ulp_below_overflow _ Hsumlt. nra. }
unfold DWDivFP3, Fast2Mult_err, Fast2Mult, Fast2Sum.
cbn [fst snd]. split; [exact Ffst |].
apply is_finite_FastSum_small; [exact Htl | exact Ffst].
Qed.

End DWDivFPFinite.
