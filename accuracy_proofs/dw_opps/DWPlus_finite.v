(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Precision-independent result finiteness for the double-word addition
    kernels under their public safe-input conditions. *)

Require Import vcfloat.VCFloat.
Require Import common float_acc_lems op_defs DDModels DDConds DWord_defs FLT_helpers FLT_lemmas.
Require Import DW_acc_lemmas.
Require Import DD.accuracy_proofs.basic_blocks.TwoSum_acc_helpers.
From Flocq Require Import Pff2Flocq Core.
Require Import mathcomp.ssreflect.ssreflect.

Set Bullet Behavior "Strict Subproofs".

Section DWPlusFPFinite.
Context {NANS : Nans} {t : type} {STD : is_standard t}.

Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Notation Omega := (bpow radix2 (femax t)).
Notation u := (bpow radix2 (- fprec t)).
Notation ulp := (Ulp.ulp radix2 fexp).

Local Instance valid_fexp_finite : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.

Local Lemma u_le_quarter : u <= /4.
Proof.
have -> : (/4 = bpow radix2 (-2))%R by (simpl; lra).
apply bpow_le. pose proof (fprec_lb t). lia.
Qed.

Local Lemma round_abs_le_half_Omega (v : R) :
  Rabs v <= /2 * Omega ->
  Rabs (round radix2 fexp (Znearest choice) v) <= /2 * Omega.
Proof.
move => Hv. apply Generic_fmt.abs_round_le_generic.
- exact valid_fexp_finite.
- apply valid_rnd_N.
- apply generic_format_half_Omega.
- exact Hv.
Qed.

Local Lemma round_abs_le_quarter_Omega (v : R) :
  Rabs v <= /4 * Omega ->
  Rabs (round radix2 fexp (Znearest choice) v) <= /4 * Omega.
Proof.
move => Hv. apply Generic_fmt.abs_round_le_generic.
- exact valid_fexp_finite.
- apply valid_rnd_N.
- apply generic_format_quarter_Omega.
- exact Hv.
Qed.

Lemma DWPlusFP_finite_from_safe_input_cond (xh xl y : ftype t) :
  DWPlusFP_safe_input_cond xh xl y ->
  is_finite_p (DWPlusFP xh xl y).
Proof.
intros (Hfxh & Hfxl & Hfy & Hdw & Hxh & Hy).
have HO : 0 < Omega by apply bpow_gt_0.
have Hu : u <= /4 by apply u_le_quarter.
have Hu0 : 0 <= u by apply bpow_ge_0.
have Hsum : Rabs (FT2R xh + FT2R y) <= /2 * Omega.
{ eapply Rle_trans; [apply Rabs_triang |]. lra. }
have Hdiff : Rabs (FT2R xh - FT2R y) <= /2 * Omega.
{ replace (FT2R xh - FT2R y) with (FT2R xh + - FT2R y) by ring.
  eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp. lra. }
have Fs : is_finite (BPLUS xh y) = true.
{ apply no_overflow_sum_is_finite; [exact Hfxh | exact Hfy |].
  red. eapply Rle_lt_trans; [apply round_abs_le_half_Omega; exact Hsum |].
  lra. }
have Fm : is_finite (BMINUS xh y) = true.
{ apply no_overflow_minus_is_finite; [exact Hfxh | exact Hfy |].
  red. eapply Rle_lt_trans; [apply round_abs_le_half_Omega; exact Hdiff |].
  lra. }
have Fsl : is_finite (TwoSumF_err xh y) = true.
{ apply TwoSum_acc_helpers.is_finite_TwoSum; [exact Fs | exact Fm |].
  eapply Rle_lt_trans; [exact Hy |]. apply FLT_lemmas.Omega4_lt_predOmega. }
have Fts : is_finite_p (TwoSumF xh y) by exact (conj Fs Fsl).
have Hxl : Rabs (FT2R xl) <= /16 * Omega.
{ have Hlow : Rabs (FT2R xl) <= u * Rabs (FT2R xh)
    by exact (DW_acc_lemmas.dw_low_le_u_high xh xl Hdw).
  have Hx0 : 0 <= Rabs (FT2R xh) by apply Rabs_pos.
  have HO0 : 0 <= Omega by apply bpow_ge_0.
  have H1 : u * Rabs (FT2R xh) <= /4 * Rabs (FT2R xh) by nra.
  eapply Rle_trans; [exact Hlow |].
  eapply Rle_trans; [exact H1 |]. nra. }
have Hsl : Rabs (FT2R (TwoSumF_err xh y)) <= /8 * Omega.
{ destruct (TwoSum_acc_helpers.TwoSumF_error xh y Fts)
      as (d & Hd & Hdel).
  have Heq : /2 * bpow radix2 (- fprec t + 1) = u.
  { rewrite bpow_plus. simpl.
    replace (IZR (Z.pow_pos 2 1)) with 2 by reflexivity. lra. }
  rewrite Heq in Hdel. rewrite Hd Rabs_mult.
  have Hxy0 : 0 <= Rabs (FT2R xh + FT2R y) by apply Rabs_pos.
  nra. }
have Hvarg : Rabs (FT2R xl + FT2R (TwoSumF_err xh y)) <= /4 * Omega.
{ eapply Rle_trans; [apply Rabs_triang |]. lra. }
have Fv : is_finite (BPLUS xl (TwoSumF_err xh y)) = true.
{ apply no_overflow_sum_is_finite; [exact Hfxl | exact Fsl |].
  red. eapply Rle_lt_trans;
    [apply round_abs_le_quarter_Omega; exact Hvarg |]. lra. }
have Hv : Rabs (FT2R (BPLUS xl (TwoSumF_err xh y))) <= /4 * Omega.
{ rewrite -(BPLUS_round_correct t _ _ Fv).
  apply round_abs_le_quarter_Omega. exact Hvarg. }
have Hsh : Rabs (FT2R (TwoSumF_sum xh y)) <= /2 * Omega.
{ change (TwoSumF_sum xh y) with (BPLUS xh y).
  rewrite -(BPLUS_round_correct t xh y Fs).
  apply round_abs_le_half_Omega. exact Hsum. }
have Fzh : is_finite
    (BPLUS (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y))) = true.
{ apply no_overflow_sum_is_finite; [exact Fs | exact Fv |].
  red. eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp |].
  have Harg : Rabs (FT2R (TwoSumF_sum xh y) +
                          FT2R (BPLUS xl (TwoSumF_err xh y)))
                  <= 3/4 * Omega.
  { eapply Rle_trans; [apply Rabs_triang |]. lra. }
  have Harglt : Rabs (FT2R (TwoSumF_sum xh y) +
                            FT2R (BPLUS xl (TwoSumF_err xh y))) < Omega by lra.
  have Hulp := ulp_below_overflow _ Harglt.
  have Htop := @bpow_femax_fprec_le_quarter_Omega t.
  lra. }
destruct (TwoSumF xh y) as [sh sl] eqn:E.
unfold TwoSumF_sum, TwoSumF_err in Fzh, Hv.
rewrite E in Fzh, Hv. cbn [fst snd] in Fzh, Hv.
unfold DWPlusFP. rewrite E. cbn [fst snd].
split; [exact Fzh |].
apply TwoSum_acc_helpers.is_finite_FastSum_small; [exact Hv | exact Fzh].
Qed.

End DWPlusFPFinite.

Section DWPlusDWFinite.
Context {NANS : Nans} {t : type} {STD : is_standard t}.

Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Notation Omega := (bpow radix2 (femax t)).
Notation u := (bpow radix2 (- fprec t)).
Notation ulp := (Ulp.ulp radix2 fexp).

Local Instance valid_fexp_dwplus : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.

Local Lemma half_ulp_below_half_dwplus (v : R) :
  Rabs v < /2 * Omega -> /2 * ulp v <= /16 * Omega.
Proof.
move => Hv.
have Hhalf : /2 * Omega = bpow radix2 (femax t - 1).
{ have -> : (/2:R) = bpow radix2 (-1) by (simpl; lra).
  rewrite -bpow_plus. f_equal; lia. }
have Hul : ulp v <= bpow radix2 (femax t - 1 - fprec t).
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
have HO : 0 <= Omega by apply bpow_ge_0. lra.
Qed.

Local Lemma half_ulp_below_quarter_dwplus (v : R) :
  Rabs v < /4 * Omega -> /2 * ulp v <= /32 * Omega.
Proof.
move => Hv.
have Hquarter : /4 * Omega = bpow radix2 (femax t - 2).
{ symmetry. apply bpow_femax_minus_two. }
have Hul : ulp v <= bpow radix2 (femax t - 2 - fprec t).
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
have HO : 0 <= Omega by apply bpow_ge_0. lra.
Qed.

Local Lemma half_ulp_below_overflow_dwplus (v : R) :
  Rabs v < Omega -> /2 * ulp v <= /8 * Omega.
Proof.
move => Hv.
have Hul := ulp_below_overflow v Hv.
have Hb := @bpow_femax_fprec_le_quarter_Omega t.
have HO : 0 <= Omega by apply bpow_ge_0. lra.
Qed.

Local Lemma round_error_below_half_dwplus (v : R) :
  Rabs v < /2 * Omega ->
  Rabs (round radix2 fexp (Znearest choice) v - v) <= /16 * Omega.
Proof.
move => Hv. eapply Rle_trans.
- apply Ulp.error_le_half_ulp.
  exact valid_fexp_dwplus.
- apply half_ulp_below_half_dwplus. exact Hv.
Qed.

Local Lemma round_error_below_quarter_dwplus (v : R) :
  Rabs v < /4 * Omega ->
  Rabs (round radix2 fexp (Znearest choice) v - v) <= /32 * Omega.
Proof.
move => Hv. eapply Rle_trans.
- apply Ulp.error_le_half_ulp.
  exact valid_fexp_dwplus.
- apply half_ulp_below_quarter_dwplus. exact Hv.
Qed.

Local Lemma round_abs_le_eighth_Omega_dwplus (v : R) :
  Rabs v <= /8 * Omega ->
  Rabs (round radix2 fexp (Znearest choice) v) <= /8 * Omega.
Proof.
move => Hv.
have Hb : /8 * Omega = bpow radix2 (femax t - 3).
{ have -> : (/8:R) = bpow radix2 (-3) by (simpl; lra).
  rewrite -bpow_plus. f_equal; lia. }
rewrite Hb in Hv |- *.
apply Generic_fmt.abs_round_le_generic.
- exact valid_fexp_dwplus.
- apply valid_rnd_N.
- apply Generic_fmt.generic_format_bpow.
  unfold SpecFloat.fexp, SpecFloat.emin. apply Z.max_lub.
  + pose proof (fprec_lb t). lia.
  + pose proof (fprec_lb t). pose proof (fprec_lt_femax t). lia.
- exact Hv.
Qed.

Local Lemma two_sum_finite_quarter (a b : ftype t) :
  is_finite a = true -> is_finite b = true ->
  Rabs (FT2R a) <= /4 * Omega -> Rabs (FT2R b) <= /4 * Omega ->
  is_finite_p (TwoSumF a b).
Proof.
move => Fa Fb Ha Hb.
have HO : 0 < Omega by apply bpow_gt_0.
have Hsum : Rabs (FT2R a + FT2R b) <= /2 * Omega.
{ eapply Rle_trans; [apply Rabs_triang |]. lra. }
have Hdiff : Rabs (FT2R a - FT2R b) <= /2 * Omega.
{ replace (FT2R a - FT2R b) with (FT2R a + - FT2R b) by ring.
  eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp. lra. }
have Fsum : is_finite (BPLUS a b) = true.
{ apply no_overflow_sum_is_finite; [exact Fa | exact Fb |].
  red. eapply Rle_lt_trans;
    [apply round_abs_le_half_Omega; exact Hsum |]. lra. }
have Fdiff : is_finite (BMINUS a b) = true.
{ apply no_overflow_minus_is_finite; [exact Fa | exact Fb |].
  red. eapply Rle_lt_trans;
    [apply round_abs_le_half_Omega; exact Hdiff |]. lra. }
split; [exact Fsum |].
apply TwoSum_acc_helpers.is_finite_TwoSum; [exact Fsum | exact Fdiff |].
eapply Rle_lt_trans; [exact Hb |]. apply FLT_lemmas.Omega4_lt_predOmega.
Qed.

Lemma DWPlusDW_finite_safe
    (xh xl yh yl : ftype t) :
  DWPlusDW_safe_input_cond xh xl yh yl ->
  is_finite_p (DWPlusDW xh xl yh yl).
Proof.
intros (F_xh & F_xl & F_yh & F_yl & DWx & DWy & Hxh & Hyh).
have HO : 0 < Omega by apply bpow_gt_0.
have Hu : u <= /4 by apply u_le_quarter.
have Hu0 : 0 <= u by apply bpow_ge_0.
have Hxl : Rabs (FT2R xl) <= /16 * Omega.
{ have Hlow : Rabs (FT2R xl) <= u * Rabs (FT2R xh)
    by exact (DW_acc_lemmas.dw_low_le_u_high xh xl DWx).
  have Hx0 : 0 <= Rabs (FT2R xh) by apply Rabs_pos.
  have H1 : u * Rabs (FT2R xh) <= /4 * Rabs (FT2R xh) by nra.
  eapply Rle_trans; [exact Hlow |]. eapply Rle_trans; [exact H1 |]. nra. }
have Hyl : Rabs (FT2R yl) <= /16 * Omega.
{ have Hlow : Rabs (FT2R yl) <= u * Rabs (FT2R yh)
    by exact (DW_acc_lemmas.dw_low_le_u_high yh yl DWy).
  have Hy0 : 0 <= Rabs (FT2R yh) by apply Rabs_pos.
  have H1 : u * Rabs (FT2R yh) <= /4 * Rabs (FT2R yh) by nra.
  eapply Rle_trans; [exact Hlow |]. eapply Rle_trans; [exact H1 |]. nra. }
have Fhi := two_sum_finite_quarter xh yh F_xh F_yh Hxh Hyh.
have Flo := two_sum_finite_quarter xl yl F_xl F_yl ltac:(lra) ltac:(lra).
have Hhisum : Rabs (FT2R xh + FT2R yh) <= /2 * Omega.
{ eapply Rle_trans; [apply Rabs_triang |]. lra. }
have Hlowsum : Rabs (FT2R xl + FT2R yl) <= /8 * Omega.
{ eapply Rle_trans; [apply Rabs_triang |]. lra. }
have Hsh : Rabs (FT2R (TwoSumF_sum xh yh)) <= /2 * Omega.
{ change (TwoSumF_sum xh yh) with (BPLUS xh yh).
  rewrite -(BPLUS_round_correct t xh yh (proj1 Fhi)).
  apply round_abs_le_half_Omega. exact Hhisum. }
have Hsl : Rabs (FT2R (TwoSumF_err xh yh)) <= /8 * Omega.
{ destruct (TwoSum_acc_helpers.TwoSumF_error xh yh Fhi) as (d & Hd & Hdel).
  have Heq : /2 * bpow radix2 (- fprec t + 1) = u.
  { rewrite bpow_plus. simpl.
    replace (IZR (Z.pow_pos 2 1)) with 2 by reflexivity. lra. }
  rewrite Heq in Hdel. rewrite Hd Rabs_mult.
  have H0 : 0 <= Rabs (FT2R xh + FT2R yh) by apply Rabs_pos. nra. }
have Fth : is_finite (BPLUS xl yl) = true := proj1 Flo.
have Hth : Rabs (FT2R (TwoSumF_sum xl yl)) <= /8 * Omega.
{ change (TwoSumF_sum xl yl) with (BPLUS xl yl).
  rewrite -(BPLUS_round_correct t xl yl Fth).
  apply round_abs_le_eighth_Omega_dwplus. exact Hlowsum. }
have Htl : Rabs (FT2R (TwoSumF_err xl yl)) <= /32 * Omega.
{ destruct (TwoSum_acc_helpers.TwoSumF_error xl yl Flo) as (d & Hd & Hdel).
  have Heq : /2 * bpow radix2 (- fprec t + 1) = u.
  { rewrite bpow_plus. simpl.
    replace (IZR (Z.pow_pos 2 1)) with 2 by reflexivity. lra. }
  rewrite Heq in Hdel. rewrite Hd Rabs_mult.
  have H0 : 0 <= Rabs (FT2R xl + FT2R yl) by apply Rabs_pos. nra. }
have Hcarg : Rabs (FT2R (TwoSumF_err xh yh) + FT2R (TwoSumF_sum xl yl))
               <= /4 * Omega.
{ eapply Rle_trans; [apply Rabs_triang |]. lra. }
have Fc : is_finite (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl)) = true.
{ apply no_overflow_sum_is_finite; [exact (proj2 Fhi) | exact Fth |].
  red. eapply Rle_lt_trans;
    [apply round_abs_le_quarter_Omega; exact Hcarg |]. lra. }
have Hc : Rabs (FT2R (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl)))
             <= /4 * Omega.
{ rewrite -(BPLUS_round_correct t _ _ Fc).
  apply round_abs_le_quarter_Omega. exact Hcarg. }
have Hec : Rabs (FT2R (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl)) -
                       (FT2R (TwoSumF_err xh yh) + FT2R (TwoSumF_sum xl yl)))
             <= /16 * Omega.
{ rewrite -(BPLUS_round_correct t _ _ Fc).
  apply round_error_below_half_dwplus. lra. }
have Hcorrhi := TwoSum_acc_helpers.TwoSumF_correct xh yh Fhi.
have Hcorrlo := TwoSum_acc_helpers.TwoSumF_correct xl yl Flo.
have Hvharg : Rabs (FT2R (TwoSumF_sum xh yh) +
                          FT2R (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl)))
                 <= 11/16 * Omega.
{ replace (FT2R (TwoSumF_sum xh yh) +
    FT2R (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl))) with
    ((FT2R xh + FT2R yh) + FT2R (TwoSumF_sum xl yl) +
     (FT2R (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl)) -
      (FT2R (TwoSumF_err xh yh) + FT2R (TwoSumF_sum xl yl)))).
  - eapply Rle_trans; [apply Rabs_triang |].
    have HA : Rabs (FT2R xh + FT2R yh + FT2R (TwoSumF_sum xl yl))
                <= 5/8 * Omega.
    { eapply Rle_trans; [apply Rabs_triang |]. lra. }
    lra.
  - rewrite Hcorrhi. ring. }
have Hvharglt : Rabs (FT2R (TwoSumF_sum xh yh) +
                            FT2R (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl)))
                   < Omega.
  by lra.
have Fvh : is_finite (BPLUS (TwoSumF_sum xh yh)
    (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl))) = true.
{ apply no_overflow_sum_is_finite; [exact (proj1 Fhi) | exact Fc |].
  red. eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp |].
  have He := half_ulp_below_overflow_dwplus _ Hvharglt. lra. }
have Hevh : Rabs (FT2R (BPLUS (TwoSumF_sum xh yh)
    (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl))) -
    (FT2R (TwoSumF_sum xh yh) +
     FT2R (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl)))) <= /8 * Omega.
{ rewrite -(BPLUS_round_correct t _ _ Fvh).
  eapply Rle_trans; [apply Ulp.error_le_half_ulp |].
  - exact valid_fexp_dwplus.
  - apply half_ulp_below_overflow_dwplus. exact Hvharglt. }
set sh := TwoSumF_sum xh yh.
set sl := TwoSumF_err xh yh.
set th := TwoSumF_sum xl yl.
set tl := TwoSumF_err xl yl.
set c := BPLUS sl th.
set vh := BPLUS sh c.
set z := BMINUS vh sh.
set vl := BMINUS c z.
fold sh sl th tl c vh in Hsh, Hsl, Hth, Htl, Hc, Hec, Hevh, Fvh, Fc.
have Hzarg : Rabs (FT2R vh - FT2R sh) <= 3/8 * Omega.
{ replace (FT2R vh - FT2R sh) with
    (FT2R c + (FT2R vh - (FT2R sh + FT2R c))) by ring.
  eapply Rle_trans; [apply Rabs_triang |]. lra. }
have Fz : is_finite z = true.
{ unfold z. apply no_overflow_minus_is_finite; [exact Fvh | exact (proj1 Fhi) |].
  red. eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp |].
  have Hlt : Rabs (FT2R vh - FT2R sh) < Omega by lra.
  have He := half_ulp_below_overflow_dwplus _ Hlt. lra. }
have Hez : Rabs (FT2R z - (FT2R vh - FT2R sh)) <= /16 * Omega.
{ unfold z. rewrite -(BMINUS_round_correct t vh sh Fz).
  apply round_error_below_half_dwplus. lra. }
have Hvlarg : Rabs (FT2R c - FT2R z) <= 3/16 * Omega.
{ replace (FT2R c - FT2R z) with
    (- (FT2R vh - (FT2R sh + FT2R c)) -
       (FT2R z - (FT2R vh - FT2R sh))) by ring.
  eapply Rle_trans; [apply Rabs_triang |].
  rewrite !Rabs_Ropp. lra. }
have Fvl : is_finite vl = true.
{ unfold vl. apply no_overflow_minus_is_finite; [exact Fc | exact Fz |].
  red. eapply Rle_lt_trans;
    [apply round_abs_le_quarter_Omega;
     eapply Rle_trans; [exact Hvlarg |]; lra |]. lra. }
have Hvl : Rabs (FT2R vl) <= /4 * Omega.
{ unfold vl. rewrite -(BMINUS_round_correct t c z Fvl).
  apply round_abs_le_quarter_Omega.
  eapply Rle_trans; [exact Hvlarg |]. lra. }
have Hevl : Rabs (FT2R vl - (FT2R c - FT2R z)) <= /32 * Omega.
{ unfold vl. rewrite -(BMINUS_round_correct t c z Fvl).
  apply round_error_below_quarter_dwplus. lra. }
have Hvl7 : Rabs (FT2R vl) <= 7/32 * Omega.
{ replace (FT2R vl) with
    ((FT2R c - FT2R z) + (FT2R vl - (FT2R c - FT2R z))) by ring.
  eapply Rle_trans; [apply Rabs_triang |]. lra. }
set w := BPLUS tl vl.
have Hwarg : Rabs (FT2R tl + FT2R vl) <= /4 * Omega.
{ eapply Rle_trans; [apply Rabs_triang |]. lra. }
have Fw : is_finite w = true.
{ unfold w. apply no_overflow_sum_is_finite; [exact (proj2 Flo) | exact Fvl |].
  red. eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp |].
  have Hlt : Rabs (FT2R tl + FT2R vl) < /2 * Omega by lra.
  have He := half_ulp_below_half_dwplus _ Hlt. lra. }
have Hw : Rabs (FT2R w) <= /4 * Omega.
{ unfold w. rewrite -(BPLUS_round_correct t tl vl Fw).
  apply round_abs_le_quarter_Omega. exact Hwarg. }
have Hew : Rabs (FT2R w - (FT2R tl + FT2R vl)) <= /16 * Omega.
{ unfold w. rewrite -(BPLUS_round_correct t tl vl Fw).
  apply round_error_below_half_dwplus. lra. }
have Hinputs : Rabs (FT2R xh + FT2R xl + (FT2R yh + FT2R yl))
                 <= 5/8 * Omega.
{ replace (FT2R xh + FT2R xl + (FT2R yh + FT2R yl)) with
    ((FT2R xh + FT2R yh) + (FT2R xl + FT2R yl)) by ring.
  eapply Rle_trans; [apply Rabs_triang |]. lra. }
have Hfinalarg : Rabs (FT2R vh + FT2R w) <= 27/32 * Omega.
{ replace (FT2R vh + FT2R w) with
    ((FT2R xh + FT2R xl + (FT2R yh + FT2R yl)) +
     (FT2R c - (FT2R sl + FT2R th)) -
     (FT2R z - (FT2R vh - FT2R sh)) +
     (FT2R vl - (FT2R c - FT2R z)) +
     (FT2R w - (FT2R tl + FT2R vl))).
  - eapply Rle_trans; [apply Rabs_triang |].
    have H0 : Rabs
        ((FT2R xh + FT2R xl + (FT2R yh + FT2R yl)) +
         (FT2R c - (FT2R sl + FT2R th))) <= 22/32 * Omega.
    { eapply Rle_trans; [apply Rabs_triang |]. lra. }
    have H1 : Rabs
        ((FT2R xh + FT2R xl + (FT2R yh + FT2R yl)) +
         (FT2R c - (FT2R sl + FT2R th)) -
         (FT2R z - (FT2R vh - FT2R sh))) <= 24/32 * Omega.
    { replace (_ - _) with
        (((FT2R xh + FT2R xl + (FT2R yh + FT2R yl)) +
          (FT2R c - (FT2R sl + FT2R th))) +
         - (FT2R z - (FT2R vh - FT2R sh))) by ring.
      eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp. lra. }
    have H2 : Rabs
        ((FT2R xh + FT2R xl + (FT2R yh + FT2R yl)) +
         (FT2R c - (FT2R sl + FT2R th)) -
         (FT2R z - (FT2R vh - FT2R sh)) +
         (FT2R vl - (FT2R c - FT2R z))) <= 25/32 * Omega.
    { eapply Rle_trans; [apply Rabs_triang |]. lra. }
    lra.
  - unfold sh, sl, th, tl in *. rewrite Hcorrhi Hcorrlo. ring. }
have Fzh : is_finite (BPLUS vh w) = true.
{ apply no_overflow_sum_is_finite; [exact Fvh | exact Fw |].
  red. eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp |].
  have Hlt : Rabs (FT2R vh + FT2R w) < Omega by lra.
  have He := half_ulp_below_overflow_dwplus _ Hlt. lra. }
unfold DWPlusDW.
destruct (TwoSumF xh yh) as [shi sli] eqn:Ehi.
destruct (TwoSumF xl yl) as [thi tli] eqn:Elo.
cbn [fst snd]. unfold Fast2Sum. cbn.
unfold is_finite_p. cbn [fst snd].
cbv [vh w c vl z sh sl th tl TwoSumF_sum TwoSumF_err] in Fzh, Hw.
rewrite Ehi Elo in Fzh, Hw. cbn [fst snd] in Fzh, Hw.
split; [exact Fzh |].
apply TwoSum_acc_helpers.is_finite_FastSum_small; [exact Hw | exact Fzh].
Qed.

End DWPlusDWFinite.
