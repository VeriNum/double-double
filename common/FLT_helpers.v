(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Small helpers for Flocq's FLT format, independent of any operation. *)

Require Import vcfloat.VCFloat.
Require Import common.
From Flocq Require Import Pff2Flocq Core.
From Stdlib Require Import Reals.Reals.
Require Import mathcomp.ssreflect.ssreflect.

Section FLTHelpers.
Context {t : type} {STD : is_standard t}.

Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Notation ulp := (Ulp.ulp Zaux.radix2 fexp).
Notation Omega := (bpow Zaux.radix2 (femax t)).

Local Instance valid_fexp_inst : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.

Local Instance valid_flx_exp_inst :
  Generic_fmt.Valid_exp (FLX_exp (fprec t)).
Proof. apply FLX.FLX_exp_valid, fprec_gt_0. Qed.

Lemma generic_format_half_Omega :
  generic_format radix2 fexp (/2 * Omega).
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

Lemma generic_format_quarter_Omega :
  generic_format radix2 fexp (/4 * Omega).
Proof.
have -> : (/4 * Omega = bpow radix2 (femax t - 2))%R.
{ have -> : Omega = (bpow radix2 (femax t - 2) * bpow radix2 2)%R
    by rewrite -bpow_plus; f_equal; lia.
  have -> : bpow radix2 2 = 4%R by reflexivity.
  lra. }
apply Generic_fmt.generic_format_bpow.
unfold SpecFloat.fexp, SpecFloat.emin.
apply Z.max_lub; pose proof femax_lb t; pose proof fprec_lb t; lia.
Qed.

Lemma bpow_femax_fprec_le_quarter_Omega :
  bpow radix2 (femax t - fprec t) <= /4 * Omega.
Proof.
have -> : (/4 * Omega = bpow radix2 (femax t - 2))%R.
{ have -> : Omega = (bpow radix2 (femax t - 2) * bpow radix2 2)%R
    by rewrite -bpow_plus; f_equal; lia.
  have -> : bpow radix2 2 = 4%R by reflexivity.
  lra. }
apply bpow_le. pose proof fprec_lb t; lia.
Qed.

Lemma round_abs_le_abs_plus_half_ulp (v : R) :
  Rabs (round radix2 fexp
    (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) v)
    <= Rabs v + /2 * ulp v.
Proof.
have He := @Ulp.error_le_half_ulp radix2 fexp valid_fexp_inst choice v.
replace (round radix2 fexp (Znearest choice) v)
  with ((round radix2 fexp (Znearest choice) v - v) + v) at 1 by ring.
eapply Rle_trans; [apply Rabs_triang|].
rewrite Rplus_comm. apply Rplus_le_compat_l. exact He.
Qed.

Lemma ulp_below_overflow (v : R) :
  Rabs v < Omega -> ulp v <= bpow radix2 (femax t - fprec t).
Proof.
move => Hlt. destruct (Req_dec v 0) as [Hv0 | Hv0].
- rewrite Hv0.
  change (Ulp.ulp radix2 fexp 0) with
    (Ulp.ulp radix2 (FLT.FLT_exp (3 - femax t - fprec t) (fprec t)) 0).
  rewrite FLT.ulp_FLT_0. apply bpow_le.
  pose proof femax_lb t; pose proof fprec_lb t; lia.
- rewrite (Ulp.ulp_neq_0 radix2 fexp _ Hv0). apply bpow_le.
  have Hmag : (mag radix2 v <= femax t)%Z
    by apply (mag_le_bpow radix2 v (femax t) Hv0 Hlt).
  unfold cexp, SpecFloat.fexp, SpecFloat.emin.
  apply Z.max_lub; pose proof femax_lb t; pose proof fprec_lb t; lia.
Qed.

Lemma generic_format_below_emin_eq_zero (x : R) :
  generic_format radix2 fexp x ->
  Rabs x < bpow radix2 (common.emin (t:=t)) -> x = 0.
Proof.
move => Hf Hlt. destruct (Req_dec x 0) as [Hx0 | Hx0]; [exact Hx0|].
exfalso.
have Hule : ulp x <= Rabs x.
{ apply Ulp.ulp_le_abs; first [exact Hx0 | exact Hf]. }
have Hge : bpow radix2 (common.emin (t:=t)) <= ulp x.
{ rewrite (Ulp.ulp_neq_0 radix2 fexp _ Hx0). apply bpow_le.
  unfold cexp, SpecFloat.fexp, SpecFloat.emin, common.emin.
  apply Z.le_max_r. }
lra.
Qed.

(** Universal FLT ulp bound: a relative step plus the subnormal floor. *)
Lemma ulp_le_relative_plus_emin (v : R) :
  ulp v <= 2 * bpow radix2 (- fprec t) * Rabs v +
    bpow radix2 (common.emin (t:=t)).
Proof.
have HE0 : 0 <= bpow radix2 (common.emin (t:=t)) by apply bpow_ge_0.
have Hvp : 0 <= Rabs v by apply Rabs_pos.
have Hu0 : 0 <= bpow radix2 (- fprec t) by apply bpow_ge_0.
destruct (Rle_lt_dec
  (bpow radix2 (common.emin (t:=t) + fprec t - 1)) (Rabs v)) as [Hn | Hs].
- have Hle : ulp v <= Rabs v * bpow radix2 (1 - fprec t)
    by apply ulp_FLT_le.
  have HBe : bpow radix2 (1 - fprec t) =
      2 * bpow radix2 (- fprec t).
  { replace (1 - fprec t)%Z with (1 + - fprec t)%Z by lia.
    rewrite bpow_plus.
    have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
  rewrite HBe in Hle. nra.
- have Heq : ulp v = bpow radix2 (common.emin (t:=t)).
  { apply ulp_FLT_small; first [apply fprec_gt_0 |
      eapply Rlt_trans; [exact Hs | apply bpow_lt; lia]]. }
  rewrite Heq.
  have := bpow_ge_0 radix2 (- fprec t).
  have := Rabs_pos v. nra.
Qed.

(** Universal FLT rounding error bound: a relative term plus half the
    subnormal floor. *)
Lemma round_FLT_error_rel_emin (v : R) :
  Rabs (round radix2 fexp (Znearest choice) v - v) <=
    bpow radix2 (- fprec t) * Rabs v +
    /2 * bpow radix2 (common.emin (t:=t)).
Proof.
have He := @Ulp.error_le_half_ulp radix2 fexp valid_fexp_inst choice v.
have Hu := ulp_le_relative_plus_emin v.
eapply Rle_trans; [exact He|]. nra.
Qed.

Lemma round_abs_le_relative_plus_half_emin (v : R) :
  Rabs (round radix2 fexp (Znearest choice) v) <=
  (1 + bpow radix2 (- fprec t)) * Rabs v +
    /2 * bpow radix2 (common.emin (t:=t)).
Proof.
eapply Rle_trans; [apply round_abs_le_abs_plus_half_ulp|].
have Hulp := ulp_le_relative_plus_emin v. nra.
Qed.

Lemma round_abs_le_of_abs_bound (v c : R) :
  Rabs v <= c ->
  Rabs (round radix2 fexp (Znearest choice) v) <=
  c * (1 + bpow radix2 (- fprec t)) +
    /2 * bpow radix2 (common.emin (t:=t)).
Proof.
move => Hv.
eapply Rle_trans; [apply round_abs_le_relative_plus_half_emin|].
have Hu0 : 0 <= bpow radix2 (- fprec t) by apply bpow_ge_0.
have := Rabs_pos v. nra.
Qed.

Lemma bpow_femax_minus_two :
  bpow radix2 (femax t - 2) = /4 * Omega.
Proof.
have -> : Omega = (bpow radix2 (femax t - 2) * bpow radix2 2)%R
  by rewrite -bpow_plus; f_equal; lia.
have -> : bpow radix2 2 = 4%R by reflexivity. lra.
Qed.

Lemma ulp_le_lin (v : R) :
  ulp v <= Rabs v * bpow radix2 (1 - fprec t) +
    bpow radix2 (common.emin (t:=t)).
Proof.
have Hu := ulp_le_relative_plus_emin v.
have Hb : bpow radix2 (1 - fprec t) =
    2 * bpow radix2 (-fprec t).
{ replace (1 - fprec t)%Z with (1 + -fprec t)%Z by lia.
  rewrite bpow_plus. have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
rewrite Hb. nra.
Qed.

Lemma nonzero_float_abs_ge_emin (y : ftype t) :
  FT2R y <> 0 ->
  bpow radix2 (common.emin (t:=t)) <= Rabs (FT2R y).
Proof.
move => Hy.
have H1 : ulp (FT2R y) <= Rabs (FT2R y)
  by apply ulp_le_abs; [exact Hy | apply generic_format_FLT_FT2R].
have Hlb : bpow radix2 (common.emin (t:=t)) <= ulp (FT2R y).
{ rewrite (Ulp.ulp_neq_0 radix2 fexp _ Hy). apply bpow_le.
  unfold cexp, SpecFloat.fexp, common.emin, SpecFloat.emin.
  apply Z.le_max_r. }
lra.
Qed.

Lemma round_ub_emin (v : R) :
  Rabs (round radix2 fexp (Znearest choice) v) <=
    Rabs v + Rabs v * bpow radix2 (-fprec t) +
      /2 * bpow radix2 (common.emin (t:=t)).
Proof.
have H := round_abs_le_relative_plus_half_emin v.
have Hu := bpow_ge_0 radix2 (-fprec t).
have Hv := Rabs_pos v. nra.
Qed.

Lemma round_err_emin (v : R) :
  Rabs (round radix2 fexp (Znearest choice) v - v) <=
    Rabs v * bpow radix2 (-fprec t) +
      /2 * bpow radix2 (common.emin (t:=t)).
Proof.
have H := round_FLT_error_rel_emin v.
rewrite Rmult_comm. exact H.
Qed.

(** FLT and FLX rounding can differ only by one underflow floor ulp. *)
Lemma round_FLT_FLX_diff (v : R) :
  Rabs (round radix2 fexp (Znearest choice) v
        - round radix2 (FLX_exp (fprec t)) (Znearest choice) v)
    <= bpow radix2 (common.emin (t:=t)).
Proof.
destruct (Rle_lt_dec
  (bpow radix2 (common.emin (t:=t) + fprec t - 1)) (Rabs v))
  as [Hn | Hs].
- rewrite round_FLT_FLX; [|exact Hn].
  rewrite Rminus_diag Rabs_R0. apply bpow_ge_0.
- destruct (Req_dec v 0) as [Hv0 | Hvn].
  + subst v. rewrite !round_0 Rminus_diag Rabs_R0. apply bpow_ge_0.
  + have Ef : Rabs (round radix2 fexp (Znearest choice) v - v) <=
        /2 * ulp v
      by apply (@error_le_half_ulp radix2 fexp valid_fexp_inst choice v).
    have Ex : Rabs (round radix2 (FLX_exp (fprec t)) (Znearest choice) v - v)
          <= /2 * Ulp.ulp radix2 (FLX_exp (fprec t)) v
      by apply (@error_le_half_ulp radix2 (FLX_exp (fprec t))
           valid_flx_exp_inst choice v).
    have Hle : Ulp.ulp radix2 (FLX_exp (fprec t)) v <= ulp v.
    { rewrite !ulp_neq_0 //. apply bpow_le.
      unfold cexp, FLX_exp, SpecFloat.fexp. apply Z.le_max_l. }
    have Hbnd : Rabs v < bpow radix2 (common.emin (t:=t) + fprec t).
    { eapply Rlt_le_trans; [exact Hs |]. apply bpow_le.
      unfold common.emin. lia. }
    have Hulp : ulp v = bpow radix2 (common.emin (t:=t))
      by apply (@ulp_FLT_small radix2 (common.emin (t:=t))
           (fprec t) (fprec_gt_0 t) v Hbnd).
    have Htri :
      Rabs (round radix2 fexp (Znearest choice) v
            - round radix2 (FLX_exp (fprec t)) (Znearest choice) v)
      <= Rabs (round radix2 fexp (Znearest choice) v - v) +
         Rabs (round radix2 (FLX_exp (fprec t)) (Znearest choice) v - v).
    { replace (round radix2 fexp (Znearest choice) v
               - round radix2 (FLX_exp (fprec t)) (Znearest choice) v)
        with ((round radix2 fexp (Znearest choice) v - v) +
              -(round radix2 (FLX_exp (fprec t)) (Znearest choice) v - v))
        by ring.
      eapply Rle_trans; [apply Rabs_triang |].
      rewrite Rabs_Ropp. apply Rle_refl. }
    rewrite -Hulp. eapply Rle_trans; [exact Htri |]. nra.
Qed.

Lemma round_FLT_error_max_emin (v c : R) :
  Rabs v <= c ->
  Rabs (round radix2 fexp (Znearest choice) v - v) <=
    Rmax (c * bpow radix2 (-fprec t))
         (/2 * bpow radix2 (common.emin (t:=t))).
Proof.
move => Hv.
have He := @Ulp.error_le_half_ulp radix2 fexp valid_fexp_inst choice v.
have Hvp := Rabs_pos v.
have Hu0 : 0 <= bpow radix2 (-fprec t) by apply bpow_ge_0.
destruct (Rle_lt_dec
  (bpow radix2 (common.emin (t:=t) + fprec t - 1)) (Rabs v))
  as [Hn | Hs].
- have Hle : ulp v <= Rabs v * bpow radix2 (1 - fprec t)
    by apply ulp_FLT_le.
  have HBe : bpow radix2 (1 - fprec t) =
      2 * bpow radix2 (-fprec t).
  { replace (1 - fprec t)%Z with (1 + -fprec t)%Z by lia.
    rewrite bpow_plus.
    have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
  rewrite HBe in Hle.
  eapply Rle_trans; [exact He |].
  eapply Rle_trans; [|apply Rmax_l]. nra.
- have Heq : ulp v = bpow radix2 (common.emin (t:=t)).
  { apply ulp_FLT_small; first [apply fprec_gt_0 |
      eapply Rlt_trans; [exact Hs | apply bpow_lt; lia]]. }
  eapply Rle_trans; [exact He |]. rewrite Heq. apply Rmax_r.
Qed.

Lemma fix_format_lower (x : R) (e1 e2 : Z) :
  (e1 <= e2)%Z ->
  generic_format radix2 (FIX_exp e2) x ->
  generic_format radix2 (FIX_exp e1) x.
Proof.
move => He Fx.
eapply (@generic_inclusion_mag radix2 (FIX_exp e2) (FIX_exp e1) x).
- move => _. unfold FIX_exp. exact He.
- exact Fx.
Qed.

End FLTHelpers.
