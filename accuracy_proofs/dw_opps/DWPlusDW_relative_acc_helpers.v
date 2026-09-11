(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Helper lemmas for the relative accuracy proof of [DWPlusDW]. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common FLT_lemmas DW_acc_lemmas.
Require Import TwoSum_acc Fast2Sum_acc.
Require Import DD.accuracy_proofs.dw_opps.DWPlus_finite.
Require Import DDConds DWord_defs.
Require DWPlus.
From Flocq Require Import Pff2Flocq Core.

Require Import mathcomp.ssreflect.ssreflect.

Section DWPlusDWFinite.
Context {NANS: Nans} {t : type} {STD: is_standard t}.
Variables (xh xl yh yl : ftype t).

Hypothesis DWx : double_word xh xl.
Hypothesis DWy : double_word yh yl.

Hypothesis HFINxh : is_finite xh = true.
Hypothesis HFINxl : is_finite xl = true.
Hypothesis HFINyh : is_finite yh = true.
Hypothesis HFINyl : is_finite yl = true.

Hypothesis Hxh : Rabs (FT2R xh) <= /4 * bpow radix2 (femax t).
Hypothesis Hyh : Rabs (FT2R yh) <= /4 * bpow radix2 (femax t).

Hypothesis Hprec : (3 <= fprec t)%Z.

Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Notation Omega := (bpow radix2 (femax t)).

Let sh := TwoSumF_sum xh yh.
Let sl := TwoSumF_err xh yh.
Let th := TwoSumF_sum xl yl.
Let tl := TwoSumF_err xl yl.
Let c  := BPLUS sl th.
Let vh := Fast2Sum_sum sh c.
Let vl := Fast2Sum_err sh c.
Let w  := BPLUS tl vl.

Lemma Hxh_tight_bnd : Rabs (FT2R xh) <= /4 * Omega.
Proof. exact Hxh. Qed.

Lemma Hyh_tight_bnd : Rabs (FT2R yh) <= /4 * Omega.
Proof. exact Hyh. Qed.

Lemma two_mul_bpow : forall e : Z, bpow radix2 e * 2 = bpow radix2 (e + 1).
Proof.
intros e.
have H2 : (2:R) = bpow radix2 1 by (simpl; lra).
rewrite H2 -bpow_plus. f_equal; lia.
Qed.

Lemma pos_sub_fprec : Z.pos_sub 1 (fprecp t) = (- fprec t + 1)%Z.
Proof. rewrite -Pos2Z.add_pos_neg fprec_eq. lia. Qed.

Lemma uro_eq_rel : / 2 * bpow radix2 (Z.pos_sub 1 (fprecp t)) = default_rel t.
Proof. unfold default_rel. rewrite pos_sub_fprec. reflexivity. Qed.

Lemma default_rel_pos : 0 < default_rel t.
Proof. unfold default_rel. have := bpow_gt_0 radix2 (- fprec t + 1). lra. Qed.

Lemma default_rel_le8 : default_rel t <= /8.
Proof.
unfold default_rel.
have Hle : bpow radix2 (- fprec t + 1) <= bpow radix2 (-2)
  by (apply bpow_le; lia).
have Heq : bpow radix2 (-2) = /4 by (simpl; lra).
rewrite Heq in Hle. lra.
Qed.

Lemma uro_frac_le8 : forall d : R,
  Rabs d <= Relative.u_ro radix2 (fprec t) / (1 + Relative.u_ro radix2 (fprec t)) ->
  Rabs d <= /8.
Proof.
intros d Hd.
have Hule : Relative.u_ro radix2 (fprec t) <= /8.
{ unfold Relative.u_ro.
  have Hle : bpow radix2 (- fprec t + 1) <= bpow radix2 (-2) by (apply bpow_le; lia).
  have Heq : bpow radix2 (-2) = /4 by (simpl; lra).
  rewrite Heq in Hle. lra. }
have Hupos : 0 < Relative.u_ro radix2 (fprec t).
{ unfold Relative.u_ro. have := bpow_gt_0 radix2 (- fprec t + 1). lra. }
apply (Rle_trans _ _ _ Hd).
apply Rle_trans with (Relative.u_ro radix2 (fprec t)); [|exact Hule].
apply Rmult_le_reg_r with (1 + Relative.u_ro radix2 (fprec t)); [lra|].
have Heq : Relative.u_ro radix2 (fprec t) / (1 + Relative.u_ro radix2 (fprec t))
           * (1 + Relative.u_ro radix2 (fprec t)) = Relative.u_ro radix2 (fprec t)
  by (field; lra).
rewrite Heq. nra.
Qed.

Lemma no_ov_sh : Bplus_no_overflow t (FT2R xh) (FT2R yh).
Proof.
unfold Bplus_no_overflow.
have Hxhb := Hxh_tight_bnd.
have Hyhb := Hyh_tight_bnd.
pose proof (Plus_error.FLT_plus_error_N_ex Zaux.radix2
  (SpecFloat.emin (fprec t) (femax t)) (fprec t)
  (fun x0 : Z => negb (Z.even x0)) (FT2R xh) (FT2R yh)) as H.
destruct H as (d1 & Hd & B).
1,2: rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.
move: Hd. unfold default_rel, Relative.u_ro. simpl.
intros Hd. simpl in Hxhb, Hyhb.

set b := bpow radix2 (Z.pos_sub 1 (fprecp t)) in Hd.
have Hb : 0 < b by apply bpow_gt_0.
have HO : 0 < Omega by apply bpow_gt_0.
have Hpd : 0 <= Rabs d1 by apply Rabs_pos.

have Hmul : Rabs d1 * (1 + /2*b) <= /2*b.
{ have Hstep : Rabs d1 * (1 + /2*b) <= (/2*b/(1+/2*b)) * (1+/2*b)
    by (apply Rmult_le_compat_r; [lra | exact Hd]).
  have Heq : (/2*b/(1+/2*b)) * (1+/2*b) = /2*b by (field; lra).
  rewrite Heq in Hstep; exact Hstep. }
have Hd1 : Rabs d1 < 1 by nra.

rewrite Rabs_mult.
have Hsum : Rabs (FT2R xh + FT2R yh) <= /2 * Omega
  by (eapply Rle_trans; [apply Rabs_triang | lra]).
have H1d : Rabs (1 + d1) < 2
  by (eapply Rle_lt_trans; [apply Rabs_triang | rewrite Rabs_R1; lra]).
apply Rle_lt_trans with (/2*Omega * Rabs (1+d1)).
{ apply Rmult_le_compat_r; [apply Rabs_pos | exact Hsum]. }
apply Rlt_le_trans with (/2*Omega * 2).
{ apply Rmult_lt_compat_l; [lra | exact H1d]. }
lra.
Qed.

Lemma no_ov_minus_xhyh : Bminus_no_overflow t (FT2R xh) (FT2R yh).
Proof.
unfold Bminus_no_overflow.
have Hxhb := Hxh_tight_bnd.
have Hyhb := Hyh_tight_bnd.
pose proof (Plus_error.FLT_plus_error_N_ex Zaux.radix2
  (SpecFloat.emin (fprec t) (femax t)) (fprec t)
  (fun x0 : Z => negb (Z.even x0)) (FT2R xh) (-(FT2R yh))) as H.
destruct H as (d1 & Hd & B).
1,2: rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.
move: Hd. unfold default_rel, Relative.u_ro. simpl.
intros Hd. simpl in Hxhb, Hyhb.

set b := bpow radix2 (Z.pos_sub 1 (fprecp t)) in Hd.
have Hb : 0 < b by apply bpow_gt_0.
have HO : 0 < Omega by apply bpow_gt_0.
have Hpd : 0 <= Rabs d1 by apply Rabs_pos.
have Hmul : Rabs d1 * (1 + /2*b) <= /2*b.
{ have Hstep : Rabs d1 * (1 + /2*b) <= (/2*b/(1+/2*b)) * (1+/2*b)
    by (apply Rmult_le_compat_r; [lra | exact Hd]).
  have Heq : (/2*b/(1+/2*b)) * (1+/2*b) = /2*b by (field; lra).
  rewrite Heq in Hstep; exact Hstep. }
have Hd1 : Rabs d1 < 1 by nra.
rewrite Rabs_mult.
have Hsum : Rabs (FT2R xh + - FT2R yh) <= /2 * Omega
  by (eapply Rle_trans; [apply Rabs_triang | rewrite Rabs_Ropp; lra]).
have H1d : Rabs (1 + d1) < 2
  by (eapply Rle_lt_trans; [apply Rabs_triang | rewrite Rabs_R1; lra]).
apply Rle_lt_trans with (/2*Omega * Rabs (1+d1)).
{ apply Rmult_le_compat_r; [apply Rabs_pos | exact Hsum]. }
apply Rlt_le_trans with (/2*Omega * 2).
{ apply Rmult_lt_compat_l; [lra | exact H1d]. }
lra.
Qed.

Lemma FIN_sh : is_finite sh = true.
Proof.
unfold sh, TwoSumF_sum, TwoSumF, fst.
exact (no_overflow_sum_is_finite t xh yh HFINxh HFINyh no_ov_sh).
Qed.

Lemma FIN_sl : is_finite sl = true.
Proof.
unfold sl.
apply (is_finite_TwoSum xh yh).
- exact (no_overflow_sum_is_finite t xh yh HFINxh HFINyh no_ov_sh).
- exact (no_overflow_minus_is_finite t xh yh HFINxh HFINyh no_ov_minus_xhyh).
- apply (Rle_lt_trans _ (/4 * Omega));
    [exact Hyh_tight_bnd | exact Omega4_lt_predOmega].
Qed.

Lemma xl_ul_bnd : Rabs (FT2R xl) <= /2 * bpow radix2 (femax t - 1 - fprec t).
Proof.
have HDWxu := dw_ulp xh xl DWx.
refine (Rle_trans _ _ _ HDWxu _).
apply Rmult_le_compat_l; [nra | ].
have Hconv : bpow radix2 (femax t - 2) = /4 * bpow radix2 (femax t).
{ have H14 : (/ 4 : R) = bpow radix2 (-2).
  { simpl. lra. }
  rewrite H14. rewrite Rmult_comm. rewrite -bpow_plus. f_equal; lia. }
refine (Rle_trans _ (Ulp.ulp radix2 (SpecFloat.fexp (fprec t) (femax t))
                      (bpow radix2 (femax t - 2))) _ _ _).
- apply Ulp.ulp_le.
  apply BinarySingleNaN.fexp_correct. apply fprec_gt_0.
  apply FLT_exp_monotone.
  refine (Rle_trans _ _ _ Hxh_tight_bnd _).
  rewrite Hconv. rewrite Rabs_pos_eq;
    [nra | apply Rmult_le_pos; [lra | apply bpow_ge_0]].
- rewrite Ulp.ulp_bpow.
  apply bpow_le.
  unfold SpecFloat.fexp, SpecFloat.emin.
  pose proof fprec_lb t; pose proof femax_lb t; lia.
Qed.

Lemma yl_ul_bnd : Rabs (FT2R yl) <= /2 * bpow radix2 (femax t - 1 - fprec t).
Proof.
have HDWyu := dw_ulp yh yl DWy.
refine (Rle_trans _ _ _ HDWyu _).
apply Rmult_le_compat_l; [nra | ].
have Hconv : bpow radix2 (femax t - 2) = /4 * bpow radix2 (femax t).
{ have H14 : (/ 4 : R) = bpow radix2 (-2).
  { simpl. lra. }
  rewrite H14. rewrite Rmult_comm. rewrite -bpow_plus. f_equal; lia. }
refine (Rle_trans _ (Ulp.ulp radix2 (SpecFloat.fexp (fprec t) (femax t))
                      (bpow radix2 (femax t - 2))) _ _ _).
- apply Ulp.ulp_le.
  apply BinarySingleNaN.fexp_correct. apply fprec_gt_0.
  apply FLT_exp_monotone.
  refine (Rle_trans _ _ _ Hyh_tight_bnd _).
  rewrite Hconv. rewrite Rabs_pos_eq;
    [nra | apply Rmult_le_pos; [lra | apply bpow_ge_0]].
- rewrite Ulp.ulp_bpow.
  apply bpow_le.
  unfold SpecFloat.fexp, SpecFloat.emin.
  pose proof fprec_lb t; pose proof femax_lb t; lia.
Qed.

Lemma no_ov_th : Bplus_no_overflow t (FT2R xl) (FT2R yl).
Proof.
unfold Bplus_no_overflow.
have Hxl := xl_ul_bnd.
have Hyl := yl_ul_bnd.
pose proof (Plus_error.FLT_plus_error_N_ex Zaux.radix2
  (SpecFloat.emin (fprec t) (femax t)) (fprec t)
  (fun x0 : Z => negb (Z.even x0)) (FT2R xl) (FT2R yl)) as H.
destruct H as (d1 & Hd & B).
1,2: rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.
move: Hd. unfold default_rel, Relative.u_ro. simpl.
intros Hd. simpl in Hxl, Hyl.

set b := bpow radix2 (Z.pos_sub 1 (fprecp t)) in Hd.
have Hb : 0 < b by apply bpow_gt_0.
have Hpd : 0 <= Rabs d1 by apply Rabs_pos.
have Hmul : Rabs d1 * (1 + /2*b) <= /2*b.
{ have Hstep : Rabs d1 * (1 + /2*b) <= (/2*b/(1+/2*b)) * (1+/2*b)
    by (apply Rmult_le_compat_r; [lra | exact Hd]).
  have Heq : (/2*b/(1+/2*b)) * (1+/2*b) = /2*b by (field; lra).
  rewrite Heq in Hstep; exact Hstep. }
have Hd1 : Rabs d1 < 1 by nra.
rewrite Rabs_mult.
have Hsum : Rabs (FT2R xl + FT2R yl) <= bpow radix2 (femax t - 1 - fprec t)
  by (eapply Rle_trans; [apply Rabs_triang | lra]).
have H1d : Rabs (1 + d1) < 2
  by (eapply Rle_lt_trans; [apply Rabs_triang | rewrite Rabs_R1; lra]).
apply Rle_lt_trans with (bpow radix2 (femax t - 1 - fprec t) * Rabs (1+d1)).
{ apply Rmult_le_compat_r; [apply Rabs_pos | exact Hsum]. }
apply Rlt_le_trans with (bpow radix2 (femax t - 1 - fprec t) * 2).
{ apply Rmult_lt_compat_l; [apply bpow_gt_0 | exact H1d]. }
rewrite two_mul_bpow. apply bpow_le. pose proof fprec_lb t; lia.
Qed.

Lemma no_ov_minus_xlyl : Bminus_no_overflow t (FT2R xl) (FT2R yl).
Proof.
unfold Bminus_no_overflow.
have Hxl := xl_ul_bnd.
have Hyl := yl_ul_bnd.
pose proof (Plus_error.FLT_plus_error_N_ex Zaux.radix2
  (SpecFloat.emin (fprec t) (femax t)) (fprec t)
  (fun x0 : Z => negb (Z.even x0)) (FT2R xl) (-(FT2R yl))) as H.
destruct H as (d1 & Hd & B).
1,2: rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.
move: Hd. unfold default_rel, Relative.u_ro. simpl.
intros Hd. simpl in Hxl, Hyl.
set b := bpow radix2 (Z.pos_sub 1 (fprecp t)) in Hd.
have Hb : 0 < b by apply bpow_gt_0.
have Hpd : 0 <= Rabs d1 by apply Rabs_pos.
have Hmul : Rabs d1 * (1 + /2*b) <= /2*b.
{ have Hstep : Rabs d1 * (1 + /2*b) <= (/2*b/(1+/2*b)) * (1+/2*b)
    by (apply Rmult_le_compat_r; [lra | exact Hd]).
  have Heq : (/2*b/(1+/2*b)) * (1+/2*b) = /2*b by (field; lra).
  rewrite Heq in Hstep; exact Hstep. }
have Hd1 : Rabs d1 < 1 by nra.
rewrite Rabs_mult.
have Hsum : Rabs (FT2R xl + - FT2R yl) <= bpow radix2 (femax t - 1 - fprec t)
  by (eapply Rle_trans; [apply Rabs_triang | rewrite Rabs_Ropp; lra]).
have H1d : Rabs (1 + d1) < 2
  by (eapply Rle_lt_trans; [apply Rabs_triang | rewrite Rabs_R1; lra]).
apply Rle_lt_trans with (bpow radix2 (femax t - 1 - fprec t) * Rabs (1+d1)).
{ apply Rmult_le_compat_r; [apply Rabs_pos | exact Hsum]. }
apply Rlt_le_trans with (bpow radix2 (femax t - 1 - fprec t) * 2).
{ apply Rmult_lt_compat_l; [apply bpow_gt_0 | exact H1d]. }
rewrite two_mul_bpow. apply bpow_le. pose proof fprec_lb t; lia.
Qed.

Lemma FIN_th : is_finite th = true.
Proof.
unfold th, TwoSumF_sum, TwoSumF, fst.
exact (no_overflow_sum_is_finite t xl yl HFINxl HFINyl no_ov_th).
Qed.

Lemma yl_le_qOmega : Rabs (FT2R yl) <= /4 * Omega.
Proof.
apply (Rle_trans _ (/2 * bpow radix2 (femax t - 1 - fprec t))); [exact yl_ul_bnd|].
have Heq14 : /4 * Omega = bpow radix2 (femax t - 2).
{ have H14 : (/ 4 : R) = bpow radix2 (-2) by (simpl; lra).
  rewrite H14 -bpow_plus. f_equal; lia. }
have Heq12 : /2 * bpow radix2 (femax t - 1 - fprec t) =
             bpow radix2 (femax t - 2 - fprec t).
{ have H12 : (/ 2 : R) = bpow radix2 (-1) by (simpl; lra).
  rewrite H12 -bpow_plus. f_equal; lia. }
rewrite Heq12 Heq14. apply bpow_le. pose proof fprec_lb t; lia.
Qed.

Lemma FIN_tl : is_finite tl = true.
Proof.
unfold tl.
apply (is_finite_TwoSum xl yl).
- exact (no_overflow_sum_is_finite t xl yl HFINxl HFINyl no_ov_th).
- exact (no_overflow_minus_is_finite t xl yl HFINxl HFINyl no_ov_minus_xlyl).
- apply (Rle_lt_trans _ (/4 * Omega));
    [exact yl_le_qOmega | exact Omega4_lt_predOmega].
Qed.

Lemma ulp_finite_bnd : forall x : ftype t,
  is_finite x = true ->
  Ulp.ulp radix2 fexp (FT2R x) <= bpow radix2 (femax t - fprec t).
Proof.
intros x Hxfin.
have Hlt : Rabs (FT2R x) < Omega by apply is_finite_no_overflow.
destruct (Req_dec (FT2R x) 0) as [Hx0 | Hx0].
- rewrite Hx0.
  change (Ulp.ulp radix2 fexp 0) with
    (Ulp.ulp radix2 (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t)) 0).
  rewrite FLT.ulp_FLT_0.
  apply bpow_le.
  unfold SpecFloat.emin.
  pose proof femax_lb t. pose proof fprec_lb t. lia.
- rewrite (Ulp.ulp_neq_0 radix2 fexp _ Hx0).
  apply bpow_le.
  unfold Generic_fmt.cexp, SpecFloat.fexp, SpecFloat.emin.
  have Hmag := mag_le_bpow radix2 (FT2R x) (femax t) Hx0 Hlt.
  pose proof femax_lb t. pose proof fprec_lb t. lia.
Qed.

Lemma sl_bnd : Rabs (FT2R sl) <= /2 * bpow radix2 (femax t - fprec t).
Proof.
have HFIN : is_finite_p (TwoSumF xh yh) by split; [exact FIN_sh | exact FIN_sl].
have HDW := TwoSum_is_DW xh yh HFIN.
have Hdw := dw_ulp _ _ HDW.
change (Rabs (FT2R (TwoSumF_err xh yh)) <= /2 * bpow radix2 (femax t - fprec t)).
apply (Rle_trans _ _ _ Hdw).
apply Rmult_le_compat_l; [lra|].
exact (ulp_finite_bnd _ FIN_sh).
Qed.

Lemma tl_bnd : Rabs (FT2R tl) <= /2 * bpow radix2 (femax t - fprec t).
Proof.
have HFIN : is_finite_p (TwoSumF xl yl) by split; [exact FIN_th | exact FIN_tl].
have HDW := TwoSum_is_DW xl yl HFIN.
have Hdw := dw_ulp _ _ HDW.
change (Rabs (FT2R (TwoSumF_err xl yl)) <= /2 * bpow radix2 (femax t - fprec t)).
apply (Rle_trans _ _ _ Hdw).
apply Rmult_le_compat_l; [lra|].
exact (ulp_finite_bnd _ FIN_th).
Qed.

Lemma th_bnd : Rabs (FT2R th) <=
  bpow radix2 (femax t - 1 - fprec t) * (1 + default_rel t).
Proof.
have HFIN : is_finite (BPLUS xl yl) = true.
{ change (is_finite (TwoSumF_sum xl yl) = true); exact FIN_th. }
destruct (BPLUS_accurate' t xl yl HFIN) as (d & Hd & Heq).
have Hth_eq : FT2R th = (FT2R xl + FT2R yl) * (1 + d).
{ change (FT2R (TwoSumF_sum xl yl) = (FT2R xl + FT2R yl) * (1 + d)).
  change (TwoSumF_sum xl yl) with (BPLUS xl yl).
  exact Heq. }
rewrite Hth_eq.
have Hxl := xl_ul_bnd. have Hyl := yl_ul_bnd.
have Hbnd_xlyl : Rabs (FT2R xl + FT2R yl) <= bpow radix2 (femax t - 1 - fprec t).
{ apply (Rle_trans _ (Rabs (FT2R xl) + Rabs (FT2R yl))); [apply Rabs_triang|].
  have Heq12 : bpow radix2 (femax t - 1 - fprec t) =
               /2 * bpow radix2 (femax t - 1 - fprec t) +
               /2 * bpow radix2 (femax t - 1 - fprec t) by lra.
  rewrite Heq12. lra. }
rewrite Rabs_mult.
apply Rmult_le_compat; try apply Rabs_pos; [exact Hbnd_xlyl|].
have Hd1 : Rabs (1 + d) <= 1 + Rabs d.
{ apply (Rle_trans _ (Rabs 1 + Rabs d)); [apply Rabs_triang|].
  rewrite Rabs_R1. apply Rle_refl. }
apply (Rle_trans _ _ _ Hd1).
apply Rplus_le_compat_l. exact Hd.
Qed.

Lemma no_ov_c : Bplus_no_overflow t (FT2R sl) (FT2R th).
Proof.
unfold Bplus_no_overflow.
have Hsl := sl_bnd.
have Hth := th_bnd.
pose proof (Plus_error.FLT_plus_error_N_ex Zaux.radix2
  (SpecFloat.emin (fprec t) (femax t)) (fprec t)
  (fun x0 : Z => negb (Z.even x0)) (FT2R sl) (FT2R th)) as H.
destruct H as (d1 & Hd & B).
1,2: rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.
move: Hd. unfold default_rel, Relative.u_ro. simpl.
intros Hd.

set b := bpow radix2 (Z.pos_sub 1 (fprecp t)) in Hd.
have Hb : 0 < b by apply bpow_gt_0.
have Hpd : 0 <= Rabs d1 by apply Rabs_pos.
have Hmul : Rabs d1 * (1 + /2*b) <= /2*b.
{ have Hstep : Rabs d1 * (1 + /2*b) <= (/2*b/(1+/2*b)) * (1+/2*b)
    by (apply Rmult_le_compat_r; [lra | exact Hd]).
  have Heq : (/2*b/(1+/2*b)) * (1+/2*b) = /2*b by (field; lra).
  rewrite Heq in Hstep; exact Hstep. }
have Hd1 : Rabs d1 < 1 by nra.
rewrite Rabs_mult.
have HB : 0 < bpow radix2 (femax t - fprec t) by apply bpow_gt_0.
have HP : bpow radix2 (femax t - 1 - fprec t) = /2 * bpow radix2 (femax t - fprec t).
{ have HH := two_mul_bpow (femax t - 1 - fprec t).
  replace (femax t - 1 - fprec t + 1)%Z with (femax t - fprec t)%Z in HH by lia.
  lra. }
have Hrel : default_rel t <= /8 by apply default_rel_le8.
have Hrel0 : 0 < default_rel t by apply default_rel_pos.
rewrite HP in Hth.
have Hsum : Rabs (FT2R sl + FT2R th) <= 2 * bpow radix2 (femax t - fprec t).
{ eapply Rle_trans; [apply Rabs_triang|]. nra. }
have H1d : Rabs (1 + d1) < 2
  by (eapply Rle_lt_trans; [apply Rabs_triang | rewrite Rabs_R1; lra]).
apply Rle_lt_trans with (2 * bpow radix2 (femax t - fprec t) * Rabs (1+d1)).
{ apply Rmult_le_compat_r; [apply Rabs_pos | exact Hsum]. }
apply Rlt_le_trans with (2 * bpow radix2 (femax t - fprec t) * 2).
{ apply Rmult_lt_compat_l; [lra | exact H1d]. }
have H4a := two_mul_bpow (femax t - fprec t).
have H4b := two_mul_bpow (femax t - fprec t + 1).
replace (femax t - fprec t + 1 + 1)%Z with (femax t - fprec t + 2)%Z in H4b by lia.
have Hbnd : bpow radix2 (femax t - fprec t + 2) <= Omega by (apply bpow_le; lia).
lra.
Qed.

Lemma FIN_c : is_finite c = true.
Proof.
unfold c.
exact (no_overflow_sum_is_finite t sl th FIN_sl FIN_th no_ov_c).
Qed.

Lemma sh_bnd : Rabs (FT2R sh) <= /2 * Omega * (1 + default_rel t).
Proof.
have HFIN : is_finite (BPLUS xh yh) = true.
{ change (is_finite (TwoSumF_sum xh yh) = true); exact FIN_sh. }
destruct (BPLUS_accurate' t xh yh HFIN) as (d & Hd & Heq).
have Hsh_eq : FT2R sh = (FT2R xh + FT2R yh) * (1 + d).
{ change (FT2R (TwoSumF_sum xh yh) = (FT2R xh + FT2R yh) * (1 + d)).
  change (TwoSumF_sum xh yh) with (BPLUS xh yh); exact Heq. }
rewrite Hsh_eq.
have Hxhb := Hxh_tight_bnd. have Hyhb := Hyh_tight_bnd.
have Hbnd : Rabs (FT2R xh + FT2R yh) <= /2 * Omega.
{ apply (Rle_trans _ (Rabs (FT2R xh) + Rabs (FT2R yh))); [apply Rabs_triang|]. lra. }
rewrite Rabs_mult.
apply Rmult_le_compat; try apply Rabs_pos; [exact Hbnd|].
have Hd1 : Rabs (1 + d) <= 1 + Rabs d.
{ apply (Rle_trans _ (Rabs 1 + Rabs d)); [apply Rabs_triang|].
  rewrite Rabs_R1. apply Rle_refl. }
apply (Rle_trans _ _ _ Hd1). apply Rplus_le_compat_l. exact Hd.
Qed.

Lemma c_bnd : Rabs (FT2R c) <=
  (/2 * bpow radix2 (femax t - fprec t) +
   bpow radix2 (femax t - 1 - fprec t) * (1 + default_rel t)) *
  (1 + default_rel t).
Proof.
destruct (BPLUS_accurate' t sl th FIN_c) as (d & Hd & Heq).
have Hc_eq : FT2R c = (FT2R sl + FT2R th) * (1 + d).
{ change (FT2R (BPLUS sl th) = (FT2R sl + FT2R th) * (1 + d)); exact Heq. }
rewrite Hc_eq.
have Hsl := sl_bnd. have Hth := th_bnd.
have Hbnd : Rabs (FT2R sl + FT2R th) <=
  /2 * bpow radix2 (femax t - fprec t) +
  bpow radix2 (femax t - 1 - fprec t) * (1 + default_rel t).
{ apply (Rle_trans _ (Rabs (FT2R sl) + Rabs (FT2R th))); [apply Rabs_triang|]. lra. }
rewrite Rabs_mult.
apply Rmult_le_compat; try apply Rabs_pos; [exact Hbnd|].
have Hd1 : Rabs (1 + d) <= 1 + Rabs d.
{ apply (Rle_trans _ (Rabs 1 + Rabs d)); [apply Rabs_triang|].
  rewrite Rabs_R1. apply Rle_refl. }
apply (Rle_trans _ _ _ Hd1). apply Rplus_le_compat_l. exact Hd.
Qed.

Lemma no_ov_vh : Bplus_no_overflow t (FT2R sh) (FT2R c).
Proof.
unfold Bplus_no_overflow.
have Hsh := sh_bnd. have Hc := c_bnd.
pose proof (Plus_error.FLT_plus_error_N_ex Zaux.radix2
  (SpecFloat.emin (fprec t) (femax t)) (fprec t)
  (fun x0 : Z => negb (Z.even x0)) (FT2R sh) (FT2R c)) as H.
destruct H as (d1 & Hd & B).
1,2: rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.
move: Hd. unfold default_rel, Relative.u_ro. simpl.
intros Hd.

set b := bpow radix2 (Z.pos_sub 1 (fprecp t)) in Hd.
have Hb : 0 < b by apply bpow_gt_0.
have Hpd : 0 <= Rabs d1 by apply Rabs_pos.
have Hrelb : default_rel t = /2 * b by (rewrite -uro_eq_rel; reflexivity).
have Hmul : Rabs d1 * (1 + /2*b) <= /2*b.
{ have Hstep : Rabs d1 * (1 + /2*b) <= (/2*b/(1+/2*b)) * (1+/2*b)
    by (apply Rmult_le_compat_r; [lra | exact Hd]).
  have Heq : (/2*b/(1+/2*b)) * (1+/2*b) = /2*b by (field; lra).
  rewrite Heq in Hstep; exact Hstep. }
have Hd1le : Rabs d1 <= /2*b by nra.
have H1d : Rabs (1 + d1) <= 1 + default_rel t.
{ rewrite Hrelb. eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rabs_R1. lra. }
have HO : 0 < Omega by apply bpow_gt_0.
have HB : 0 < bpow radix2 (femax t - fprec t) by apply bpow_gt_0.
have HP : bpow radix2 (femax t - 1 - fprec t) = /2 * bpow radix2 (femax t - fprec t).
{ have HH := two_mul_bpow (femax t - 1 - fprec t).
  replace (femax t - 1 - fprec t + 1)%Z with (femax t - fprec t)%Z in HH by lia.
  lra. }
have HQO : bpow radix2 (femax t - fprec t) <= /8 * Omega.
{ have HH : /8 * Omega = bpow radix2 (femax t - 3).
  { have H8 : (/8:R) = bpow radix2 (-3) by (simpl; lra).
    rewrite H8 -bpow_plus. f_equal; lia. }
  rewrite HH. apply bpow_le. lia. }
have Hrel : default_rel t <= /8 by apply default_rel_le8.
have Hrel0 : 0 < default_rel t by apply default_rel_pos.
rewrite HP in Hc.
have HcA : /2 * bpow radix2 (femax t - fprec t) +
           /2 * bpow radix2 (femax t - fprec t) * (1 + default_rel t)
           <= 17/16 * bpow radix2 (femax t - fprec t) by nra.
have HcB : Rabs (FT2R c) <=
           17/16 * bpow radix2 (femax t - fprec t) * (1 + default_rel t).
{ apply (Rle_trans _ _ _ Hc).
  apply Rmult_le_compat_r; [lra | exact HcA]. }
have HcC : 17/16 * bpow radix2 (femax t - fprec t) * (1 + default_rel t)
           <= /4 * Omega by nra.
have HcO : Rabs (FT2R c) <= /4 * Omega by (apply (Rle_trans _ _ _ HcB HcC)).
rewrite Rabs_mult.
apply Rle_lt_trans with
  ((/2*Omega*(1+default_rel t) + /4*Omega) * Rabs (1+d1)).
{ apply Rmult_le_compat_r; [apply Rabs_pos|].
  eapply Rle_trans; [apply Rabs_triang|].
  apply Rplus_le_compat; [exact Hsh | exact HcO]. }
apply Rle_lt_trans with
  ((/2*Omega*(1+default_rel t) + /4*Omega) * (1 + default_rel t)).
{ apply Rmult_le_compat_l; [nra | exact H1d]. }

have Hfac : (/2*(1+default_rel t) + /4) * (1 + default_rel t) < 1 by nra.
have Hring : (/2*Omega*(1+default_rel t) + /4*Omega) * (1 + default_rel t) =
             Omega * ((/2*(1+default_rel t) + /4) * (1 + default_rel t)) by ring.
rewrite Hring -{2}(Rmult_1_r Omega).
apply Rmult_lt_compat_l; [exact HO | exact Hfac].
Qed.

Lemma FIN_vh : is_finite vh = true.
Proof.
unfold vh, Fast2Sum_sum, Fast2Sum, fst.
exact (no_overflow_sum_is_finite t sh c FIN_sh FIN_c no_ov_vh).
Qed.

Lemma no_ov_z : Bminus_no_overflow t (FT2R (BPLUS sh c)) (FT2R sh).
Proof.
have HFIN1 : is_finite (BPLUS sh c) = true.
{ have HFIN_vh := FIN_vh.
  unfold vh, Fast2Sum_sum, Fast2Sum, fst in HFIN_vh; exact HFIN_vh. }
rewrite /Bminus_no_overflow.
pose proof (Plus_error.FLT_plus_error_N_ex Zaux.radix2
  (SpecFloat.emin (fprec t) (femax t)) (fprec t)
  (fun x0 : Z => negb (Z.even x0)) (FT2R (BPLUS sh c)) (- FT2R sh)) as H.
destruct H as (d2 & Hd2 & B).
1,2: rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.
destruct (BPLUS_accurate' t sh c HFIN1) as (d1 & Hd1 & B1).
rewrite B1.
have Hsh := sh_bnd. have Hc := c_bnd.
move: Hd2. unfold Relative.u_ro. simpl. intros Hd2.

have Hd1_8 : Rabs d1 <= /8 by (apply (Rle_trans _ _ _ Hd1 default_rel_le8)).
have Hbpos : 0 < /2 * bpow radix2 (Z.pos_sub 1 (fprecp t))
  by (have := bpow_gt_0 radix2 (Z.pos_sub 1 (fprecp t)); lra).
have Hd2x : Rabs d2 <= /2 * bpow radix2 (Z.pos_sub 1 (fprecp t)).
{ have Hpd : 0 <= Rabs d2 by apply Rabs_pos.
  have Hmul : Rabs d2 * (1 + /2 * bpow radix2 (Z.pos_sub 1 (fprecp t)))
              <= /2 * bpow radix2 (Z.pos_sub 1 (fprecp t)).
  { have Hstep : Rabs d2 * (1 + /2 * bpow radix2 (Z.pos_sub 1 (fprecp t)))
        <= (/2 * bpow radix2 (Z.pos_sub 1 (fprecp t)) /
            (1 + /2 * bpow radix2 (Z.pos_sub 1 (fprecp t)))) *
           (1 + /2 * bpow radix2 (Z.pos_sub 1 (fprecp t)))
      by (apply Rmult_le_compat_r; [lra | exact Hd2]).
    have Heq : (/2 * bpow radix2 (Z.pos_sub 1 (fprecp t)) /
                (1 + /2 * bpow radix2 (Z.pos_sub 1 (fprecp t)))) *
               (1 + /2 * bpow radix2 (Z.pos_sub 1 (fprecp t)))
               = /2 * bpow radix2 (Z.pos_sub 1 (fprecp t)) by (field; lra).
    rewrite Heq in Hstep; exact Hstep. }
  nra. }
have Hd2_8 : Rabs d2 <= /8.
{ apply (Rle_trans _ _ _ Hd2x). rewrite uro_eq_rel. exact default_rel_le8. }
have HO : 0 < Omega by apply bpow_gt_0.
have Hrel : default_rel t <= /8 by apply default_rel_le8.
have Hrel0 : 0 < default_rel t by apply default_rel_pos.
have HB : 0 < bpow radix2 (femax t - fprec t) by apply bpow_gt_0.
have HP : bpow radix2 (femax t - 1 - fprec t) = /2 * bpow radix2 (femax t - fprec t).
{ have HH := two_mul_bpow (femax t - 1 - fprec t).
  replace (femax t - 1 - fprec t + 1)%Z with (femax t - fprec t)%Z in HH by lia.
  lra. }
have HQO : bpow radix2 (femax t - fprec t) <= /8 * Omega.
{ have HH : /8 * Omega = bpow radix2 (femax t - 3).
  { have H8 : (/8:R) = bpow radix2 (-3) by (simpl; lra).
    rewrite H8 -bpow_plus. f_equal; lia. }
  rewrite HH. apply bpow_le. lia. }
rewrite HP in Hc.
have HcA : /2 * bpow radix2 (femax t - fprec t) +
           /2 * bpow radix2 (femax t - fprec t) * (1 + default_rel t)
           <= 17/16 * bpow radix2 (femax t - fprec t) by nra.
have HcB : Rabs (FT2R c) <=
           17/16 * bpow radix2 (femax t - fprec t) * (1 + default_rel t).
{ apply (Rle_trans _ _ _ Hc).
  apply Rmult_le_compat_r; [lra | exact HcA]. }
have HcC : 17/16 * bpow radix2 (femax t - fprec t) * (1 + default_rel t)
           <= /4 * Omega by nra.
have HcO : Rabs (FT2R c) <= /4 * Omega by (apply (Rle_trans _ _ _ HcB HcC)).
have HSC : Rabs (FT2R sh) + Rabs (FT2R c) <= 13/16 * Omega.
{ apply (Rle_trans _ (/2*Omega*(1+default_rel t) + /4*Omega));
    [apply Rplus_le_compat; [exact Hsh | exact HcO] | nra]. }
rewrite Rabs_mult.
have Hrw : (FT2R sh + FT2R c) * (1 + d1) + - FT2R sh
           = FT2R c + (FT2R sh + FT2R c) * d1 by ring.
rewrite Hrw.
have Hinner : Rabs (FT2R c + (FT2R sh + FT2R c) * d1)
              <= /4 * Omega + 13/16 * Omega * (/8).
{ eapply Rle_trans; [apply Rabs_triang|].
  apply Rplus_le_compat; [exact HcO|].
  rewrite Rabs_mult.
  apply Rle_trans with ((Rabs (FT2R sh) + Rabs (FT2R c)) * Rabs d1).
  - apply Rmult_le_compat_r; [apply Rabs_pos | apply Rabs_triang].
  - apply Rmult_le_compat;
      [apply Rplus_le_le_0_compat; apply Rabs_pos | apply Rabs_pos
       | exact HSC | exact Hd1_8]. }
apply Rle_lt_trans with ((/4*Omega + 13/16*Omega*(/8)) * Rabs (1+d2)).
{ apply Rmult_le_compat_r; [apply Rabs_pos | exact Hinner]. }
apply Rle_lt_trans with ((/4*Omega + 13/16*Omega*(/8)) * (9/8)).
{ apply Rmult_le_compat_l; [nra|].
  eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_R1. lra. }
nra.
Qed.

Lemma FIN_z : is_finite (BMINUS (BPLUS sh c) sh) = true.
Proof.
have HFIN1 : is_finite (BPLUS sh c) = true.
{ have HFIN_vh := FIN_vh.
  unfold vh, Fast2Sum_sum, Fast2Sum, fst in HFIN_vh; exact HFIN_vh. }
exact (no_overflow_minus_is_finite t (BPLUS sh c) sh HFIN1 FIN_sh no_ov_z).
Qed.

Lemma FIN_vl : is_finite vl = true.
Proof.
unfold vl, Fast2Sum_err, Fast2Sum, snd.
have HFIN1 : is_finite (BPLUS sh c) = true.
{ have HFIN_vh := FIN_vh.
  unfold vh, Fast2Sum_sum, Fast2Sum, fst in HFIN_vh; exact HFIN_vh. }
have HFIN_z := FIN_z.
apply (no_overflow_minus_is_finite t c (BMINUS (BPLUS sh c) sh) FIN_c HFIN_z).
rewrite /Bminus_no_overflow.

have Hz_eq : FT2R (BMINUS (BPLUS sh c) sh) =
             round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
               (Znearest choice) (FT2R (BPLUS sh c) - FT2R sh).
{ symmetry. exact (BMINUS_round_correct t (BPLUS sh c) sh HFIN_z). }
rewrite Hz_eq.

have Hvexp : Valid_exp (SpecFloat.fexp (fprec t) (femax t))
  by (apply FLT.FLT_exp_valid; apply fprec_gt_0).
have Hvrnd : Valid_rnd (Znearest choice) := Generic_fmt.valid_rnd_N choice.
have Hfmt_z : Generic_fmt.generic_format Zaux.radix2
  (SpecFloat.fexp (fprec t) (femax t))
  (round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
    (Znearest choice) (FT2R (BPLUS sh c) - FT2R sh))
  by apply Generic_fmt.generic_format_round.
pose proof (Plus_error.FLT_plus_error_N_ex Zaux.radix2
  (SpecFloat.emin (fprec t) (femax t)) (fprec t)
  (fun x0 : Z => negb (Z.even x0)) (FT2R c)
  (- round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
       (Znearest choice) (FT2R (BPLUS sh c) - FT2R sh))) as H.
destruct H as (d3 & Hd3 & B).
- rewrite -B2R_float_of_ftype. apply Binary.generic_format_B2R.
- apply Generic_fmt.generic_format_opp. exact Hfmt_z.
- have Heq : FT2R c +
    - round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
        (FT2R (BPLUS sh c) - FT2R sh) =
    FT2R c -
    round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
        (FT2R (BPLUS sh c) - FT2R sh) by ring.
  rewrite Heq in B. rewrite B. clear B Heq.

  pose proof (Plus_error.FLT_plus_error_N_ex Zaux.radix2
    (SpecFloat.emin (fprec t) (femax t)) (fprec t)
    (fun x0 : Z => negb (Z.even x0)) (FT2R (BPLUS sh c)) (- FT2R sh)) as H2.
  destruct H2 as (d2 & Hd2 & B2).
  1,2: rewrite -B2R_float_of_ftype; try
    apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
  have Heq2 : FT2R (BPLUS sh c) + - FT2R sh = FT2R (BPLUS sh c) - FT2R sh by ring.
  rewrite Heq2 in B2. rewrite B2. clear B2 Heq2.

  destruct (BPLUS_accurate' t sh c HFIN1) as (d1 & Hd1 & B1).
  rewrite B1.
  have Hsh := sh_bnd. have Hc := c_bnd.

  have Hd1_8 : Rabs d1 <= /8 by (apply (Rle_trans _ _ _ Hd1 default_rel_le8)).
  have Hd2_8 : Rabs d2 <= /8 by (apply uro_frac_le8; exact Hd2).
  have Hd3_8 : Rabs d3 <= /8 by (apply uro_frac_le8; exact Hd3).
  have HO : 0 < Omega by apply bpow_gt_0.
  have Hrel : default_rel t <= /8 by apply default_rel_le8.
  have Hrel0 : 0 < default_rel t by apply default_rel_pos.
  have HB : 0 < bpow radix2 (femax t - fprec t) by apply bpow_gt_0.
  have HP : bpow radix2 (femax t - 1 - fprec t) = /2 * bpow radix2 (femax t - fprec t).
  { have HH := two_mul_bpow (femax t - 1 - fprec t).
    replace (femax t - 1 - fprec t + 1)%Z with (femax t - fprec t)%Z in HH by lia.
    lra. }
  have HQO : bpow radix2 (femax t - fprec t) <= /8 * Omega.
  { have HH : /8 * Omega = bpow radix2 (femax t - 3).
    { have H8 : (/8:R) = bpow radix2 (-3) by (simpl; lra).
      rewrite H8 -bpow_plus. f_equal; lia. }
    rewrite HH. apply bpow_le. lia. }
  rewrite HP in Hc.
  have HcA : /2 * bpow radix2 (femax t - fprec t) +
             /2 * bpow radix2 (femax t - fprec t) * (1 + default_rel t)
             <= 17/16 * bpow radix2 (femax t - fprec t) by nra.
  have HcB : Rabs (FT2R c) <=
             17/16 * bpow radix2 (femax t - fprec t) * (1 + default_rel t).
  { apply (Rle_trans _ _ _ Hc).
    apply Rmult_le_compat_r; [lra | exact HcA]. }
  have HcC : 17/16 * bpow radix2 (femax t - fprec t) * (1 + default_rel t)
             <= /4 * Omega by nra.
  have HcO : Rabs (FT2R c) <= /4 * Omega by (apply (Rle_trans _ _ _ HcB HcC)).
  have HM : Rabs (FT2R sh + FT2R c) <= 13/16 * Omega.
  { eapply Rle_trans; [apply Rabs_triang|].
    apply (Rle_trans _ (/2*Omega*(1+default_rel t) + /4*Omega));
      [apply Rplus_le_compat; [exact Hsh | exact HcO] | nra]. }
  have Hcm : Rabs (FT2R c + (FT2R sh + FT2R c) * d1)
             <= /4 * Omega + 13/16 * Omega * (/8).
  { eapply Rle_trans; [apply Rabs_triang|].
    apply Rplus_le_compat; [exact HcO|].
    rewrite Rabs_mult.
    apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact HM | exact Hd1_8]. }
  have Hrw : FT2R c - ((FT2R sh + FT2R c) * (1 + d1) - FT2R sh) * (1 + d2)
             = (- ((FT2R sh + FT2R c) * d1))
               + (- ((FT2R c + (FT2R sh + FT2R c) * d1) * d2)) by ring.
  rewrite Hrw Rabs_mult.
  have Hval : Rabs ((- ((FT2R sh + FT2R c) * d1))
                    + (- ((FT2R c + (FT2R sh + FT2R c) * d1) * d2)))
              <= /4 * Omega.
  { eapply Rle_trans; [apply Rabs_triang|].
    rewrite !Rabs_Ropp !Rabs_mult.
    apply Rle_trans with
      (13/16*Omega*(/8) + (/4*Omega + 13/16*Omega*(/8))*(/8)).
    - apply Rplus_le_compat.
      + apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact HM | exact Hd1_8].
      + apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hcm | exact Hd2_8].
    - nra. }
  apply Rle_lt_trans with (/4 * Omega * Rabs (1+d3)).
  { apply Rmult_le_compat_r; [apply Rabs_pos | exact Hval]. }
  apply Rle_lt_trans with (/4 * Omega * (9/8)).
  { apply Rmult_le_compat_l; [lra|].
    eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_R1. lra. }
  lra.
Qed.

Lemma ulp_le_abs (a b : R) :
  Rabs b <= Rabs a ->
  (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) b <=
   Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) a)%R.
Proof.
intro Hab.
apply Ulp.ulp_le;
  [ apply BinarySingleNaN.fexp_correct; apply fprec_gt_0
  | apply FLT_exp_monotone
  | exact Hab ].
Qed.

Lemma DWPlusDW_sh_c_disjunction :
  (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (FT2R c) <=
   Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (FT2R sh))%R
  \/ FT2R sh = 0%R.
Proof.

destruct (Req_dec (FT2R sh) 0) as [Hsh0 | Hsh_nz]; [right; exact Hsh0 | left].

destruct (Req_dec (FT2R c) 0) as [Hc0 | Hc_nz].
{ rewrite Hc0. apply ulp_le_abs. rewrite Rabs_R0; apply Rabs_pos. }

have HFIN_sh : is_finite (BPLUS xh yh) = true.
{ change (is_finite (TwoSumF_sum xh yh) = true); exact FIN_sh. }
destruct (Req_dec (FT2R xh + FT2R yh) 0) as [Hxhyh_zero | Hxhyh_nz].
{ exfalso. apply Hsh_nz.
  destruct (BPLUS_accurate' t xh yh HFIN_sh) as (d & _ & Heq).
  change (FT2R (TwoSumF_sum xh yh) = 0).
  change (TwoSumF_sum xh yh) with (BPLUS xh yh).
  rewrite Heq Hxhyh_zero Rmult_0_l; reflexivity. }
have DWx_R : DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl)
  by apply (dw_word_DWdouble xh xl xh DWx).
have DWy_R : DWPlus.double_word (fprec t) choice (FT2R yh) (FT2R yl)
  by apply (dw_word_DWdouble yh yl yh DWy).
have fin_tsxhyh : is_finite_p (TwoSumF xh yh) by split; [exact FIN_sh | exact FIN_sl].
have fin_tsxlyl : is_finite_p (TwoSumF xl yl) by split; [exact FIN_th | exact FIN_tl].
have heq_xhyh : DWPlus.TwoSum (fprec t) choice (FT2R xh) (FT2R yh) = F2Rp (TwoSumF xh yh)
  by exact (TwoSumEq_FLT xh yh fin_tsxhyh).
have heq_xlyl : DWPlus.TwoSum (fprec t) choice (FT2R xl) (FT2R yl) = F2Rp (TwoSumF xl yl)
  by exact (TwoSumEq_FLT xl yl fin_tsxlyl).
have Hsh_eq : DWPlus.TwoSum_sum (fprec t) choice (FT2R xh) (FT2R yh) = FT2R sh.
{ unfold DWPlus.TwoSum_sum. rewrite heq_xhyh /F2Rp /fst //. }
have Hsl_eq : DWPlus.TwoSum_err (fprec t) choice (FT2R xh) (FT2R yh) = FT2R sl.
{ unfold DWPlus.TwoSum_err. rewrite heq_xhyh /F2Rp /snd //. }
have Hth_eq : DWPlus.TwoSum_sum (fprec t) choice (FT2R xl) (FT2R yl) = FT2R th.
{ unfold DWPlus.TwoSum_sum. rewrite heq_xlyl /F2Rp /fst //. }
have Hc_eq :
  round Zaux.radix2 (FLX_exp (fprec t)) (Znearest choice)
    (DWPlus.TwoSum_err (fprec t) choice (FT2R xh) (FT2R yh) +
     DWPlus.TwoSum_sum (fprec t) choice (FT2R xl) (FT2R yl)) = FT2R c.
{ rewrite Hsl_eq Hth_eq rnd_plus_FLT_FLX_eq'.
  change (FT2R c) with (FT2R (BPLUS sl th)).
  apply BPLUS_round_correct. exact FIN_c. }
have Hp3 : (3 <= fprec t)%Z by exact Hprec.
destruct (@DWPlus.DWPlusDW_sh_c_cexp_or_zero (fprec t) (fprec_gt_one t)
            choice (eq_refl _) Hp3
            (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl) DWx_R DWy_R)
  as [Hcexp_FLX | [Hsh_FLX_0 | Hc_FLX_0]].
-
  have Hcexp : (Generic_fmt.cexp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (FT2R c) <=
                Generic_fmt.cexp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (FT2R sh))%Z.
  { rewrite Hsh_eq Hc_eq in Hcexp_FLX.
    unfold Generic_fmt.cexp, SpecFloat.fexp, FLT.FLT_exp in *.
    unfold FLX_exp in Hcexp_FLX.
    apply Z.max_le_compat_r. exact Hcexp_FLX. }
  rewrite !ulp_neq_0 //. apply bpow_le. exact Hcexp.
-
  exfalso. apply Hsh_nz. rewrite -Hsh_eq. exact Hsh_FLX_0.
-
  exfalso. apply Hc_nz. rewrite -Hc_eq. exact Hc_FLX_0.
Qed.

Lemma no_ov_w : Bplus_no_overflow t (FT2R tl) (FT2R vl).
Proof.
have HFIN1 : is_finite (BPLUS sh c) = true.
{ have HFIN_vh := FIN_vh.
  unfold vh, Fast2Sum_sum, Fast2Sum, fst in HFIN_vh; exact HFIN_vh. }
have HFIN_z := FIN_z.
have HFIN_vl := FIN_vl.
have Hvexp : Valid_exp (SpecFloat.fexp (fprec t) (femax t))
  by (apply FLT.FLT_exp_valid; apply fprec_gt_0).
have Hvrnd : Valid_rnd (Znearest choice) := Generic_fmt.valid_rnd_N choice.

have Hvl_eq : FT2R vl =
  round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
    (FT2R c - FT2R (BMINUS (BPLUS sh c) sh)).
{ change (FT2R vl) with (FT2R (BMINUS c (BMINUS (BPLUS sh c) sh))).
  symmetry. exact (BMINUS_round_correct t c (BMINUS (BPLUS sh c) sh) HFIN_vl). }
have Hz_eq : FT2R (BMINUS (BPLUS sh c) sh) =
  round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
    (FT2R (BPLUS sh c) - FT2R sh).
{ symmetry. exact (BMINUS_round_correct t (BPLUS sh c) sh HFIN_z). }
destruct (BPLUS_accurate' t sh c HFIN1) as (d1 & Hd1 & B1).
unfold Bplus_no_overflow.

rewrite Hvl_eq Hz_eq B1.

have Hfmt_inner1 : Generic_fmt.generic_format Zaux.radix2
  (SpecFloat.fexp (fprec t) (femax t))
  (round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
    (FT2R c -
     round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
       ((FT2R sh + FT2R c) * (1 + d1) - FT2R sh)))
  by apply Generic_fmt.generic_format_round.
pose proof (Plus_error.FLT_plus_error_N_ex Zaux.radix2
  (SpecFloat.emin (fprec t) (femax t)) (fprec t)
  (fun x0 : Z => negb (Z.even x0)) (FT2R tl)
  (round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
     (FT2R c -
      round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
        ((FT2R sh + FT2R c) * (1 + d1) - FT2R sh)))) as Houter.
destruct Houter as (d4 & Hd4 & B4).
- rewrite -B2R_float_of_ftype. apply Binary.generic_format_B2R.
- exact Hfmt_inner1.
- rewrite B4. clear B4.

  have Hfmt_inner2 : Generic_fmt.generic_format Zaux.radix2
    (SpecFloat.fexp (fprec t) (femax t))
    (round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
       ((FT2R sh + FT2R c) * (1 + d1) - FT2R sh))
    by apply Generic_fmt.generic_format_round.
  pose proof (Plus_error.FLT_plus_error_N_ex Zaux.radix2
    (SpecFloat.emin (fprec t) (femax t)) (fprec t)
    (fun x0 : Z => negb (Z.even x0)) (FT2R c)
    (- round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
       ((FT2R sh + FT2R c) * (1 + d1) - FT2R sh))) as Hmid.
  destruct Hmid as (d3 & Hd3 & B3).
  + rewrite -B2R_float_of_ftype. apply Binary.generic_format_B2R.
  + apply Generic_fmt.generic_format_opp. exact Hfmt_inner2.
  + have Heq3 : FT2R c +
       - round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
           ((FT2R sh + FT2R c) * (1 + d1) - FT2R sh) =
       FT2R c -
       round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
           ((FT2R sh + FT2R c) * (1 + d1) - FT2R sh) by ring.
    rewrite Heq3 in B3. rewrite B3. clear B3 Heq3.

    pose proof (Plus_error.FLT_plus_error_N_ex Zaux.radix2
      (SpecFloat.emin (fprec t) (femax t)) (fprec t)
      (fun x0 : Z => negb (Z.even x0))
      ((FT2R sh + FT2R c) * (1 + d1)) (- FT2R sh)) as Hinner.
    destruct Hinner as (d2 & Hd2 & B2).
    *
      have Heq_BPLUS : (FT2R sh + FT2R c) * (1 + d1) = FT2R (BPLUS sh c).
      { rewrite -B1. reflexivity. }
      rewrite Heq_BPLUS. rewrite -B2R_float_of_ftype.
      apply Binary.generic_format_B2R.
    * rewrite -B2R_float_of_ftype.
      apply Generic_fmt.generic_format_opp. apply Binary.generic_format_B2R.
    * have Heq2 : (FT2R sh + FT2R c) * (1 + d1) + - FT2R sh =
                  (FT2R sh + FT2R c) * (1 + d1) - FT2R sh by ring.
      rewrite Heq2 in B2. rewrite B2. clear B2 Heq2.

      have Htl := tl_bnd. have Hsh := sh_bnd. have Hc := c_bnd.

      have Hd1_8 : Rabs d1 <= /8 by (apply (Rle_trans _ _ _ Hd1 default_rel_le8)).
      have Hd2_8 : Rabs d2 <= /8 by (apply uro_frac_le8; exact Hd2).
      have Hd3_8 : Rabs d3 <= /8 by (apply uro_frac_le8; exact Hd3).
      have Hd4_8 : Rabs d4 <= /8 by (apply uro_frac_le8; exact Hd4).
      have HO : 0 < Omega by apply bpow_gt_0.
      have Hrel : default_rel t <= /8 by apply default_rel_le8.
      have Hrel0 : 0 < default_rel t by apply default_rel_pos.
      have HB : 0 < bpow radix2 (femax t - fprec t) by apply bpow_gt_0.
      have HP : bpow radix2 (femax t - 1 - fprec t) =
                /2 * bpow radix2 (femax t - fprec t).
      { have HH := two_mul_bpow (femax t - 1 - fprec t).
        replace (femax t - 1 - fprec t + 1)%Z with (femax t - fprec t)%Z in HH by lia.
        lra. }
      have HQO : bpow radix2 (femax t - fprec t) <= /8 * Omega.
      { have HH : /8 * Omega = bpow radix2 (femax t - 3).
        { have H8 : (/8:R) = bpow radix2 (-3) by (simpl; lra).
          rewrite H8 -bpow_plus. f_equal; lia. }
        rewrite HH. apply bpow_le. lia. }
      rewrite HP in Hc.
      have HcA : /2 * bpow radix2 (femax t - fprec t) +
                 /2 * bpow radix2 (femax t - fprec t) * (1 + default_rel t)
                 <= 17/16 * bpow radix2 (femax t - fprec t) by nra.
      have HcB : Rabs (FT2R c) <=
                 17/16 * bpow radix2 (femax t - fprec t) * (1 + default_rel t).
      { apply (Rle_trans _ _ _ Hc).
        apply Rmult_le_compat_r; [lra | exact HcA]. }
      have HcC : 17/16 * bpow radix2 (femax t - fprec t) * (1 + default_rel t)
                 <= /4 * Omega by nra.
      have HcO : Rabs (FT2R c) <= /4 * Omega by (apply (Rle_trans _ _ _ HcB HcC)).
      have HM : Rabs (FT2R sh + FT2R c) <= 13/16 * Omega.
      { eapply Rle_trans; [apply Rabs_triang|].
        apply (Rle_trans _ (/2*Omega*(1+default_rel t) + /4*Omega));
          [apply Rplus_le_compat; [exact Hsh | exact HcO] | nra]. }
      have Hcm : Rabs (FT2R c + (FT2R sh + FT2R c) * d1)
                 <= /4 * Omega + 13/16 * Omega * (/8).
      { eapply Rle_trans; [apply Rabs_triang|].
        apply Rplus_le_compat; [exact HcO|].
        rewrite Rabs_mult.
        apply Rmult_le_compat;
          [apply Rabs_pos | apply Rabs_pos | exact HM | exact Hd1_8]. }
      have Hval : Rabs (FT2R c - ((FT2R sh + FT2R c) * (1 + d1) - FT2R sh) * (1 + d2))
                  <= /4 * Omega.
      { have Hrw : FT2R c - ((FT2R sh + FT2R c) * (1 + d1) - FT2R sh) * (1 + d2)
                   = (- ((FT2R sh + FT2R c) * d1))
                     + (- ((FT2R c + (FT2R sh + FT2R c) * d1) * d2)) by ring.
        rewrite Hrw.
        eapply Rle_trans; [apply Rabs_triang|].
        rewrite !Rabs_Ropp !Rabs_mult.
        apply Rle_trans with
          (13/16*Omega*(/8) + (/4*Omega + 13/16*Omega*(/8))*(/8)).
        - apply Rplus_le_compat.
          + apply Rmult_le_compat;
              [apply Rabs_pos | apply Rabs_pos | exact HM | exact Hd1_8].
          + apply Rmult_le_compat;
              [apply Rabs_pos | apply Rabs_pos | exact Hcm | exact Hd2_8].
        - nra. }
      have Htl16 : Rabs (FT2R tl) <= /16 * Omega
        by (apply (Rle_trans _ _ _ Htl); nra).
      rewrite Rabs_mult.
      have Hsum2 : Rabs (FT2R tl +
                     (FT2R c - ((FT2R sh + FT2R c) * (1 + d1) - FT2R sh) * (1 + d2))
                     * (1 + d3))
                   <= /16 * Omega + /4 * Omega * (9/8).
      { eapply Rle_trans; [apply Rabs_triang|].
        apply Rplus_le_compat; [exact Htl16|].
        rewrite Rabs_mult.
        apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hval|].
        eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_R1. lra. }
      apply Rle_lt_trans with ((/16*Omega + /4*Omega*(9/8)) * Rabs (1+d4)).
      { apply Rmult_le_compat_r; [apply Rabs_pos | exact Hsum2]. }
      apply Rle_lt_trans with ((/16*Omega + /4*Omega*(9/8)) * (9/8)).
      { apply Rmult_le_compat_l; [nra|].
        eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_R1. lra. }
      nra.
Qed.

Lemma FIN_w : is_finite w = true.
Proof.
unfold w.
exact (no_overflow_sum_is_finite t tl vl FIN_tl FIN_vl no_ov_w).
Qed.

Lemma DWPlusDW_vh_w_disjunction_core
    (Fsh : is_finite sh = true)
    (Fsl : is_finite sl = true)
    (Fth : is_finite th = true)
    (Ftl : is_finite tl = true)
    (Fc : is_finite c = true)
    (Fvh : is_finite vh = true)
    (Fz : is_finite (BMINUS (BPLUS sh c) sh) = true)
    (Fvl : is_finite vl = true)
    (Fw : is_finite w = true) :
  (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (FT2R w) <=
   Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (FT2R vh))%R
  \/ FT2R vh = 0%R.
Proof.
destruct (Req_dec (FT2R vh) 0) as [Hvh0 | Hvh_nz]; [right; exact Hvh0|].
destruct (Req_dec (FT2R w) 0) as [Hw0 | Hw_nz];
  [left; rewrite Hw0; apply ulp_le_abs; rewrite Rabs_R0; apply Rabs_pos|].
left.
have HFIN_sh : is_finite (BPLUS xh yh) = true.
{ change (is_finite (TwoSumF_sum xh yh) = true); exact Fsh. }
destruct (Req_dec (FT2R xh + FT2R yh) 0) as [Hxhyh_zero | Hxhyh_nz].
{

  have Fmt_th := generic_format_FLT_FT2R th.
  have Hsh0 : FT2R sh = 0.
  { change (FT2R sh) with (FT2R (BPLUS xh yh)).
    rewrite -(BPLUS_round_correct t xh yh HFIN_sh) Hxhyh_zero round_0 //. }
  have Hsl0 : FT2R sl = 0.
  { change (FT2R sl) with (FT2R (TwoSumF_err xh yh)).
    rewrite (TwoSumF_correct xh yh (conj Fsh Fsl)).
    change (FT2R (TwoSumF_sum xh yh)) with (FT2R sh).
    rewrite Hxhyh_zero Hsh0; ring. }
  have Hc_th : FT2R c = FT2R th.
  { change (FT2R c) with (FT2R (BPLUS sl th)).
    rewrite -(BPLUS_round_correct t sl th Fc) Hsl0 Rplus_0_l.
    rewrite round_generic; [done | apply: generic_format_FLT_FT2R]. }
  have Hvh_th : FT2R vh = FT2R th.
  { change (FT2R vh) with (FT2R (BPLUS sh c)).
    rewrite -(BPLUS_round_correct t sh c Fvh) Hsh0 Rplus_0_l Hc_th.
    rewrite round_generic; [done | apply: generic_format_FLT_FT2R]. }
  have Hz_th : FT2R (BMINUS (BPLUS sh c) sh) = FT2R th.
  { rewrite -(BMINUS_round_correct t (BPLUS sh c) sh Fz).
    change (FT2R (BPLUS sh c)) with (FT2R vh).
    rewrite Hvh_th Hsh0 Rminus_0_r.
    rewrite round_generic; [done | apply: generic_format_FLT_FT2R]. }
  have Hvl0 : FT2R vl = 0.
  { change (FT2R vl) with (FT2R (BMINUS c (BMINUS (BPLUS sh c) sh))).
    rewrite -(BMINUS_round_correct t c (BMINUS (BPLUS sh c) sh) Fvl).
    rewrite Hz_th Hc_th.
    have ->: FT2R th - FT2R th = 0 by ring.
    rewrite round_0 //. }
  have Hw_tl : FT2R w = FT2R tl.
  { change (FT2R w) with (FT2R (BPLUS tl vl)).
    rewrite -(BPLUS_round_correct t tl vl Fw) Hvl0 Rplus_0_r.
    rewrite round_generic; [done | apply: generic_format_FLT_FT2R]. }
  rewrite Hw_tl Hvh_th.
  apply: ulp_dw_le.
  - exact (TwoSum_is_DW xl yl (conj Fth Ftl)).
  - rewrite -Hvh_th; exact Hvh_nz.
  - rewrite -Hw_tl; exact Hw_nz. }
destruct (Req_dec (FT2R xh) 0) as [Hxh_zero | Hxh_nz].
{

  have Hxl0 : FT2R xl = 0 by exact (double_word_0 xh xl DWx Hxh_zero).
  have Hsh_yh : FT2R sh = FT2R yh.
  { change (FT2R sh) with (FT2R (BPLUS xh yh)).
    rewrite -(BPLUS_round_correct t xh yh HFIN_sh) Hxh_zero Rplus_0_l.
    rewrite round_generic; [done | apply: generic_format_FLT_FT2R]. }
  have Hsl0 : FT2R sl = 0.
  { change (FT2R sl) with (FT2R (TwoSumF_err xh yh)).
    rewrite (TwoSumF_correct xh yh (conj Fsh Fsl)).
    change (FT2R (TwoSumF_sum xh yh)) with (FT2R sh).
    rewrite Hxh_zero Hsh_yh; ring. }
  have Hth_yl : FT2R th = FT2R yl.
  { change (FT2R th) with (FT2R (BPLUS xl yl)).
    rewrite -(BPLUS_round_correct t xl yl Fth) Hxl0 Rplus_0_l.
    rewrite round_generic; [done | apply: generic_format_FLT_FT2R]. }
  have Htl0 : FT2R tl = 0.
  { change (FT2R tl) with (FT2R (TwoSumF_err xl yl)).
    rewrite (TwoSumF_correct xl yl (conj Fth Ftl)).
    change (FT2R (TwoSumF_sum xl yl)) with (FT2R th).
    rewrite Hxl0 Hth_yl; ring. }
  have Hc_yl : FT2R c = FT2R yl.
  { change (FT2R c) with (FT2R (BPLUS sl th)).
    rewrite -(BPLUS_round_correct t sl th Fc) Hsl0 Rplus_0_l Hth_yl.
    rewrite round_generic; [done | apply: generic_format_FLT_FT2R]. }
  have Hvh_yh : FT2R vh = FT2R yh.
  { change (FT2R vh) with (FT2R (BPLUS sh c)).
    rewrite -(BPLUS_round_correct t sh c Fvh) Hsh_yh Hc_yl.
    move: DWy; rewrite /double_word /rounded => HDWy; symmetry; exact HDWy. }
  have Hz0 : FT2R (BMINUS (BPLUS sh c) sh) = 0.
  { rewrite -(BMINUS_round_correct t (BPLUS sh c) sh Fz).
    change (FT2R (BPLUS sh c)) with (FT2R vh).
    rewrite Hvh_yh Hsh_yh.
    have ->: FT2R yh - FT2R yh = 0 by ring.
    rewrite round_0 //. }
  have Hvl_yl : FT2R vl = FT2R yl.
  { change (FT2R vl) with (FT2R (BMINUS c (BMINUS (BPLUS sh c) sh))).
    rewrite -(BMINUS_round_correct t c (BMINUS (BPLUS sh c) sh) Fvl).
    rewrite Hz0 Hc_yl Rminus_0_r.
    rewrite round_generic; [done | apply: generic_format_FLT_FT2R]. }
  have Hw_yl : FT2R w = FT2R yl.
  { change (FT2R w) with (FT2R (BPLUS tl vl)).
    rewrite -(BPLUS_round_correct t tl vl Fw) Htl0 Rplus_0_l Hvl_yl.
    rewrite round_generic; [done | apply: generic_format_FLT_FT2R]. }
  rewrite Hw_yl Hvh_yh.
  apply: ulp_dw_le.
  - exact DWy.
  - rewrite -Hvh_yh; exact Hvh_nz.
  - rewrite -Hw_yl; exact Hw_nz. }
have DWx_R : DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl)
  by apply (dw_word_DWdouble xh xl xh DWx).
have DWy_R : DWPlus.double_word (fprec t) choice (FT2R yh) (FT2R yl)
  by apply (dw_word_DWdouble yh yl yh DWy).
have fin_tsxhyh : is_finite_p (TwoSumF xh yh) by split; [exact Fsh | exact Fsl].
have fin_tsxlyl : is_finite_p (TwoSumF xl yl) by split; [exact Fth | exact Ftl].
have fin_f2s_shc : is_finite_p (DDModels.Fast2Sum sh c).
{ split.
  - change (is_finite (Fast2Sum_sum sh c) = true); exact Fvh.
  - exact Fvl. }
have heq_xhyh : DWPlus.TwoSum (fprec t) choice (FT2R xh) (FT2R yh) = F2Rp (TwoSumF xh yh)
  by exact (TwoSumEq_FLT xh yh fin_tsxhyh).
have heq_xlyl : DWPlus.TwoSum (fprec t) choice (FT2R xl) (FT2R yl) = F2Rp (TwoSumF xl yl)
  by exact (TwoSumEq_FLT xl yl fin_tsxlyl).
have heq_f2s : F2Sum.Fast2Sum (fprec t) choice (FT2R sh) (FT2R c) =
               F2Rp (DDModels.Fast2Sum sh c)
  by exact (FastTwoSumEq_FLT sh c fin_f2s_shc).
have Hsh_eq : DWPlus.TwoSum_sum (fprec t) choice (FT2R xh) (FT2R yh) = FT2R sh.
{ unfold DWPlus.TwoSum_sum. rewrite heq_xhyh /F2Rp /fst //. }
have Hsl_eq : DWPlus.TwoSum_err (fprec t) choice (FT2R xh) (FT2R yh) = FT2R sl.
{ unfold DWPlus.TwoSum_err. rewrite heq_xhyh /F2Rp /snd //. }
have Hth_eq : DWPlus.TwoSum_sum (fprec t) choice (FT2R xl) (FT2R yl) = FT2R th.
{ unfold DWPlus.TwoSum_sum. rewrite heq_xlyl /F2Rp /fst //. }
have Htl_eq : DWPlus.TwoSum_err (fprec t) choice (FT2R xl) (FT2R yl) = FT2R tl.
{ unfold DWPlus.TwoSum_err. rewrite heq_xlyl /F2Rp /snd //. }
have Hc_eq :
  round Zaux.radix2 (FLX_exp (fprec t)) (Znearest choice)
    (DWPlus.TwoSum_err (fprec t) choice (FT2R xh) (FT2R yh) +
     DWPlus.TwoSum_sum (fprec t) choice (FT2R xl) (FT2R yl)) = FT2R c.
{ rewrite Hsl_eq Hth_eq rnd_plus_FLT_FLX_eq'.
  change (FT2R c) with (FT2R (BPLUS sl th)).
  apply BPLUS_round_correct. exact Fc. }
have Hvh_eq : fst (F2Sum.Fast2Sum (fprec t) choice (FT2R sh) (FT2R c)) = FT2R vh.
{ rewrite heq_f2s /F2Rp /fst //. }
have Hvl_eq : snd (F2Sum.Fast2Sum (fprec t) choice (FT2R sh) (FT2R c)) = FT2R vl.
{ rewrite heq_f2s /F2Rp /snd //. }
have Hp3 : (3 <= fprec t)%Z by exact Hprec.
case: (@DWPlus.DWPlusDW_w_le_vh_aux (fprec t) (fprec_gt_one t) choice (eq_refl _)
         (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl) Hp3
         DWx_R DWy_R Hxh_nz Hxhyh_nz)
  => [Hle | [HvhFLX | HwFLX]].
-
  have Hw_FT2R :
    round Zaux.radix2 (FLX_exp (fprec t)) (Znearest choice)
      (DWPlus.TwoSum_err (fprec t) choice (FT2R xl) (FT2R yl) +
       snd (F2Sum.Fast2Sum (fprec t) choice
             (DWPlus.TwoSum_sum (fprec t) choice (FT2R xh) (FT2R yh))
             (round Zaux.radix2 (FLX_exp (fprec t)) (Znearest choice)
               (DWPlus.TwoSum_err (fprec t) choice (FT2R xh) (FT2R yh) +
                DWPlus.TwoSum_sum (fprec t) choice (FT2R xl) (FT2R yl))))) =
    FT2R w.
  { rewrite Htl_eq Hsh_eq Hc_eq Hvl_eq rnd_plus_FLT_FLX_eq'.
    change (FT2R w) with (FT2R (BPLUS tl vl)).
    apply BPLUS_round_correct. exact Fw. }
  have Hvh_FT2R : fst (F2Sum.Fast2Sum (fprec t) choice
                        (DWPlus.TwoSum_sum (fprec t) choice (FT2R xh) (FT2R yh))
                        (round Zaux.radix2 (FLX_exp (fprec t)) (Znearest choice)
                          (DWPlus.TwoSum_err (fprec t) choice (FT2R xh) (FT2R yh) +
                           DWPlus.TwoSum_sum (fprec t) choice (FT2R xl) (FT2R yl)))) =
                  FT2R vh.
  { rewrite Hsh_eq Hc_eq. exact Hvh_eq. }
  rewrite Hw_FT2R Hvh_FT2R in Hle.
  exact (ulp_le_abs _ _ Hle).
- exfalso. apply Hvh_nz.
  rewrite -Hvh_eq -Hsh_eq -Hc_eq. exact HvhFLX.
- exfalso. apply Hw_nz.
  have Hw_FT2R :
    round Zaux.radix2 (FLX_exp (fprec t)) (Znearest choice)
      (DWPlus.TwoSum_err (fprec t) choice (FT2R xl) (FT2R yl) +
       snd (F2Sum.Fast2Sum (fprec t) choice
             (DWPlus.TwoSum_sum (fprec t) choice (FT2R xh) (FT2R yh))
             (round Zaux.radix2 (FLX_exp (fprec t)) (Znearest choice)
               (DWPlus.TwoSum_err (fprec t) choice (FT2R xh) (FT2R yh) +
                DWPlus.TwoSum_sum (fprec t) choice (FT2R xl) (FT2R yl))))) =
    FT2R w.
  { rewrite Htl_eq Hsh_eq Hc_eq Hvl_eq rnd_plus_FLT_FLX_eq'.
    change (FT2R w) with (FT2R (BPLUS tl vl)).
    apply BPLUS_round_correct. exact Fw. }
  by rewrite -Hw_FT2R.
Qed.

Lemma DWPlusDW_vh_w_disjunction :
  (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (FT2R w) <=
   Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (FT2R vh))%R
  \/ FT2R vh = 0%R.
Proof.
exact (DWPlusDW_vh_w_disjunction_core
         FIN_sh FIN_sl FIN_th FIN_tl FIN_c FIN_vh FIN_z FIN_vl FIN_w).
Qed.

Lemma no_ov_zh : Bplus_no_overflow t (FT2R vh) (FT2R w).
Proof.
have HFIN_BPLUS_sh_c : is_finite (BPLUS sh c) = true.
{ have HFIN_vh := FIN_vh.
  unfold vh, Fast2Sum_sum, Fast2Sum, fst in HFIN_vh; exact HFIN_vh. }
have HFIN_BPLUS_tl_vl : is_finite (BPLUS tl vl) = true.
{ change (is_finite w = true); exact FIN_w. }
destruct (BPLUS_accurate' t sh c HFIN_BPLUS_sh_c) as (dvh & Hdvh & Bvh).
have Hvh_eq : FT2R vh = (FT2R sh + FT2R c) * (1 + dvh).
{ change (FT2R vh) with (FT2R (BPLUS sh c)). exact Bvh. }
destruct (BPLUS_accurate' t tl vl HFIN_BPLUS_tl_vl) as (dw & Hdw & Bw).
have Hw_eq : FT2R w = (FT2R tl + FT2R vl) * (1 + dw).
{ change (FT2R w) with (FT2R (BPLUS tl vl)). exact Bw. }

have Hcond_sh_c : Fast2Sum_exact_cond sh c.
{ unfold Fast2Sum_exact_cond; split.
  - change (is_finite (BPLUS sh c) = true).
    change (is_finite vh = true). exact FIN_vh.
  - exact DWPlusDW_sh_c_disjunction. }
have Hexact : FT2R vh + FT2R vl = FT2R sh + FT2R c.
{ have HH := FastTwoSum_correct_from_exact_cond sh c Hcond_sh_c.
  change (FT2R vl) with (FT2R (Fast2Sum_err sh c)).
  change (FT2R vh) with (FT2R (Fast2Sum_sum sh c)).
  rewrite HH. ring. }
have Hvl_val : FT2R vl = - ((FT2R sh + FT2R c) * dvh).
{ have Hv : FT2R vl = (FT2R sh + FT2R c) - FT2R vh by (rewrite -Hexact; ring).
  rewrite Hv Hvh_eq. ring. }
unfold Bplus_no_overflow.
rewrite Hvh_eq Hw_eq Hvl_val.
pose proof (Plus_error.FLT_plus_error_N_ex Zaux.radix2
  (SpecFloat.emin (fprec t) (femax t)) (fprec t)
  (fun x0 : Z => negb (Z.even x0))
  ((FT2R sh + FT2R c) * (1 + dvh))
  ((FT2R tl + - ((FT2R sh + FT2R c) * dvh)) * (1 + dw))) as H.
destruct H as (d5 & Hd5 & B).
- have Heq_vh : (FT2R sh + FT2R c) * (1 + dvh) = FT2R vh by (rewrite -Hvh_eq; reflexivity).
  rewrite Heq_vh -B2R_float_of_ftype. apply Binary.generic_format_B2R.
- have Heq_w : (FT2R tl + - ((FT2R sh + FT2R c) * dvh)) * (1 + dw) = FT2R w
    by (rewrite -Hvl_val -Hw_eq; reflexivity).
  rewrite Heq_w -B2R_float_of_ftype. apply Binary.generic_format_B2R.
- rewrite B. clear B.
  have Hsh := sh_bnd. have Hc := c_bnd. have Htl := tl_bnd.
  have Hd_vh8 : Rabs dvh <= /8 by (apply (Rle_trans _ _ _ Hdvh default_rel_le8)).
  have Hd_w8 : Rabs dw <= /8 by (apply (Rle_trans _ _ _ Hdw default_rel_le8)).
  have Hd5_8 : Rabs d5 <= /8 by (apply uro_frac_le8; exact Hd5).
  have HO : 0 < Omega by apply bpow_gt_0.
  have Hrel : default_rel t <= /8 by apply default_rel_le8.
  have Hrel0 : 0 < default_rel t by apply default_rel_pos.
  have HB : 0 < bpow radix2 (femax t - fprec t) by apply bpow_gt_0.
  have HP : bpow radix2 (femax t - 1 - fprec t) =
            /2 * bpow radix2 (femax t - fprec t).
  { have HH := two_mul_bpow (femax t - 1 - fprec t).
    replace (femax t - 1 - fprec t + 1)%Z with (femax t - fprec t)%Z in HH by lia.
    lra. }
  have HQO : bpow radix2 (femax t - fprec t) <= /8 * Omega.
  { have HH : /8 * Omega = bpow radix2 (femax t - 3).
    { have H8 : (/8:R) = bpow radix2 (-3) by (simpl; lra).
      rewrite H8 -bpow_plus. f_equal; lia. }
    rewrite HH. apply bpow_le. lia. }
  rewrite HP in Hc.
  have HcA : /2 * bpow radix2 (femax t - fprec t) +
             /2 * bpow radix2 (femax t - fprec t) * (1 + default_rel t)
             <= 17/16 * bpow radix2 (femax t - fprec t) by nra.
  have HcB : Rabs (FT2R c) <=
             17/16 * bpow radix2 (femax t - fprec t) * (1 + default_rel t).
  { apply (Rle_trans _ _ _ Hc).
    apply Rmult_le_compat_r; [lra | exact HcA]. }
  have HcC : 17/16 * bpow radix2 (femax t - fprec t) * (1 + default_rel t)
             <= 5/32 * Omega by nra.
  have HcO : Rabs (FT2R c) <= 5/32 * Omega by (apply (Rle_trans _ _ _ HcB HcC)).
  have HM : Rabs (FT2R sh + FT2R c) <= 23/32 * Omega.
  { eapply Rle_trans; [apply Rabs_triang|].
    apply (Rle_trans _ (/2*Omega*(1+default_rel t) + 5/32*Omega));
      [apply Rplus_le_compat; [exact Hsh | exact HcO] | nra]. }
  have Htl16 : Rabs (FT2R tl) <= /16 * Omega by (apply (Rle_trans _ _ _ Htl); nra).
  rewrite Rabs_mult.
  have Hrw : (FT2R sh + FT2R c) * (1 + dvh) +
             (FT2R tl + - ((FT2R sh + FT2R c) * dvh)) * (1 + dw)
             = (FT2R sh + FT2R c) + FT2R tl
               + (FT2R tl + - ((FT2R sh + FT2R c) * dvh)) * dw by ring.
  rewrite Hrw.
  have HVterm : Rabs (FT2R tl + - ((FT2R sh + FT2R c) * dvh))
                <= /16 * Omega + 23/32 * Omega * (/8).
  { eapply Rle_trans; [apply Rabs_triang|].
    rewrite Rabs_Ropp Rabs_mult.
    apply Rplus_le_compat; [exact Htl16|].
    apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact HM | exact Hd_vh8]. }
  have HV : Rabs ((FT2R sh + FT2R c) + FT2R tl
                  + (FT2R tl + - ((FT2R sh + FT2R c) * dvh)) * dw)
            <= 13/16 * Omega.
  { eapply Rle_trans; [apply Rabs_triang|].
    apply Rle_trans with
      ((23/32*Omega + /16*Omega) + (/16*Omega + 23/32*Omega*(/8))*(/8)).
    - apply Rplus_le_compat.
      + eapply Rle_trans; [apply Rabs_triang|].
        apply Rplus_le_compat; [exact HM | exact Htl16].
      + rewrite Rabs_mult.
        apply Rmult_le_compat;
          [apply Rabs_pos | apply Rabs_pos | exact HVterm | exact Hd_w8].
    - nra. }
  apply Rle_lt_trans with (13/16 * Omega * Rabs (1+d5)).
  { apply Rmult_le_compat_r; [apply Rabs_pos | exact HV]. }
  apply Rle_lt_trans with (13/16 * Omega * (9/8)).
  { apply Rmult_le_compat_l; [nra|].
    eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_R1. lra. }
  nra.
Qed.

Theorem DWPlusDW_finite :
  is_finite_p (DWPlusDW xh xl yh yl).
Proof.
rewrite /is_finite_p /DWPlusDW.
replace (TwoSumF xh yh) with (sh, sl) => //.
replace (TwoSumF xl yl) with (th, tl) => //.
rewrite /fst /snd.
replace (Fast2Sum sh c) with (vh, vl) => //.
split.
-
  unfold Fast2Sum, fst.
  exact (no_overflow_sum_is_finite t vh w FIN_vh FIN_w no_ov_zh).
-
  apply (is_finite_FastSum_ulp vh w).
  + exact DWPlusDW_vh_w_disjunction.
  + exact (no_overflow_sum_is_finite t vh w FIN_vh FIN_w no_ov_zh).
Qed.

End DWPlusDWFinite.

Section DWPlusDWCondBridge.
Context {NANS: Nans} {t : type} {STD: is_standard t}.
Variables (xh xl yh yl : ftype t).

Theorem DWPlusDW_finite_post_cond_from_strong_precond :
  DWPlusDW_strong_precond xh xl yh yl ->
  is_finite_p (DWPlusDW xh xl yh yl).
Proof.
apply DWPlus_finite.DWPlusDW_finite_safe.
Qed.

End DWPlusDWCondBridge.
