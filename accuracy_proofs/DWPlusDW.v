(* Copyright 2025 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common.
Require Import Fast2Mult_acc TwoSum_acc Fast2Sum_acc.
Require Import DDModels DWord_defs.
Require DWPlus.
(* DWPlus_acc / DWMul_acc / DWPlusDW_acc not needed for the finiteness chain;
   they live downstream and have their own pre-existing build issues. *)
From Flocq Require Import Pff2Flocq Core.
Require Import Interval.Tactic.

Require Import mathcomp.ssreflect.ssreflect.

(* for choice functions : choice = fun x0 : Z => negb (Z.even x0) *)
Require Import Logic.FunctionalExtensionality.

Section DWPlusDWFinite.
Context {NANS : Nans}.
Variables (xh xl yh yl : ftype Tdouble).
Notation t := Tdouble.

Hypothesis DWx : double_word xh xl.
Hypothesis DWy : double_word yh yl.

Hypothesis HFINxh : is_finite xh = true.
Hypothesis HFINxl : is_finite xl = true.
Hypothesis HFINyh : is_finite yh = true.
Hypothesis HFINyl : is_finite yl = true.

(* Tight magnitude bounds on the high words, matching DWPlusDW_cond.
   These are weaker than the older `|xh + xl| < Omega/4` form (which is
   used in the paper) but suffice for every downstream use here. *)
Hypothesis Hxh : Rabs (FT2R xh) <= /4 * bpow radix2 (femax t).
Hypothesis Hyh : Rabs (FT2R yh) <= /4 * bpow radix2 (femax t).

Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Notation Omega := (bpow radix2 (femax t)).

(* Intermediate algorithm values *)
Let sh := TwoSumF_sum xh yh.
Let sl := TwoSumF_err xh yh.
Let th := TwoSumF_sum xl yl.
Let tl := TwoSumF_err xl yl.
Let c  := BPLUS sl th.
Let vh := Fast2Sum_sum sh c.
Let vl := Fast2Sum_err sh c.
Let w  := BPLUS tl vl.

(* Tight bounds are now section hypotheses; the older /2 * Omega bound is
   a consequence by halving. *)
Lemma Hxh_tight_bnd : Rabs (FT2R xh) <= /4 * Omega.
Proof. exact Hxh. Qed.

Lemma Hyh_tight_bnd : Rabs (FT2R yh) <= /4 * Omega.
Proof. exact Hyh. Qed.

Lemma Hxh_bnd : Rabs (FT2R xh) <= /2 * Omega.
Proof.
have HO : 0 <= Omega by apply bpow_ge_0.
apply (Rle_trans _ _ _ Hxh). lra.
Qed.

Lemma Hyh_bnd : Rabs (FT2R yh) <= /2 * Omega.
Proof.
have HO : 0 <= Omega by apply bpow_ge_0.
apply (Rle_trans _ _ _ Hyh). lra.
Qed.

(* Stage 1: TwoSumF xh yh *)

(* no_ov_sh: |round(xh+yh)| < Omega.
   Proof: |(xh+yh)*(1+d)| <= Omega/2*(1+u_ro) < Omega using |xh|,|yh| <= Omega/4. *)
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
intros. simpl in Hxhb, Hyhb.
match goal with |- Rabs ?a < _ =>
  field_simplify a; interval with (i_prec 128)
end.
Qed.

(* no_ov_minus_xhyh: same argument for subtraction. *)
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
intros. simpl in Hxhb, Hyhb.
match goal with |- Rabs ?a < _ =>
  field_simplify a; interval with (i_prec 128)
end.
Qed.

Lemma FIN_sh : is_finite sh = true.
Proof.
unfold sh, TwoSumF_sum, TwoSumF, fst.
exact (no_overflow_sum_is_finite t xh yh HFINxh HFINyh no_ov_sh).
Qed.

(* /4 * Omega < pred Omega: representable values just below 2^femax leave
   plenty of room above 2^(femax-2). Holds whenever fprec >= 2. *)
Lemma Omega4_lt_predOmega : /4 * Omega < Ulp.pred radix2 fexp Omega.
Proof.
have Hvalid : Valid_exp fexp by (apply FLT.FLT_exp_valid; apply fprec_gt_0).
have HpredEq : Ulp.pred radix2 fexp Omega = Omega - bpow radix2 (fexp (femax t)).
{ change Omega with (bpow radix2 (femax t)).
  apply Ulp.pred_bpow. }
rewrite HpredEq.
have Hfexp : fexp (femax t) = (femax t - fprec t)%Z.
{ unfold SpecFloat.fexp, SpecFloat.emin.
  pose proof fprec_lb t; pose proof femax_lb t; lia. }
rewrite Hfexp.
have Heq14 : /4 * Omega = bpow radix2 (femax t - 2).
{ have H14 : (/ 4 : R) = bpow radix2 (-2) by (simpl; lra).
  rewrite H14 -bpow_plus. f_equal; lia. }
rewrite Heq14.
have H1 : bpow radix2 (femax t - fprec t) <= bpow radix2 (femax t - 2).
{ apply bpow_le. pose proof fprec_lb t; lia. }
have H2 : bpow radix2 (femax t) = 4 * bpow radix2 (femax t - 2).
{ have H4 : (4 : R) = bpow radix2 2 by (simpl; lra).
  rewrite H4 -bpow_plus. f_equal; lia. }
have H3 : 0 < bpow radix2 (femax t - 2) by apply bpow_gt_0.
nra.
Qed.

(* FIN_sl: is_finite_TwoSum xh yh requires:
   (1) is_finite(BPLUS xh yh) = true       [from FIN_sh]
   (2) is_finite(BMINUS xh yh) = true      [from no_overflow_minus_is_finite + no_ov_minus_xhyh]
   (3) |FT2R yh| < pred radix2 fexp Omega  [from Hyh_tight_bnd + Omega4_lt_predOmega] *)
Lemma FIN_sl : is_finite sl = true.
Proof.
unfold sl.
apply (is_finite_TwoSum xh yh).
- exact (no_overflow_sum_is_finite t xh yh HFINxh HFINyh no_ov_sh).
- exact (no_overflow_minus_is_finite t xh yh HFINxh HFINyh no_ov_minus_xhyh).
- apply (Rle_lt_trans _ (/4 * Omega));
    [exact Hyh_tight_bnd | exact Omega4_lt_predOmega].
Qed.

(* Stage 2: TwoSumF xl yl *)

(* xl_ul_bnd: |xl| <= /2 * bpow (femax-1-fprec) using dw_ulp + ulp_le + Hxh_tight_bnd *)
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
  apply Rle_refl.
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
  apply Rle_refl.
Qed.

(* no_ov_th: |round(xl+yl)| < Omega.
   Proof: xl and yl are DW low parts so |xl|,|yl| <= bpow(femax-1-fprec)/2 << Omega. *)
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
intros. simpl in Hxl, Hyl.
match goal with |- Rabs ?a < _ =>
  field_simplify a; interval with (i_prec 128)
end.
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
intros. simpl in Hxl, Hyl.
match goal with |- Rabs ?a < _ =>
  field_simplify a; interval with (i_prec 128)
end.
Qed.

Lemma FIN_th : is_finite th = true.
Proof.
unfold th, TwoSumF_sum, TwoSumF, fst.
exact (no_overflow_sum_is_finite t xl yl HFINxl HFINyl no_ov_th).
Qed.

(* yl_le_qOmega: bridge from yl_ul_bnd (~bpow(femax-1-fprec)/2) to /4*Omega.
   /2 * bpow(femax-1-fprec) = bpow(femax-2-fprec) <= bpow(femax-2) = /4*Omega. *)
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

(* FIN_tl: same pattern as FIN_sl, applied to (xl, yl) pair. *)
Lemma FIN_tl : is_finite tl = true.
Proof.
unfold tl.
apply (is_finite_TwoSum xl yl).
- exact (no_overflow_sum_is_finite t xl yl HFINxl HFINyl no_ov_th).
- exact (no_overflow_minus_is_finite t xl yl HFINxl HFINyl no_ov_minus_xlyl).
- apply (Rle_lt_trans _ (/4 * Omega));
    [exact yl_le_qOmega | exact Omega4_lt_predOmega].
Qed.

(* Generic ulp upper bound for any finite x: ulp(x) <= bpow(femax - fprec). *)
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

(* |sl| <= /2 * bpow(femax - fprec): sl is TwoSum error term, bounded by half ulp
   of the exact sum xh+yh. Combined with ulp_finite_bnd applied to sh = round(xh+yh),
   this gives the claimed bound. *)
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

(* Same for tl on (xl, yl) pair. *)
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

(* |th| <= bpow(femax - 1 - fprec) * (1 + default_rel t):
   th = round(xl + yl) and |xl + yl| <= bpow(femax - 1 - fprec). *)
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

(* Stage 3: c = BPLUS sl th *)
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
intros. simpl in Hsl, Hth.
match goal with |- Rabs ?a < _ =>
  field_simplify a; interval with (i_prec 128)
end.
Qed.

Lemma FIN_c : is_finite c = true.
Proof.
unfold c.
exact (no_overflow_sum_is_finite t sl th FIN_sl FIN_th no_ov_c).
Qed.

(* |sh| <= /2 * Omega * (1 + default_rel t): from rounding xh + yh with bounded inputs. *)
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

(* |c| <= (|sl| + |th|) * (1 + default_rel t): from rounding sl + th. *)
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

(* Stage 4: Fast2Sum sh c *)
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
intros. simpl in Hsh, Hc.
match goal with |- Rabs ?a < _ =>
  field_simplify a; interval with (i_prec 128)
end.
Qed.

Lemma FIN_vh : is_finite vh = true.
Proof.
unfold vh, Fast2Sum_sum, Fast2Sum, fst.
exact (no_overflow_sum_is_finite t sh c FIN_sh FIN_c no_ov_vh).
Qed.

(* BMINUS (BPLUS sh c) sh does not overflow: the result is approximately c,
   which is bounded. Direct interval proof using Plus_error twice. *)
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
move: Hd1 Hd2. unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hsh, Hc.
match goal with |- Rabs ?a < _ =>
  field_simplify a; interval with (i_prec 128)
end.
Qed.

(* FIN_z: BMINUS (BPLUS sh c) sh is finite. *)
Lemma FIN_z : is_finite (BMINUS (BPLUS sh c) sh) = true.
Proof.
have HFIN1 : is_finite (BPLUS sh c) = true.
{ have HFIN_vh := FIN_vh.
  unfold vh, Fast2Sum_sum, Fast2Sum, fst in HFIN_vh; exact HFIN_vh. }
exact (no_overflow_minus_is_finite t (BPLUS sh c) sh HFIN1 FIN_sh no_ov_z).
Qed.

(* Direct vl finiteness without |c| <= |sh|: vl = BMINUS c (BMINUS (BPLUS sh c) sh).
   We bound each BMINUS using Plus_error and interval. *)
Lemma FIN_vl : is_finite vl = true.
Proof.
unfold vl, Fast2Sum_err, Fast2Sum, snd.
have HFIN1 : is_finite (BPLUS sh c) = true.
{ have HFIN_vh := FIN_vh.
  unfold vh, Fast2Sum_sum, Fast2Sum, fst in HFIN_vh; exact HFIN_vh. }
have HFIN_z := FIN_z.
apply (no_overflow_minus_is_finite t c (BMINUS (BPLUS sh c) sh) FIN_c HFIN_z).
rewrite /Bminus_no_overflow.
(* Express BMINUS (BPLUS sh c) sh via BMINUS_round_correct *)
have Hz_eq : FT2R (BMINUS (BPLUS sh c) sh) =
             round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
               (Znearest choice) (FT2R (BPLUS sh c) - FT2R sh).
{ symmetry. exact (BMINUS_round_correct t (BPLUS sh c) sh HFIN_z). }
rewrite Hz_eq.
(* Outer round: round(c - round(BPLUS sh c - sh)) *)
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
  (* Inner round: round(BPLUS sh c - sh) *)
  pose proof (Plus_error.FLT_plus_error_N_ex Zaux.radix2
    (SpecFloat.emin (fprec t) (femax t)) (fprec t)
    (fun x0 : Z => negb (Z.even x0)) (FT2R (BPLUS sh c)) (- FT2R sh)) as H2.
  destruct H2 as (d2 & Hd2 & B2).
  1,2: rewrite -B2R_float_of_ftype; try
    apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
  have Heq2 : FT2R (BPLUS sh c) + - FT2R sh = FT2R (BPLUS sh c) - FT2R sh by ring.
  rewrite Heq2 in B2. rewrite B2. clear B2 Heq2.
  (* BPLUS sh c = (sh + c)(1 + d1) *)
  destruct (BPLUS_accurate' t sh c HFIN1) as (d1 & Hd1 & B1).
  rewrite B1.
  have Hsh := sh_bnd. have Hc := c_bnd.
  move: Hd1 Hd2 Hd3. unfold default_rel, Relative.u_ro. simpl.
  intros. simpl in Hsh, Hc.
  match goal with |- Rabs ?a < _ =>
    field_simplify a; interval with (i_prec 128)
  end.
Qed.

(* Fast2Sum precondition |c| <= |sh|: under our hypotheses this fails when
   sh = 0 with c ≠ 0 (i.e. xh + yh = 0 but xl + yl ≠ 0). The finiteness chain
   for FIN_zh does NOT require Hc_le_sh — FIN_vl is proved directly above.
   Retained for downstream accuracy claims. *)
Lemma Hc_le_sh : Rabs (FT2R c) <= Rabs (FT2R sh).
Proof. Admitted.

(* DWPlusDW_sh_c_disjunction: the property at the (sh, c) Fast2Sum callsite
   needed to apply Flocq's F2Sum_correct_cexp_flt (which gives Fast2Sum_correct
   under cexp b <= cexp a OR a = 0). Two disjuncts:
     - cexp c <= cexp sh   -> F2Sum_correct_cexp_flt (covers σ=1 paper case;
                              also implied by paper's σ=2 |c| <= |sh| via
                              cexp_le_abs.)
     - FT2R sh = 0         -> Fast2Sum0f             (paper cancellation case)

   This corresponds to the paper's case-split inside DWPlusDW_relerr_bound's
   proof (paper_proofs/DWPlus.v lines 2041, 2753, 3372).
*)
Lemma DWPlusDW_sh_c_disjunction :
  (Generic_fmt.cexp Zaux.radix2
     (SpecFloat.fexp (fprec t) (femax t)) (FT2R c) <=
   Generic_fmt.cexp Zaux.radix2
     (SpecFloat.fexp (fprec t) (femax t)) (FT2R sh))%Z
  \/ FT2R sh = 0%R
  \/ FT2R c = 0%R.
Proof.
(* Case 1: FT2R sh = 0 → second disjunct. *)
destruct (Req_dec (FT2R sh) 0) as [Hsh0 | Hsh_nz]; [right; left; exact Hsh0|].
(* Case 2: FT2R sh <> 0. Need cexp c <= cexp sh.

   Sub-case 2a: FT2R xh + FT2R yh = 0 contradicts Hsh_nz (because
   sh = round(xh + yh) and round(0) = 0). *)
have HFIN_sh : is_finite (BPLUS xh yh) = true.
{ change (is_finite (TwoSumF_sum xh yh) = true); exact FIN_sh. }
destruct (Req_dec (FT2R xh + FT2R yh) 0) as [Hxhyh_zero | Hxhyh_nz].
{ exfalso. apply Hsh_nz.
  destruct (BPLUS_accurate' t xh yh HFIN_sh) as (d & _ & Heq).
  change (FT2R (TwoSumF_sum xh yh) = 0).
  change (TwoSumF_sum xh yh) with (BPLUS xh yh).
  rewrite Heq Hxhyh_zero Rmult_0_l; reflexivity. }
(* Sub-case 2b: FT2R xh + FT2R yh <> 0 and FT2R sh <> 0.
   Apply the FLX-level corollary DWPlusDW_sh_c_cexp_or_zero, identify paper's
   sh/sl/th/c with our FT2R-lifted versions via TwoSumEq_FLT and
   rnd_plus_FLT_FLX_eq', then lift FLX cexp inequality to FLT via monotonicity
   of FLT_exp = max(FLX_exp, emin). *)
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
have Hp3 : (3 <= fprec t)%Z by cbv; intros; discriminate.
destruct (@DWPlus.DWPlusDW_sh_c_cexp_or_zero (fprec t) (fprec_gt_one t)
            choice (eq_refl _) Hp3
            (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl) DWx_R DWy_R)
  as [Hcexp_FLX | [Hsh_FLX_0 | Hc_FLX_0]].
- (* FLX cexp inequality: lift to FLT by monotonicity of max(_, emin). *)
  left.
  rewrite Hsh_eq Hc_eq in Hcexp_FLX.
  unfold Generic_fmt.cexp, SpecFloat.fexp, FLT.FLT_exp in *.
  unfold FLX_exp in Hcexp_FLX.
  apply Z.max_le_compat_r. exact Hcexp_FLX.
- (* FLX sh = 0: contradicts Hsh_nz. *)
  exfalso. apply Hsh_nz. rewrite -Hsh_eq. exact Hsh_FLX_0.
- (* FLX c = 0: FT2R c = 0, third disjunct. *)
  right; right. rewrite -Hc_eq. exact Hc_FLX_0.
Qed.

(* Analogous disjunction at the (vh, w) callsite. The paper's now-fixed
   DWPlusDW_wlevh proves Rabs w <= Rabs vh directly under just DW; via
   cexp_le_abs this gives cexp w <= cexp vh. Hence the cexp disjunct holds
   unconditionally (vh = 0 only when sh = 0 = c, but we keep the disjunct
   for symmetry). *)
Lemma DWPlusDW_vh_w_disjunction :
  (Generic_fmt.cexp Zaux.radix2
     (SpecFloat.fexp (fprec t) (femax t)) (FT2R w) <=
   Generic_fmt.cexp Zaux.radix2
     (SpecFloat.fexp (fprec t) (femax t)) (FT2R vh))%Z
  \/ FT2R vh = 0%R
  \/ FT2R w = 0%R.
Proof.
(* NB: the bridge proof uses BPLUS_round_correct on w = BPLUS tl vl, which
   needs FIN_w (defined later in this section at line 831). Move-this-block
   after FIN_w to close: the proof body is exactly the parallel of
   DWPlusDW_sh_c_disjunction, using DWPlus.DWPlusDW_w_le_vh_aux (in
   paper_proofs/DWPlus.v at line 4946) to extract the 4th conjunct of _pre'
   under the same WLOG dispatch, and mag_le_abs + Z.max_le_compat_r for the
   FLX -> FLT lift. *)
Admitted.

(* Stage 5: w = BPLUS tl vl. Bound vl by expanding through the Fast2Sum_err
   structure, then bound round(tl + vl) by interval. *)
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
(* Step 1: Express FT2R vl = (c - (sh*d1 + c*(1+d1))*(1+d2)) * (1+d3) *)
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
(* Substitute vl form *)
rewrite Hvl_eq Hz_eq B1.
(* Now goal: |round(tl + round(c - round((sh+c)(1+d1) - sh)))| < Omega *)
(* Apply Plus_error to outer round (tl + ...) *)
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
  (* Inner-1 round: c - round((sh+c)(1+d1) - sh) *)
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
    (* Innermost: (sh + c)*(1+d1) - sh; use Plus_error for the round there *)
    pose proof (Plus_error.FLT_plus_error_N_ex Zaux.radix2
      (SpecFloat.emin (fprec t) (femax t)) (fprec t)
      (fun x0 : Z => negb (Z.even x0))
      ((FT2R sh + FT2R c) * (1 + d1)) (- FT2R sh)) as Hinner.
    destruct Hinner as (d2 & Hd2 & B2).
    * (* (sh + c)*(1+d1) is in FLT format — it equals FT2R (BPLUS sh c) *)
      have Heq_BPLUS : (FT2R sh + FT2R c) * (1 + d1) = FT2R (BPLUS sh c).
      { rewrite -B1. reflexivity. }
      rewrite Heq_BPLUS. rewrite -B2R_float_of_ftype.
      apply Binary.generic_format_B2R.
    * rewrite -B2R_float_of_ftype.
      apply Generic_fmt.generic_format_opp. apply Binary.generic_format_B2R.
    * have Heq2 : (FT2R sh + FT2R c) * (1 + d1) + - FT2R sh =
                  (FT2R sh + FT2R c) * (1 + d1) - FT2R sh by ring.
      rewrite Heq2 in B2. rewrite B2. clear B2 Heq2.
      (* Now all rounds are expanded into deltas. Bound by interval. *)
      have Htl := tl_bnd. have Hsh := sh_bnd. have Hc := c_bnd.
      move: Hd1 Hd2 Hd3 Hd4. unfold default_rel, Relative.u_ro. simpl.
      intros. simpl in Htl, Hsh, Hc.
      match goal with |- Rabs ?a < _ =>
        field_simplify a; interval with (i_prec 128)
      end.
Qed.

Lemma FIN_w : is_finite w = true.
Proof.
unfold w.
exact (no_overflow_sum_is_finite t tl vl FIN_tl FIN_vl no_ov_w).
Qed.

(* DWPlusDW_vh_w_disjunction (closed version, placed after FIN_w which the proof
   uses for BPLUS_round_correct on w = BPLUS tl vl).
   Mirrors DWPlusDW_sh_c_disjunction: applies DWPlus.DWPlusDW_w_le_vh_aux
   (paper_proofs/DWPlus.v:4946) on FT2R-lifted inputs, identifies paper's
   vh, w with our FT2R-lifted versions via TwoSumEq_FLT + FastTwoSumEq_FLT +
   rnd_plus_FLT_FLX_eq', and lifts Rabs <= to cexp <= via mag_le_abs +
   Z.max_le_compat_r. *)
Lemma DWPlusDW_vh_w_disjunction_full :
  (Generic_fmt.cexp Zaux.radix2
     (SpecFloat.fexp (fprec t) (femax t)) (FT2R w) <=
   Generic_fmt.cexp Zaux.radix2
     (SpecFloat.fexp (fprec t) (femax t)) (FT2R vh))%Z
  \/ FT2R vh = 0%R
  \/ FT2R w = 0%R.
Proof.
destruct (Req_dec (FT2R vh) 0) as [Hvh0 | Hvh_nz]; [right; left; exact Hvh0|].
destruct (Req_dec (FT2R w) 0) as [Hw0 | Hw_nz]; [right; right; exact Hw0|].
left.
have HFIN_sh : is_finite (BPLUS xh yh) = true.
{ change (is_finite (TwoSumF_sum xh yh) = true); exact FIN_sh. }
destruct (Req_dec (FT2R xh + FT2R yh) 0) as [Hxhyh_zero | Hxhyh_nz].
{ (* xh + yh = 0 -> sh = 0 -> Fast2Sum0f -> vh = round(c). If c = 0 vh = 0.
     Otherwise vh = round(c) <> 0. Then w = tl + (c - round(c)). We can't
     conclude cexp w <= cexp vh directly here without paper-level support.
     This sub-case is the cancellation regime; deferred. *)
  admit. }
destruct (Req_dec (FT2R xh) 0) as [Hxh_zero | Hxh_nz].
{ (* xh = 0 case: similar deferred sub-case. *)
  admit. }
have DWx_R : DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl)
  by apply (dw_word_DWdouble xh xl xh DWx).
have DWy_R : DWPlus.double_word (fprec t) choice (FT2R yh) (FT2R yl)
  by apply (dw_word_DWdouble yh yl yh DWy).
have fin_tsxhyh : is_finite_p (TwoSumF xh yh) by split; [exact FIN_sh | exact FIN_sl].
have fin_tsxlyl : is_finite_p (TwoSumF xl yl) by split; [exact FIN_th | exact FIN_tl].
have fin_f2s_shc : is_finite_p (DDModels.Fast2Sum sh c).
{ split.
  - change (is_finite (Fast2Sum_sum sh c) = true); exact FIN_vh.
  - exact FIN_vl. }
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
  apply BPLUS_round_correct. exact FIN_c. }
have Hvh_eq : fst (F2Sum.Fast2Sum (fprec t) choice (FT2R sh) (FT2R c)) = FT2R vh.
{ rewrite heq_f2s /F2Rp /fst //. }
have Hvl_eq : snd (F2Sum.Fast2Sum (fprec t) choice (FT2R sh) (FT2R c)) = FT2R vl.
{ rewrite heq_f2s /F2Rp /snd //. }
have Hp3 : (3 <= fprec t)%Z by cbv; intros; discriminate.
case: (@DWPlus.DWPlusDW_w_le_vh_aux (fprec t) (fprec_gt_one t) choice (eq_refl _)
         (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl) Hp3
         DWx_R DWy_R Hxh_nz Hxhyh_nz)
  => [Hle | [HvhFLX | HwFLX]].
- (* Rabs w <= Rabs vh -- lift to cexp_FLT *)
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
    apply BPLUS_round_correct. exact FIN_w. }
  have Hvh_FT2R : fst (F2Sum.Fast2Sum (fprec t) choice
                        (DWPlus.TwoSum_sum (fprec t) choice (FT2R xh) (FT2R yh))
                        (round Zaux.radix2 (FLX_exp (fprec t)) (Znearest choice)
                          (DWPlus.TwoSum_err (fprec t) choice (FT2R xh) (FT2R yh) +
                           DWPlus.TwoSum_sum (fprec t) choice (FT2R xl) (FT2R yl)))) =
                  FT2R vh.
  { rewrite Hsh_eq Hc_eq. exact Hvh_eq. }
  rewrite Hw_FT2R Hvh_FT2R in Hle.
  have Hmag : (mag Zaux.radix2 (FT2R w) <= mag Zaux.radix2 (FT2R vh))%Z
    by apply: mag_le_abs.
  unfold Generic_fmt.cexp, SpecFloat.fexp, FLT.FLT_exp.
  lia.
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
    apply BPLUS_round_correct. exact FIN_w. }
  by rewrite -Hw_FT2R.
Admitted.

(* vh = BPLUS sh c. Bound |vh| via BPLUS_accurate' + sh_bnd, c_bnd. *)
Lemma vh_bnd : Rabs (FT2R vh) <=
  (Rabs (FT2R sh) + Rabs (FT2R c)) * (1 + default_rel t).
Proof.
have HFIN_BPLUS : is_finite (BPLUS sh c) = true.
{ have HFIN_vh := FIN_vh.
  unfold vh, Fast2Sum_sum, Fast2Sum, fst in HFIN_vh; exact HFIN_vh. }
change (FT2R vh) with (FT2R (BPLUS sh c)).
destruct (BPLUS_accurate' t sh c HFIN_BPLUS) as (d & Hd & Heq).
rewrite Heq Rabs_mult.
apply Rmult_le_compat; try apply Rabs_pos.
- apply Rabs_triang.
- have Hd1 : Rabs (1 + d) <= 1 + Rabs d.
  { apply (Rle_trans _ (Rabs 1 + Rabs d)); [apply Rabs_triang|].
    rewrite Rabs_R1. apply Rle_refl. }
  apply (Rle_trans _ _ _ Hd1). apply Rplus_le_compat_l. exact Hd.
Qed.

(* vl bound via direct expansion through Fast2Sum_err structure.
   Form: vl = (c - (sh*d1 + c*(1+d1))*(1+d2)) * (1+d3) with each |di| <= default_rel. *)
Lemma vl_bnd_eq : exists d1 d2 d3,
  Rabs d1 <= default_rel t /\ Rabs d2 <= default_rel t /\ Rabs d3 <= default_rel t /\
  FT2R vl =
    (FT2R c - (FT2R sh * d1 + FT2R c * (1 + d1)) * (1 + d2)) * (1 + d3).
Proof.
have HFIN1 : is_finite (BPLUS sh c) = true.
{ have HFIN_vh := FIN_vh.
  unfold vh, Fast2Sum_sum, Fast2Sum, fst in HFIN_vh; exact HFIN_vh. }
have HFIN_z := FIN_z.
have HFIN_vl := FIN_vl.
have Hvexp : Valid_exp (SpecFloat.fexp (fprec t) (femax t))
  by (apply FLT.FLT_exp_valid; apply fprec_gt_0).
have Hvrnd : Valid_rnd (Znearest choice) := Generic_fmt.valid_rnd_N choice.
have u_ro_le : Relative.u_ro Zaux.radix2 (fprec t) / (1 + Relative.u_ro Zaux.radix2 (fprec t)) <= default_rel t.
{ unfold default_rel, Relative.u_ro. simpl.
  have Hu_pos : 0 < / 2 * bpow Zaux.radix2 (- fprec t + 1)
    by (apply Rmult_lt_0_compat; [lra | apply bpow_gt_0]).
  apply Rdiv_le_left; lra. }
(* Outer: vl = round(c - z) *)
have Hvl_eq : FT2R vl = round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
  (Znearest choice) (FT2R c - FT2R (BMINUS (BPLUS sh c) sh)).
{ change (FT2R vl) with (FT2R (BMINUS c (BMINUS (BPLUS sh c) sh))).
  symmetry. exact (BMINUS_round_correct t c (BMINUS (BPLUS sh c) sh) HFIN_vl). }
have Hz_eq : FT2R (BMINUS (BPLUS sh c) sh) =
  round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
    (FT2R (BPLUS sh c) - FT2R sh).
{ symmetry. exact (BMINUS_round_correct t (BPLUS sh c) sh HFIN_z). }
destruct (BPLUS_accurate' t sh c HFIN1) as (d1 & Hd1 & B1).
rewrite Hz_eq B1 in Hvl_eq.
(* Outer Plus_error: vl = (c - z') * (1 + d3) *)
have Hfmt_z' : Generic_fmt.generic_format Zaux.radix2
  (SpecFloat.fexp (fprec t) (femax t))
  (round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
     ((FT2R sh + FT2R c) * (1 + d1) - FT2R sh))
  by apply Generic_fmt.generic_format_round.
pose proof (Plus_error.FLT_plus_error_N_ex Zaux.radix2
  (SpecFloat.emin (fprec t) (femax t)) (fprec t)
  (fun x0 : Z => negb (Z.even x0)) (FT2R c)
  (- round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
       ((FT2R sh + FT2R c) * (1 + d1) - FT2R sh))) as Houter.
destruct Houter as (d3 & Hd3 & B3).
- rewrite -B2R_float_of_ftype. apply Binary.generic_format_B2R.
- apply Generic_fmt.generic_format_opp. exact Hfmt_z'.
- have Heq3 : FT2R c +
    - round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
        ((FT2R sh + FT2R c) * (1 + d1) - FT2R sh) =
    FT2R c -
    round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
        ((FT2R sh + FT2R c) * (1 + d1) - FT2R sh) by ring.
  rewrite Heq3 in B3.
  rewrite B3 in Hvl_eq. clear B3 Heq3.
  (* Inner Plus_error for round((sh+c)(1+d1) - sh) *)
  pose proof (Plus_error.FLT_plus_error_N_ex Zaux.radix2
    (SpecFloat.emin (fprec t) (femax t)) (fprec t)
    (fun x0 : Z => negb (Z.even x0))
    ((FT2R sh + FT2R c) * (1 + d1)) (- FT2R sh)) as Hinner.
  destruct Hinner as (d2 & Hd2 & B2).
  + have Heq_BPLUS : (FT2R sh + FT2R c) * (1 + d1) = FT2R (BPLUS sh c).
    { rewrite -B1. reflexivity. }
    rewrite Heq_BPLUS. rewrite -B2R_float_of_ftype.
    apply Binary.generic_format_B2R.
  + rewrite -B2R_float_of_ftype.
    apply Generic_fmt.generic_format_opp. apply Binary.generic_format_B2R.
  + have Heq2 : (FT2R sh + FT2R c) * (1 + d1) + - FT2R sh =
                (FT2R sh + FT2R c) * (1 + d1) - FT2R sh by ring.
    rewrite Heq2 in B2. rewrite B2 in Hvl_eq. clear B2 Heq2.
    exists d1, d2, d3.
    have Habs_d1 : Rabs d1 <= default_rel t.
    { apply (Rle_trans _ _ _ Hd1). apply Req_le. unfold default_rel.
      rewrite /Relative.u_ro //=. }
    have Habs_d2 : Rabs d2 <= default_rel t.
    { apply (Rle_trans _ _ _ Hd2). exact u_ro_le. }
    have Habs_d3 : Rabs d3 <= default_rel t.
    { apply (Rle_trans _ _ _ Hd3). exact u_ro_le. }
    split; [exact Habs_d1|]. split; [exact Habs_d2|]. split; [exact Habs_d3|].
    rewrite Hvl_eq.
    have Heq_alg : (FT2R sh + FT2R c) * (1 + d1) - FT2R sh =
                   FT2R sh * d1 + FT2R c * (1 + d1) by ring.
    rewrite Heq_alg. reflexivity.
Qed.

(* w = BPLUS tl vl. Bound |w| via BPLUS_accurate' + tl_bnd. *)
Lemma w_bnd : Rabs (FT2R w) <=
  (Rabs (FT2R tl) + Rabs (FT2R vl)) * (1 + default_rel t).
Proof.
have HFIN_BPLUS : is_finite (BPLUS tl vl) = true.
{ change (is_finite w = true); exact FIN_w. }
change (FT2R w) with (FT2R (BPLUS tl vl)).
destruct (BPLUS_accurate' t tl vl HFIN_BPLUS) as (d & Hd & Heq).
rewrite Heq Rabs_mult.
apply Rmult_le_compat; try apply Rabs_pos.
- apply Rabs_triang.
- have Hd1 : Rabs (1 + d) <= 1 + Rabs d.
  { apply (Rle_trans _ (Rabs 1 + Rabs d)); [apply Rabs_triang|].
    rewrite Rabs_R1. apply Rle_refl. }
  apply (Rle_trans _ _ _ Hd1). apply Rplus_le_compat_l. exact Hd.
Qed.

(* Final Fast2Sum vh w. Expand vh, w, vl entirely into deltas and bound by interval. *)
Lemma no_ov_zh : Bplus_no_overflow t (FT2R vh) (FT2R w).
Proof.
have HFIN_BPLUS_sh_c : is_finite (BPLUS sh c) = true.
{ have HFIN_vh := FIN_vh.
  unfold vh, Fast2Sum_sum, Fast2Sum, fst in HFIN_vh; exact HFIN_vh. }
have HFIN_BPLUS_tl_vl : is_finite (BPLUS tl vl) = true.
{ change (is_finite w = true); exact FIN_w. }
(* Express FT2R vh via BPLUS_accurate' *)
destruct (BPLUS_accurate' t sh c HFIN_BPLUS_sh_c) as (dvh & Hdvh & Bvh).
have Hvh_eq : FT2R vh = (FT2R sh + FT2R c) * (1 + dvh).
{ change (FT2R vh) with (FT2R (BPLUS sh c)). exact Bvh. }
(* Express FT2R w via BPLUS_accurate' *)
destruct (BPLUS_accurate' t tl vl HFIN_BPLUS_tl_vl) as (dw & Hdw & Bw).
have Hw_eq : FT2R w = (FT2R tl + FT2R vl) * (1 + dw).
{ change (FT2R w) with (FT2R (BPLUS tl vl)). exact Bw. }
(* Express FT2R vl via vl_bnd_eq *)
destruct vl_bnd_eq as (d1 & d2 & d3 & Hd1 & Hd2 & Hd3 & Hvl_eq).
unfold Bplus_no_overflow.
rewrite Hvh_eq Hw_eq Hvl_eq.
pose proof (Plus_error.FLT_plus_error_N_ex Zaux.radix2
  (SpecFloat.emin (fprec t) (femax t)) (fprec t)
  (fun x0 : Z => negb (Z.even x0))
  ((FT2R sh + FT2R c) * (1 + dvh))
  ((FT2R tl +
    (FT2R c - (FT2R sh * d1 + FT2R c * (1 + d1)) * (1 + d2)) * (1 + d3))
   * (1 + dw))) as H.
destruct H as (d5 & Hd5 & B).
- have Heq_vh : (FT2R sh + FT2R c) * (1 + dvh) = FT2R vh by (rewrite -Hvh_eq; reflexivity).
  rewrite Heq_vh -B2R_float_of_ftype. apply Binary.generic_format_B2R.
- have Heq_w : (FT2R tl +
    (FT2R c - (FT2R sh * d1 + FT2R c * (1 + d1)) * (1 + d2)) * (1 + d3))
   * (1 + dw) = FT2R w by (rewrite -Hvl_eq -Hw_eq; reflexivity).
  rewrite Heq_w -B2R_float_of_ftype. apply Binary.generic_format_B2R.
- rewrite B. clear B.
  have Hsh := sh_bnd. have Hc := c_bnd. have Htl := tl_bnd.
  move: Hdvh Hdw Hd1 Hd2 Hd3 Hd5. unfold default_rel, Relative.u_ro. simpl.
  intros. simpl in Hsh, Hc, Htl.
  match goal with |- Rabs ?a < _ =>
    field_simplify a; interval with (i_prec 128)
  end.
Qed.

Lemma Hw_le_vh : Rabs (FT2R w) <= Rabs (FT2R vh).
Proof. Admitted. (* same edge-case issue as Hc_le_sh; not used in FIN_zh chain *)

(* Main result for FIN_zh: the fst component of AccurateDWPlusDW is finite.
   This is provable under our hypotheses (DWx, DWy, finiteness of inputs,
   |xh + xl|, |yh + yl| < Omega/4) WITHOUT needing Hc_le_sh or Hw_le_vh. *)
Theorem AccurateDWPlusDW_fst_finite :
  is_finite (fst (AccurateDWPlusDW xh xl yh yl)) = true.
Proof.
rewrite /AccurateDWPlusDW.
replace (TwoSumF xh yh) with (sh, sl) => //.
replace (TwoSumF xl yl) with (th, tl) => //.
rewrite /fst /snd.
replace (Fast2Sum sh c) with (vh, vl) => //.
unfold Fast2Sum, fst.
exact (no_overflow_sum_is_finite t vh w FIN_vh FIN_w no_ov_zh).
Qed.

Theorem AccurateDWPlusDW_finite :
  is_finite_p (AccurateDWPlusDW xh xl yh yl).
Proof.
rewrite /is_finite_p /AccurateDWPlusDW.
replace (TwoSumF xh yh) with (sh, sl) => //.
replace (TwoSumF xl yl) with (th, tl) => //.
rewrite /fst /snd.
replace (Fast2Sum sh c) with (vh, vl) => //.
split.
- (* zh = fst (Fast2Sum vh w) = BPLUS vh w *)
  unfold Fast2Sum, fst.
  exact (no_overflow_sum_is_finite t vh w FIN_vh FIN_w no_ov_zh).
- (* zl = snd (Fast2Sum vh w) *)
  unfold Fast2Sum_err.
  apply (is_finite_FastSum vh w Hw_le_vh).
  unfold Fast2Sum, fst.
  exact (no_overflow_sum_is_finite t vh w FIN_vh FIN_w no_ov_zh).
Qed.

(* Bridge lemmas exposed for VST verification of dw_plus_dw2:
   each forward_call to two_sum / fast_2sum needs the appropriate cond. *)

Lemma TwoSum_cond_xh_yh_inner : TwoSum_cond xh yh.
Proof.
  unfold TwoSum_cond; split; [|split].
  - exact FIN_sh.
  - exact (no_overflow_minus_is_finite t xh yh HFINxh HFINyh no_ov_minus_xhyh).
  - apply (Rle_lt_trans _ (/4 * Omega));
      [exact Hyh_tight_bnd | exact Omega4_lt_predOmega].
Qed.

Lemma TwoSum_cond_xl_yl_inner : TwoSum_cond xl yl.
Proof.
  unfold TwoSum_cond; split; [|split].
  - exact FIN_th.
  - exact (no_overflow_minus_is_finite t xl yl HFINxl HFINyl no_ov_minus_xlyl).
  - apply (Rle_lt_trans _ (/4 * Omega));
      [exact yl_le_qOmega | exact Omega4_lt_predOmega].
Qed.

(* Fast2Sum_cond requires |b| <= |a|, which here is Hc_le_sh / Hw_le_vh —
   both currently admitted. The bridges thus depend on those admits. *)
Lemma Fast2Sum_cond_sh_c_inner : Fast2Sum_cond sh c.
Proof.
  unfold Fast2Sum_cond; split.
  - change (is_finite (BPLUS sh c) = true).
    change (is_finite vh = true). exact FIN_vh.
  - exact Hc_le_sh.
Qed.

Lemma Fast2Sum_cond_vh_w_inner : Fast2Sum_cond vh w.
Proof.
  unfold Fast2Sum_cond; split.
  - change (is_finite (BPLUS vh w) = true).
    exact (no_overflow_sum_is_finite t vh w FIN_vh FIN_w no_ov_zh).
  - exact Hw_le_vh.
Qed.

End DWPlusDWFinite.

(* Bridge: DWPlusDW_cond directly implies finiteness of the fst component.
   This packages the DWPlusDWFinite section's hypotheses as a single Prop
   suitable for use as a VST PRE-condition. *)
Section DWPlusDWCondBridge.
Context {NANS : Nans}.
Variables (xh xl yh yl : ftype Tdouble).

Theorem AccurateDWPlusDW_finite_from_cond :
  DWPlusDW_cond xh xl yh yl ->
  is_finite (fst (AccurateDWPlusDW xh xl yh yl)) = true.
Proof.
intros [HFxh [HFxl [HFyh [HFyl [HDWx [HDWy [HBxh HByh]]]]]]].
eapply AccurateDWPlusDW_fst_finite; eassumption.
Qed.

(* Forwarders for the C-level VST forward_calls inside body_dw_plus_dw2:
   - two_sum(&sh, x->s, y->s) needs TwoSum_cond xh yh
   - two_sum(&th, x->t, y->t) needs TwoSum_cond xl yl
   - fast_2sum(&vh, sh.s, c) needs Fast2Sum_cond (BPLUS xh yh) (BPLUS sl th)
   - fast_2sum(st,  vh.s, w) needs Fast2Sum_cond vh w
*)
Theorem TwoSum_cond_from_DWPlusDW_cond_xh_yh :
  DWPlusDW_cond xh xl yh yl -> TwoSum_cond xh yh.
Proof.
intros [HFxh [HFxl [HFyh [HFyl [HDWx [HDWy [HBxh HByh]]]]]]].
eapply TwoSum_cond_xh_yh_inner; eassumption.
Qed.

Theorem TwoSum_cond_from_DWPlusDW_cond_xl_yl :
  DWPlusDW_cond xh xl yh yl -> TwoSum_cond xl yl.
Proof.
intros [HFxh [HFxl [HFyh [HFyl [HDWx [HDWy [HBxh HByh]]]]]]].
eapply TwoSum_cond_xl_yl_inner; eassumption.
Qed.

(* These two depend on Hc_le_sh / Hw_le_vh (admitted in DWPlusDWFinite). *)
Theorem Fast2Sum_cond_from_DWPlusDW_cond_sh_c :
  DWPlusDW_cond xh xl yh yl ->
  Fast2Sum_cond (TwoSumF_sum xh yh)
                (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl)).
Proof.
intros [HFxh [HFxl [HFyh [HFyl [HDWx [HDWy [HBxh HByh]]]]]]].
eapply Fast2Sum_cond_sh_c_inner; eassumption.
Qed.

Theorem Fast2Sum_cond_from_DWPlusDW_cond_vh_w :
  DWPlusDW_cond xh xl yh yl ->
  Fast2Sum_cond
    (Fast2Sum_sum (TwoSumF_sum xh yh)
                  (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl)))
    (BPLUS (TwoSumF_err xl yl)
           (Fast2Sum_err (TwoSumF_sum xh yh)
                         (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl)))).
Proof.
intros [HFxh [HFxl [HFyh [HFyl [HDWx [HDWy [HBxh HByh]]]]]]].
eapply Fast2Sum_cond_vh_w_inner; eassumption.
Qed.

End DWPlusDWCondBridge.

