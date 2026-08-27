(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Mixed error and output validity when the leading quotient of [DWDivFP3] is
    subnormal.  The normal FLT to FLX bridge does not apply here.  Instead, the
    quotient, correction, and final sum lie on the [2^emin] lattice.  This
    gives [|th-xh/y| <= eta/2], keeps the low input contribution below
    [eta/2], and makes the final [Fast2Sum] exact.  The result has the same
    [3u^2|Q| + eta] bound as the normal leading quotient case.
    [DWDivFP_mixed_acc] combines both cases. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common FLT_helpers.
Require Import DWTimesFP DWDivFP DDConds DWord_defs Fast2Mult_acc
        Fast2Mult_acc_helpers Fast2Sum_acc.
Require Import DWPlusFP_relative_acc_helpers DWMulFP_relative_acc DW_acc_lemmas.
Require Import DD.accuracy_proofs.dw_opps.DWDivFP_relative_acc.
From Flocq Require Import Pff2Flocq Core.
From Flocq Require Import Mult_error FLT Div_sqrt_error Plus_error.
Require Import mathcomp.ssreflect.ssreflect.

Section Sub.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (@common.emin t).
Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Notation u := (bpow radix2 (- fprec t)).
Notation eta := (bpow radix2 (@common.emin t)).
Notation ulp := (Ulp.ulp Zaux.radix2 fexp).

Local Instance valid_fexp_inst_sub : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.

Variables (xh xl y : ftype t).

Hypothesis Hp4 : (4 <= fprec t)%Z.
Hypothesis FIN : is_finite_p (DWDivFP3 xh xl y).
Hypothesis Hyne : FT2R y <> 0.
Hypothesis Hdwp : double_word_prop xh xl.
Hypothesis Hxhlb : bpow radix2 (emin + 2 * fprec t) <= Rabs (FT2R xh).
Hypothesis Hsub : Rabs (FT2R xh / FT2R y) < bpow radix2 (emin + fprec t - 1).

(* ---------- setup facts ---------- *)

Local Lemma sub_ulp_q : ulp (FT2R xh / FT2R y) = eta.
Proof.
apply ulp_FLT_small; [ apply fprec_gt_0 |].
eapply Rlt_le_trans; [ exact Hsub |]. apply bpow_le.
change (@common.emin t) with (SpecFloat.emin (fprec t) (femax t)). lia.
Qed.

Local Lemma sub_th_eq : FT2R (BDIV xh y) = round radix2 fexp (Znearest choice) (FT2R xh / FT2R y).
Proof. by rewrite (BDIV_round_correct t xh y Hyne (FINth xh xl y FIN)). Qed.

Local Lemma sub_th_close : Rabs (FT2R (BDIV xh y) - FT2R xh / FT2R y) <= /2 * eta.
Proof.
rewrite sub_th_eq -sub_ulp_q.
exact (@error_le_half_ulp radix2 fexp valid_fexp_inst_sub choice (FT2R xh / FT2R y)).
Qed.

(* |xh| = |q| * |y| *)
Local Lemma sub_xh_split : Rabs (FT2R xh) = Rabs (FT2R xh / FT2R y) * Rabs (FT2R y).
Proof.
rewrite -Rabs_mult. f_equal. field; exact Hyne.
Qed.

(* u * |xh| < eta * |y| / 2 : the key smallness fact *)
Local Lemma sub_u_xh : u * Rabs (FT2R xh) < /2 * (eta * Rabs (FT2R y)).
Proof.
have HY : 0 < Rabs (FT2R y) by (apply Rabs_pos_lt; exact Hyne).
rewrite sub_xh_split.
have Hkey : u * Rabs (FT2R xh / FT2R y) < /2 * eta.
{ have Hstep : u * Rabs (FT2R xh / FT2R y) < u * bpow radix2 (emin + fprec t - 1)
    by (apply Rmult_lt_compat_l; [ apply bpow_gt_0 | exact Hsub ]).
  have Heq : u * bpow radix2 (emin + fprec t - 1) = /2 * eta.
  { rewrite -bpow_plus.
    have -> : (- fprec t + (emin + fprec t - 1))%Z = (emin - 1)%Z by lia.
    have -> : (emin - 1)%Z = (emin + -1)%Z by lia.
    rewrite bpow_plus. have -> : bpow radix2 (-1) = /2 by (simpl; lra). ring. }
  rewrite Heq in Hstep; exact Hstep. }
nra.
Qed.

(* |y| > 2^(p+1) : forced by clause 8 together with the subnormal quotient *)
Local Lemma sub_y_big : bpow radix2 (fprec t + 1) < Rabs (FT2R y).
Proof.
have HY : 0 < Rabs (FT2R y) by (apply Rabs_pos_lt; exact Hyne).
have H1 : bpow radix2 (emin + 2 * fprec t) <= Rabs (FT2R xh / FT2R y) * Rabs (FT2R y)
  by (rewrite -sub_xh_split; exact Hxhlb).
have H2 : Rabs (FT2R xh / FT2R y) * Rabs (FT2R y)
          < bpow radix2 (emin + fprec t - 1) * Rabs (FT2R y)
  by (apply Rmult_lt_compat_r; [ exact HY | exact Hsub ]).
have H3 : bpow radix2 (emin + 2 * fprec t)
          < bpow radix2 (emin + fprec t - 1) * Rabs (FT2R y) by lra.
have Heq : bpow radix2 (emin + 2 * fprec t)
         = bpow radix2 (emin + fprec t - 1) * bpow radix2 (fprec t + 1).
{ rewrite -bpow_plus. f_equal. lia. }
rewrite Heq in H3.
have Hpos : 0 < bpow radix2 (emin + fprec t - 1) by apply bpow_gt_0.
apply (Rmult_lt_reg_l (bpow radix2 (emin + fprec t - 1))); [ exact Hpos |].
rewrite (Rmult_comm _ (bpow radix2 (fprec t + 1))) in H3. lra.
Qed.

Local Lemma sub_u_small : u <= /16.
Proof.
have -> : (/16:R) = bpow radix2 (-4) by (simpl; lra).
apply bpow_le. lia.
Qed.


(* ---------- eta is negligible: eta <= u*M/2, with M = eta*|y| ---------- *)
Local Lemma sub_eta_uM : eta <= /2 * (u * (eta * Rabs (FT2R y))).
Proof.
have He : 0 < eta by apply bpow_gt_0.
have Hy := sub_y_big.
have Hu0 : 0 < u by apply bpow_gt_0.
have Hprod : 2 <= u * Rabs (FT2R y).
{ have H2 : u * bpow radix2 (fprec t + 1) = 2.
  { rewrite -bpow_plus. have -> : (- fprec t + (fprec t + 1))%Z = 1%Z by lia.
    by (simpl; lra). }
  have Hstep : u * bpow radix2 (fprec t + 1) <= u * Rabs (FT2R y)
    by (apply Rmult_le_compat_l; [ lra | lra ]).
  lra. }
nra.
Qed.

(* ---------- node finiteness ---------- *)
Local Lemma sub_fin_pih : is_finite (BMULT (BDIV xh y) y) = true.
Proof. exact (proj2 (BMINUS_finite_e t xh (BMULT (BDIV xh y) y) (FIN_dh xh xl y FIN))). Qed.

Local Lemma sub_fin_pil : is_finite (Fast2Mult_err (BDIV xh y) y) = true.
Proof.
exact (proj2 (BMINUS_finite_e t (BMINUS xh (BMULT (BDIV xh y) y))
                (Fast2Mult_err (BDIV xh y) y) (FIN_dt xh xl y FIN))).
Qed.

(* ---------- Computation over the reals ---------- *)
Notation X   := (FT2R xh).
Notation L   := (FT2R xl).
Notation Y   := (FT2R y).
Notation T   := (FT2R (BDIV xh y)).
Notation A   := (FT2R (BDIV xh y) * FT2R y).
Notation Pih := (FT2R (BMULT (BDIV xh y) y)).
Notation Pil := (FT2R (Fast2Mult_err (BDIV xh y) y)).
Notation Dh  := (FT2R (BMINUS xh (BMULT (BDIV xh y) y))).
Notation Dt  := (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                              (Fast2Mult_err (BDIV xh y) y))).
Notation Dd  := (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                     (Fast2Mult_err (BDIV xh y) y)) xl)).
Notation M   := (eta * Rabs (FT2R y)).

Local Lemma sub_M_pos : 0 <= M.
Proof. apply Rmult_le_pos; [ apply bpow_ge_0 | apply Rabs_pos ]. Qed.

Local Lemma sub_uM_pos : 0 <= u * M.
Proof. apply Rmult_le_pos; [ apply bpow_ge_0 | apply sub_M_pos ]. Qed.

(* the single nonlinear fact everything downstream needs *)
Local Lemma sub_uM : u * M <= /16 * M.
Proof. have Hu := sub_u_small. have HM := sub_M_pos. nra. Qed.

(* |A - X| <= M/2 *)
Local Lemma sub_A_X : Rabs (A - X) <= /2 * M.
Proof.
have HT := sub_th_close.
have Heq : A - X = (T - FT2R xh / FT2R y) * Y.
{ field; exact Hyne. }
rewrite Heq Rabs_mult.
have Hy : 0 <= Rabs Y by apply Rabs_pos.
have Hstep : Rabs (T - FT2R xh / FT2R y) * Rabs Y <= (/2 * eta) * Rabs Y
  by (apply Rmult_le_compat_r; [ exact Hy | exact HT ]).
nra.
Qed.

(* u*|A| <= M/2 + u*M/2 *)
Local Lemma sub_uA : u * Rabs A <= /2 * M + /2 * (u * M).
Proof.
have H1 := sub_A_X. have H2 := sub_u_xh.
have Hu0 : 0 < u by apply bpow_gt_0.
have HA : Rabs A <= Rabs X + /2 * M.
{ have Ht : Rabs A - Rabs X <= Rabs (A - X) by apply Rabs_triang_inv.
  lra. }
have Hstep : u * Rabs A <= u * (Rabs X + /2 * M)
  by (apply Rmult_le_compat_l; [ lra | exact HA ]).
have Hexp : u * (Rabs X + /2 * M) = u * Rabs X + /2 * (u * M) by ring.
rewrite Hexp in Hstep. lra.
Qed.

(* |Pih - A| <= 5/8 * M *)
Local Lemma sub_pih_err : Rabs (Pih - A) <= 5/8 * M.
Proof.
have He : Rabs (Pih - A) <= u * Rabs A + /2 * eta.
{ have H : Rabs (round radix2 fexp (Znearest choice) A - A)
             <= u * Rabs A + /2 * eta by apply round_FLT_error_rel_emin.
  have Hpih : Pih = round radix2 fexp (Znearest choice) A
    by rewrite (BMULT_round_correct t (BDIV xh y) y sub_fin_pih).
  rewrite Hpih; exact H. }
have HuA := sub_uA. have HeM := sub_eta_uM.
have HuM := sub_uM. have HM := sub_M_pos.
lra.
Qed.

(* |X - Pih| <= 9/8 * M *)
Local Lemma sub_X_pih : Rabs (X - Pih) <= 9/8 * M.
Proof.
have H1 := sub_A_X. have H2 := sub_pih_err.
have Ht : Rabs (X - Pih) <= Rabs (X - A) + Rabs (A - Pih).
{ have He : X - Pih = (X - A) + (A - Pih) by ring.
  rewrite He. apply Rabs_triang. }
rewrite (Rabs_minus_sym X A) (Rabs_minus_sym A Pih) in Ht.
lra.
Qed.

(* |Pil| <= 5/8 * M  (Fast2Mult accuracy + universal ulp bound) *)
Local Lemma sub_Pil : Rabs Pil <= 5/8 * M.
Proof.
have Hacc : Rabs Pil <= /2 * ulp A
  by exact (Fast2Mult_accuracy_from_acc_only_cond (BDIV xh y) y sub_fin_pih).
have Hulp : ulp A <= 2 * u * Rabs A + eta
  by apply ulp_le_relative_plus_emin.
have HuA := sub_uA. have HeM := sub_eta_uM.
have HuM := sub_uM. have HM := sub_M_pos.
lra.
Qed.

(* Fast2Mult defect: |Pih + Pil - A| <= u * M *)
Local Lemma sub_defect : Rabs (Pih + Pil - A) <= u * M.
Proof.
have Hmid : Rabs (A - Pih) <= /2 * ulp A.
{ have Hpih : Pih = round radix2 fexp (Znearest choice) A
    by rewrite (BMULT_round_correct t (BDIV xh y) y sub_fin_pih).
  rewrite (Rabs_minus_sym A Pih) Hpih.
  exact (@error_le_half_ulp radix2 fexp valid_fexp_inst_sub choice A). }
have Hpil : Rabs (Pil - (A - Pih)) <= u * Rabs (A - Pih) + /2 * eta.
{ have H : Rabs (round radix2 fexp (Znearest choice) (A - Pih) - (A - Pih))
             <= u * Rabs (A - Pih) + /2 * eta by apply round_FLT_error_rel_emin.
  have Hf := sub_fin_pil.
  have Hp : Pil = round radix2 fexp (Znearest choice) (A - Pih).
  { unfold Fast2Mult_err, Fast2Mult, snd in Hf |- *.
    rewrite -(BFMA_round_correct t (BDIV xh y) y (BOPP (BMULT (BDIV xh y) y)) Hf).
    rewrite -(BOPP_binary t (BMULT (BDIV xh y) y) (or_intror sub_fin_pih)).
    f_equal; ring. }
  rewrite Hp; exact H. }
have Hulp : ulp A <= 2 * u * Rabs A + eta
  by apply ulp_le_relative_plus_emin.
have HuA := sub_uA. have HeM := sub_eta_uM.
have HuM := sub_uM. have HM := sub_M_pos.
have Hu := sub_u_small.
have Hpos : 0 <= u * Rabs A
  by (apply Rmult_le_pos; [ apply bpow_ge_0 | apply Rabs_pos ]).
have He0 : 0 <= eta by apply bpow_ge_0.
have HuMpos : 0 <= u * M
  by (apply Rmult_le_pos; [ apply bpow_ge_0 | exact HM ]).
(* Bound involving only M on the product node rounding error. *)
have HAP : Rabs (A - Pih) <= 9/16 * M by lra.
have Hb2 : u * Rabs (A - Pih) <= u * (9/16 * M)
  by (apply Rmult_le_compat_l; [ apply bpow_ge_0 | exact HAP ]).
have Hexp : u * (9/16 * M) = 9/16 * (u * M) by ring.
rewrite Hexp in Hb2.
have Heq : Rabs (Pih + Pil - A) = Rabs (Pil - (A - Pih))
  by (f_equal; ring).
rewrite Heq. lra.
Qed.


(* ---------- the residual chain ---------- *)

Local Lemma sub_L : Rabs L <= /2 * M.
Proof.
have Hrel : Rabs L <= u * Rabs X
  by exact (@dw_low_le_u_high t STD xh xl Hdwp).
have H := sub_u_xh. lra.
Qed.

Local Lemma sub_Dh_eq : Dh = round radix2 fexp (Znearest choice) (X - Pih).
Proof.
by rewrite (BMINUS_round_correct t xh (BMULT (BDIV xh y) y) (FIN_dh xh xl y FIN)).
Qed.

Local Lemma sub_e1 : Rabs (Dh - (X - Pih)) <= 3/2 * (u * M).
Proof.
have He : Rabs (Dh - (X - Pih)) <= u * Rabs (X - Pih) + /2 * eta.
{ have H : Rabs (round radix2 fexp (Znearest choice) (X - Pih) - (X - Pih))
             <= u * Rabs (X - Pih) + /2 * eta by apply round_FLT_error_rel_emin.
  rewrite sub_Dh_eq; exact H. }
have HX := sub_X_pih. have HeM := sub_eta_uM. have HM := sub_M_pos. have HuP := sub_uM_pos.
have Hstep : u * Rabs (X - Pih) <= u * (9/8 * M)
  by (apply Rmult_le_compat_l; [ apply bpow_ge_0 | exact HX ]).
have Hexp : u * (9/8 * M) = 9/8 * (u * M) by ring.
rewrite Hexp in Hstep. lra.
Qed.

Local Lemma sub_Dh : Rabs Dh <= 5/4 * M.
Proof.
have HX := sub_X_pih.
have Hr : Rabs Dh <= 9/8 * M * (1 + u) + /2 * eta.
{ have H : Rabs (round radix2 fexp (Znearest choice) (X - Pih))
             <= 9/8 * M * (1 + u) + /2 * eta
    by apply round_abs_le_of_abs_bound.
  rewrite sub_Dh_eq; exact H. }
have HeM := sub_eta_uM. have HuM := sub_uM. have HM := sub_M_pos. have HuP := sub_uM_pos.
have Hexp : 9/8 * M * (1 + u) = 9/8 * M + 9/8 * (u * M) by ring.
rewrite Hexp in Hr. lra.
Qed.

Local Lemma sub_Dh_Pil : Rabs (Dh - Pil) <= 15/8 * M.
Proof.
have H1 := sub_Dh. have H2 := sub_Pil.
have Ht : Rabs (Dh - Pil) <= Rabs Dh + Rabs Pil.
{ have He : Dh - Pil = Dh + (- Pil) by ring.
  rewrite He.
  eapply Rle_trans; [ apply Rabs_triang |].
  rewrite Rabs_Ropp. lra. }
lra.
Qed.

Local Lemma sub_Dt_eq : Dt = round radix2 fexp (Znearest choice) (Dh - Pil).
Proof.
by rewrite (BMINUS_round_correct t (BMINUS xh (BMULT (BDIV xh y) y))
              (Fast2Mult_err (BDIV xh y) y) (FIN_dt xh xl y FIN)).
Qed.

Local Lemma sub_e2 : Rabs (Dt - (Dh - Pil)) <= 17/8 * (u * M).
Proof.
have He : Rabs (Dt - (Dh - Pil)) <= u * Rabs (Dh - Pil) + /2 * eta.
{ have H : Rabs (round radix2 fexp (Znearest choice) (Dh - Pil) - (Dh - Pil))
             <= u * Rabs (Dh - Pil) + /2 * eta by apply round_FLT_error_rel_emin.
  rewrite sub_Dt_eq; exact H. }
have HD := sub_Dh_Pil. have HeM := sub_eta_uM. have HM := sub_M_pos. have HuP := sub_uM_pos.
have Hstep : u * Rabs (Dh - Pil) <= u * (15/8 * M)
  by (apply Rmult_le_compat_l; [ apply bpow_ge_0 | exact HD ]).
have Hexp : u * (15/8 * M) = 15/8 * (u * M) by ring.
rewrite Hexp in Hstep. lra.
Qed.

Local Lemma sub_Dt : Rabs Dt <= 17/8 * M.
Proof.
have HD := sub_Dh_Pil.
have Hr : Rabs Dt <= 15/8 * M * (1 + u) + /2 * eta.
{ have H : Rabs (round radix2 fexp (Znearest choice) (Dh - Pil))
             <= 15/8 * M * (1 + u) + /2 * eta
    by apply round_abs_le_of_abs_bound.
  rewrite sub_Dt_eq; exact H. }
have HeM := sub_eta_uM. have HuM := sub_uM. have HM := sub_M_pos. have HuP := sub_uM_pos.
have Hexp : 15/8 * M * (1 + u) = 15/8 * M + 15/8 * (u * M) by ring.
rewrite Hexp in Hr. lra.
Qed.

Local Lemma sub_Dt_L : Rabs (Dt + L) <= 21/8 * M.
Proof.
have H1 := sub_Dt. have H2 := sub_L.
eapply Rle_trans; [ apply Rabs_triang |]. lra.
Qed.

Local Lemma sub_Dd_eq : Dd = round radix2 fexp (Znearest choice) (Dt + L).
Proof.
by rewrite (BPLUS_round_correct t (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
              (Fast2Mult_err (BDIV xh y) y)) xl (FIN_d xh xl y FIN)).
Qed.

Local Lemma sub_e3 : Rabs (Dd - (Dt + L)) <= 23/8 * (u * M).
Proof.
have He : Rabs (Dd - (Dt + L)) <= u * Rabs (Dt + L) + /2 * eta.
{ have H : Rabs (round radix2 fexp (Znearest choice) (Dt + L) - (Dt + L))
             <= u * Rabs (Dt + L) + /2 * eta by apply round_FLT_error_rel_emin.
  rewrite sub_Dd_eq; exact H. }
have HD := sub_Dt_L. have HeM := sub_eta_uM. have HM := sub_M_pos. have HuP := sub_uM_pos.
have Hstep : u * Rabs (Dt + L) <= u * (21/8 * M)
  by (apply Rmult_le_compat_l; [ apply bpow_ge_0 | exact HD ]).
have Hexp : u * (21/8 * M) = 21/8 * (u * M) by ring.
rewrite Hexp in Hstep. lra.
Qed.

(* The computed d tracks the true residual to within M/2. *)
Local Lemma sub_resid : Rabs (Dd - (X + L - A)) <= /2 * M.
Proof.
have E1 := sub_e1. have E2 := sub_e2. have E3 := sub_e3. have DF := sub_defect.
have HuM := sub_uM. have HM := sub_M_pos. have HuP := sub_uM_pos.
have DF2 : Rabs (A - (Pih + Pil)) <= u * M.
{ rewrite (Rabs_minus_sym A (Pih + Pil)). exact DF. }
have Ht : Rabs (Dd - (X + L - A))
        <= Rabs (Dd - (Dt + L)) + Rabs (Dt - (Dh - Pil))
           + Rabs (Dh - (X - Pih)) + Rabs (A - (Pih + Pil)).
{ have Hsplit : Dd - (X + L - A)
              = (Dd - (Dt + L)) + (Dt - (Dh - Pil)) + (Dh - (X - Pih))
                + (A - (Pih + Pil)) by ring.
  rewrite Hsplit.
  eapply Rle_trans; [ apply Rabs_triang |].
  apply Rplus_le_compat_r.
  eapply Rle_trans; [ apply Rabs_triang |].
  apply Rplus_le_compat_r.
  apply Rabs_triang. }
lra.
Qed.


(* ---------- from the residual to the corrected quotient ---------- *)

Notation Tl := (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                          (Fast2Mult_err (BDIV xh y) y)) xl) y)).
Notation Q  := ((FT2R xh + FT2R xl) / FT2R y).

Local Lemma sub_u_q : u * Rabs (X / Y) < /2 * eta.
Proof.
have Hstep : u * Rabs (X / Y) < u * bpow radix2 (emin + fprec t - 1)
  by (apply Rmult_lt_compat_l; [ apply bpow_gt_0 | exact Hsub ]).
have Heq : u * bpow radix2 (emin + fprec t - 1) = /2 * eta.
{ rewrite -bpow_plus.
  have -> : (- fprec t + (emin + fprec t - 1))%Z = (emin + -1)%Z by lia.
  rewrite bpow_plus. have -> : bpow radix2 (-1) = /2 by (simpl; lra). ring. }
lra.
Qed.

(* |Q - T| <= eta : the target is already within one eta of the leading node *)
Local Lemma sub_Q_T : Rabs (Q - T) <= eta.
Proof.
have HY : 0 < Rabs Y by (apply Rabs_pos_lt; exact Hyne).
have HL := sub_L. have HT := sub_th_close. have Huq := sub_u_q.
have HQq : Rabs (Q - X / Y) <= u * Rabs (X / Y).
{ have Heq : Q - X / Y = L / Y by (field; exact Hyne).
  have Hrel : Rabs L <= u * Rabs X
    by exact (@dw_low_le_u_high t STD xh xl Hdwp).
  rewrite Heq /Rdiv !Rabs_mult Rabs_inv.
  have Hexp : u * (Rabs X * / Rabs Y) = (u * Rabs X) * / Rabs Y by ring.
  rewrite Hexp.
  apply Rmult_le_compat_r;
    [ apply Rlt_le, Rinv_0_lt_compat; exact HY | exact Hrel ]. }
have Ht : Rabs (Q - T) <= Rabs (Q - X / Y) + Rabs (X / Y - T).
{ have Hsplit : Q - T = (Q - X / Y) + (X / Y - T) by ring.
  rewrite Hsplit. apply Rabs_triang. }
rewrite (Rabs_minus_sym (X / Y) T) in Ht. lra.
Qed.

(* the computed correction tracks Q - T to within eta/2 *)
Local Lemma sub_dy_close : Rabs (Dd / Y - (Q - T)) <= /2 * eta.
Proof.
have HY : 0 < Rabs Y by (apply Rabs_pos_lt; exact Hyne).
have HR := sub_resid.
have Heq : Dd / Y - (Q - T) = (Dd - (X + L - A)) / Y by (field; exact Hyne).
rewrite Heq /Rdiv Rabs_mult Rabs_inv.
apply (Rmult_le_reg_r (Rabs Y)); [ exact HY |].
have Hl : Rabs (Dd - (X + L - A)) * / Rabs Y * Rabs Y
        = Rabs (Dd - (X + L - A)) by (field; lra).
rewrite Hl.
have Hr : /2 * eta * Rabs Y = /2 * (eta * Rabs Y) by ring.
rewrite Hr. exact HR.
Qed.

Local Lemma sub_dy_bnd : Rabs (Dd / Y) <= 3/2 * eta.
Proof.
have H1 := sub_dy_close. have H2 := sub_Q_T.
have Ht : Rabs (Dd / Y) <= Rabs (Dd / Y - (Q - T)) + Rabs (Q - T).
{ have Hsplit : Dd / Y = (Dd / Y - (Q - T)) + (Q - T) by ring.
  rewrite {1}Hsplit. apply Rabs_triang. }
lra.
Qed.

Local Lemma sub_ulp_dy : ulp (Dd / Y) = eta.
Proof.
apply ulp_FLT_small; [ apply fprec_gt_0 |].
have H := sub_dy_bnd. have He : 0 < eta by apply bpow_gt_0.
have Hb : 3/2 * eta < bpow radix2 (emin + fprec t).
{ have Heq : bpow radix2 (emin + fprec t) = eta * bpow radix2 (fprec t)
    by (rewrite -bpow_plus; f_equal; lia).
  have H16 : (16:R) <= bpow radix2 (fprec t).
  { have -> : (16:R) = bpow radix2 4 by (simpl; lra). apply bpow_le; lia. }
  rewrite Heq. nra. }
change (SpecFloat.emin (fprec t) (femax t) + fprec t)%Z
  with (emin + fprec t)%Z. lra.
Qed.

Local Lemma sub_Tl_close : Rabs (Tl - Dd / Y) <= /2 * eta.
Proof.
have HTl : Tl = round radix2 fexp (Znearest choice) (Dd / Y)
  by rewrite (BDIV_round_correct t _ y Hyne (FINtl xh xl y FIN)).
rewrite HTl -sub_ulp_dy.
exact (@error_le_half_ulp radix2 fexp valid_fexp_inst_sub choice (Dd / Y)).
Qed.

(* the correction lands within eta of the exact one: this IS the theorem *)
Local Lemma sub_Tl_Q_T : Rabs (Tl - (Q - T)) <= eta.
Proof.
have H1 := sub_Tl_close. have H2 := sub_dy_close.
have Ht : Rabs (Tl - (Q - T)) <= Rabs (Tl - Dd / Y) + Rabs (Dd / Y - (Q - T)).
{ have Hsplit : Tl - (Q - T) = (Tl - Dd / Y) + (Dd / Y - (Q - T)) by ring.
  rewrite Hsplit. apply Rabs_triang. }
lra.
Qed.

Local Lemma sub_Tl_bnd : Rabs Tl <= 2 * eta.
Proof.
have H1 := sub_Tl_close. have H2 := sub_dy_bnd.
have Ht : Rabs Tl <= Rabs (Tl - Dd / Y) + Rabs (Dd / Y).
{ have Hsplit : Tl = (Tl - Dd / Y) + Dd / Y by ring.
  rewrite {1}Hsplit. apply Rabs_triang. }
lra.
Qed.

Local Lemma sub_T_bnd : Rabs T <= bpow radix2 (emin + fprec t - 1) + /2 * eta.
Proof.
have HT := sub_th_close.
have Ht : Rabs T <= Rabs (T - X / Y) + Rabs (X / Y).
{ have Hsplit : T = (T - X / Y) + X / Y by ring.
  rewrite {1}Hsplit. apply Rabs_triang. }
lra.
Qed.


(* ---------- Fast2Sum is exact here: T + Tl lands on the eta lattice ---------- *)

Local Lemma sub_sum_bnd : Rabs (T + Tl) <= bpow radix2 (fprec t + emin).
Proof.
have HT := sub_T_bnd. have HTl := sub_Tl_bnd.
have Ht : Rabs (T + Tl) <= Rabs T + Rabs Tl by apply Rabs_triang.
have He : 0 < eta by apply bpow_gt_0.
have Heq1 : bpow radix2 (emin + fprec t - 1) = eta * bpow radix2 (fprec t - 1)
  by (rewrite -bpow_plus; f_equal; lia).
have Heq2 : bpow radix2 (fprec t + emin) = eta * bpow radix2 (fprec t)
  by (rewrite -bpow_plus; f_equal; lia).
have Heq3 : 2 * bpow radix2 (fprec t - 1) = bpow radix2 (fprec t).
{ have H1 : bpow radix2 1 = 2 by reflexivity.
  rewrite -H1 -bpow_plus. f_equal. lia. }
have H8 : (8:R) <= bpow radix2 (fprec t - 1).
{ have -> : (8:R) = bpow radix2 3 by (simpl; lra). apply bpow_le; lia. }
rewrite Heq2 -Heq3. rewrite Heq1 in HT. nra.
Qed.

Local Lemma sub_sum_fmt : generic_format radix2 fexp (T + Tl).
Proof.
have FT : generic_format radix2 fexp T by apply generic_format_FLT_FT2R.
have FTl : generic_format radix2 fexp Tl by apply generic_format_FLT_FT2R.
apply FLT_format_plus_small; [ apply fprec_gt_0 | exact FT | exact FTl |].
exact sub_sum_bnd.
Qed.

Local Lemma sub_f2s :
  FT2R (fst (DWDivFP3 xh xl y)) + FT2R (snd (DWDivFP3 xh xl y)) = T + Tl.
Proof.
have Heqr : DWDivFP3 xh xl y
  = DDModels.Fast2Sum (BDIV xh y)
      (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                           (Fast2Mult_err (BDIV xh y) y)) xl) y)
  by rewrite /DWDivFP3 /Fast2Mult_err /Fast2Mult /Fast2Sum //=.
destruct FIN as [Ffst Fsnd].
rewrite Heqr in Ffst, Fsnd |- *.
rewrite /DDModels.Fast2Sum /fst /snd in Ffst, Fsnd |- *.
(* s = BPLUS T Tl is exact *)
have Hs : FT2R (BPLUS (BDIV xh y)
            (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                 (Fast2Mult_err (BDIV xh y) y)) xl) y)) = T + Tl.
{ rewrite -(BPLUS_round_correct t _ _ Ffst).
  apply: round_generic. exact sub_sum_fmt. }
(* z = BMINUS s T computes Tl exactly *)
have Fz : is_finite (BMINUS (BPLUS (BDIV xh y)
            (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                 (Fast2Mult_err (BDIV xh y) y)) xl) y))
            (BDIV xh y)) = true
  by exact (proj2 (BMINUS_finite_e t _ _ Fsnd)).
have Hz : FT2R (BMINUS (BPLUS (BDIV xh y)
            (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                 (Fast2Mult_err (BDIV xh y) y)) xl) y))
            (BDIV xh y)) = Tl.
{ rewrite -(BMINUS_round_correct t _ _ Fz) Hs.
  have -> : T + Tl - T = Tl by ring.
  apply: round_generic. apply generic_format_FLT_FT2R. }
(* e = BMINUS Tl z = 0 *)
have He : FT2R (BMINUS (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                            (Fast2Mult_err (BDIV xh y) y)) xl) y)
            (BMINUS (BPLUS (BDIV xh y)
               (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                    (Fast2Mult_err (BDIV xh y) y)) xl) y))
               (BDIV xh y))) = 0.
{ rewrite -(BMINUS_round_correct t _ _ Fsnd) Hz.
  have -> : Tl - Tl = 0 by ring.
  by rewrite round_0. }
rewrite Hs He. ring.
Qed.

(* ================= the subnormal quotient leg ================= *)
Local Theorem sub_main :
  Rabs (FT2R (fst (DWDivFP3 xh xl y)) + FT2R (snd (DWDivFP3 xh xl y)) - Q)
    <= 3 * u ^ 2 * Rabs Q + eta.
Proof.
have Hf2s := sub_f2s. have H := sub_Tl_Q_T.
have Heq : FT2R (fst (DWDivFP3 xh xl y)) + FT2R (snd (DWDivFP3 xh xl y)) - Q
         = Tl - (Q - T) by (rewrite Hf2s; ring).
rewrite Heq.
have Hpos : 0 <= 3 * u ^ 2 * Rabs Q.
{ apply Rmult_le_pos; [| apply Rabs_pos ].
  have Hu : 0 <= u by apply bpow_ge_0. nra. }
lra.
Qed.


(* ---------- Output validity follows from preservation of the sum ---------- *)
Local Theorem sub_double_word :
  double_word_prop (fst (DWDivFP3 xh xl y)) (snd (DWDivFP3 xh xl y)).
Proof.
have Heqr : DWDivFP3 xh xl y
  = DDModels.Fast2Sum (BDIV xh y)
      (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                           (Fast2Mult_err (BDIV xh y) y)) xl) y)
  by rewrite /DWDivFP3 /Fast2Mult_err /Fast2Mult /Fast2Sum //=.
have Hsum := sub_f2s.
rewrite Heqr in Hsum |- *.
apply Fast2Sum_double_word_of_sum; [| exact Hsum ].
rewrite -Heqr. exact FIN.
Qed.

End Sub.






Section SubFin.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin  := (@common.emin t).
Notation fexp  := (SpecFloat.fexp (fprec t) (femax t)).
Notation u     := (bpow radix2 (- fprec t)).
Notation eta   := (bpow radix2 (@common.emin t)).
Notation ulp   := (Ulp.ulp Zaux.radix2 fexp).
Notation Om    := (bpow radix2 (femax t)).

Local Instance valid_fexp_inst_fin : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.

Variables (xh xl y : ftype t).

Hypothesis Hp4   : (4 <= fprec t)%Z.
Hypothesis Hfxh  : is_finite xh = true.
Hypothesis Hfxl  : is_finite xl = true.
Hypothesis Hfy   : is_finite y  = true.
Hypothesis Hdwp  : double_word_prop xh xl.
Hypothesis Hfth  : is_finite (BDIV xh y) = true.
Hypothesis Hxhb  : Rabs (FT2R xh) <= bpow radix2 (femax t - 2).
Hypothesis Hqub  : Rabs (FT2R xh / FT2R y) <= bpow radix2 (femax t - 2).
Hypothesis Hsub  : Rabs (FT2R xh / FT2R y) < bpow radix2 (emin + fprec t - 1).
Hypothesis Hxhlb : bpow radix2 (emin + 2 * fprec t) <= Rabs (FT2R xh).

(* ---------- ambient constants ---------- *)

Local Lemma fin_Om32 : 32 <= Om.
Proof.
have -> : (32 = bpow radix2 5)%R by (simpl; lra).
apply bpow_le; pose proof (fprec_lt_femax t); pose proof (fprec_lb t); lia.
Qed.

Local Lemma fin_Om_pos : 0 < Om. Proof. apply bpow_gt_0. Qed.

Local Lemma fin_X4 : Rabs (FT2R xh) <= /4 * Om.
Proof. rewrite -(@bpow_femax_minus_two t). exact Hxhb. Qed.

Local Lemma fin_Y_lt : Rabs (FT2R y) < Om.
Proof. rewrite -B2R_float_of_ftype. apply Binary.abs_B2R_lt_emax. Qed.

Local Lemma fin_yne : FT2R y <> 0.
Proof.
intro Hb0.
have Hf := Hfth.
rewrite <- B2R_float_of_ftype in Hb0.
unfold BDIV, BINOP in Hf.
rewrite is_finite_Binary float_of_ftype_of_float in Hf.
have Hb := Hfy. rewrite is_finite_Binary in Hb.
destruct (float_of_ftype y) eqn:E; simpl in Hb; try discriminate.
- destruct (float_of_ftype xh); cbn [Binary.Bdiv] in Hf; try discriminate.
- revert Hb0. cbn [Binary.B2R]. apply F2R_neq_0. destruct s; simpl; lia.
Qed.

(* eta*|y| <= 1/2 : the subnormal case slack is an absolute constant *)
Local Lemma fin_etaY : eta * Rabs (FT2R y) <= /2.
Proof.
have HY := fin_Y_lt. have He : 0 < eta by apply bpow_gt_0.
have Hprod : eta * Om = bpow radix2 (3 - fprec t).
{ rewrite -bpow_plus. f_equal.
  change (@common.emin t) with (SpecFloat.emin (fprec t) (femax t)).
  unfold SpecFloat.emin. lia. }
have Hb : bpow radix2 (3 - fprec t) <= /2.
{ have -> : (/2:R) = bpow radix2 (-1) by (simpl; lra).
  apply bpow_le; lia. }
have Hstep : eta * Rabs (FT2R y) <= eta * Om by nra.
lra.
Qed.

(* ---------- the two workhorses ---------- *)

Local Lemma fin_half_ulp (v : R) : Rabs v < Om -> /2 * ulp v <= /16 * Om.
Proof. move => Hv. exact (@half_ulp_le t v Hp4 Hv). Qed.

Local Lemma fin_no_ovf (v : R) : Rabs v <= 3/4 * Om -> Rabs (rounded t v) < Om.
Proof.
move => Hv.
have HO := fin_Om_pos.
have Hlt : Rabs v < Om by lra.
have Hu := fin_half_ulp v Hlt.
eapply Rle_lt_trans; [ apply round_abs_le_abs_plus_half_ulp |]. lra.
Qed.

Local Lemma fin_round_abs (v : R) :
  Rabs v < Om ->
  Rabs (round radix2 fexp (Znearest choice) v) <= Rabs v + /16 * Om.
Proof.
move => Hv. have Hu := fin_half_ulp v Hv.
eapply Rle_trans; [ apply round_abs_le_abs_plus_half_ulp |]. lra.
Qed.

(* ---------- node 1: the product th*y stays within 1/4 of xh ---------- *)

Local Lemma fin_ulp_q : ulp (FT2R xh / FT2R y) = eta.
Proof.
apply ulp_FLT_small; [ apply fprec_gt_0 |].
eapply Rlt_le_trans; [ exact Hsub |]. apply bpow_le.
change (@common.emin t) with (SpecFloat.emin (fprec t) (femax t)). lia.
Qed.

Local Lemma fin_th_close :
  Rabs (FT2R (BDIV xh y) - FT2R xh / FT2R y) <= /2 * eta.
Proof.
rewrite -(BDIV_round_correct t xh y fin_yne Hfth) -fin_ulp_q.
exact (@error_le_half_ulp radix2 fexp valid_fexp_inst_fin choice
         (FT2R xh / FT2R y)).
Qed.

(* |th*y - xh| <= 1/4 *)
Local Lemma fin_A_X : Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh) <= /4.
Proof.
have HT := fin_th_close. have HeY := fin_etaY.
have Hy : 0 <= Rabs (FT2R y) by apply Rabs_pos.
have Heq : FT2R (BDIV xh y) * FT2R y - FT2R xh
         = (FT2R (BDIV xh y) - FT2R xh / FT2R y) * FT2R y
  by (field; exact fin_yne).
rewrite Heq Rabs_mult.
have Hstep : Rabs (FT2R (BDIV xh y) - FT2R xh / FT2R y) * Rabs (FT2R y)
           <= (/2 * eta) * Rabs (FT2R y)
  by (apply Rmult_le_compat_r; [ exact Hy | exact HT ]).
have Hexp : (/2 * eta) * Rabs (FT2R y) = /2 * (eta * Rabs (FT2R y)) by ring.
rewrite Hexp in Hstep. lra.
Qed.

Local Lemma fin_A_bnd : Rabs (FT2R (BDIV xh y) * FT2R y) <= /4 * Om + /4.
Proof.
have H1 := fin_A_X. have H2 := fin_X4.
have Ht : Rabs (FT2R (BDIV xh y) * FT2R y)
        <= Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh) + Rabs (FT2R xh).
{ have He : FT2R (BDIV xh y) * FT2R y
          = (FT2R (BDIV xh y) * FT2R y - FT2R xh) + FT2R xh by ring.
  rewrite {1}He. apply Rabs_triang. }
lra.
Qed.

Local Lemma fin_pih : is_finite (BMULT (BDIV xh y) y) = true.
Proof.
apply no_overflow_mult_is_finite; [ exact Hfth | exact Hfy |].
apply fin_no_ovf.
have H := fin_A_bnd. have HO := fin_Om32. lra.
Qed.

Local Lemma fin_pil : is_finite (Fast2Mult_err (BDIV xh y) y) = true.
Proof.
have H := Fast2Mult_finite_unconditional (BDIV xh y) y fin_pih.
unfold Fast2Mult_err. exact (proj2 H).
Qed.


(* ---------- |y| is large: clause 8 against the subnormal quotient ---------- *)
Local Lemma fin_y_big : bpow radix2 (fprec t + 1) < Rabs (FT2R y).
Proof.
have HY : 0 < Rabs (FT2R y) by (apply Rabs_pos_lt; exact fin_yne).
have Hsplit : Rabs (FT2R xh) = Rabs (FT2R xh / FT2R y) * Rabs (FT2R y)
  by (rewrite -Rabs_mult; f_equal; field; exact fin_yne).
have H1 : bpow radix2 (emin + 2 * fprec t)
          <= Rabs (FT2R xh / FT2R y) * Rabs (FT2R y) by (rewrite -Hsplit; exact Hxhlb).
have H2 : Rabs (FT2R xh / FT2R y) * Rabs (FT2R y)
          < bpow radix2 (emin + fprec t - 1) * Rabs (FT2R y)
  by (apply Rmult_lt_compat_r; [ exact HY | exact Hsub ]).
have Heq : bpow radix2 (emin + 2 * fprec t)
         = bpow radix2 (emin + fprec t - 1) * bpow radix2 (fprec t + 1)
  by (rewrite -bpow_plus; f_equal; lia).
have Hpos : 0 < bpow radix2 (emin + fprec t - 1) by apply bpow_gt_0.
rewrite Heq in H1.
apply (Rmult_lt_reg_l (bpow radix2 (emin + fprec t - 1))); [ exact Hpos |].
rewrite (Rmult_comm _ (bpow radix2 (fprec t + 1))) in H1. lra.
Qed.

Local Lemma fin_Y32 : 32 <= Rabs (FT2R y).
Proof.
have H := fin_y_big.
have H32 : (32:R) <= bpow radix2 (fprec t + 1).
{ have -> : (32:R) = bpow radix2 5 by (simpl; lra). apply bpow_le; lia. }
lra.
Qed.

(* ---------- node 2: dh = xh - pih ---------- *)

Local Lemma fin_pih_err :
  Rabs (FT2R (BMULT (BDIV xh y) y) - FT2R (BDIV xh y) * FT2R y) <= /16 * Om.
Proof.
have HA := fin_A_bnd. have HO := fin_Om32.
have Hlt : Rabs (FT2R (BDIV xh y) * FT2R y) < Om by lra.
have Hu := fin_half_ulp _ Hlt.
have Hpih : FT2R (BMULT (BDIV xh y) y)
          = round radix2 fexp (Znearest choice) (FT2R (BDIV xh y) * FT2R y)
  by rewrite (BMULT_round_correct t (BDIV xh y) y fin_pih).
rewrite Hpih.
eapply Rle_trans; [| exact Hu ].
exact (@error_le_half_ulp radix2 fexp valid_fexp_inst_fin choice
         (FT2R (BDIV xh y) * FT2R y)).
Qed.

Local Lemma fin_X_pih :
  Rabs (FT2R xh - FT2R (BMULT (BDIV xh y) y)) <= /4 + /16 * Om.
Proof.
have H1 := fin_A_X. have H2 := fin_pih_err.
have Ht : Rabs (FT2R xh - FT2R (BMULT (BDIV xh y) y))
        <= Rabs (FT2R xh - FT2R (BDIV xh y) * FT2R y)
           + Rabs (FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y)).
{ have He : FT2R xh - FT2R (BMULT (BDIV xh y) y)
          = (FT2R xh - FT2R (BDIV xh y) * FT2R y)
            + (FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y)) by ring.
  rewrite He. apply Rabs_triang. }
rewrite (Rabs_minus_sym (FT2R xh) (FT2R (BDIV xh y) * FT2R y)) in Ht.
rewrite (Rabs_minus_sym (FT2R (BDIV xh y) * FT2R y)
           (FT2R (BMULT (BDIV xh y) y))) in Ht.
lra.
Qed.

Local Lemma fin_dh : is_finite (BMINUS xh (BMULT (BDIV xh y) y)) = true.
Proof.
apply no_overflow_minus_is_finite; [ exact Hfxh | exact fin_pih |].
red. apply fin_no_ovf. have H := fin_X_pih. have HO := fin_Om32. lra.
Qed.

Local Lemma fin_Dh_bnd :
  Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y))) <= /4 + /8 * Om.
Proof.
have H := fin_X_pih. have HO := fin_Om32.
have Hlt : Rabs (FT2R xh - FT2R (BMULT (BDIV xh y) y)) < Om by lra.
have Hr := fin_round_abs _ Hlt.
have Hdh : FT2R (BMINUS xh (BMULT (BDIV xh y) y))
         = round radix2 fexp (Znearest choice)
             (FT2R xh - FT2R (BMULT (BDIV xh y) y))
  by rewrite (BMINUS_round_correct t xh (BMULT (BDIV xh y) y) fin_dh).
rewrite Hdh. lra.
Qed.

(* ---------- node 3: dt = dh - pil ---------- *)

Local Lemma fin_Pil_bnd :
  Rabs (FT2R (Fast2Mult_err (BDIV xh y) y)) <= /16 * Om.
Proof.
have Hacc : Rabs (FT2R (Fast2Mult_err (BDIV xh y) y))
          <= /2 * ulp (FT2R (BDIV xh y) * FT2R y)
  by exact (Fast2Mult_accuracy_from_acc_only_cond (BDIV xh y) y fin_pih).
have HA := fin_A_bnd. have HO := fin_Om32.
have Hlt : Rabs (FT2R (BDIV xh y) * FT2R y) < Om by lra.
have Hu := fin_half_ulp _ Hlt. lra.
Qed.

Local Lemma fin_dt :
  is_finite (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                    (Fast2Mult_err (BDIV xh y) y)) = true.
Proof.
apply no_overflow_minus_is_finite; [ exact fin_dh | exact fin_pil |].
red. apply fin_no_ovf.
have H1 := fin_Dh_bnd. have H2 := fin_Pil_bnd. have HO := fin_Om32.
have Ht : Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y))
                - FT2R (Fast2Mult_err (BDIV xh y) y))
        <= Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y)))
           + Rabs (FT2R (Fast2Mult_err (BDIV xh y) y)).
{ have He : FT2R (BMINUS xh (BMULT (BDIV xh y) y))
            - FT2R (Fast2Mult_err (BDIV xh y) y)
          = FT2R (BMINUS xh (BMULT (BDIV xh y) y))
            + (- FT2R (Fast2Mult_err (BDIV xh y) y)) by ring.
  rewrite He. eapply Rle_trans; [ apply Rabs_triang |].
  rewrite Rabs_Ropp. lra. }
lra.
Qed.

Local Lemma fin_Dt_bnd :
  Rabs (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                     (Fast2Mult_err (BDIV xh y) y))) <= /4 + /4 * Om.
Proof.
have H1 := fin_Dh_bnd. have H2 := fin_Pil_bnd. have HO := fin_Om32.
have Ht : Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y))
                - FT2R (Fast2Mult_err (BDIV xh y) y))
        <= Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y)))
           + Rabs (FT2R (Fast2Mult_err (BDIV xh y) y)).
{ have He : FT2R (BMINUS xh (BMULT (BDIV xh y) y))
            - FT2R (Fast2Mult_err (BDIV xh y) y)
          = FT2R (BMINUS xh (BMULT (BDIV xh y) y))
            + (- FT2R (Fast2Mult_err (BDIV xh y) y)) by ring.
  rewrite He. eapply Rle_trans; [ apply Rabs_triang |].
  rewrite Rabs_Ropp. lra. }
have Hlt : Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y))
                 - FT2R (Fast2Mult_err (BDIV xh y) y)) < Om by lra.
have Hr := fin_round_abs _ Hlt.
have Hdt : FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                        (Fast2Mult_err (BDIV xh y) y))
         = round radix2 fexp (Znearest choice)
             (FT2R (BMINUS xh (BMULT (BDIV xh y) y))
              - FT2R (Fast2Mult_err (BDIV xh y) y))
  by rewrite (BMINUS_round_correct t (BMINUS xh (BMULT (BDIV xh y) y))
                (Fast2Mult_err (BDIV xh y) y) fin_dt).
rewrite Hdt. lra.
Qed.


(* ---------- node 4: d = dt + xl ---------- *)

Local Lemma fin_L_bnd : Rabs (FT2R xl) <= /64 * Om.
Proof.
have Hrel : Rabs (FT2R xl) <= u * Rabs (FT2R xh)
  by exact (@dw_low_le_u_high t STD xh xl Hdwp).
have HX := fin_X4. have HO := fin_Om32.
have Hu : u <= /16.
{ have -> : (/16:R) = bpow radix2 (-4) by (simpl; lra). apply bpow_le; lia. }
have Hu0 : 0 <= u by apply bpow_ge_0.
have HXp : 0 <= Rabs (FT2R xh) by apply Rabs_pos.
nra.
Qed.

Local Lemma fin_d :
  is_finite (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                           (Fast2Mult_err (BDIV xh y) y)) xl) = true.
Proof.
apply no_overflow_sum_is_finite; [ exact fin_dt | exact Hfxl |].
red. apply fin_no_ovf.
have H1 := fin_Dt_bnd. have H2 := fin_L_bnd. have HO := fin_Om32.
eapply Rle_trans; [ apply Rabs_triang |]. lra.
Qed.

Local Lemma fin_Dd_bnd :
  Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                            (Fast2Mult_err (BDIV xh y) y)) xl)) <= /2 * Om.
Proof.
have H1 := fin_Dt_bnd. have H2 := fin_L_bnd. have HO := fin_Om32.
have Ht : Rabs (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                             (Fast2Mult_err (BDIV xh y) y)) + FT2R xl)
        <= /4 + /4 * Om + /64 * Om
  by (eapply Rle_trans; [ apply Rabs_triang |]; lra).
have Hlt : Rabs (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                              (Fast2Mult_err (BDIV xh y) y)) + FT2R xl) < Om
  by lra.
have Hr := fin_round_abs _ Hlt.
have Hd : FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                              (Fast2Mult_err (BDIV xh y) y)) xl)
        = round radix2 fexp (Znearest choice)
            (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                          (Fast2Mult_err (BDIV xh y) y)) + FT2R xl)
  by rewrite (BPLUS_round_correct t (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                (Fast2Mult_err (BDIV xh y) y)) xl fin_d).
rewrite Hd. lra.
Qed.

(* ---------- node 5: tl = d / y ---------- *)

Local Lemma fin_div_bnd (v : R) :
  32 <= Rabs (FT2R y) -> Rabs (v / FT2R y) <= /32 * Rabs v.
Proof.
move => HY.
have HYp : 0 < Rabs (FT2R y) by lra.
have Hv : 0 <= Rabs v by apply Rabs_pos.
rewrite /Rdiv Rabs_mult Rabs_inv.
have Hinv : / Rabs (FT2R y) <= /32 by (apply Rinv_le_contravar; lra).
nra.
Qed.

Local Lemma fin_tl :
  is_finite (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                 (Fast2Mult_err (BDIV xh y) y)) xl) y) = true.
Proof.
apply no_overflow_div_is_finite; [ exact fin_d | exact fin_yne |].
apply fin_no_ovf.
have H := fin_Dd_bnd. have HO := fin_Om32.
have Hdiv : Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                     (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
          <= /32 * Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                     (Fast2Mult_err (BDIV xh y) y)) xl))
  by (apply fin_div_bnd; exact fin_Y32).
eapply Rle_trans; [ exact Hdiv |]. lra.
Qed.

Local Lemma fin_Tl_bnd :
  Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                  (Fast2Mult_err (BDIV xh y) y)) xl) y))
    <= /8 * Om.
Proof.
have H := fin_Dd_bnd. have HO := fin_Om32.
have Hdiv : Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                     (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
          <= /32 * Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                     (Fast2Mult_err (BDIV xh y) y)) xl))
  by (apply fin_div_bnd; exact fin_Y32).
have Hlt : Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                     (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y) < Om by lra.
have Hr := fin_round_abs _ Hlt.
have Htl : FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                              (Fast2Mult_err (BDIV xh y) y)) xl) y)
         = round radix2 fexp (Znearest choice)
             (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                           (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
  by rewrite (BDIV_round_correct t _ y fin_yne fin_tl).
rewrite Htl. lra.
Qed.

(* ---------- node 6: the leading node is tiny ---------- *)

Local Lemma fin_eta_small : eta <= /64.
Proof.
have H := fin_etaY. have HY := fin_Y32. have He : 0 < eta by apply bpow_gt_0.
nra.
Qed.

Local Lemma fin_T_bnd : Rabs (FT2R (BDIV xh y)) <= 2.
Proof.
have HT := fin_th_close. have He := fin_eta_small.
have Hq : Rabs (FT2R xh / FT2R y) <= 1.
{ have Hb : bpow radix2 (emin + fprec t - 1) <= 1.
  { have -> : (1:R) = bpow radix2 0 by reflexivity.
    apply bpow_le.
    change (@common.emin t) with (SpecFloat.emin (fprec t) (femax t)).
    unfold SpecFloat.emin. pose proof (femax_lb t). lia. }
  lra. }
have Ht : Rabs (FT2R (BDIV xh y))
        <= Rabs (FT2R (BDIV xh y) - FT2R xh / FT2R y) + Rabs (FT2R xh / FT2R y).
{ have He2 : FT2R (BDIV xh y)
           = (FT2R (BDIV xh y) - FT2R xh / FT2R y) + FT2R xh / FT2R y by ring.
  rewrite {1}He2. apply Rabs_triang. }
lra.
Qed.

(* ---------- nodes 7,8: the closing Fast2Sum ---------- *)

Local Lemma fin_fst_aux :
  is_finite (BPLUS (BDIV xh y)
    (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                         (Fast2Mult_err (BDIV xh y) y)) xl) y)) = true.
Proof.
apply no_overflow_sum_is_finite; [ exact Hfth | exact fin_tl |].
red. apply fin_no_ovf.
have H1 := fin_T_bnd. have H2 := fin_Tl_bnd. have HO := fin_Om32.
eapply Rle_trans; [ apply Rabs_triang |]. lra.
Qed.

Local Lemma fin_S_bnd :
  Rabs (FT2R (BPLUS (BDIV xh y)
    (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                         (Fast2Mult_err (BDIV xh y) y)) xl) y))) <= /4 * Om.
Proof.
have H1 := fin_T_bnd. have H2 := fin_Tl_bnd. have HO := fin_Om32.
have Ht : Rabs (FT2R (BDIV xh y)
          + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                       (Fast2Mult_err (BDIV xh y) y)) xl) y)) <= 2 + /8 * Om
  by (eapply Rle_trans; [ apply Rabs_triang |]; lra).
have Hlt : Rabs (FT2R (BDIV xh y)
          + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                       (Fast2Mult_err (BDIV xh y) y)) xl) y)) < Om by lra.
have Hr := fin_round_abs _ Hlt.
have Hs : FT2R (BPLUS (BDIV xh y)
            (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                          (Fast2Mult_err (BDIV xh y) y)) xl) y))
        = round radix2 fexp (Znearest choice)
            (FT2R (BDIV xh y)
             + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                           (Fast2Mult_err (BDIV xh y) y)) xl) y))
  by rewrite (BPLUS_round_correct t _ _ fin_fst_aux).
rewrite Hs. lra.
Qed.

Local Lemma fin_z :
  is_finite (BMINUS (BPLUS (BDIV xh y)
    (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                         (Fast2Mult_err (BDIV xh y) y)) xl) y)) (BDIV xh y))
  = true.
Proof.
apply no_overflow_minus_is_finite; [ exact fin_fst_aux | exact Hfth |].
red. apply fin_no_ovf.
have H1 := fin_S_bnd. have H2 := fin_T_bnd. have HO := fin_Om32.
eapply Rle_trans; [unfold Rminus; apply Rabs_triang |].
rewrite Rabs_Ropp. lra.
Qed.

Local Lemma fin_Z_bnd :
  Rabs (FT2R (BMINUS (BPLUS (BDIV xh y)
    (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                         (Fast2Mult_err (BDIV xh y) y)) xl) y)) (BDIV xh y)))
    <= /2 * Om.
Proof.
have H1 := fin_S_bnd. have H2 := fin_T_bnd. have HO := fin_Om32.
have Ht : Rabs (FT2R (BPLUS (BDIV xh y)
            (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                          (Fast2Mult_err (BDIV xh y) y)) xl) y))
          - FT2R (BDIV xh y)) <= /4 * Om + 2
  by (eapply Rle_trans;
      [unfold Rminus; apply Rabs_triang |];
      rewrite Rabs_Ropp; lra).
have Hlt : Rabs (FT2R (BPLUS (BDIV xh y)
            (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                          (Fast2Mult_err (BDIV xh y) y)) xl) y))
          - FT2R (BDIV xh y)) < Om by lra.
have Hr := fin_round_abs _ Hlt.
have Hz : FT2R (BMINUS (BPLUS (BDIV xh y)
            (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                          (Fast2Mult_err (BDIV xh y) y)) xl) y)) (BDIV xh y))
        = round radix2 fexp (Znearest choice)
            (FT2R (BPLUS (BDIV xh y)
              (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                            (Fast2Mult_err (BDIV xh y) y)) xl) y))
             - FT2R (BDIV xh y))
  by rewrite (BMINUS_round_correct t _ _ fin_z).
rewrite Hz. lra.
Qed.

Local Lemma fin_snd_aux :
  is_finite (BMINUS
    (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                         (Fast2Mult_err (BDIV xh y) y)) xl) y)
    (BMINUS (BPLUS (BDIV xh y)
      (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                           (Fast2Mult_err (BDIV xh y) y)) xl) y)) (BDIV xh y)))
  = true.
Proof.
apply no_overflow_minus_is_finite; [ exact fin_tl | exact fin_z |].
red. apply fin_no_ovf.
have H1 := fin_Tl_bnd. have H2 := fin_Z_bnd. have HO := fin_Om32.
eapply Rle_trans; [unfold Rminus; apply Rabs_triang |].
rewrite Rabs_Ropp. lra.
Qed.

(* ================= finiteness in the subnormal branch ================= *)
Local Theorem fin_main : is_finite_p (DWDivFP3 xh xl y).
Proof.
have Heqr : DWDivFP3 xh xl y
  = DDModels.Fast2Sum (BDIV xh y)
      (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                           (Fast2Mult_err (BDIV xh y) y)) xl) y)
  by rewrite /DWDivFP3 /Fast2Mult_err /Fast2Mult /Fast2Sum //=.
rewrite Heqr. split.
- exact fin_fst_aux.
- exact fin_snd_aux.
Qed.

End SubFin.

(** The subnormal proof leg exposed to the public mixed interface file.  Its
    internal error and validity proofs remain private to this file. *)
Theorem DWDivFP3_subnormal_accuracy_and_double_word
    {NANS : Nans} {t : type} {STD : is_standard t}
    (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  is_finite_p (DWDivFP3 xh xl y) ->
  FT2R y <> 0 ->
  double_word_prop xh xl ->
  bpow radix2 (@common.emin t + 2 * fprec t) <= Rabs (FT2R xh) ->
  Rabs (FT2R xh / FT2R y) <
    bpow radix2 (@common.emin t + fprec t - 1) ->
  Rabs (FT2R (fst (DWDivFP3 xh xl y)) + FT2R (snd (DWDivFP3 xh xl y))
        - (FT2R xh + FT2R xl) / FT2R y)
    <= 3 * bpow radix2 (-fprec t) ^ 2 *
         Rabs ((FT2R xh + FT2R xl) / FT2R y) +
       bpow radix2 (@common.emin t) /\
  double_word_prop (fst (DWDivFP3 xh xl y))
                   (snd (DWDivFP3 xh xl y)).
Proof.
intros Hp4 FIN Hyne Hdwp Hxhlb Hsub. split.
- exact (sub_main xh xl y Hp4 FIN Hyne Hdwp Hxhlb Hsub).
- exact (sub_double_word xh xl y Hp4 FIN Hyne Hdwp Hxhlb Hsub).
Qed.



(* Safe input subnormal bridge.  The whole range public ladder is in
   DWDivFP_mixed_acc.v. *)
Section CondMin.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (@common.emin t).
Notation u    := (bpow radix2 (- fprec t)).

(* ============ the subnormal quotient leg, discharged from the cond ============
   All three deliverables at once: the mixed bound, output validity, and
   finiteness of the computed pair.  Section SubFin supplies the finiteness,
   Section Sub proves accuracy and output validity. *)
Theorem DWDivFP3_subnormal_leg (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_mixed_safe_input_cond xh xl y ->
  Rabs (FT2R xh / FT2R y) < bpow radix2 (emin + fprec t - 1) ->
  Rabs (FT2R (fst (DWDivFP3 xh xl y)) + FT2R (snd (DWDivFP3 xh xl y))
        - (FT2R xh + FT2R xl) / FT2R y)
    <= 3 * u ^ 2 * Rabs ((FT2R xh + FT2R xl) / FT2R y) + bpow radix2 emin
  /\ double_word_prop (fst (DWDivFP3 xh xl y)) (snd (DWDivFP3 xh xl y))
  /\ is_finite_p (DWDivFP3 xh xl y).
Proof.
intros Hp4 (Hfxh & Hfxl & Hfy & Hdwp & Hfth & Hxhb & Hqub & Hxhlb) Hsub.
have Hyne : FT2R y <> 0 by
  exact (DWDivFP_denom_nonzero_from_finite xh y Hfy Hfth).
have FIN : is_finite_p (DWDivFP3 xh xl y) by (apply fin_main; assumption).
have [Hacc Hdw] := DWDivFP3_subnormal_accuracy_and_double_word
  xh xl y Hp4 FIN Hyne Hdwp Hxhlb Hsub.
exact (conj Hacc (conj Hdw FIN)).
Qed.

End CondMin.
