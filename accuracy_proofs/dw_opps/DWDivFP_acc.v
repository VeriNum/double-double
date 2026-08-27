(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Accuracy proof for double-word divided by a floating-point number
    (Algorithm 15, DWDivFP3).  Mirrors the two-layer structure of
    DWMulFP_acc.v: an FLX->FLT bridge collapsing every rounded node of the
    FLT runtime model [DDModels.DWDivFP3] onto the paper's real-valued FLX
    model [DWDivFP.DWDivFP3], then the Layer-1 relative-error theorem obtained
    from the paper's tight 3u^2 bound (DWDivFP.DWDFP3_correct), and finally the
    Layer-2 condition-level tiers.

    Notation: u = 2^(-p) is the relative rounding unit and eta = 2^emin is the
    smallest positive subnormal, the physical underflow floor.  ADMIT-FREE.

    ============================================================================
    PUBLIC INTERFACE

      There are exactly two accuracy tiers, and neither is obtained from the
      other by absorbing eta.

      (1) NORMAL-RANGE PURE RELATIVE, this file:

        DWDivFP_relative_accuracy    relerr <= 3u^2
                                     from DDConds.DWDivFP_relative_error_input_cond

      That cond is the whole-range safe-input condition plus
      DDConds.DWDivFP_normal, which says the leading quotient is normal and the
      closing correction is either exactly zero or has a normal quotient.  In
      that regime DWDivFP3 agrees with the paper's FLX model node for node, so
      the paper's constant transfers with nothing added.  The exact-division
      disjunct keeps exact quotients inside the tier.

        relative_errorDWDivFP3_correct   the FLX-bridged Layer-1 core, stated
                                         directly from per-node normal-range
                                         premises

      (2) WHOLE-RANGE MIXED, this file's normal-leading-quotient half plus
          DWDivFP_subnormal.v's subnormal half:

        DWDivFP3_error_mixed_acc     |Qhat - Q| <= 3u^2|Q| + eta
                                     from DWDivFP_normal_quotient_input_cond
        DWDivFP3_is_DW_from_cond_acc     output is a double word
        DWDivFP3_{fst,snd}_finite_acc    finiteness of the computed pair

      The runtime guard dw_div_fp_check discharges the canonical whole-range
      DWDivFP_mixed_safe_input_cond; the API on that cond
      (DWDivFP_mixed_accuracy_from_safe_input_cond,
      DWDivFP_double_word_from_safe_input_cond,
      DWDivFP_mixed_guarantee_from_safe_input_cond) lives in
      DWDivFP_subnormal.v and case-splits into this file's normal-quotient half
      and the subnormal-leading-quotient proof.

    Sharing between the tiers.  The two tiers meet at
    DWDivFP3_error_underflow_perturbation, which bounds the error by
    3u^2|Q| plus the SYMBOLIC divergence of the single node tl = round(d/y)
    from its FLX counterpart.  The mixed tier charges that divergence at one
    floor ulp (DWDivFP3_tl_perturbation_le_eta); the exact-division case of the
    relative tier observes it is identically zero
    (DWDivFP3_error_exact_division).
    ============================================================================ *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common FLT_helpers.
Require Import DWTimesFP DWDivFP DDConds DWord_defs Fast2Mult_acc TwoSum_acc Fast2Sum_acc.
Require Import DWPlusFP_acc_helpers DWMulFP_acc DW_acc_lemmas.
From Flocq Require Import Pff2Flocq Core.
From Flocq Require Import Mult_error FLT Div_sqrt_error Plus_error.
From Flocq Require Relative Sterbenz.

Require Import mathcomp.ssreflect.ssreflect.
From Stdlib Require Import Logic.FunctionalExtensionality.

Set Bullet Behavior "Strict Subproofs".

(* ============================================================
   Abstract real-arithmetic lemmas for the finiteness cascade.

   [nra]/[lra] cannot parse [Rabs], so instead of massaging goals that mention
   it, the affine bookkeeping of the finiteness proof is stated here over plain
   real variables:  X stands for |xh|, W for |xh|*2^-p, E for 2^emin, Om for the
   overflow threshold 2^femax.  Each node's magnitude is bounded by an affine
   form  c0*X + c1*W + c2*E, and these lemmas are the once-and-for-all algebra,
   applied pointwise below with X,W,E,Om instantiated to the concrete terms. *)

(* One rounding step (via round_ub_emin): if |z| <= K*W + M*E then the rounded
   node |round z| <= |z| + |z|*u + E/2 is at most (K+1)*W + (M+1)*E, provided
   u <= 1/16 and the coefficients stay in the used range. *)
Lemma abst_round_step (W u E B R0 K M : R) :
  0 <= u -> u <= /16 -> 0 <= E -> 0 <= B -> 0 <= W ->
  0 <= K -> K <= 16 -> 0 <= M -> M <= 8 ->
  B <= K*W + M*E ->
  R0 <= B + B*u + /2*E ->
  R0 <= (K+1)*W + (M+1)*E.
Proof. intros; nra. Qed.

(* Product-error node (via round_err_emin): |pih - th*y| <= |th*y|*u + E/2 with
   |th*y| <= X + X*u yields the 2*W + E bound (W = X*u). *)
Lemma abst_pih_err (X u E B R0 : R) :
  0 <= X -> 0 <= u -> u <= /16 -> 0 <= E -> 0 <= B ->
  B <= X + X*u ->
  R0 <= B*u + /2*E ->
  R0 <= X*u*2 + E.
Proof.
intros HX Hu Hu16 HE HB Hthy Hr.
assert (Hxu : 0 <= X*u) by (apply Rmult_le_pos; assumption).
assert (HBu : B*u <= X*u + X*u).
{ apply Rle_trans with ((X + X*u)*u).
  - apply Rmult_le_compat_r; [exact Hu | exact Hthy].
  - replace ((X + X*u)*u) with (X*u + X*u*u) by ring.
    apply Rplus_le_compat_l.
    rewrite -{2}(Rmult_1_r (X*u)); apply Rmult_le_compat_l; [exact Hxu | lra]. }
lra.
Qed.

(* |xl| <= 1/2 ulp(xh) <= 1/2 (X*(2u) + E) = W + E/2 <= W + E. *)
Lemma abst_xl (X u E V UL : R) :
  0 <= E -> V <= /2*UL -> UL <= X*(2*u) + E -> V <= X*u + E.
Proof. intros; nra. Qed.

(* A node in canonical affine form c0*X + c1*W + c2*E stays below Omega. *)
Lemma abst_lt_Om (V Om X W E c0 c1 c2 : R) :
  0 <= c0 -> c0 <= 1 -> 0 <= c1 -> c1 <= 10 -> 0 <= c2 -> c2 <= 7 ->
  32 <= Om -> X <= /4*Om -> W <= /64*Om -> E <= 1 -> 0 <= X -> 0 <= W -> 0 <= E ->
  V <= c0*X + c1*W + c2*E ->
  V < Om.
Proof. intros; nra. Qed.

(* Finiteness closing: |round v| <= |v| + 1/2 ulp v, with |v| affine and
   1/2 ulp v <= Om/16, stays below the overflow threshold Om. *)
Lemma abst_fin (RV UV Om X W E c0 c1 c2 : R) :
  0 <= c0 -> c0 <= 1 -> 0 <= c1 -> c1 <= 10 -> 0 <= c2 -> c2 <= 7 ->
  32 <= Om -> X <= /4*Om -> W <= /64*Om -> E <= 1 -> 0 <= X -> 0 <= W -> 0 <= E ->
  RV <= c0*X + c1*W + c2*E ->
  UV <= /16*Om ->
  RV + UV < Om.
Proof. intros; nra. Qed.

(* The two arithmetic facts for the |d/y| residual bound. *)
Lemma abst_H1 (L Om Y u : R) :
  0 <= Om -> 0 <= Y -> 0 <= u -> u <= /16 ->
  L <= (/4*Om*Y)*u*10 ->
  L <= 5/32*Om*Y.
Proof.
intros HOm HY Hu Hu16 HL.
apply Rle_trans with ((/4*Om*Y)*u*10); [exact HL|].
assert (HP : 0 <= /4*Om*Y) by (repeat apply Rmult_le_pos; lra).
apply Rle_trans with ((/4*Om*Y)*(/16)*10).
- apply Rmult_le_compat_r; [lra|].
  apply Rmult_le_compat_l; [exact HP | exact Hu16].
- apply Req_le; field.
Qed.

Lemma abst_dy_lt (V Om : R) : 32 <= Om -> V <= 5/32*Om + 7 -> V < Om.
Proof. intros; lra. Qed.

Lemma abst_fin_dy (RV UV Om : R) :
  32 <= Om -> RV <= 5/32*Om + 7 -> UV <= /16*Om -> RV + UV < Om.
Proof. intros; lra. Qed.

(* Closing Fast2Sum node: |th| and |tl| are each round_ub_emin bounds of the two
   quotients (Q1 = |xh/y| <= Om/4, Q2 = |d/y| <= 5/32 Om + 7), so |th + tl| (and
   the rounded sum, adding 1/2 ulp <= Om/16) stays below the overflow threshold. *)
Lemma abst_fst_sum (S Q1 Q2 Om u E : R) :
  0 <= u -> u <= /16 -> 0 <= E -> E <= 1 -> 32 <= Om ->
  0 <= Q1 -> Q1 <= /4*Om -> 0 <= Q2 -> Q2 <= 5/32*Om + 7 ->
  S <= (Q1 + Q1*u + /2*E) + (Q2 + Q2*u + /2*E) ->
  S < Om.
Proof. intros; nra. Qed.

Lemma abst_fst_fin (S UV Q1 Q2 Om u E : R) :
  0 <= u -> u <= /16 -> 0 <= E -> E <= 1 -> 32 <= Om ->
  0 <= Q1 -> Q1 <= /4*Om -> 0 <= Q2 -> Q2 <= 5/32*Om + 7 ->
  S <= (Q1 + Q1*u + /2*E) + (Q2 + Q2*u + /2*E) ->
  UV <= /16*Om ->
  S + UV < Om.
Proof. intros; nra. Qed.

(* |th| <= Om/2: th = round(xh/y), |xh/y| <= Om/4. *)
Lemma abst_th_half (X u E Om : R) :
  0<=X -> X<=/4*Om -> 0<=u -> u<=/16 -> 0<=E -> E<=1 -> 32<=Om ->
  X + X*u + /2*E <= /2*Om.
Proof.
intros. assert (X*u <= /4*Om*/16)
  by (apply Rle_trans with (/4*Om*u);
      [apply Rmult_le_compat_r|apply Rmult_le_compat_l]; nra). nra.
Qed.

(* |tl| <= Om/2: tl = round(d/y), |d/y| <= 5/32 Om + 7. *)
Lemma abst_tl_half (Q u E Om : R) :
  0<=Q -> Q<=5/32*Om+7 -> 0<=u -> u<=/16 -> 0<=E -> E<=1 -> 32<=Om ->
  Q + Q*u + /2*E <= /2*Om.
Proof.
intros. assert (Q*u <= (5/32*Om+7)*/16)
  by (apply Rle_trans with ((5/32*Om+7)*u);
      [apply Rmult_le_compat_r|apply Rmult_le_compat_l]; nra). nra.
Qed.

(* Closing Fast2Sum-error nodes stay below Omega (all residual ulps <= Om/16). *)
Lemma abst_z (D U1 U2 Tl Om : R) :
  32<=Om -> U1<=/16*Om -> Tl<=/2*Om -> U2<=/16*Om -> D <= U1+Tl -> D+U2 < Om.
Proof. intros; lra. Qed.

Lemma abst_snd (D U1 U2 U3 Om : R) :
  32<=Om -> U1<=/16*Om -> U2<=/16*Om -> U3<=/16*Om -> D <= U1+U2 -> D+U3 < Om.
Proof. intros; lra. Qed.

(* Closeness of the product node to xh: 2u + u^2 <= 1/2 for u <= 1/16. *)
Lemma abst_pih_close (X u : R) :
  0 <= X -> 0 <= u -> u <= /16 -> u * (X + u * X) + u * X <= /2 * X.
Proof.
intros HX Hu Hu16.
assert (HuX : 0 <= u * X) by (apply Rmult_le_pos; assumption).
assert (H1 : u * X <= /16 * X) by (apply Rmult_le_compat_r; [ exact HX | exact Hu16 ]).
assert (H2 : u * (u * X) <= /16 * (u * X)) by (apply Rmult_le_compat_r; [ exact HuX | exact Hu16 ]).
nra.
Qed.

(* Reverse-triangle rearrangement and the product lower-bound arithmetic used by
   cond_UF_prod (stated over plain reals so lra applies cleanly). *)
Lemma abst_revtri (A B C : R) : A - B <= C -> A - C <= B.
Proof. lra. Qed.

Lemma abst_prod_lb (P R X B2 : R) :
  R <= X * / 2 -> X - R <= P -> B2 <= X -> / 2 * B2 <= P.
Proof. lra. Qed.

(* triangle + ulp bookkeeping for the tl single-node underflow perturbation *)
Lemma abst_diff_ulp (A B UF UX : R) :
  A <= / 2 * UF -> B <= / 2 * UX -> UX <= UF -> A + B <= UF.
Proof. lra. Qed.

(* Keep the paper's two-product folded; proofs expose it via DWTimesFP.TwoProdE. *)
Opaque DWTimesFP.TwoProd.
Arguments DWTimesFP.TwoProd : simpl never.

(* NOTE: the paper's DWDFP3_correct (Algo15) no longer carries an abstract
   two-product hypothesis (see paper_proofs/DWDivFP.v), so it is instantiated at
   the concrete operator with only (p, choice, ZNE, Hp4, ...) — no F2Mult
   discharge lemma is needed here. *)

Section CorrectDWDivFP.
  Context {NANS: Nans} {t : type} {STD: is_standard t}.

  Variables (xh xl y : ftype t).

  Hypothesis FIN : is_finite_p (DWDivFP3 xh xl y).

  Ltac prove_finite :=
    move: FIN;
    rewrite /DWDivFP3/is_finite_p //=;
    move => [] //=;
    subexpr_finite => //
  .

  (* th = BDIV xh y, pih = BMULT th y, pil = Fast2Mult_err th y,
     dh = BMINUS xh pih, dt = BMINUS dh pil, d = BPLUS dt xl, tl = BDIV d y. *)
  Let th  := BDIV xh y.
  Let pih := fst (Fast2Mult th y).
  Let pil := snd (Fast2Mult th y).
  Let dh  := BMINUS xh pih.
  Let dt  := BMINUS dh pil.
  Let d   := BPLUS dt xl.

  Fact FINth : is_finite th = true.
  Proof. prove_finite. Qed.

  Fact FINxh : is_finite xh = true.
  Proof. prove_finite. Qed.

  Fact FINpih : is_finite (BMULT th y) = true.
  Proof. prove_finite. Qed.

  Fact FINtl : is_finite (BDIV d y) = true.
  Proof. prove_finite. Qed.

End CorrectDWDivFP.

(* ============================================================
   FLX -> FLT bridge for DWDivFP3.

   Collapses every rounded node of the FLT runtime model
   [DDModels.DWDivFP3] onto the paper's real-valued FLX model
   [DWDivFP.DWDivFP3], under a declarative strong-underflow discipline: each
   rounded node carries a lower bound placing it in the normal range so that
   round_FLT agrees with round_FLX (round_FLT_FLX), and the closing Fast2Sum
   is handled by FastTwoSumEq_FLT.  The two exact subtractions (dh = xh - pih,
   dt = dh - pil) become round-identities in FLT via the FLX-format facts from
   the paper (xhmpih_exact) lifted to FLT.
   ============================================================ *)
Section BridgeDWDivFP.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (common.emin (t:=t)).
Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Notation rnd_p := (round radix2 (FLX_exp (fprec t)) (Znearest choice)).

Variables (xh xl y : ftype t).

Hypothesis FIN : is_finite_p (DWDivFP3 xh xl y).
Hypothesis Hp4 : (4 <= fprec t)%Z.
Hypothesis Hyne : FT2R y <> 0.

(* th = BDIV xh y ; d = BPLUS (BMINUS (BMINUS xh (BMULT th y)) (Fast2Mult_err th y)) xl *)
Notation th := (BDIV xh y).
Notation pih := (BMULT th y).
Notation pil := (Fast2Mult_err th y).
Notation dh := (BMINUS xh pih).
Notation dt := (BMINUS dh pil).
Notation d  := (BPLUS dt xl).

(* per-node normal-range hypotheses (strong-underflow discipline) *)
Hypothesis UF_th   : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xh / FT2R y).
Hypothesis UF_prod : bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R th * FT2R y).
(* UF_dh eliminated: dh = xh - pih is exact by Sterbenz (bridge_dh), unconditionally. *)
(* UF_dt eliminated: dt = dh - pil is exact by a magnitude case split (bridge_dt),
   unconditionally -- large residual lifts FLX->FLT, small residual is exact by
   Hauser's FLT_format_plus_small. *)
Hypothesis UF_tl   : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R d / FT2R y).

(* Node (A), proven standalone to validate the round_FLT_FLX + BDIV_round_correct
   collapse pattern used throughout the bridge. *)
Lemma bridge_th :
  round radix2 (FLX_exp (fprec t)) (Znearest choice) (FT2R xh / FT2R y)
    = FT2R (BDIV xh y).
Proof.
rewrite -(BDIV_round_correct t xh y Hyne (FINth xh xl y FIN)).
by rewrite round_FLT_FLX //; exact UF_th.
Qed.

(* FLX-format facts for the two floating-point operands. *)
Lemma Fxh_flx : generic_format radix2 (FLX_exp (fprec t)) (FT2R xh).
Proof.
apply (generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t)).
apply generic_format_FLT_FT2R.
Qed.

Lemma Fy_flx : generic_format radix2 (FLX_exp (fprec t)) (FT2R y).
Proof.
apply (generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t)).
apply generic_format_FLT_FT2R.
Qed.

Lemma Fbdiv_flx : generic_format radix2 (FLX_exp (fprec t)) (FT2R (BDIV xh y)).
Proof.
apply (generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t)).
apply generic_format_FLT_FT2R.
Qed.

(* Finiteness of the BPLUS/BMINUS intermediates, chained from FINtl. *)
Lemma FIN_d :
  is_finite (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                           (Fast2Mult_err (BDIV xh y) y)) xl) = true.
Proof. exact (BDIV_finite_e t _ y (FINtl xh xl y FIN)). Qed.

Lemma FIN_dt :
  is_finite (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                    (Fast2Mult_err (BDIV xh y) y)) = true.
Proof. exact (proj1 (BPLUS_finite_e t _ xl FIN_d)). Qed.

Lemma FIN_dh : is_finite (BMINUS xh (BMULT (BDIV xh y) y)) = true.
Proof. exact (proj1 (BMINUS_finite_e t _ _ FIN_dt)). Qed.

(* Node (B): the FLX two-product equals the runtime Fast2Mult (product bridge).
   Uses the WEAK variant (Fast2Mult_correct_weak) at the minimal TwoProd-exactness
   threshold emin+2p-1, not the strong emin+3p (the latter is an artifact of Pff's
   format_dq).  This lets cond_UF_prod be discharged from a |xh| lower bound of only
   bpow(emin+2p). *)
Lemma bridge_prod :
  DWTimesFP.Fast2Mult (fprec t) choice (FT2R (BDIV xh y)) (FT2R y)
    = F2Rp (Fast2Mult (BDIV xh y) y).
Proof.
exact (DWMulFP_acc.Fast2Mult_correct_weak (BDIV xh y) y (FINpih xh xl y FIN)
         (fun _ => UF_prod)).
Qed.

Lemma bridge_pih :
  round radix2 (FLX_exp (fprec t)) (Znearest choice) (FT2R (BDIV xh y) * FT2R y)
    = FT2R (BMULT (BDIV xh y) y).
Proof.
have H := f_equal (@fst R R) bridge_prod.
rewrite /DWTimesFP.Fast2Mult /F2Rp /Fast2Mult /= in H. exact H.
Qed.

Lemma bridge_pil :
  round radix2 (FLX_exp (fprec t)) (Znearest choice)
    (FT2R (BDIV xh y) * FT2R y
     - round radix2 (FLX_exp (fprec t)) (Znearest choice) (FT2R (BDIV xh y) * FT2R y))
    = FT2R (Fast2Mult_err (BDIV xh y) y).
Proof.
have H := f_equal (@snd R R) bridge_prod.
rewrite /DWTimesFP.Fast2Mult /F2Rp /= in H. exact H.
Qed.

(* Product exactness: pih + pil = th*y  (Dekker / mult_error_FLX). *)
Lemma prodExact :
  FT2R (BMULT (BDIV xh y) y) + FT2R (Fast2Mult_err (BDIV xh y) y)
    = FT2R (BDIV xh y) * FT2R y.
Proof.
rewrite -bridge_pih -bridge_pil.
have Hg : generic_format radix2 (FLX_exp (fprec t))
   (FT2R (BDIV xh y) * FT2R y
    - round radix2 (FLX_exp (fprec t)) (Znearest choice) (FT2R (BDIV xh y) * FT2R y)).
{ rewrite -Ropp_minus_distr; apply: generic_format_opp.
  apply: (mult_error_FLX radix2 (fprec t) (Znearest choice)
           (FT2R (BDIV xh y)) (FT2R y)); [ exact Fbdiv_flx | exact Fy_flx ]. }
rewrite (round_generic radix2 (FLX_exp (fprec t)) (Znearest choice) _ Hg); ring.
Qed.

(* pih = round(th*y) lies within a factor 2 of xh, so the FLT subtraction
   xh - pih is exact by Sterbenz -- no normal-range hypothesis needed. *)
Lemma pih_close_xh :
  Rabs (FT2R (BMULT (BDIV xh y) y) - FT2R xh) <= / 2 * Rabs (FT2R xh).
Proof.
set u := bpow radix2 (- fprec t).
have upos : 0 <= u by apply bpow_ge_0.
have Hu16 : u <= /16.
{ rewrite /u. have -> : (/ 16 = bpow radix2 (-4))%R by (simpl; lra).
  apply bpow_le; lia. }
have Hxpos : 0 <= Rabs (FT2R xh) by apply Rabs_pos.
have Hyabs : 0 <= Rabs (FT2R y) by apply Rabs_pos.
have Hth  : FT2R (BDIV xh y) = rnd_p (FT2R xh / FT2R y) by rewrite bridge_th.
have Hpih : FT2R (BMULT (BDIV xh y) y) = rnd_p (FT2R (BDIV xh y) * FT2R y)
  by rewrite bridge_pih.
have Hxhy : FT2R xh / FT2R y * FT2R y = FT2R xh by (field; exact Hyne).
have Heq2u : (/2 * bpow radix2 (- fprec t + 1) = u)%R.
{ rewrite /u. have -> : (- fprec t + 1 = 1 + - fprec t)%Z by lia.
  rewrite bpow_plus. have -> : bpow radix2 1 = 2%R by reflexivity. lra. }
(* |th*y - xh| <= u * |xh| *)
have Hrel1 : Rabs (rnd_p (FT2R xh / FT2R y) - FT2R xh / FT2R y)
             <= /2 * bpow radix2 (- fprec t + 1) * Rabs (FT2R xh / FT2R y)
  by apply: Relative.relative_error_N_FLX; lia.
rewrite Heq2u -Hth in Hrel1.
have HthyX : Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh) <= u * Rabs (FT2R xh).
{ have Hid : FT2R (BDIV xh y) * FT2R y - FT2R xh
            = (FT2R (BDIV xh y) - FT2R xh / FT2R y) * FT2R y
    by (field; exact Hyne).
  rewrite Hid Rabs_mult.
  apply Rle_trans with (u * Rabs (FT2R xh / FT2R y) * Rabs (FT2R y)).
  { apply Rmult_le_compat_r; [exact Hyabs | exact Hrel1]. }
  rewrite Rmult_assoc -Rabs_mult Hxhy. apply Req_le; ring. }
(* |th*y| <= |xh| + u*|xh| *)
have HthyBnd : Rabs (FT2R (BDIV xh y) * FT2R y) <= Rabs (FT2R xh) + u * Rabs (FT2R xh).
{ apply Rle_trans with (Rabs (FT2R xh) + Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh)).
  - rewrite Rplus_comm. apply Rcomplements.Rle_minus_l.
    exact (Rabs_triang_inv (FT2R (BDIV xh y) * FT2R y) (FT2R xh)).
  - apply Rplus_le_compat_l. exact HthyX. }
(* |pih - th*y| <= u*(|xh| + u*|xh|) *)
have Hrel2 : Rabs (rnd_p (FT2R (BDIV xh y) * FT2R y) - FT2R (BDIV xh y) * FT2R y)
             <= /2 * bpow radix2 (- fprec t + 1) * Rabs (FT2R (BDIV xh y) * FT2R y)
  by apply: Relative.relative_error_N_FLX; lia.
rewrite Heq2u -Hpih in Hrel2.
have Hpih2 : Rabs (FT2R (BMULT (BDIV xh y) y) - FT2R (BDIV xh y) * FT2R y)
           <= u * (Rabs (FT2R xh) + u * Rabs (FT2R xh)).
{ apply Rle_trans with (u * Rabs (FT2R (BDIV xh y) * FT2R y)); [ exact Hrel2 |].
  apply Rmult_le_compat_l; [ exact upos | exact HthyBnd ]. }
(* combine: |pih - xh| <= |pih - th*y| + |th*y - xh| <= /2 |xh| *)
apply Rle_trans with (Rabs (FT2R (BMULT (BDIV xh y) y) - FT2R (BDIV xh y) * FT2R y)
                      + Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh)).
- have -> : FT2R (BMULT (BDIV xh y) y) - FT2R xh
          = (FT2R (BMULT (BDIV xh y) y) - FT2R (BDIV xh y) * FT2R y)
          + (FT2R (BDIV xh y) * FT2R y - FT2R xh) by ring.
  apply Rabs_triang.
- eapply Rle_trans; [ apply Rplus_le_compat; [ exact Hpih2 | exact HthyX ] |].
  exact (abst_pih_close (Rabs (FT2R xh)) u Hxpos upos Hu16).
Qed.

(* Node (C): dh = xh - pih is exact -- via Sterbenz (no UF_dh needed). *)
Lemma bridge_dh :
  FT2R xh - FT2R (BMULT (BDIV xh y) y) = FT2R (BMINUS xh (BMULT (BDIV xh y) y)).
Proof.
have Hclose := pih_close_xh.
have FX : generic_format radix2 (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
            (FT2R xh) by apply generic_format_FLT_FT2R.
have FP : generic_format radix2 (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
            (FT2R (BMULT (BDIV xh y) y)) by apply generic_format_FLT_FT2R.
have HgFLT : generic_format radix2 (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
               (FT2R xh - FT2R (BMULT (BDIV xh y) y)).
{ have HXP := Rabs_le_inv (FT2R (BMULT (BDIV xh y) y) - FT2R xh)
                          (/2 * Rabs (FT2R xh)) Hclose.
  destruct (Rcase_abs (FT2R xh)) as [HX0|HX0].
  - have HrX : Rabs (FT2R xh) = - FT2R xh by (rewrite Rabs_left //).
    rewrite HrX in HXP.
    have Hopp : FT2R xh - FT2R (BMULT (BDIV xh y) y)
              = - ((- FT2R xh) - (- FT2R (BMULT (BDIV xh y) y))) by ring.
    rewrite Hopp. apply generic_format_opp.
    apply (Sterbenz.sterbenz radix2 (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t)));
      [ apply generic_format_opp; exact FX
      | apply generic_format_opp; exact FP
      | ]. lra.
  - have HrX : Rabs (FT2R xh) = FT2R xh by (rewrite Rabs_pos_eq //; lra).
    rewrite HrX in HXP.
    apply (Sterbenz.sterbenz radix2 (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t)));
      [ exact FX | exact FP | ]. lra. }
rewrite -(BMINUS_round_correct t xh (BMULT (BDIV xh y) y) FIN_dh).
symmetry; apply: round_generic; exact HgFLT.
Qed.

(* Node (D): dt = dh - pil is exact (residual xh - th*y is a float, div_error_FLX). *)
Lemma bridge_dt :
  FT2R (BMINUS xh (BMULT (BDIV xh y) y)) - FT2R (Fast2Mult_err (BDIV xh y) y)
    = FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)).
Proof.
have Heq : FT2R (BMINUS xh (BMULT (BDIV xh y) y)) - FT2R (Fast2Mult_err (BDIV xh y) y)
         = FT2R xh - FT2R (BDIV xh y) * FT2R y
  by rewrite -bridge_dh -prodExact; ring.
have Hgflx : generic_format radix2 (FLX_exp (fprec t))
    (FT2R (BMINUS xh (BMULT (BDIV xh y) y)) - FT2R (Fast2Mult_err (BDIV xh y) y)).
{ rewrite Heq -bridge_th.
  apply: (div_error_FLX radix2 (fprec t) (Znearest choice)
           (FT2R xh) (FT2R y)); [ exact Fxh_flx | exact Fy_flx ]. }
(* dt exact WITHOUT the normal-range hypothesis UF_dt: prodExact (from UF_prod)
   already gives dh - pil = xh - th*y, which is FLX-format (div_error_FLX).  Split
   on the residual's own magnitude -- the residual can be tiny/subnormal even when
   the quotient is large, which is exactly why UF_dt is not derivable:
   - large (>= bpow(emin+p-1)): normal range, lift FLX->FLT (the old UF_dt path,
     but now the normal-range side is PROVEN by the branch, not assumed);
   - small (< bpow(emin+p-1)): Hauser's FLT_format_plus_small on the two floats
     dh, -pil -- a small difference of floats is exactly representable. *)
have HgFLT : generic_format radix2 (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
    (FT2R (BMINUS xh (BMULT (BDIV xh y) y)) - FT2R (Fast2Mult_err (BDIV xh y) y)).
{ destruct (Rle_lt_dec (bpow radix2 (emin + fprec t - 1))
              (Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y))
                     - FT2R (Fast2Mult_err (BDIV xh y) y)))) as [Hbig | Hsmall].
  - apply: generic_format_FLT_FLX; [ exact Hbig | exact Hgflx ].
  - have Fdh : generic_format radix2 (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
                 (FT2R (BMINUS xh (BMULT (BDIV xh y) y))) by apply generic_format_FLT_FT2R.
    have Fpil : generic_format radix2 (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
                 (FT2R (Fast2Mult_err (BDIV xh y) y)) by apply generic_format_FLT_FT2R.
    have Hsplit : FT2R (BMINUS xh (BMULT (BDIV xh y) y)) - FT2R (Fast2Mult_err (BDIV xh y) y)
                = FT2R (BMINUS xh (BMULT (BDIV xh y) y))
                  + (- FT2R (Fast2Mult_err (BDIV xh y) y)) by ring.
    rewrite Hsplit.
    apply FLT_format_plus_small;
      [ apply fprec_gt_0 | exact Fdh | apply generic_format_opp; exact Fpil |].
    rewrite -Hsplit.
    apply Rlt_le. eapply Rlt_le_trans; [ exact Hsmall |].
    apply bpow_le. change (@common.emin t) with (SpecFloat.emin (fprec t) (femax t)). lia. }
rewrite -(BMINUS_round_correct t (BMINUS xh (BMULT (BDIV xh y) y))
            (Fast2Mult_err (BDIV xh y) y) FIN_dt).
symmetry; apply: round_generic; exact HgFLT.
Qed.

(* Node (E): d = rnd(dt + xl). *)
Lemma bridge_d :
  round radix2 (FLX_exp (fprec t)) (Znearest choice)
    (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) + FT2R xl)
    = FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                          (Fast2Mult_err (BDIV xh y) y)) xl).
Proof.
rewrite -(BPLUS_round_correct t _ xl FIN_d).
by rewrite rnd_plus_FLT_FLX_eq'.
Qed.

(* Node (F): tl = rnd(d / y). *)
Lemma bridge_tl :
  round radix2 (FLX_exp (fprec t)) (Znearest choice)
    (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                         (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
    = FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                (Fast2Mult_err (BDIV xh y) y)) xl) y).
Proof.
rewrite -(BDIV_round_correct t _ y Hyne (FINtl xh xl y FIN)).
by rewrite round_FLT_FLX //; exact UF_tl.
Qed.

Lemma DWDivFP3_FLX_FLT :
  DWDivFP.DWDivFP3 (fprec t) choice (FT2R xh) (FT2R xl) (FT2R y)
    = F2Rp (DDModels.DWDivFP3 xh xl y).
Proof.
rewrite /DWDivFP.DWDivFP3.
cbv zeta.
rewrite DWTimesFP.TwoProdE.
rewrite bridge_th bridge_prod.
rewrite /F2Rp; cbv beta iota.
change (fst (Fast2Mult (BDIV xh y) y)) with (BMULT (BDIV xh y) y).
change (snd (Fast2Mult (BDIV xh y) y)) with (Fast2Mult_err (BDIV xh y) y).
rewrite bridge_dh bridge_dt bridge_d bridge_tl.
rewrite (FastTwoSumEq_FLT (BDIV xh y) _ FIN).
by rewrite /DDModels.DWDivFP3.
Qed.

(* The paper FLX DWDivFP3 peeled down to the closing Fast2Sum, WITHOUT bridge_tl:
   every node except tl is rewritten to the runtime float value, leaving the
   second Fast2Sum argument as the FLX rounding of the runtime d/y.  Does not use
   UF_tl -- this is the shared reduction behind both the normal and underflow legs. *)
Lemma paper_reduced :
  DWDivFP.DWDivFP3 (fprec t) choice (FT2R xh) (FT2R xl) (FT2R y)
    = F2Sum.Fast2Sum (fprec t) choice (FT2R (BDIV xh y))
        (round radix2 (FLX_exp (fprec t)) (Znearest choice)
          (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                               (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)).
Proof.
rewrite /DWDivFP.DWDivFP3.
cbv zeta.
rewrite DWTimesFP.TwoProdE.
rewrite bridge_th bridge_prod.
rewrite /F2Rp; cbv beta iota.
change (fst (Fast2Mult (BDIV xh y) y)) with (BMULT (BDIV xh y) y).
change (snd (Fast2Mult (BDIV xh y) y)) with (Fast2Mult_err (BDIV xh y) y).
by rewrite bridge_dh bridge_dt bridge_d.
Qed.

End BridgeDWDivFP.

Section DWDivFP3_DoubleWord.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

(* The result of DWDivFP3 is a double word.  Pure structural consequence of the
   closing Fast2Sum (Fast2Sum_is_DW): it needs ONLY (a) finiteness of the sum
   node BPLUS th tl and (b) the magnitude ordering |tl| <= |th|.  No FLX/FLT
   bridge, no strong-underflow node discipline, no accuracy bound. *)
Lemma DWDivFP3_is_DW (xh xl y : ftype t) :
  is_finite (BPLUS (BDIV xh y)
              (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                           (Fast2Mult_err (BDIV xh y) y)) xl) y)) = true ->
  Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                          (Fast2Mult_err (BDIV xh y) y)) xl) y))
    <= Rabs (FT2R (BDIV xh y)) ->
  double_word_prop (fst (DWDivFP3 xh xl y)) (snd (DWDivFP3 xh xl y)).
Proof.
move => Hfin Hord.
have Heqr : DWDivFP3 xh xl y
          = Fast2Sum (BDIV xh y)
              (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                           (Fast2Mult_err (BDIV xh y) y)) xl) y)
  by rewrite /DWDivFP3 /Fast2Mult_err /Fast2Mult /Fast2Sum //=.
rewrite Heqr.
have HDW := Fast2Sum_is_DW (BDIV xh y)
             (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                          (Fast2Mult_err (BDIV xh y) y)) xl) y) Hfin Hord.
by move: HDW; rewrite /double_word /double_word_prop /Fast2Sum_sum /Fast2Sum_err.
Qed.

End DWDivFP3_DoubleWord.

Section FiniteAccuracyDWDivFP.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (common.emin (t:=t)).
Notation u   := (bpow radix2 (- fprec t)).

Variables (xh xl y : ftype t).
Let zh := FT2R (fst (DWDivFP3 xh xl y)).
Let zl := FT2R (snd (DWDivFP3 xh xl y)).

Hypothesis DWx : double_word xh xl.
Hypothesis FIN : is_finite_p (DWDivFP3 xh xl y).
Hypothesis Hp4 : (4 <= fprec t)%Z.
Hypothesis Hyne : FT2R y <> 0.
Hypothesis UF_th   : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xh / FT2R y).
Hypothesis UF_prod : bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R (BDIV xh y) * FT2R y).
(* UF_dh, UF_dt eliminated (dh, dt exact -- Sterbenz / magnitude case split). *)
Hypothesis UF_tl   : bpow radix2 (emin + fprec t - 1)
                     <= Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                                   (Fast2Mult_err (BDIV xh y) y)) xl)
                              / FT2R y).

Definition relative_error_DWDivFP :=
  Rabs ((zh + zl - (FT2R xh + FT2R xl) / FT2R y) / ((FT2R xh + FT2R xl) / FT2R y)).

Theorem relative_errorDWDivFP3_correct :
  relative_error_DWDivFP <= 3 * u ^ 2.
Proof.
have HFy : generic_format radix2 (FLX_exp (fprec t)) (FT2R y).
{ apply (generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t)).
  apply generic_format_FLT_FT2R. }
have HDWx : DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl)
  by (apply (dw_word_DWdouble xh xl y); exact DWx).
pose proof (@DWDFP3_correct (fprec t) (fprec_gt_one t) choice eq_refl
              (FT2R xh) (FT2R xl) (FT2R y) HDWx HFy Hp4 Hyne) as Hpaper.
rewrite (DWDivFP3_FLX_FLT xh xl y FIN Hp4 Hyne UF_th UF_prod UF_tl) in Hpaper.
rewrite /F2Rp/= in Hpaper.
unfold relative_error_DWDivFP, zh, zl.
eapply Rle_trans; [ apply Req_le; reflexivity | ].
rewrite (_ : 3 * u ^ 2 = 3 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t)));
  [ exact Hpaper | rewrite /=; ring ].
Qed.

End FiniteAccuracyDWDivFP.

(* ============================================================
   Layer-2: finiteness + underflow-discipline facts derived from DWDivFP_relative_error_input_cond.

   The cond bounds only the components (|xh| <= bpow(femax/2-1), |y| >=
   bpow(1-femax/2)) plus the quotient underflow bound; from these the QUOTIENT
   is bounded, |xh/y| <= Omega/4 (cond_quotient_bound, PROVEN), which is what
   keeps every rounded node of DWDivFP3 finite.
   ============================================================ *)
Section DWDivFP_Finite.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin  := (@common.emin t).
Notation fexp  := (SpecFloat.fexp (fprec t) (femax t)).
Notation ulp   := (Ulp.ulp Zaux.radix2 fexp).
Notation Omega := (bpow Zaux.radix2 (femax t)).

(* Internal normal-leading-quotient proof condition for DWDivFP3.  This is not
   a runtime guard or a public accuracy tier: DWDivFP_mixed_safe_input_cond is
   the canonical whole-range mixed-error condition, while
   DWDivFP_relative_error_input_cond is the normal-range pure-relative one.
   The helper records the normal-quotient branch used to reuse the FLX proof
   when |xh/y| is at least 2^(emin+p-1).  It differs from the safe-input cond
   only in the clause-5 slot, where finiteness of the leading quotient node is
   traded for that node being normal; the final lower bound is on the distinct
   product node th*y and remains necessary in this branch. *)
Definition DWDivFP_normal_quotient_input_cond
    (xh xl y : ftype t) : Prop :=
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite y  = true /\
  double_word_prop xh xl /\
  bpow Zaux.radix2
    (SpecFloat.emin (fprec t) (femax t) + fprec t - 1)
    <= Rabs (FT2R xh / FT2R y) /\
  Rabs (FT2R xh)          <= bpow Zaux.radix2 (femax t - 2) /\
  Rabs (FT2R xh / FT2R y) <= bpow Zaux.radix2 (femax t - 2) /\
  bpow Zaux.radix2
    (SpecFloat.emin (fprec t) (femax t) + 2 * fprec t)
    <= Rabs (FT2R xh).

Lemma DWDivFP_normal_quotient_input_cond_of_relative_error_input_cond (xh xl y : ftype t) :
  DWDivFP_relative_error_input_cond xh xl y -> DWDivFP_normal_quotient_input_cond xh xl y.
Proof.
  intros ((Hfxh & Hfxl & Hfy & Hdwp & Hfth & Hxhb & Hqub & Hxhlb) & Hquot & _).
  repeat split; assumption.
Qed.

Local Instance valid_fexp_inst_div : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.

Local Instance valid_flx_inst_div : Generic_fmt.Valid_exp (FLX_exp (fprec t)).
Proof. apply FLX.FLX_exp_valid, fprec_gt_0. Qed.

(* The tl single-node underflow perturbation: FLT and FLX rounding of the same
   real v differ by at most one ulp at the underflow floor, 2^emin.  This is the
   ONLY place the runtime DWDivFP3 can diverge from its FLX model when the cond
   holds (all other nodes are exact or FLX-insensitive), so it bounds the whole
   underflow-leg perturbation of the result. *)
Lemma round_FLT_FLX_diff (v : R) :
  Rabs (round radix2 fexp (Znearest choice) v
        - round radix2 (FLX_exp (fprec t)) (Znearest choice) v)
    <= bpow radix2 emin.
Proof.
destruct (Rle_lt_dec (bpow radix2 (@common.emin t + fprec t - 1)) (Rabs v)) as [Hn | Hs].
- (* normal: FLT rounding coincides with FLX rounding *)
  rewrite round_FLT_FLX; [| exact Hn].
  rewrite Rminus_diag Rabs_R0. apply bpow_ge_0.
- destruct (Req_dec v 0) as [Hv0 | Hvn].
  + subst v. rewrite !round_0 Rminus_diag Rabs_R0. apply bpow_ge_0.
  + have Ef : Rabs (round radix2 fexp (Znearest choice) v - v) <= /2 * ulp v
      by apply (@error_le_half_ulp radix2 fexp valid_fexp_inst_div choice v).
    have Ex : Rabs (round radix2 (FLX_exp (fprec t)) (Znearest choice) v - v)
              <= /2 * Ulp.ulp radix2 (FLX_exp (fprec t)) v
      by apply (@error_le_half_ulp radix2 (FLX_exp (fprec t)) valid_flx_inst_div choice v).
    have Hle : Ulp.ulp radix2 (FLX_exp (fprec t)) v <= ulp v.
    { rewrite !ulp_neq_0 //. apply bpow_le.
      unfold cexp, FLX_exp, SpecFloat.fexp. apply Z.le_max_l. }
    have Hbnd : Rabs v < bpow radix2 (@common.emin t + fprec t).
    { eapply Rlt_le_trans; [ exact Hs |]. apply bpow_le. unfold common.emin. lia. }
    have Hulp : ulp v = bpow radix2 (@common.emin t)
      by apply (@ulp_FLT_small radix2 (@common.emin t) (fprec t) (fprec_gt_0 t) v Hbnd).
    have Htri : Rabs (round radix2 fexp (Znearest choice) v
                      - round radix2 (FLX_exp (fprec t)) (Znearest choice) v)
                <= Rabs (round radix2 fexp (Znearest choice) v - v)
                   + Rabs (round radix2 (FLX_exp (fprec t)) (Znearest choice) v - v).
    { replace (round radix2 fexp (Znearest choice) v
               - round radix2 (FLX_exp (fprec t)) (Znearest choice) v)
        with ((round radix2 fexp (Znearest choice) v - v)
              + - (round radix2 (FLX_exp (fprec t)) (Znearest choice) v - v)) by ring.
      eapply Rle_trans; [ apply Rabs_triang |]. rewrite Rabs_Ropp. apply Rle_refl. }
    rewrite -Hulp. eapply Rle_trans; [ exact Htri |].
    apply (abst_diff_ulp _ _ (ulp v) (Ulp.ulp radix2 (FLX_exp (fprec t)) v));
      [ exact Ef | exact Ex | exact Hle ].
Qed.

(* FLX Fast2Sum preserves the sum exactly, given the magnitude ordering. *)
Lemma flx_f2s_sum (a b : R) :
  generic_format radix2 (FLX_exp (fprec t)) a ->
  generic_format radix2 (FLX_exp (fprec t)) b ->
  Rabs b <= Rabs a ->
  fst (F2Sum.Fast2Sum (fprec t) choice a b)
  + snd (F2Sum.Fast2Sum (fprec t) choice a b) = a + b.
Proof.
intros Fa Fb Hle.
have Hsym : forall x, round radix2 (FLX_exp (fprec t)) (Znearest choice) (- x)
                    = - round radix2 (FLX_exp (fprec t)) (Znearest choice) x
  by (intro x; apply round_NE_opp).
have Hb3 : (radix2 <= 3)%Z by (simpl; lia).
have H := F2Sum.F2Sum_correct_abs (fprec_gt_one t) Hsym Hb3 Fa Fb Hle.
unfold F2Sum.Fast2Sum_correct in H. lra.
Qed.

(* Omega/4 = bpow(femax-2). *)
Lemma aux_quarter_Omega : bpow radix2 (femax t - 2) = /4 * Omega.
Proof.
have -> : Omega = (bpow radix2 (femax t - 2) * bpow radix2 2)%R
  by rewrite -bpow_plus; f_equal; lia.
have -> : bpow radix2 2 = 4%R by reflexivity. lra.
Qed.

(* Case-free linear upper bound on ulp: ulp(v) <= |v|*2^(1-p) + 2^emin.
   (Normal: <= |v|*2^(1-p) by ulp_FLT_le; subnormal/zero: = 2^emin.)  This lets
   the finiteness bounds avoid a normal/subnormal split at every node. *)
Lemma ulp_le_lin (v : R) :
  ulp v <= Rabs v * bpow radix2 (1 - fprec t) + bpow radix2 emin.
Proof.
have HB := bpow_ge_0 radix2 (@common.emin t).
have HA := bpow_ge_0 radix2 (1 - fprec t).
have Hp := Rabs_pos v.
destruct (Rle_lt_dec (bpow radix2 (emin + fprec t - 1)) (Rabs v)) as [Hn|Hs].
- have Hle : ulp v <= Rabs v * bpow radix2 (1 - fprec t) by apply ulp_FLT_le; exact Hn.
  lra.
- have -> : ulp v = bpow radix2 (@common.emin t).
  { apply ulp_FLT_small; [apply fprec_gt_0 |].
    eapply Rlt_trans; [exact Hs | apply bpow_lt; lia]. }
  nra.
Qed.

(* A nonzero float has magnitude at least the smallest positive float 2^emin:
   2^emin = ulp(0) <= ulp(y) <= |y|. *)
Lemma y_ge_emin (y : ftype t) :
  FT2R y <> 0 -> bpow radix2 emin <= Rabs (FT2R y).
Proof.
move => Hy.
have H1 : ulp (FT2R y) <= Rabs (FT2R y)
  by apply ulp_le_abs; [ exact Hy | apply generic_format_FLT_FT2R ].
have Hlb : bpow radix2 (@common.emin t) <= ulp (FT2R y).
{ rewrite (Ulp.ulp_neq_0 radix2 fexp _ Hy). apply bpow_le.
  unfold cexp, SpecFloat.fexp, common.emin, SpecFloat.emin. apply Z.le_max_r. }
lra.
Qed.

(* Round upper bound that keeps the tiny (subnormal) term proportional to Y:
   |round(v)| <= |v| + 1/2*|v|*2^(1-p) + 1/2*Y, given 2^emin <= Y.  Applied with
   Y = |y| this makes every node's bound divisible by |y| for the d/y estimate. *)
Lemma round_ub_Y (v Y : R) :
  bpow radix2 emin <= Y ->
  Rabs (round radix2 fexp (Znearest choice) v)
    <= Rabs v + / 2 * (Rabs v * bpow radix2 (1 - fprec t)) + / 2 * Y.
Proof.
move => HY.
have He := @error_le_half_ulp radix2 fexp valid_fexp_inst_div choice v.
have Hu := ulp_le_lin v.
have HB := bpow_ge_0 radix2 (@common.emin t).
have Ht : Rabs (round radix2 fexp (Znearest choice) v)
        <= Rabs (round radix2 fexp (Znearest choice) v - v) + Rabs v.
{ have H := Rabs_triang (round radix2 fexp (Znearest choice) v - v) v.
  replace (round radix2 fexp (Znearest choice) v - v + v)
     with (round radix2 fexp (Znearest choice) v) in H by ring.
  exact H. }
lra.
Qed.

(* Round upper bound keeping the tiny term as bpow(emin) (NOT bounded by |y|):
   |round v| <= |v| + 1/2*|v|*2^(1-p) + 1/2*2^emin.  Because the additive part is
   genuinely tiny, dividing a node bound by |y| >= 2^emin yields a constant, so
   the finiteness bounds hold for all femax (no Omega >= 24 constraint). *)
Lemma round_ub_emin (v : R) :
  Rabs (round radix2 fexp (Znearest choice) v)
    <= Rabs v + Rabs v * bpow radix2 (- fprec t) + / 2 * bpow radix2 emin.
Proof.
have He := @error_le_half_ulp radix2 fexp valid_fexp_inst_div choice v.
have Hu := ulp_le_lin v.
have Hb1p : bpow radix2 (1 - fprec t) = 2 * bpow radix2 (- fprec t).
{ replace (1 - fprec t)%Z with (1 + - fprec t)%Z by lia.
  rewrite bpow_plus. have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
have Ht : Rabs (round radix2 fexp (Znearest choice) v)
        <= Rabs (round radix2 fexp (Znearest choice) v - v) + Rabs v.
{ have H := Rabs_triang (round radix2 fexp (Znearest choice) v - v) v.
  replace (round radix2 fexp (Znearest choice) v - v + v)
     with (round radix2 fexp (Znearest choice) v) in H by ring.
  exact H. }
rewrite Hb1p in Hu. lra.
Qed.

(* Rounding-error companion of round_ub_emin: |round v - v| <= |v|*2^-p + 1/2*2^emin. *)
Lemma round_err_emin (v : R) :
  Rabs (round radix2 fexp (Znearest choice) v - v)
    <= Rabs v * bpow radix2 (- fprec t) + / 2 * bpow radix2 emin.
Proof.
have He := @error_le_half_ulp radix2 fexp valid_fexp_inst_div choice v.
have Hu := ulp_le_lin v.
have Hb1p : bpow radix2 (1 - fprec t) = 2 * bpow radix2 (- fprec t).
{ replace (1 - fprec t)%Z with (1 + - fprec t)%Z by lia.
  rewrite bpow_plus. have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
rewrite Hb1p in Hu. lra.
Qed.

(* Residual of the quotient node: th*y is within |xh|*2^-p of xh, since
   th = round(xh/y) and the quotient is in the normal range. *)
Lemma thy_residual (xh y : ftype t) :
  is_finite (BDIV xh y) = true -> FT2R y <> 0 ->
  bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xh / FT2R y) ->
  Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh)
    <= Rabs (FT2R xh) * bpow radix2 (- fprec t).
Proof.
move => Hfth Hyne Hnorm.
have Hyy : FT2R xh / FT2R y * FT2R y = FT2R xh.
{ unfold Rdiv. rewrite Rmult_assoc (Rinv_l (FT2R y) Hyne) Rmult_1_r. reflexivity. }
have Hth : FT2R (BDIV xh y) = round radix2 fexp (Znearest choice) (FT2R xh / FT2R y)
  by rewrite BDIV_round_correct.
have Hid : FT2R (BDIV xh y) * FT2R y - FT2R xh
         = (FT2R (BDIV xh y) - FT2R xh / FT2R y) * FT2R y
  by field; exact Hyne.
have He : Rabs (FT2R (BDIV xh y) - FT2R xh / FT2R y) <= / 2 * ulp (FT2R xh / FT2R y)
  by rewrite Hth;
     exact (@error_le_half_ulp radix2 fexp valid_fexp_inst_div choice (FT2R xh / FT2R y)).
have Hu : ulp (FT2R xh / FT2R y) <= Rabs (FT2R xh / FT2R y) * bpow radix2 (1 - fprec t)
  by apply ulp_FLT_le; exact Hnorm.
have Hxhy : Rabs (FT2R xh / FT2R y) * Rabs (FT2R y) = Rabs (FT2R xh)
  by rewrite -Rabs_mult Hyy.
have Hyp : 0 <= Rabs (FT2R y) by apply Rabs_pos.
have Hb1p : bpow radix2 (1 - fprec t) = 2 * bpow radix2 (- fprec t).
{ replace (1 - fprec t)%Z with (1 + - fprec t)%Z by lia.
  rewrite bpow_plus. have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
rewrite Hid Rabs_mult.
apply Rle_trans with (/ 2 * ulp (FT2R xh / FT2R y) * Rabs (FT2R y)).
{ apply Rmult_le_compat_r; [ exact Hyp | exact He ]. }
apply Rle_trans with
  (/ 2 * (Rabs (FT2R xh / FT2R y) * bpow radix2 (1 - fprec t)) * Rabs (FT2R y)).
{ apply Rmult_le_compat_r; [ exact Hyp |].
  apply Rmult_le_compat_l; [ lra | exact Hu ]. }
have Hbp : bpow radix2 (- fprec t) = / 2 * bpow radix2 (1 - fprec t)
  by rewrite Hb1p; lra.
rewrite Hbp -Hxhy. apply Req_le. field.
Qed.

(* The quotient node th = BDIV xh y is finite: |round(xh/y)| <= Omega/4 + tiny. *)
Lemma th_finite (xh y : ftype t) :
  is_finite xh = true -> FT2R y <> 0 ->
  Rabs (FT2R xh / FT2R y) <= bpow radix2 (femax t - 2) ->
  is_finite (BDIV xh y) = true.
Proof.
move => Hfxh Hyne Hq.
have HΩ : 0 < Omega by apply bpow_gt_0.
have Hlt : Rabs (FT2R xh / FT2R y) < Omega.
{ eapply Rle_lt_trans; [exact Hq|]. apply bpow_lt; pose proof femax_lb t; lia. }
apply (no_overflow_div_is_finite t xh y Hfxh Hyne).
eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
have Hu := ulp_below_overflow _ Hlt.
have H4 := aux_quarter_Omega.
have Hhalf : bpow radix2 (femax t - fprec t) <= /2 * Omega.
{ have -> : (/2 * Omega = bpow radix2 (femax t - 1))%R.
  { have -> : Omega = (bpow radix2 (femax t - 1) * bpow radix2 1)%R
      by rewrite -bpow_plus; f_equal; lia.
    have -> : bpow radix2 1 = 2%R by reflexivity. lra. }
  apply bpow_le; pose proof fprec_lb t; lia. }
lra.
Qed.

(* MAIN finiteness of fst (DWDivFP3 xh xl y) from the cond.

   PROOF OBLIGATION (overflow analysis; the quotient bound cond_quotient_bound
   + th_finite gives the th node; the remaining nodes are, in order):
     pih = BMULT th y  : |th*y| <= |xh|(1+2^-p) < Omega  (th*y ~ xh, ulp_FLT_le);
     pil = Fast2Mult_err th y : Fast2Mult_finite_if_BMULT_finite;
     dh,dt,d           : residual sums/diffs, crude |.|+|.| < Omega;
     tl = BDIV d y     : the delicate node — the TIGHT residual bound
                         d = round((xh+xl) - th*y) gives |d/y| <= |(xh+xl)/y|+|th|
                         ~ 2*Omega/4, via the exactness facts (dh=xh-pih,
                         dt=xh-th*y) once dh,dt finite; normal/subnormal split;
     fst = BPLUS th tl : |th+tl| < Omega. *)
(* Worst-case half-ulp bound (fprec>=4): 1/2 ulp v <= Omega/16 for |v| < Omega.
   Kept OUT of the finiteness proof context: a forall-quantified hypothesis makes
   [lra] bail ("No applicable tactic"), so this is a standalone lemma applied
   pointwise, never a local [have]. *)
Lemma half_ulp_le (v : R) :
  (4 <= fprec t)%Z -> Rabs v < Omega -> / 2 * ulp v <= / 16 * Omega.
Proof.
move => Hp4 Hv.
have Hu := ulp_below_overflow v Hv.
have Hufe : bpow radix2 (femax t - fprec t) <= / 16 * Omega.
{ have -> : (/ 16 * Omega = bpow radix2 (femax t - 4))%R.
  { have -> : Omega = (bpow radix2 (femax t - 4) * bpow radix2 4)%R
      by rewrite -bpow_plus; f_equal; lia.
    have -> : bpow radix2 4 = 16%R by (simpl; lra). lra. }
  apply bpow_le; lia. }
have HΩ0 : 0 <= Omega by apply bpow_ge_0.
lra.
Qed.

(* Shared finiteness cascade for DWDivFP3: proves both quotient nodes and their
   BPLUS are finite, with |th| and |tl| bounded by Omega/2 and |th+tl| < Omega.
   Consumed by both DWDivFP3_fst_finite_acc and DWDivFP3_snd_finite_acc.

   Stated on DWDivFP_normal_quotient_input_cond: the quotient bound enters only
   through Hnorm below, at emin+p-1 (thy_residual / ulp_FLT_le), and the
   product node is carried by clause 8, which the relaxed cond keeps. *)
Lemma DWDivFP3_cascade_acc (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_normal_quotient_input_cond xh xl y ->
  is_finite (BDIV xh y) = true /\
  is_finite (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y) = true /\
  is_finite (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) = true /\
  Rabs (FT2R (BDIV xh y)) <= / 2 * Omega /\
  Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) <= / 2 * Omega /\
  Rabs (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) < Omega
  /\ Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                       (Fast2Mult_err (BDIV xh y) y)) xl)) <= Rabs (FT2R xh).
Proof.
intros Hp4 (Hfxh & Hfxl & Hfy & Hdwp & Hquot & Hxhb & Hqub & Hxhlb).
(* ---- constants + nonneg facts ---- *)
have HΩ : 0 < Omega by apply bpow_gt_0.
have HΩ0 : 0 <= Omega by apply bpow_ge_0.
have HΩ32 : 32 <= Omega.
{ have -> : (32 = bpow radix2 5)%R by (simpl; lra).
  apply bpow_le; pose proof (fprec_lt_femax t); lia. }
have Hu16 : (bpow radix2 (- fprec t)) <= / 16.
{ have -> : (/ 16 = bpow radix2 (-4))%R by (simpl; lra).
  apply bpow_le; lia. }
have Hu0 : 0 <= (bpow radix2 (- fprec t)) by (apply bpow_ge_0).
have He0 : 0 <= bpow radix2 (@common.emin t) by apply bpow_ge_0.
have H4Ω : bpow radix2 (femax t - 2) = / 4 * Omega by apply aux_quarter_Omega.
have Hyne : FT2R y <> 0.
{ intro H0.
  have Hp := bpow_gt_0 radix2 (SpecFloat.emin (fprec t) (femax t) + fprec t - 1).
  move: Hquot; rewrite H0 /Rdiv Rinv_0 Rmult_0_r Rabs_R0 => Hc. lra. }
have HYe : bpow radix2 emin <= Rabs (FT2R y) by apply y_ge_emin, Hyne.
have HYpos : 0 < Rabs (FT2R y)
  by (eapply Rlt_le_trans; [apply bpow_gt_0 | exact HYe]).
have Hxh4 : Rabs (FT2R xh) <= / 4 * Omega by (rewrite -H4Ω; exact Hxhb).
have Hxhp : 0 <= Rabs (FT2R xh) by apply Rabs_pos.
(* 2^emin <= 1 (emin <= 0) and |xh|*2^-p <= Omega/64 : the two abstract-lemma
   side facts used by the finiteness / <Omega applications below. *)
have He1 : bpow radix2 emin <= 1.
{ have Hb0 : bpow radix2 0 = 1 by reflexivity.
  rewrite -Hb0. apply bpow_le.
  change (@common.emin t) with (SpecFloat.emin (fprec t) (femax t)).
  unfold SpecFloat.emin. pose proof (femax_lb t). pose proof (fprec_gt_0 t). lia. }
have HW : Rabs (FT2R xh) * bpow radix2 (- fprec t) <= / 64 * Omega.
{ apply Rle_trans with (/ 4 * Omega * bpow radix2 (- fprec t)).
  - apply Rmult_le_compat_r; [ apply bpow_ge_0 | exact Hxh4 ].
  - apply Rle_trans with (/ 4 * Omega * / 16).
    + apply Rmult_le_compat_l; [ apply Rmult_le_pos; [ lra | apply bpow_ge_0 ] | exact Hu16 ].
    + apply Req_le; field. }
have HW0 : 0 <= Rabs (FT2R xh) * bpow radix2 (- fprec t)
  by apply Rmult_le_pos; [ exact Hxhp | apply bpow_ge_0 ].
have Hnorm : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xh / FT2R y).
{ change (@common.emin t) with (SpecFloat.emin (fprec t) (femax t)). exact Hquot. }
(* ---- th ---- *)
have Fth : is_finite (BDIV xh y) = true
  by apply th_finite; [ exact Hfxh | exact Hyne | exact Hqub ].
have Hthy_res : Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh) <= Rabs (FT2R xh) * (bpow radix2 (- fprec t))
  by apply thy_residual; [ exact Fth | exact Hyne | exact Hnorm ].
have Hthy_xh : Rabs (FT2R (BDIV xh y) * FT2R y) <= Rabs (FT2R xh) + Rabs (FT2R xh) * (bpow radix2 (- fprec t)).
{ have Hti := Rabs_triang_inv (FT2R (BDIV xh y) * FT2R y) (FT2R xh).
  rewrite Rplus_comm.
  apply Rcomplements.Rle_minus_l.
  eapply Rle_trans. apply Hti. exact Hthy_res. } 
have Hthy_lt : Rabs (FT2R (BDIV xh y) * FT2R y) < Omega.
{ apply (abst_lt_Om _ Omega (Rabs (FT2R xh)) (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 emin) 1 1 0);
    [ lra | lra | lra | lra | lra | lra | exact HΩ32 | exact Hxh4 | exact HW | exact He1
    | exact Hxhp | exact HW0 | exact He0
    | (eapply Rle_trans; [ exact Hthy_xh |]; apply Req_le; ring) ]. }
(* ---- pih ---- *)
have Fpih : is_finite (BMULT (BDIV xh y) y) = true.
{ apply no_overflow_mult_is_finite; [ exact Fth | exact Hfy |].
  eapply Rle_lt_trans; [ apply round_abs_le_abs_plus_half_ulp |].
  apply (abst_fin _ _ _ (Rabs (FT2R xh)) (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 emin) 1 1 0);
    [ lra | lra | lra | lra | lra | lra | exact HΩ32 | exact Hxh4 | exact HW | exact He1
    | exact Hxhp | exact HW0 | exact He0
    | (eapply Rle_trans; [ exact Hthy_xh |]; apply Req_le; ring)
    | exact (half_ulp_le _ Hp4 Hthy_lt) ]. }
have Hpih_e : FT2R (BMULT (BDIV xh y) y)
            = round radix2 fexp (Znearest choice) (FT2R (BDIV xh y) * FT2R y)
  by rewrite BMULT_round_correct.
have Hpiherr : Rabs (FT2R (BMULT (BDIV xh y) y) - FT2R (BDIV xh y) * FT2R y)
             <= Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 2 + bpow radix2 emin.
{ rewrite Hpih_e.
  apply (abst_pih_err (Rabs (FT2R xh)) (bpow radix2 (- fprec t)) (bpow radix2 emin)
                      (Rabs (FT2R (BDIV xh y) * FT2R y)));
    [ exact Hxhp | apply bpow_ge_0 | exact Hu16 | apply bpow_ge_0 | apply Rabs_pos
    | exact Hthy_xh
    | exact (round_err_emin (FT2R (BDIV xh y) * FT2R y)) ]. }
have Hpih_b : Rabs (FT2R (BMULT (BDIV xh y) y))
            <= Rabs (FT2R xh) + Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 3 + bpow radix2 emin.
{ apply Rle_trans with (Rabs (FT2R (BMULT (BDIV xh y) y) - FT2R (BDIV xh y) * FT2R y)
                        + Rabs (FT2R (BDIV xh y) * FT2R y)).
  - apply Rcomplements.Rle_minus_l.
    exact (Rabs_triang_inv (FT2R (BMULT (BDIV xh y) y)) (FT2R (BDIV xh y) * FT2R y)).
  - eapply Rle_trans; [ apply Rplus_le_compat; [ exact Hpiherr | exact Hthy_xh ] |].
    apply Req_le; ring. }
have Hpih_lt : Rabs (FT2R (BMULT (BDIV xh y) y)) < Omega.
{ apply (abst_lt_Om _ Omega (Rabs (FT2R xh)) (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 emin) 1 3 1);
    [ lra | lra | lra | lra | lra | lra | exact HΩ32 | exact Hxh4 | exact HW | exact He1
    | exact Hxhp | exact HW0 | exact He0
    | (eapply Rle_trans; [ exact Hpih_b |]; apply Req_le; ring) ]. }
(* ---- pil = BFMA th y (BOPP pih) ---- *)
have FBpih : is_finite (BOPP (BMULT (BDIV xh y) y)) = true
  by (apply (BOPP_is_finite t (BMULT (BDIV xh y) y)); exact Fpih).
have Hpe_e : FT2R (BDIV xh y) * FT2R y + FT2R (BOPP (BMULT (BDIV xh y) y))
           = FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y).
{ rewrite -BOPP_binary; [ ring | right; exact Fpih ]. }
have Hpe_lt : Rabs (FT2R (BDIV xh y) * FT2R y + FT2R (BOPP (BMULT (BDIV xh y) y))) < Omega.
{ rewrite Hpe_e.
  have Hsym : Rabs (FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y))
            = Rabs (FT2R (BMULT (BDIV xh y) y) - FT2R (BDIV xh y) * FT2R y)
    by rewrite -Rabs_Ropp; f_equal; ring.
  rewrite Hsym.
  apply (abst_lt_Om _ Omega (Rabs (FT2R xh)) (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 emin) 0 2 1);
    [ lra | lra | lra | lra | lra | lra | exact HΩ32 | exact Hxh4 | exact HW | exact He1
    | exact Hxhp | exact HW0 | exact He0
    | (eapply Rle_trans; [ exact Hpiherr |]; apply Req_le; ring) ]. }
have Hpe_b : Rabs (FT2R (BDIV xh y) * FT2R y + FT2R (BOPP (BMULT (BDIV xh y) y)))
           <= Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 2 + bpow radix2 emin.
{ rewrite Hpe_e.
  have Hs : Rabs (FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y))
          = Rabs (FT2R (BMULT (BDIV xh y) y) - FT2R (BDIV xh y) * FT2R y)
      by (rewrite -Rabs_Ropp; f_equal; ring).
  rewrite Hs. exact Hpiherr. }
have Fpil : is_finite (BFMA (BDIV xh y) y (BOPP (BMULT (BDIV xh y) y))) = true.
{ apply no_overflow_fma_is_finite; [ exact Fth | exact Hfy | exact FBpih |].
  eapply Rle_lt_trans; [ apply round_abs_le_abs_plus_half_ulp |].
  apply (abst_fin _ _ _ (Rabs (FT2R xh)) (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 emin) 0 2 1);
    [ lra | lra | lra | lra | lra | lra | exact HΩ32 | exact Hxh4 | exact HW | exact He1
    | exact Hxhp | exact HW0 | exact He0
    | (eapply Rle_trans; [ exact Hpe_b |]; apply Req_le; ring)
    | exact (half_ulp_le _ Hp4 Hpe_lt) ]. }
have Fpil' : is_finite (Fast2Mult_err (BDIV xh y) y) = true by exact Fpil.
have Hpil_e : FT2R (Fast2Mult_err (BDIV xh y) y)
            = round radix2 fexp (Znearest choice)
                (FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y)).
{ change (FT2R (Fast2Mult_err (BDIV xh y) y))
    with (FT2R (BFMA (BDIV xh y) y (BOPP (BMULT (BDIV xh y) y)))).
  rewrite -BFMA_round_correct; [| exact Fpil]. rewrite Hpe_e. reflexivity. }
have Hpil_b : Rabs (FT2R (Fast2Mult_err (BDIV xh y) y)) <= Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 3 + bpow radix2 emin * 2.
{ rewrite Hpil_e.
  have Hsym : Rabs (FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y))
            = Rabs (FT2R (BMULT (BDIV xh y) y) - FT2R (BDIV xh y) * FT2R y)
      by (rewrite -Rabs_Ropp; f_equal; ring).
  eapply Rle_trans.
  - apply (abst_round_step (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 (- fprec t))
             (bpow radix2 emin) (Rabs (FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y))) _ 2 1);
      [ apply bpow_ge_0 | exact Hu16 | apply bpow_ge_0 | apply Rabs_pos | exact HW0
      | lra | lra | lra | lra
      | (rewrite Hsym; eapply Rle_trans; [ exact Hpiherr |]; apply Req_le; ring)
      | exact (round_ub_emin (FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y))) ].
  - apply Req_le; ring. }
(* ---- dh = BMINUS xh pih ---- *)
have Hxhpih_b : Rabs (FT2R xh - FT2R (BMULT (BDIV xh y) y)) <= Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 3 + bpow radix2 emin.
{ have Hsplit : Rabs (FT2R xh - FT2R (BMULT (BDIV xh y) y))
              <= Rabs (FT2R xh - FT2R (BDIV xh y) * FT2R y)
               + Rabs (FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y)).
  { replace (FT2R xh - FT2R (BMULT (BDIV xh y) y))
       with ((FT2R xh - FT2R (BDIV xh y) * FT2R y)
             + (FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y))) by ring.
    apply Rabs_triang. }
  have Hsym : Rabs (FT2R xh - FT2R (BDIV xh y) * FT2R y)
            = Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh)
    by rewrite -Rabs_Ropp; f_equal; ring.
  rewrite Hsym in Hsplit.
  eapply Rle_trans; [ exact Hsplit |].
  apply Rle_trans with (Rabs (FT2R xh) * (bpow radix2 (- fprec t))
                        + (Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 2 + bpow radix2 emin)).
  - apply Rplus_le_compat; [ exact Hthy_res |].
    have Hs2 : Rabs (FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y))
             = Rabs (FT2R (BMULT (BDIV xh y) y) - FT2R (BDIV xh y) * FT2R y)
        by (rewrite -Rabs_Ropp; f_equal; ring).
    rewrite Hs2; exact Hpiherr.
  - apply Req_le; ring. }
have Hxhpih_lt : Rabs (FT2R xh - FT2R (BMULT (BDIV xh y) y)) < Omega.
{ apply (abst_lt_Om _ Omega (Rabs (FT2R xh)) (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 emin) 0 3 1);
    [ lra | lra | lra | lra | lra | lra | exact HΩ32 | exact Hxh4 | exact HW | exact He1
    | exact Hxhp | exact HW0 | exact He0
    | (eapply Rle_trans; [ exact Hxhpih_b |]; apply Req_le; ring) ]. }
have Fdh : is_finite (BMINUS xh (BMULT (BDIV xh y) y)) = true.
{ apply no_overflow_minus_is_finite; [ exact Hfxh | exact Fpih |].
  red. eapply Rle_lt_trans; [ apply round_abs_le_abs_plus_half_ulp |].
  apply (abst_fin _ _ _ (Rabs (FT2R xh)) (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 emin) 0 3 1);
    [ lra | lra | lra | lra | lra | lra | exact HΩ32 | exact Hxh4 | exact HW | exact He1
    | exact Hxhp | exact HW0 | exact He0
    | (eapply Rle_trans; [ exact Hxhpih_b |]; apply Req_le; ring)
    | exact (half_ulp_le _ Hp4 Hxhpih_lt) ]. }
have Hdh_e : FT2R (BMINUS xh (BMULT (BDIV xh y) y))
           = round radix2 fexp (Znearest choice) (FT2R xh - FT2R (BMULT (BDIV xh y) y))
  by rewrite BMINUS_round_correct.
have Hdh_b : Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y)))
           <= Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 4 + bpow radix2 emin * 2.
{ rewrite Hdh_e.
  eapply Rle_trans.
  - apply (abst_round_step (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 (- fprec t))
             (bpow radix2 emin) (Rabs (FT2R xh - FT2R (BMULT (BDIV xh y) y))) _ 3 1);
      [ apply bpow_ge_0 | exact Hu16 | apply bpow_ge_0 | apply Rabs_pos | exact HW0
      | lra | lra | lra | lra
      | (eapply Rle_trans; [ exact Hxhpih_b |]; apply Req_le; ring)
      | exact (round_ub_emin (FT2R xh - FT2R (BMULT (BDIV xh y) y))) ].
  - apply Req_le; ring. }
(* ---- dt = BMINUS dh pil ---- *)
have Hdtarg_b : Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y))
                      - FT2R (Fast2Mult_err (BDIV xh y) y))
              <= Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 7 + bpow radix2 emin * 4.
{ apply Rle_trans with (Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y)))
                        + Rabs (FT2R (Fast2Mult_err (BDIV xh y) y))).
  - replace (FT2R (BMINUS xh (BMULT (BDIV xh y) y)) - FT2R (Fast2Mult_err (BDIV xh y) y))
       with (FT2R (BMINUS xh (BMULT (BDIV xh y) y)) + - FT2R (Fast2Mult_err (BDIV xh y) y)) by ring.
    eapply Rle_trans; [ apply Rabs_triang |]. rewrite Rabs_Ropp. apply Rle_refl.
  - apply Rle_trans with (Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 4 + bpow radix2 emin * 2
                          + (Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 3 + bpow radix2 emin * 2)).
    + apply Rplus_le_compat; [ exact Hdh_b | exact Hpil_b ].
    + apply Req_le; ring. }
have Hdtarg_lt : Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y))
                       - FT2R (Fast2Mult_err (BDIV xh y) y)) < Omega.
{ apply (abst_lt_Om _ Omega (Rabs (FT2R xh)) (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 emin) 0 7 4);
    [ lra | lra | lra | lra | lra | lra | exact HΩ32 | exact Hxh4 | exact HW | exact He1
    | exact Hxhp | exact HW0 | exact He0
    | (eapply Rle_trans; [ exact Hdtarg_b |]; apply Req_le; ring) ]. }
have Fdt : is_finite (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                             (Fast2Mult_err (BDIV xh y) y)) = true.
{ apply no_overflow_minus_is_finite; [ exact Fdh | exact Fpil' |].
  red. eapply Rle_lt_trans; [ apply round_abs_le_abs_plus_half_ulp |].
  apply (abst_fin _ _ _ (Rabs (FT2R xh)) (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 emin) 0 7 4);
    [ lra | lra | lra | lra | lra | lra | exact HΩ32 | exact Hxh4 | exact HW | exact He1
    | exact Hxhp | exact HW0 | exact He0
    | (eapply Rle_trans; [ exact Hdtarg_b |]; apply Req_le; ring)
    | exact (half_ulp_le _ Hp4 Hdtarg_lt) ]. }
have Hdt_e : FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y))
           = round radix2 fexp (Znearest choice)
               (FT2R (BMINUS xh (BMULT (BDIV xh y) y)) - FT2R (Fast2Mult_err (BDIV xh y) y))
  by rewrite BMINUS_round_correct.
have Hdt_b : Rabs (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)))
           <= Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 8 + bpow radix2 emin * 5.
{ rewrite Hdt_e.
  eapply Rle_trans.
  - apply (abst_round_step (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 (- fprec t))
             (bpow radix2 emin) (Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y))
                                        - FT2R (Fast2Mult_err (BDIV xh y) y))) _ 7 4);
      [ apply bpow_ge_0 | exact Hu16 | apply bpow_ge_0 | apply Rabs_pos | exact HW0
      | lra | lra | lra | lra
      | (eapply Rle_trans; [ exact Hdtarg_b |]; apply Req_le; ring)
      | exact (round_ub_emin (FT2R (BMINUS xh (BMULT (BDIV xh y) y))
                              - FT2R (Fast2Mult_err (BDIV xh y) y))) ].
  - apply Req_le; ring. }
(* ---- xl ---- *)
have Hxl_b : Rabs (FT2R xl) <= Rabs (FT2R xh) * (bpow radix2 (- fprec t)) + bpow radix2 emin.
{ have Hdwu := DW_acc_lemmas.dw_low_le_half_ulp xh xl Hdwp.
  have Hul := ulp_le_lin (FT2R xh).
  have Hb1p : bpow radix2 (1 - fprec t) = 2 * (bpow radix2 (- fprec t)).
  { replace (1 - fprec t)%Z with (1 + - fprec t)%Z by lia.
    rewrite bpow_plus. have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
  rewrite Hb1p in Hul.
  apply (abst_xl (Rabs (FT2R xh)) (bpow radix2 (- fprec t)) (bpow radix2 emin)
                 _ (ulp (FT2R xh)));
    [ apply bpow_ge_0 | exact Hdwu | exact Hul ]. }
(* ---- d = BPLUS dt xl ---- *)
have Hdarg_b : Rabs (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y))
                     + FT2R xl)
             <= Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 9 + bpow radix2 emin * 6.
{ apply Rle_trans with (Rabs (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)))
                        + Rabs (FT2R xl)).
  - apply Rabs_triang.
  - apply Rle_trans with (Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 8 + bpow radix2 emin * 5
                          + (Rabs (FT2R xh) * (bpow radix2 (- fprec t)) + bpow radix2 emin)).
    + apply Rplus_le_compat; [ exact Hdt_b | exact Hxl_b ].
    + apply Req_le; ring. }
have Hdarg_lt : Rabs (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                   (Fast2Mult_err (BDIV xh y) y)) + FT2R xl) < Omega.
{ apply (abst_lt_Om _ Omega (Rabs (FT2R xh)) (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 emin) 0 9 6);
    [ lra | lra | lra | lra | lra | lra | exact HΩ32 | exact Hxh4 | exact HW | exact He1
    | exact Hxhp | exact HW0 | exact He0
    | (eapply Rle_trans; [ exact Hdarg_b |]; apply Req_le; ring) ]. }
have Fd : is_finite (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                   (Fast2Mult_err (BDIV xh y) y)) xl) = true.
{ apply no_overflow_sum_is_finite; [ exact Fdt | exact Hfxl |].
  red. eapply Rle_lt_trans; [ apply round_abs_le_abs_plus_half_ulp |].
  apply (abst_fin _ _ _ (Rabs (FT2R xh)) (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 emin) 0 9 6);
    [ lra | lra | lra | lra | lra | lra | exact HΩ32 | exact Hxh4 | exact HW | exact He1
    | exact Hxhp | exact HW0 | exact He0
    | (eapply Rle_trans; [ exact Hdarg_b |]; apply Req_le; ring)
    | exact (half_ulp_le _ Hp4 Hdarg_lt) ]. }
have Hd_e : FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                (Fast2Mult_err (BDIV xh y) y)) xl)
          = round radix2 fexp (Znearest choice)
              (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y))
               + FT2R xl)
  by rewrite BPLUS_round_correct.
have Hd_b : Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                      (Fast2Mult_err (BDIV xh y) y)) xl))
          <= Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 10 + bpow radix2 emin * 7.
{ rewrite Hd_e.
  eapply Rle_trans.
  - apply (abst_round_step (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 (- fprec t))
             (bpow radix2 emin)
             (Rabs (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y))
                    + FT2R xl)) _ 9 6);
      [ apply bpow_ge_0 | exact Hu16 | apply bpow_ge_0 | apply Rabs_pos | exact HW0
      | lra | lra | lra | lra
      | (eapply Rle_trans; [ exact Hdarg_b |]; apply Req_le; ring)
      | exact (round_ub_emin
                 (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y))
                  + FT2R xl)) ].
  - apply Req_le; ring. }
have Hd_le_xh : Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                  (Fast2Mult_err (BDIV xh y) y)) xl)) <= Rabs (FT2R xh).
{ have Hemin_le : bpow radix2 emin
      <= Rabs (FT2R xh) * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t)).
  { have -> : bpow radix2 emin
            = bpow radix2 (emin + 2 * fprec t)
              * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t))
      by rewrite -!bpow_plus; f_equal; lia.
    apply Rmult_le_compat_r;
      [ apply Rmult_le_pos; apply bpow_ge_0
      | change (@common.emin t) with (SpecFloat.emin (fprec t) (femax t)); exact Hxhlb ]. }
  have Huu : bpow radix2 (- fprec t) * bpow radix2 (- fprec t)
             <= / 16 * bpow radix2 (- fprec t) by nra.
  eapply Rle_trans; [ exact Hd_b |]. nra. }
(* ---- |d/y| bound (residual scaling) ---- *)
have Hxhq : Rabs (FT2R xh) <= / 4 * Omega * Rabs (FT2R y).
{ have Heq : Rabs (FT2R xh) = Rabs (FT2R xh / FT2R y) * Rabs (FT2R y)
    by (rewrite -Rabs_mult; f_equal; field; exact Hyne).
  rewrite Heq -H4Ω. apply Rmult_le_compat_r; [ apply Rabs_pos | exact Hqub ]. }
have Hdy_b : Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                       (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
           <= 5 / 32 * Omega + 7.
{ rewrite Rabs_mult Rabs_inv.
  (* |d|/|y| <= (10|xh|(bpow radix2 (- fprec t)) + 7 2^emin)/|y| <= 10(Omega/4)(bpow radix2 (- fprec t)) + 7 *)
  apply Rle_trans with ((Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 10 + bpow radix2 emin * 7) * / Rabs (FT2R y)).
  { apply Rmult_le_compat_r; [ apply Rlt_le, Rinv_0_lt_compat; exact HYpos | exact Hd_b ]. }
  (* multiply through: use |xh| <= Omega/4 |y| and 2^emin <= |y| *)
  apply (Rmult_le_reg_r (Rabs (FT2R y)) _ _ HYpos).
  rewrite Rmult_assoc Rinv_l; [ rewrite Rmult_1_r | lra ].
  (* goal: (10|xh|(bpow radix2 (- fprec t)) + 7 2^emin) <= (5/32 Omega + 7)|y| *)
  have H1 : Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 10 <= 5 / 32 * Omega * Rabs (FT2R y).
  { apply (abst_H1 _ Omega (Rabs (FT2R y)) (bpow radix2 (- fprec t)));
      [ apply bpow_ge_0 | apply Rabs_pos | exact Hu0 | exact Hu16 |].
    apply Rmult_le_compat_r; [ lra | apply Rmult_le_compat_r; [ exact Hu0 | exact Hxhq ] ]. }
  have H2 : bpow radix2 emin * 7 <= 7 * Rabs (FT2R y).
  { rewrite Rmult_comm. apply Rmult_le_compat_l; [ lra | exact HYe ]. }
  eapply Rle_trans; [ apply Rplus_le_compat; [ exact H1 | exact H2 ] |].
  apply Req_le; ring. }
have Hdy_lt : Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                        (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y) < Omega.
{ apply (abst_dy_lt _ Omega); [ exact HΩ32 | exact Hdy_b ]. }
have Ftl : is_finite (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                          (Fast2Mult_err (BDIV xh y) y)) xl) y) = true.
{ apply (no_overflow_div_is_finite t _ y Fd Hyne).
  eapply Rle_lt_trans; [ apply round_abs_le_abs_plus_half_ulp |].
  apply (abst_fin_dy _ _ Omega);
    [ exact HΩ32 | exact Hdy_b | exact (half_ulp_le _ Hp4 Hdy_lt) ]. }
(* ---- closing Fast2Sum: fst (DWDivFP3 xh xl y) = BPLUS th tl ---- *)
have Hth_r : round radix2 fexp (Znearest choice) (FT2R xh / FT2R y) = FT2R (BDIV xh y)
  by apply (BDIV_round_correct t xh y Hyne Fth).
have Htl_r : round radix2 fexp (Znearest choice)
               (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                    (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
           = FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                       (Fast2Mult_err (BDIV xh y) y)) xl) y)
  by apply (BDIV_round_correct t _ y Hyne Ftl).
have Hxhy4 : Rabs (FT2R xh / FT2R y) <= / 4 * Omega by (rewrite -H4Ω; exact Hqub).
have Hthv : Rabs (FT2R (BDIV xh y))
          <= Rabs (FT2R xh / FT2R y) + Rabs (FT2R xh / FT2R y) * bpow radix2 (- fprec t)
             + / 2 * bpow radix2 emin
  by (rewrite -Hth_r; apply round_ub_emin).
have Htlv : Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                    (Fast2Mult_err (BDIV xh y) y)) xl) y))
          <= Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                       (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
             + Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                         (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
               * bpow radix2 (- fprec t)
             + / 2 * bpow radix2 emin
  by (rewrite -Htl_r; apply round_ub_emin).
have Hsum_le : Rabs (FT2R (BDIV xh y)
                     + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                         (Fast2Mult_err (BDIV xh y) y)) xl) y))
             <= (Rabs (FT2R xh / FT2R y) + Rabs (FT2R xh / FT2R y) * bpow radix2 (- fprec t)
                 + / 2 * bpow radix2 emin)
              + (Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                    (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
                 + Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                     (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
                   * bpow radix2 (- fprec t)
                 + / 2 * bpow radix2 emin).
{ eapply Rle_trans; [ apply Rabs_triang |].
  apply Rplus_le_compat; [ exact Hthv | exact Htlv ]. }
have Hsum_lt : Rabs (FT2R (BDIV xh y)
                     + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                         (Fast2Mult_err (BDIV xh y) y)) xl) y)) < Omega.
{ apply (abst_fst_sum _ (Rabs (FT2R xh / FT2R y))
           (Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                              (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y))
           Omega (bpow radix2 (- fprec t)) (bpow radix2 emin));
    [ apply bpow_ge_0 | exact Hu16 | apply bpow_ge_0 | exact He1 | exact HΩ32
    | apply Rabs_pos | exact Hxhy4 | apply Rabs_pos | exact Hdy_b | exact Hsum_le ]. }
have Hfp : is_finite (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) = true.
{
apply no_overflow_sum_is_finite; [ exact Fth | exact Ftl |].
eapply Rle_lt_trans; [ apply round_abs_le_abs_plus_half_ulp |].
apply (abst_fst_fin _ _ (Rabs (FT2R xh / FT2R y))
         (Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                            (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y))
         Omega (bpow radix2 (- fprec t)) (bpow radix2 emin));
  [ apply bpow_ge_0 | exact Hu16 | apply bpow_ge_0 | exact He1 | exact HΩ32
  | apply Rabs_pos | exact Hxhy4 | apply Rabs_pos | exact Hdy_b
  | exact Hsum_le | exact (half_ulp_le _ Hp4 Hsum_lt) ].
}
have Hthb : Rabs (FT2R (BDIV xh y)) <= / 2 * Omega.
{ eapply Rle_trans; [ exact Hthv |].
  apply (abst_th_half (Rabs (FT2R xh / FT2R y)) (bpow radix2 (- fprec t)) (bpow radix2 emin) Omega);
    [ apply Rabs_pos | exact Hxhy4 | apply bpow_ge_0 | exact Hu16 | apply bpow_ge_0 | exact He1 | exact HΩ32 ]. }
have Htlb : Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) <= / 2 * Omega.
{ eapply Rle_trans; [ exact Htlv |].
  apply (abst_tl_half (Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)) (bpow radix2 (- fprec t)) (bpow radix2 emin) Omega);
    [ apply Rabs_pos | exact Hdy_b | apply bpow_ge_0 | exact Hu16 | apply bpow_ge_0 | exact He1 | exact HΩ32 ]. }
split; [ exact Fth | split; [ exact Ftl | split; [ exact Hfp | split; [ exact Hthb
  | split; [ exact Htlb | split; [ exact Hsum_lt | exact Hd_le_xh ]]]]]].
Qed.

Lemma DWDivFP3_fst_finite_acc (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_normal_quotient_input_cond xh xl y ->
  is_finite (fst (DWDivFP3 xh xl y)) = true.
Proof.
intros Hp4 COND.
have Hfstred : fst (DWDivFP3 xh xl y)
             = BPLUS (BDIV xh y)
                 (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                              (Fast2Mult_err (BDIV xh y) y)) xl) y)
  by rewrite /DWDivFP3 /Fast2Mult_err /Fast2Mult /Fast2Sum //=.
rewrite Hfstred.
exact (proj1 (proj2 (proj2 (DWDivFP3_cascade_acc xh xl y Hp4 COND)))).
Qed.

(* Finiteness of snd (DWDivFP3): the closing Fast2Sum's snd needs the ulp
   ordering ulp(tl) <= ulp(th) (or th = 0), from the double-word relation of the
   result (|tl| <= ulp(th)), then is_finite_FastSum_ulp. *)
Lemma DWDivFP3_snd_finite_acc (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_normal_quotient_input_cond xh xl y ->
  is_finite (snd (DWDivFP3 xh xl y)) = true.
Proof.
intros Hp4 COND.
destruct (DWDivFP3_cascade_acc xh xl y Hp4 COND) as (Fth & Ftl & Hfp & Hthb & Htlb & Hsum_lt & _).
have HΩ32 : 32 <= Omega.
{ have -> : (32 = bpow radix2 5)%R by (simpl; lra).
  apply bpow_le; pose proof (fprec_lt_femax t); lia. }
have Hsndred : snd (DWDivFP3 xh xl y)
             = BMINUS (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y) (BMINUS (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) (BDIV xh y))
  by rewrite /DWDivFP3 /Fast2Mult_err /Fast2Mult /Fast2Sum //=.
rewrite Hsndred.
have Hs_r : round radix2 fexp (Znearest choice) (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) = FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y))
  by (rewrite (BPLUS_round_correct t (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y) Hfp)).
(* z = BMINUS (BPLUS th tl) th is finite *)
have Herr : Rabs (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)) <= / 2 * ulp (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) + Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)).
{ rewrite -Hs_r.
  apply Rle_trans with (Rabs (round radix2 fexp (Znearest choice) (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y))) + Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y))).
  - have -> : round radix2 fexp (Znearest choice) (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)
            = (round radix2 fexp (Znearest choice) (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y))) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y) by ring.
    apply Rabs_triang.
  - apply Rplus_le_compat_r. exact (@error_le_half_ulp radix2 fexp valid_fexp_inst_div choice (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y))). }
have HU1 : / 2 * ulp (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) <= / 16 * Omega by exact (half_ulp_le _ Hp4 Hsum_lt).
have Hd_lt : Rabs (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)) < Omega.
{ apply Rle_lt_trans with (/ 16 * Omega + / 2 * Omega); [| lra ].
  eapply Rle_trans; [ exact Herr |]. apply Rplus_le_compat; [ exact HU1 | exact Htlb ]. }
have Fz : is_finite (BMINUS (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) (BDIV xh y)) = true.
{ apply no_overflow_minus_is_finite; [ exact Hfp | exact Fth |].
  red. eapply Rle_lt_trans; [ apply round_abs_le_abs_plus_half_ulp |].
  apply (abst_z _ (/ 2 * ulp (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y))) (/ 2 * ulp (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y))) (Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y))) Omega);
    [ exact HΩ32 | exact HU1 | exact Htlb | exact (half_ulp_le _ Hp4 Hd_lt) | exact Herr ]. }
have Hz_r : round radix2 fexp (Znearest choice) (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)) = FT2R (BMINUS (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) (BDIV xh y))
  by (rewrite (BMINUS_round_correct t (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) (BDIV xh y) Fz)).
have Htlz : Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y) - FT2R (BMINUS (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) (BDIV xh y))) <= / 2 * ulp (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) + / 2 * ulp (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)).
{ rewrite -Hz_r.
  apply Rle_trans with (Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y) - (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y))) + Rabs ((FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)) - round radix2 fexp (Znearest choice) (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)))).
  - have -> : FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y) - round radix2 fexp (Znearest choice) (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)) = (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y) - (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y))) + ((FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)) - round radix2 fexp (Znearest choice) (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y))) by ring.
    apply Rabs_triang.
  - apply Rplus_le_compat.
    + rewrite -Hs_r.
      have -> : FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y) - (round radix2 fexp (Znearest choice) (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y))
              = - (round radix2 fexp (Znearest choice) (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y))) by ring.
      rewrite Rabs_Ropp. exact (@error_le_half_ulp radix2 fexp valid_fexp_inst_div choice (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y))).
    + have -> : (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)) - round radix2 fexp (Znearest choice) (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)) = - (round radix2 fexp (Znearest choice) (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)) - (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y))) by ring.
      rewrite Rabs_Ropp. exact (@error_le_half_ulp radix2 fexp valid_fexp_inst_div choice (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y))). }
have Htlz_lt : Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y) - FT2R (BMINUS (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) (BDIV xh y))) < Omega.
{ apply Rle_lt_trans with (/ 16 * Omega + / 16 * Omega); [| lra ].
  eapply Rle_trans; [ exact Htlz |].
  apply Rplus_le_compat; [ exact HU1 | exact (half_ulp_le _ Hp4 Hd_lt) ]. }
apply no_overflow_minus_is_finite; [ exact Ftl | exact Fz |].
red. eapply Rle_lt_trans; [ apply round_abs_le_abs_plus_half_ulp |].
apply (abst_snd _ (/ 2 * ulp (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y))) (/ 2 * ulp (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)))
            (/ 2 * ulp (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y) - FT2R (BMINUS (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) (BDIV xh y)))) Omega);
  [ exact HΩ32 | exact HU1 | exact (half_ulp_le _ Hp4 Hd_lt)
  | exact (half_ulp_le _ Hp4 Htlz_lt) | exact Htlz ].
Qed.

(* The strong cond implies the normal-quotient helper
   (DWDivFP_normal_quotient_input_cond_of_relative_error_input_cond), so the
   finiteness results hold under it too.  These keep the names the file's public
   interface advertises; the widened-domain versions are the _acc ones above. *)
Lemma DWDivFP3_fst_finite (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_relative_error_input_cond xh xl y ->
  is_finite (fst (DWDivFP3 xh xl y)) = true.
Proof.
intros Hp4 H.
exact (DWDivFP3_fst_finite_acc xh xl y Hp4
         (DWDivFP_normal_quotient_input_cond_of_relative_error_input_cond xh xl y H)).
Qed.

Lemma DWDivFP3_snd_finite (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_relative_error_input_cond xh xl y ->
  is_finite (snd (DWDivFP3 xh xl y)) = true.
Proof.
intros Hp4 H.
exact (DWDivFP3_snd_finite_acc xh xl y Hp4
         (DWDivFP_normal_quotient_input_cond_of_relative_error_input_cond xh xl y H)).
Qed.

(* DWDivFP_normal_quotient_input_cond proves the ordering |tl| <= |th|:
   |d| <= |xh| (cascade) lifts
   through division by the fixed y (round monotone, |RN z| = RN|z|).  Uniform --
   no normal/underflow split, no per-node underflow hypotheses. *)
Lemma DWDivFP3_ordering_acc (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_normal_quotient_input_cond xh xl y ->
  Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                          (Fast2Mult_err (BDIV xh y) y)) xl) y))
    <= Rabs (FT2R (BDIV xh y)).
Proof.
intros Hp4 COND.
destruct (DWDivFP3_cascade_acc xh xl y Hp4 COND)
  as (Fth & Ftl & _ & _ & _ & _ & Hd_le_xh).
have Hyne : FT2R y <> 0.
{ move: COND => [_ [_ [_ [_ [Hquot _]]]]].
  intro H0. have Hp := bpow_gt_0 radix2 (SpecFloat.emin (fprec t) (femax t) + fprec t - 1).
  move: Hquot; rewrite H0 /Rdiv Rinv_0 Rmult_0_r Rabs_R0 => Hc. lra. }
set d := BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
               (Fast2Mult_err (BDIV xh y) y)) xl.
rewrite -(BDIV_round_correct t xh y Hyne Fth) -(BDIV_round_correct t d y Hyne Ftl).
rewrite -!round_NE_abs.
apply round_le; [ apply FLT.FLT_exp_valid, fprec_gt_0 | apply valid_rnd_N |].
rewrite !Rabs_mult.
apply Rmult_le_compat_r; [ apply Rabs_pos | exact Hd_le_xh ].
Qed.

(* Both simplified conditions discharged from the cond -> result is a DW.
   Output double-word closure survives the relaxation: it needs only that the
   closing Fast2Sum preserves its sum, i.e. the ordering above, which is uniform
   in the regime. *)
Corollary DWDivFP3_is_DW_from_cond_acc (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_normal_quotient_input_cond xh xl y ->
  double_word_prop (fst (DWDivFP3 xh xl y)) (snd (DWDivFP3 xh xl y)).
Proof.
intros Hp4 COND.
apply DWDivFP3_is_DW.
- exact (proj1 (proj2 (proj2 (DWDivFP3_cascade_acc xh xl y Hp4 COND)))).
- exact (DWDivFP3_ordering_acc xh xl y Hp4 COND).
Qed.

Corollary DWDivFP3_is_DW_from_cond (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_relative_error_input_cond xh xl y ->
  double_word_prop (fst (DWDivFP3 xh xl y)) (snd (DWDivFP3 xh xl y)).
Proof.
intros Hp4 H.
exact (DWDivFP3_is_DW_from_cond_acc xh xl y Hp4
         (DWDivFP_normal_quotient_input_cond_of_relative_error_input_cond xh xl y H)).
Qed.

(* The intermediate normal-range (strong-underflow) facts consumed by the
   Layer-1 theorem, derived from the cond's quotient underflow bound.  These are
   the division analog of the "|w| normal" side conditions in the multiplication
   development; each says a specific rounded node stays in the normal range. *)

(* PROVEN: the product node th*y ~ xh stays above the TwoProd-exactness threshold
   emin+2p-1.  Since |th*y| >= |xh|(1-u) (thy_residual) and the cond bounds
   |xh| >= bpow(emin+2p), and 1-u >= 1/2, we get |th*y| >= bpow(emin+2p)/2 =
   bpow(emin+2p-1).  This is why bridge_prod now uses Fast2Mult_correct_weak. *)
Lemma cond_UF_prod_acc (xh xl y : ftype t) :
  DWDivFP_normal_quotient_input_cond xh xl y ->
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R (BDIV xh y) * FT2R y).
Proof.
move => [Hfxh [Hfxl [Hfy [Hdwp [Hquot [Hxhb [Hqub Hxhlb]]]]]]].
have Hyne : FT2R y <> 0.
{ intro H0.
  have Hp := bpow_gt_0 radix2 (SpecFloat.emin (fprec t) (femax t) + fprec t - 1).
  move: Hquot; rewrite H0 /Rdiv Rinv_0 Rmult_0_r Rabs_R0 => Hc. lra. }
have Hfth : is_finite (BDIV xh y) = true
  by apply th_finite; [ exact Hfxh | exact Hyne | exact Hqub ].
have Hqn : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xh / FT2R y).
{ unfold common.emin. exact Hquot. }
have Hres := thy_residual xh y Hfth Hyne Hqn.
have HX0 : 0 <= Rabs (FT2R xh) by apply Rabs_pos.
have Hu2 : bpow radix2 (- fprec t) <= /2.
{ have H3 : bpow radix2 (1 - fprec t) = 2 * bpow radix2 (- fprec t).
  { replace (1 - fprec t)%Z with (1 + - fprec t)%Z by lia.
    rewrite bpow_plus. have -> : bpow radix2 1 = 2 by reflexivity. ring. }
  have H2 : bpow radix2 (1 - fprec t) <= 1.
  { have -> : (1:R) = bpow radix2 0 by reflexivity.
    apply bpow_le. pose proof (fprec_gt_one t). lia. }
  lra. }
have HRX : Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh) <= Rabs (FT2R xh) * /2.
{ eapply Rle_trans; [ exact Hres |].
  apply Rmult_le_compat_l; [ exact HX0 | exact Hu2 ]. }
have HP : Rabs (FT2R xh) - Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh)
          <= Rabs (FT2R (BDIV xh y) * FT2R y).
{ have Hpre : Rabs (FT2R xh) - Rabs (FT2R (BDIV xh y) * FT2R y)
              <= Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh).
  { rewrite (Rabs_minus_sym (FT2R (BDIV xh y) * FT2R y) (FT2R xh)).
    exact (Rabs_triang_inv (FT2R xh) (FT2R (BDIV xh y) * FT2R y)). }
  exact (abst_revtri _ _ _ Hpre). }
have HB : bpow radix2 (emin + 2 * fprec t - 1) = /2 * bpow radix2 (emin + 2 * fprec t).
{ set k := (emin + 2 * fprec t - 1)%Z.
  have -> : (emin + 2 * fprec t = k + 1)%Z by (unfold k; lia).
  rewrite bpow_plus. have -> : bpow radix2 1 = 2 by reflexivity. field. }
rewrite HB.
apply (abst_prod_lb (Rabs (FT2R (BDIV xh y) * FT2R y))
        (Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh)) (Rabs (FT2R xh))
        (bpow radix2 (emin + 2 * fprec t)));
  [ exact HRX | exact HP | exact Hxhlb ].
Qed.

(* cond_UF_dh removed: dh = xh - pih is exact by Sterbenz (bridge_dh).
   cond_UF_dt removed: dt = dh - pil is exact by a magnitude case split
   (bridge_dt) -- large residual lifts FLX->FLT, small residual is exact by
   Hauser's FLT_format_plus_small -- so the dt node needs no normal-range fact.
   cond_UF_tl is NOT derivable from the cond: it lower-bounds |d/y| where d is the
   division residual, which is 0 for exact division -- no input condition can force
   it.  It is therefore the split line of the case-split theorem: the normal leg
   (|d/y| normal) assumes it and gets 3u^2; the underflow leg (|d/y| subnormal)
   drops it and pays the single-node tl perturbation bounded by round_FLT_FLX_diff. *)

End DWDivFP_Finite.

(* ============================================================
   NORMAL-RANGE PURE RELATIVE TIER, part 1: the normal leg.

   The sharp 3u^2 bound under DWDivFP_normal_quotient_input_cond, in the regime
   where the closing correction d/y also stays in the FLT normal range.
   double_word, y <> 0, the leading-quotient normal-range bound (UF_th) and the
   product node (UF_prod) are derived here from the cond; is_finite_p from the
   DWDivFP_Finite lemmas.  The one thing the cond cannot supply -- |d/y| normal
   (UF_tl) -- is taken as the explicit hypothesis Hdyn: d is 0 for exact
   division, so it genuinely characterises the normal regime rather than
   following from the inputs.  DDConds.DWDivFP_normal is the caller-facing
   packaging of Hdyn together with that exact-division disjunct.
   ============================================================ *)
Section CondAccuracyDWDivFP.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (@common.emin t).
Notation u := (bpow radix2 (- fprec t)).

Variables (xh xl y : ftype t).

Hypothesis Hp4 : (4 <= fprec t)%Z.
Hypothesis COND : DWDivFP_normal_quotient_input_cond xh xl y.
Hypothesis Hdyn : bpow radix2 (emin + fprec t - 1)
  <= Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                               (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y).

Local Theorem DWDivFP3_relative_accuracy_normal_quotient :
  relative_error_DWDivFP xh xl y <= 3 * u ^ 2.
Proof.
have Hfp : is_finite_p (DWDivFP3 xh xl y).
{ split;
    [ exact (DWDivFP3_fst_finite_acc xh xl y Hp4 COND)
    | exact (DWDivFP3_snd_finite_acc xh xl y Hp4 COND) ]. }
move: (COND) => [Hfxh [Hfxl [Hfy [Hdwp [Hquot [Hxhb [Hqub _]]]]]]].
have Hyne : FT2R y <> 0.
{ intro H0.
  have Hp := bpow_gt_0 radix2 (SpecFloat.emin (fprec t) (femax t) + fprec t - 1).
  move: Hquot; rewrite H0 /Rdiv Rinv_0 Rmult_0_r Rabs_R0 => Hc.
  lra. }
have Uth : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xh / FT2R y).
{ unfold common.emin. exact Hquot. }
exact (relative_errorDWDivFP3_correct xh xl y Hdwp Hfp Hp4 Hyne
         Uth (cond_UF_prod_acc xh xl y COND) Hdyn).
Qed.

End CondAccuracyDWDivFP.

(* ============================================================
   WHOLE-RANGE MIXED TIER, part 1: the underflow leg, with the single-node
   perturbation left SYMBOLIC.

   When the closing correction d/y is subnormal, the runtime diverges from the
   FLX model at exactly one node, tl = round(d/y).  Every other node matches
   the FLX model (th via UF_th, the product via cond_UF_prod_acc, dt exact, d
   via the underflow-insensitive BPLUS), so the result carries the paper's
   3u^2 relative error plus that single divergence.

   Keeping the divergence symbolic instead of immediately charging it at one
   floor ulp is what lets the two tiers share this proof:

     - the MIXED tier bounds it by 2^emin (round_FLT_FLX_diff, packaged as
       DWDivFP3_tl_perturbation_le_eta below);
     - the exact-division case of the RELATIVE tier observes that it is
       exactly ZERO, since both roundings are applied to 0.
   ============================================================ *)
Section CondAccuracyDWDivFP_underflow.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (@common.emin t).
Notation u := (bpow radix2 (- fprec t)).

Variables (xh xl y : ftype t).

Hypothesis Hp4 : (4 <= fprec t)%Z.
Hypothesis COND : DWDivFP_normal_quotient_input_cond xh xl y.
Hypothesis Huf : Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                          (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
                 < bpow radix2 (emin + fprec t - 1).

Local Instance vfe_uf : Generic_fmt.Valid_exp (SpecFloat.fexp (fprec t) (femax t)).
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.
Local Instance vfe_flt : Generic_fmt.Valid_exp
  (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t)).
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.
Local Instance vflx_uf : Generic_fmt.Valid_exp (FLX_exp (fprec t)).
Proof. apply FLX.FLX_exp_valid, fprec_gt_0. Qed.

Local Theorem DWDivFP3_error_underflow_perturbation :
  Rabs (FT2R (fst (DWDivFP3 xh xl y)) + FT2R (snd (DWDivFP3 xh xl y))
        - (FT2R xh + FT2R xl) / FT2R y)
    <= 3 * u ^ 2 * Rabs ((FT2R xh + FT2R xl) / FT2R y)
       + Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                         (Fast2Mult_err (BDIV xh y) y)) xl) y)
               - round radix2 (FLX_exp (fprec t)) (Znearest choice)
                   (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                        (Fast2Mult_err (BDIV xh y) y)) xl)
                    / FT2R y)).
Proof.
set d := BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                       (Fast2Mult_err (BDIV xh y) y)) xl.
have Hfp : is_finite_p (DWDivFP3 xh xl y)
  by split; [ exact (DWDivFP3_fst_finite_acc xh xl y Hp4 COND)
            | exact (DWDivFP3_snd_finite_acc xh xl y Hp4 COND) ].
move: (COND) => [Hfxh [Hfxl [Hfy [Hdwp [Hquot [Hxhb [Hqub Hxhlb]]]]]]].
have Hyne : FT2R y <> 0.
{ intro H0. have Hp := bpow_gt_0 radix2 (SpecFloat.emin (fprec t) (femax t) + fprec t - 1).
  move: Hquot; rewrite H0 /Rdiv Rinv_0 Rmult_0_r Rabs_R0 => Hc. lra. }
have Uth : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xh / FT2R y).
{ unfold common.emin. exact Hquot. }
have UFprod : bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R (BDIV xh y) * FT2R y)
  by exact (cond_UF_prod_acc xh xl y COND).
have HFy : generic_format radix2 (FLX_exp (fprec t)) (FT2R y)
  by (apply (generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t));
      apply generic_format_FLT_FT2R).
have HDWx : DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl)
  by (apply (dw_word_DWdouble xh xl y); exact Hdwp).
(* FLX-format facts and the two roundings of v0 = d/y *)
set v0 := (FT2R d / FT2R y).
have Fth : generic_format radix2 (FLX_exp (fprec t)) (FT2R (BDIV xh y))
  by (apply (generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t));
      apply generic_format_FLT_FT2R).
have Ftls : generic_format radix2 (FLX_exp (fprec t))
              (round radix2 (FLX_exp (fprec t)) (Znearest choice) v0).
{ apply generic_format_round; typeclasses eauto. }
have Ftl : generic_format radix2 (FLX_exp (fprec t)) (FT2R (BDIV d y))
  by (apply (generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t));
      apply generic_format_FLT_FT2R).
(* |FT2R th| is >= bpow(emin+p-1); both roundings of v0 are <= bpow(emin+p-1).
   These two meet exactly at emin+p-1, which is why that exponent is the floor of
   the whole construction: Hord_p / Hord_r below are tight there. *)
have Fbnd_lo_flx : generic_format radix2 (FLX_exp (fprec t))
                 (bpow radix2 (emin + fprec t - 1)).
{ apply generic_format_bpow. unfold FLX_exp, common.emin. pose proof (fprec_gt_one t). lia. }
have Fbnd_lo_flt : generic_format radix2 (SpecFloat.fexp (fprec t) (femax t))
                 (bpow radix2 (emin + fprec t - 1)).
{ apply generic_format_bpow. unfold SpecFloat.fexp, common.emin. pose proof (fprec_gt_one t). lia. }
have Hth_gelo : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R (BDIV xh y)).
{ rewrite -(BDIV_round_correct t xh y Hyne (FINth xh xl y Hfp)).
  apply abs_round_ge_generic;
    first [ exact Fbnd_lo_flt | exact Fbnd_lo_flx
          | (unfold common.emin; exact Hquot)
          | exact vfe_flt | apply valid_rnd_N | typeclasses eauto ]. }
have Htls_le : Rabs (round radix2 (FLX_exp (fprec t)) (Znearest choice) v0)
               <= bpow radix2 (emin + fprec t - 1).
{ apply abs_round_le_generic;
    first [ exact Fbnd_lo_flx | (apply Rlt_le; exact Huf) | exact vflx_uf | apply valid_rnd_N ]. }
have Htl_le : Rabs (FT2R (BDIV d y)) <= bpow radix2 (emin + fprec t - 1).
{ rewrite -(BDIV_round_correct t d y Hyne (FINtl xh xl y Hfp)).
  apply abs_round_le_generic;
    first [ exact Fbnd_lo_flt | (apply Rlt_le; exact Huf) | exact vfe_flt | apply valid_rnd_N ]. }
have Hord_p : Rabs (round radix2 (FLX_exp (fprec t)) (Znearest choice) v0)
              <= Rabs (FT2R (BDIV xh y)) by (eapply Rle_trans; [ exact Htls_le | exact Hth_gelo ]).
have Hord_r : Rabs (FT2R (BDIV d y)) <= Rabs (FT2R (BDIV xh y))
  by (eapply Rle_trans; [ exact Htl_le | exact Hth_gelo ]).
(* paper bound *)
pose proof (@DWDFP3_correct (fprec t) (fprec_gt_one t) choice eq_refl
              (FT2R xh) (FT2R xl) (FT2R y) HDWx HFy Hp4 Hyne) as Hpaper.
rewrite (paper_reduced xh xl y Hfp Hp4 Hyne Uth UFprod) in Hpaper.
move: Hpaper.
case Ep : (F2Sum.Fast2Sum (fprec t) choice (FT2R (BDIV xh y))
             (round radix2 (FLX_exp (fprec t)) (Znearest choice) v0)) => [zhp zlp].
move => Hpaper.
(* paper sum = th + round_FLX(v0) *)
have Hsum_p : zhp + zlp = FT2R (BDIV xh y)
              + round radix2 (FLX_exp (fprec t)) (Znearest choice) v0.
{ have Hs := flx_f2s_sum (FT2R (BDIV xh y))
              (round radix2 (FLX_exp (fprec t)) (Znearest choice) v0) Fth Ftls Hord_p.
  rewrite Ep /= in Hs. exact Hs. }
(* runtime sum = th + tl *)
have Hrun : F2Sum.Fast2Sum (fprec t) choice (FT2R (BDIV xh y)) (FT2R (BDIV d y))
            = F2Rp (DDModels.Fast2Sum (BDIV xh y) (BDIV d y)).
{ apply (FastTwoSumEq_FLT (BDIV xh y) (BDIV d y)). exact Hfp. }
have Hsum_r : FT2R (fst (DWDivFP3 xh xl y)) + FT2R (snd (DWDivFP3 xh xl y))
              = FT2R (BDIV xh y) + FT2R (BDIV d y).
{ have Hs := flx_f2s_sum (FT2R (BDIV xh y)) (FT2R (BDIV d y)) Fth Ftl Hord_r.
  have Heqr : DWDivFP3 xh xl y = DDModels.Fast2Sum (BDIV xh y) (BDIV d y)
    by rewrite /DWDivFP3 /Fast2Mult_err /Fast2Mult /Fast2Sum //=.
  rewrite Hrun /F2Rp /= in Hs. rewrite Heqr. exact Hs. }
(* the single-node divergence, left symbolic *)
have Hdiff : Rabs ((FT2R (fst (DWDivFP3 xh xl y)) + FT2R (snd (DWDivFP3 xh xl y)))
                   - (zhp + zlp))
             <= Rabs (FT2R (BDIV d y)
                      - round radix2 (FLX_exp (fprec t)) (Znearest choice) v0).
{ have -> : (FT2R (fst (DWDivFP3 xh xl y)) + FT2R (snd (DWDivFP3 xh xl y))) - (zhp + zlp)
           = FT2R (BDIV d y)
             - round radix2 (FLX_exp (fprec t)) (Znearest choice) v0
    by rewrite Hsum_r Hsum_p; ring.
  apply Rle_refl. }
(* convert paper relative bound to absolute *)
have Hxhne : FT2R xh <> 0.
{ intro Hx0. move: Uth; rewrite Hx0 /Rdiv Rmult_0_l Rabs_R0 => Hc.
  have := bpow_gt_0 radix2 (emin + fprec t - 1). lra. }
have Hsne : FT2R xh + FT2R xl <> 0.
{ intro Hs0. apply Hxhne. move: Hdwp; rewrite /double_word_prop Hs0.
  rewrite /rounded round_0 //. }
have Hpabs : Rabs (zhp + zlp - (FT2R xh + FT2R xl) / FT2R y)
             <= 3 * u ^ 2 * Rabs ((FT2R xh + FT2R xl) / FT2R y).
{ have Hconv : Rabs (zhp + zlp - (FT2R xh + FT2R xl) / FT2R y)
             = Rabs ((zhp + zlp - (FT2R xh + FT2R xl) / FT2R y)
                     / ((FT2R xh + FT2R xl) / FT2R y))
               * Rabs ((FT2R xh + FT2R xl) / FT2R y).
  { rewrite -Rabs_mult. f_equal. field. split; [ exact Hyne | exact Hsne ]. }
  rewrite Hconv.
  have Hupow : 3 * u ^ 2 = 3 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t))
    by (rewrite /=; ring).
  apply Rmult_le_compat_r; [ apply Rabs_pos |].
  rewrite Hupow. exact Hpaper. }
(* triangle *)
eapply Rle_trans with
  (Rabs ((FT2R (fst (DWDivFP3 xh xl y)) + FT2R (snd (DWDivFP3 xh xl y))) - (zhp + zlp))
   + Rabs (zhp + zlp - (FT2R xh + FT2R xl) / FT2R y)).
{ have -> : FT2R (fst (DWDivFP3 xh xl y)) + FT2R (snd (DWDivFP3 xh xl y))
            - (FT2R xh + FT2R xl) / FT2R y
          = ((FT2R (fst (DWDivFP3 xh xl y)) + FT2R (snd (DWDivFP3 xh xl y))) - (zhp + zlp))
            + (zhp + zlp - (FT2R xh + FT2R xl) / FT2R y) by ring.
  apply Rabs_triang. }
rewrite Rplus_comm. apply Rplus_le_compat; [ exact Hpabs | exact Hdiff ].
Qed.

End CondAccuracyDWDivFP_underflow.

(* The MIXED tier's charge for the tl node: FLT and FLX rounding of the same
   real differ by at most one floor ulp (round_FLT_FLX_diff). *)
Local Lemma DWDivFP3_tl_perturbation_le_eta
  {NANS: Nans} {t : type} {STD: is_standard t}
  (xh xl y : ftype t)
  (Hp4 : (4 <= fprec t)%Z)
  (COND : DWDivFP_normal_quotient_input_cond xh xl y) :
  Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                  (Fast2Mult_err (BDIV xh y) y)) xl) y)
        - round radix2 (FLX_exp (fprec t)) (Znearest choice)
            (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                 (Fast2Mult_err (BDIV xh y) y)) xl)
             / FT2R y))
    <= bpow radix2 (@common.emin t).
Proof.
have Hfp : is_finite_p (DWDivFP3 xh xl y)
  by split; [ exact (DWDivFP3_fst_finite_acc xh xl y Hp4 COND)
            | exact (DWDivFP3_snd_finite_acc xh xl y Hp4 COND) ].
move: (COND) => [Hfxh [Hfxl [Hfy [Hdwp [Hquot _]]]]].
have Hyne : FT2R y <> 0.
{ intro H0. have Hp := bpow_gt_0 radix2 (SpecFloat.emin (fprec t) (femax t) + fprec t - 1).
  move: Hquot; rewrite H0 /Rdiv Rinv_0 Rmult_0_r Rabs_R0 => Hc. lra. }
have Htl_r : FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                       (Fast2Mult_err (BDIV xh y) y)) xl) y)
             = round radix2 (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
                 (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                      (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
  by rewrite (BDIV_round_correct t _ y Hyne (FINtl xh xl y Hfp)).
rewrite Htl_r. exact (round_FLT_FLX_diff _).
Qed.

(* The exact-division case: the correction d is zero, so BOTH roundings at the
   tl node are applied to 0 and the perturbation vanishes identically.  This is
   the disjunct DDConds.DWDivFP_normal keeps alongside "d/y is normal", and it
   is why the relative tier does not have to exclude exact divisions. *)
Local Lemma DWDivFP3_error_exact_division
  {NANS: Nans} {t : type} {STD: is_standard t}
  (xh xl y : ftype t)
  (Hp4 : (4 <= fprec t)%Z)
  (COND : DWDivFP_normal_quotient_input_cond xh xl y)
  (Hd0 : FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                             (Fast2Mult_err (BDIV xh y) y)) xl) = 0) :
  Rabs (FT2R (fst (DWDivFP3 xh xl y)) + FT2R (snd (DWDivFP3 xh xl y))
        - (FT2R xh + FT2R xl) / FT2R y)
    <= 3 * (bpow radix2 (- fprec t)) ^ 2
       * Rabs ((FT2R xh + FT2R xl) / FT2R y).
Proof.
have Hv0 : FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                               (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y = 0
  by rewrite Hd0 /Rdiv Rmult_0_l.
have Huf : Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                     (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
           < bpow radix2 (@common.emin t + fprec t - 1)
  by rewrite Hv0 Rabs_R0; apply bpow_gt_0.
have Habs := DWDivFP3_error_underflow_perturbation xh xl y Hp4 COND Huf.
have Hfp : is_finite_p (DWDivFP3 xh xl y)
  by split; [ exact (DWDivFP3_fst_finite_acc xh xl y Hp4 COND)
            | exact (DWDivFP3_snd_finite_acc xh xl y Hp4 COND) ].
move: (COND) => [Hfxh [Hfxl [Hfy [Hdwp [Hquot _]]]]].
have Hyne : FT2R y <> 0.
{ intro H0. have Hp := bpow_gt_0 radix2 (SpecFloat.emin (fprec t) (femax t) + fprec t - 1).
  move: Hquot; rewrite H0 /Rdiv Rinv_0 Rmult_0_r Rabs_R0 => Hc. lra. }
have Hpert : Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                             (Fast2Mult_err (BDIV xh y) y)) xl) y)
                   - round radix2 (FLX_exp (fprec t)) (Znearest choice)
                       (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                            (Fast2Mult_err (BDIV xh y) y)) xl)
                        / FT2R y)) = 0.
{ have Htl_r : FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                         (Fast2Mult_err (BDIV xh y) y)) xl) y)
               = round radix2 (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
                   (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                        (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
    by rewrite (BDIV_round_correct t _ y Hyne (FINtl xh xl y Hfp)).
  by rewrite Htl_r Hv0 !round_0 Rminus_diag Rabs_R0. }
rewrite Hpert Rplus_0_r in Habs.
exact Habs.
Qed.

(* ============================================================
   WHOLE-RANGE MIXED TIER, part 2: the regime-independent bound under the
   normal-leading-quotient helper.

   The split point |d/y| vs 2^(emin+p-1) is decidable, so a case split feeds
   either the normal leg (DWDivFP3_relative_accuracy_normal_quotient, whose
   extra Hdyn is exactly the >= side, scaled from relative to absolute and
   weakened by the non-negative floor term) or the underflow leg
   (DWDivFP3_error_underflow_perturbation, the < side, whose symbolic
   perturbation is charged at one floor ulp).  Both deliver

     |zh+zl - X/y| <= 3u^2 |X/y| + 2^emin.

   The runtime API is one level up: DWDivFP_subnormal.v case-splits
   DWDivFP_mixed_safe_input_cond into this theorem and the
   subnormal-leading-quotient leg.
   ============================================================ *)
Section CondAccuracyDWDivFP_mixed.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (@common.emin t).
Notation u := (bpow radix2 (- fprec t)).

Variables (xh xl y : ftype t).

Hypothesis Hp4 : (4 <= fprec t)%Z.
Hypothesis COND : DWDivFP_normal_quotient_input_cond xh xl y.

Theorem DWDivFP3_error_mixed_acc :
  Rabs (FT2R (fst (DWDivFP3 xh xl y)) + FT2R (snd (DWDivFP3 xh xl y))
        - (FT2R xh + FT2R xl) / FT2R y)
    <= 3 * u ^ 2 * Rabs ((FT2R xh + FT2R xl) / FT2R y) + bpow radix2 emin.
Proof.
destruct (Rle_or_lt (bpow radix2 (emin + fprec t - 1))
            (Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                       (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)))
  as [Hdyn | Huf].
- (* normal leg: scale the 3u^2 relative bound to absolute, then weaken by 2^emin *)
  move: (COND) => [Hfxh [Hfxl [Hfy [Hdwp [Hquot [Hxhb [Hqub Hxhlb]]]]]]].
  have Hyne : FT2R y <> 0.
  { intro H0.
    have Hp := bpow_gt_0 radix2 (SpecFloat.emin (fprec t) (femax t) + fprec t - 1).
    move: Hquot; rewrite H0 /Rdiv Rinv_0 Rmult_0_r Rabs_R0 => Hc. lra. }
  have Hxhne : FT2R xh <> 0.
  { intro Hx0. move: Hquot; rewrite Hx0 /Rdiv Rmult_0_l Rabs_R0 => Hc.
    have := bpow_gt_0 radix2 (SpecFloat.emin (fprec t) (femax t) + fprec t - 1). lra. }
  have Hsne : FT2R xh + FT2R xl <> 0.
  { intro Hs0. apply Hxhne. move: Hdwp; rewrite /double_word_prop Hs0.
    rewrite /rounded round_0 //. }
  have HDne : (FT2R xh + FT2R xl) / FT2R y <> 0.
  { apply Rmult_integral_contrapositive_currified;
      [ exact Hsne | apply Rinv_neq_0_compat; exact Hyne ]. }
  pose proof (DWDivFP3_relative_accuracy_normal_quotient xh xl y Hp4 COND Hdyn) as Hrel.
  unfold relative_error_DWDivFP in Hrel.
  set (E := FT2R (fst (DWDivFP3 xh xl y)) + FT2R (snd (DWDivFP3 xh xl y))
            - (FT2R xh + FT2R xl) / FT2R y) in *.
  set (D := (FT2R xh + FT2R xl) / FT2R y) in *.
  have Habs : Rabs E = Rabs (E / D) * Rabs D
    by (rewrite -Rabs_mult; f_equal; field; exact HDne).
  rewrite Habs.
  eapply Rle_trans; [ apply Rmult_le_compat_r; [ apply Rabs_pos | exact Hrel ] | ].
  have Hb := bpow_ge_0 radix2 emin. lra.
- (* underflow leg: charge the symbolic perturbation at one floor ulp *)
  eapply Rle_trans;
    [ exact (DWDivFP3_error_underflow_perturbation xh xl y Hp4 COND Huf) |].
  apply Rplus_le_compat_l.
  exact (DWDivFP3_tl_perturbation_le_eta xh xl y Hp4 COND).
Qed.

End CondAccuracyDWDivFP_mixed.

(* ============================================================
   NORMAL-RANGE PURE RELATIVE TIER, part 2: the public theorem.

   The sharp 3u^2 relative bound holds exactly where DWDivFP3 agrees with the
   paper's unbounded-exponent FLX model: the leading quotient is normal, and
   the closing correction is either exactly zero (exact division -- the tl node
   rounds 0 in both models) or its own quotient is normal.  Both facts are
   recorded by DDConds.DWDivFP_normal; the rest of
   DWDivFP_relative_error_input_cond is the whole-range safe-input condition,
   which supplies overflow headroom, y <> 0 and the product-node floor.

   NOTHING is absorbed here.  The constant is 3u^2 because in this regime there
   is no floor ulp to charge, not because a quotient magnitude window pays for
   one; the whole-range statement remains the mixed
   3u^2|Q| + eta of DWDivFP_subnormal.DWDivFP_mixed_accuracy_from_safe_input_cond.
   ============================================================ *)
Section RelativeAccuracyDWDivFP.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (@common.emin t).
Notation u := (bpow radix2 (- fprec t)).

Variables (xh xl y : ftype t).

Hypothesis Hp4 : (4 <= fprec t)%Z.
Hypothesis COND : DWDivFP_relative_error_input_cond xh xl y.

Theorem DWDivFP_relative_accuracy :
  relative_error_DWDivFP xh xl y <= 3 * u ^ 2.
Proof.
move: (COND) => [SAFE [Hquot Hcorr]].
have CONDn : DWDivFP_normal_quotient_input_cond xh xl y.
{ move: (SAFE) => [Hfxh [Hfxl [Hfy [Hdwp [_ [Hxhb [Hqub Hxhlb]]]]]]].
  repeat split; assumption. }
destruct Hcorr as [Hd0 | Hdyn]; last first.
- exact (DWDivFP3_relative_accuracy_normal_quotient xh xl y Hp4 CONDn Hdyn).
- (* exact division: the tl node is unperturbed, so the FLX bound transfers
     verbatim.  Convert the absolute form back to the relative one. *)
  move: (SAFE) => [Hfxh [Hfxl [Hfy [Hdwp [Hfth [Hxhb [Hqub Hxhlb]]]]]]].
  have Hyne : FT2R y <> 0.
  { intro H0.
    have Hp := bpow_gt_0 radix2 (SpecFloat.emin (fprec t) (femax t) + fprec t - 1).
    move: Hquot; rewrite H0 /Rdiv Rinv_0 Rmult_0_r Rabs_R0 => Hc. lra. }
  have Hxhne : FT2R xh <> 0.
  { intro Hx0. move: Hquot; rewrite Hx0 /Rdiv Rmult_0_l Rabs_R0 => Hc.
    have := bpow_gt_0 radix2 (SpecFloat.emin (fprec t) (femax t) + fprec t - 1). lra. }
  have Hsne : FT2R xh + FT2R xl <> 0.
  { intro Hs0. apply Hxhne. move: Hdwp; rewrite /double_word_prop Hs0.
    rewrite /rounded round_0 //. }
  have HDne : (FT2R xh + FT2R xl) / FT2R y <> 0.
  { apply Rmult_integral_contrapositive_currified;
      [ exact Hsne | apply Rinv_neq_0_compat; exact Hyne ]. }
  have HQpos : 0 < Rabs ((FT2R xh + FT2R xl) / FT2R y)
    by (apply Rabs_pos_lt; exact HDne).
  have Habs := DWDivFP3_error_exact_division xh xl y Hp4 CONDn Hd0.
  unfold relative_error_DWDivFP.
  set (E := FT2R (fst (DWDivFP3 xh xl y)) + FT2R (snd (DWDivFP3 xh xl y))
            - (FT2R xh + FT2R xl) / FT2R y) in *.
  set (D := (FT2R xh + FT2R xl) / FT2R y) in *.
  rewrite /Rdiv Rabs_mult Rabs_inv.
  apply (Rmult_le_reg_r (Rabs D)); [ exact HQpos |].
  rewrite Rmult_assoc Rinv_l; [ rewrite Rmult_1_r; exact Habs |].
  apply Rgt_not_eq; exact HQpos.
Qed.

End RelativeAccuracyDWDivFP.
