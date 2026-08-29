(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Conditions for the floating-point functional models in DDModels.v.

   Public double-word operations use the following vocabulary consistently:
   - [strong_precond]: an input-only condition sufficient to establish both
     the kernel precondition and finiteness of the computed result;
   - [weak_precond]: the mathematical assumptions required at kernel entry;
   - [finite_post_cond]: finiteness of the computed result;
   - [weak_pre_and_finite_post_cond]: the conjunction established by checking
     the weak precondition before the kernel and finiteness afterward;
   - [relative_precond]: the stronger assumptions for a pure relative bound.
 *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs common.
Require Export DDModels.


Section TwoSumCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation fexp  := (SpecFloat.fexp (fprec t) (femax t)).
Notation Omega := (bpow Zaux.radix2 (femax t)).

(* Sufficient conditions for the two returned components to reconstruct a+b
   exactly and form a valid double-word. *)
Definition TwoSum_exact_cond (a b : ftype t) : Prop :=
  is_finite (BPLUS a b) = true /\
  is_finite (BMINUS a b) = true /\
  Rabs (FT2R b) < Ulp.pred Zaux.radix2 fexp Omega.

End TwoSumCond.


Section Fast2SumCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

(* Sufficient condition for fast_2sum(a,b) to be correct (s + t = a + b,
   with s = round(a+b)).  Stated with ulp, which is regular at 0
   (ulp 0 = bpow emin, the minimum):
     - ulp b <= ulp a   covers both the Dekker case |b| <= |a| (ulp_le) and
                        Boldo's exponent case (ulp b <= ulp a <-> cexp b <=
                        cexp a for nonzero b,a).  It also subsumes b = 0,
                        since ulp 0 <= ulp a always.
     - a = 0            (Fast2Sum0f: fast_2sum(0,b) is exact).
   The stronger `|b| <= |a|` precondition implies `ulp b <= ulp a` by ulp_le, so
   any caller that established it still discharges this by `left; ulp_le`. *)
Definition Fast2Sum_exact_cond (a b : ftype t) : Prop :=
  is_finite (BPLUS a b) = true /\
  ((Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (FT2R b) <=
    Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (FT2R a))%R \/
   FT2R a = 0%R).

End Fast2SumCond.


Section Fast2MultCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

(* The rounded leading product is finite.  This is the property certified by
   [fast2_mult_product_finite_check]; it suffices for the error-component
   accuracy result but not for exact reconstruction. *)
Definition Fast2Mult_product_finite_cond (a b : ftype t) : Prop :=
  is_finite (BMULT a b) = true.

(* Sufficient conditions for the two returned components to reconstruct a*b
   exactly and form a valid double-word. *)
Definition Fast2Mult_exact_cond (a b : ftype t) : Prop :=
  Fast2Mult_product_finite_cond a b /\
  (FT2R a * FT2R b = 0 \/
   bpow Zaux.radix2 (SpecFloat.emin (fprec t) (femax t) + 2 * fprec t - 1)
   <= Rabs (FT2R a * FT2R b)).

End Fast2MultCond.


Section DWPlusDWCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation Omega := (bpow Zaux.radix2 (femax t)).

(** Sufficient input condition used by the strong C interface. *)
Definition DWPlusDW_strong_precond (xh xl yh yl : ftype t) : Prop :=
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite yh = true /\
  is_finite yl = true /\
  double_word_prop xh xl /\
  double_word_prop yh yl /\
  Rabs (FT2R xh) <= /4 * Omega /\
  Rabs (FT2R yh) <= /4 * Omega.

(* Mathematical assumptions that must hold before the kernel is called. *)
Definition DWPlusDW_weak_precond
    (xh xl yh yl : ftype t) : Prop :=
  double_word_prop xh xl /\
  double_word_prop yh yl.

Definition DWPlusDW_finite_post_cond
    (xh xl yh yl : ftype t) : Prop :=
  is_finite_p (DWPlusDW xh xl yh yl).

Definition DWPlusDW_weak_pre_and_finite_post_cond
    (xh xl yh yl : ftype t) : Prop :=
  DWPlusDW_weak_precond xh xl yh yl /\
  DWPlusDW_finite_post_cond xh xl yh yl.

End DWPlusDWCond.


Section DWPlusFPCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation Omega := (bpow Zaux.radix2 (femax t)).

(* This condition bounds only the high part of the double-word, matching the
   shape of DWPlusDW_strong_precond.
   The DW relation forces |xl| <= ulp(xh)/2, so no separate magnitude bound
   on xl is required.  is_finite xl is not implied by double_word_prop
   (which lives in R via FT2R), so it must be asserted explicitly. *)
(** Sufficient input condition used by the strong C interface. *)
Definition DWPlusFP_strong_precond (xh xl y : ftype t) : Prop :=
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite y  = true /\
  double_word_prop xh xl /\
  Rabs (FT2R xh) <= /4 * Omega /\
  Rabs (FT2R y)  <= /4 * Omega.

(* Mathematical assumptions that must hold before the kernel is called. *)
Definition DWPlusFP_weak_precond
    (xh xl y : ftype t) : Prop :=
  double_word_prop xh xl.

Definition DWPlusFP_finite_post_cond
    (xh xl y : ftype t) : Prop :=
  is_finite_p (DWPlusFP xh xl y).

Definition DWPlusFP_weak_pre_and_finite_post_cond
    (xh xl y : ftype t) : Prop :=
  DWPlusFP_weak_precond xh xl y /\
  DWPlusFP_finite_post_cond xh xl y.

End DWPlusFPCond.


Section DWTimesFPCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation Omega := (bpow Zaux.radix2 (femax t)).

(* Strong precondition for the relative bound on [DWTimesFP].
   [Fast2Mult_exact_cond] makes the leading product finite and excludes its
   underflow gap.  The other conjuncts make [xl] finite, require a double-word
   input, and keep the product below [Omega/2] so that the cross term and final
   [Fast2Sum] remain finite. *)
Definition DWTimesFP_relative_precond (xh xl y : ftype t) : Prop :=
  is_finite xl = true /\
  double_word_prop xh xl /\
  Fast2Mult_exact_cond xh y /\
  Rabs (FT2R xh * FT2R y) <= /2 * Omega.

(* Strong precondition for the whole-range guarantee on [DWTimesFP].  It requires
   only finiteness of the rounded leading product, so it permits its underflow gap.
   Together with input finiteness, the double-word relation, and the product
   ceiling, it proves result finiteness and hence the mixed error bound and
   output validity.  [dw_mult_fp_strong_precond_check] establishes this condition.  The pure
   relative bound instead requires [DWTimesFP_relative_precond]. *)
Definition DWTimesFP_strong_precond (xh xl y : ftype t) : Prop :=
  is_finite xl = true /\
  double_word_prop xh xl /\
  is_finite (BMULT xh y) = true /\
  Rabs (FT2R xh * FT2R y) <= /2 * Omega.

Definition DWTimesFP_weak_precond
    (xh xl y : ftype t) : Prop :=
  double_word_prop xh xl.

Definition DWTimesFP_finite_post_cond
    (xh xl y : ftype t) : Prop :=
  is_finite_p (DWTimesFP xh xl y).

Definition DWTimesFP_weak_pre_and_finite_post_cond
    (xh xl y : ftype t) : Prop :=
  DWTimesFP_weak_precond xh xl y /\
  DWTimesFP_finite_post_cond xh xl y.

Lemma DWTimesFP_strong_precond_of_relative_precond
    (xh xl y : ftype t) :
  DWTimesFP_relative_precond xh xl y ->
  DWTimesFP_strong_precond xh xl y.
Proof.
  intros (Hfxl & Hdwp & Hf2m & Hreal).
  repeat split; try assumption.
  exact (proj1 Hf2m).
Qed.

End DWTimesFPCond.


Section DWTimesDWCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation Omega := (bpow Zaux.radix2 (femax t)).

(* Exact leading product condition used by the closing multiplication in
   [DWDivDW].  It excludes the [Fast2Mult] underflow gap, requires finite
   double-word inputs, and keeps [|xh*yh|] below [Omega/2] so that the final
   [Fast2Sum] remains finite. *)
Definition DWTimesDW_exact_leading_product_precond (xh xl yh yl : ftype t) : Prop :=
  is_finite xl = true /\
  is_finite yl = true /\
  double_word_prop xh xl /\
  double_word_prop yh yl /\
  Fast2Mult_exact_cond xh yh /\
  Rabs (FT2R xh * FT2R yh) <= /2 * Omega.

(* Strong precondition for the whole-range guarantee on [DWTimesDW].  It requires
   only finiteness of the rounded leading product, so it permits its underflow gap.
   The remaining conjuncts require finite double-word inputs and enough
   overflow headroom to prove result finiteness.  The mixed guarantee then
   supplies the [4u^2|P| + 5/2*eta] bound and output validity.
   [dw_mult_dw_strong_precond_check] establishes this condition. *)
Definition DWTimesDW_strong_precond (xh xl yh yl : ftype t) : Prop :=
  is_finite xl = true /\
  is_finite yl = true /\
  double_word_prop xh xl /\
  double_word_prop yh yl /\
  is_finite (BMULT xh yh) = true /\
  Rabs (FT2R xh * FT2R yh) <= /2 * Omega.

(* Input condition for the sharp normal range relative bound.  The mixed
   strong precondition supplies overflow headroom and the double-word
   properties.  Normality of the leading product and the low by low product is
   sufficient: the remaining low order nodes are then either exact on the
   physical FLT lattice or normal. *)
Definition DWTimesDW_relative_precond
    (xh xl yh yl : ftype t) : Prop :=
  DWTimesDW_strong_precond xh xl yh yl /\
  bpow Zaux.radix2 (@common.emin t + 2 * fprec t - 1) <=
    Rabs (FT2R xh * FT2R yh) /\
  bpow Zaux.radix2 (@common.emin t + fprec t - 1) <=
    Rabs (FT2R xl * FT2R yl).

Definition DWTimesDW_weak_precond
    (xh xl yh yl : ftype t) : Prop :=
  double_word_prop xh xl /\
  double_word_prop yh yl.

Definition DWTimesDW_finite_post_cond
    (xh xl yh yl : ftype t) : Prop :=
  is_finite_p (DWTimesDW xh xl yh yl).

Definition DWTimesDW_weak_pre_and_finite_post_cond
    (xh xl yh yl : ftype t) : Prop :=
  DWTimesDW_weak_precond xh xl yh yl /\
  DWTimesDW_finite_post_cond xh xl yh yl.

Lemma DWTimesDW_strong_precond_of_exact_leading_product_precond
    (xh xl yh yl : ftype t) :
  DWTimesDW_exact_leading_product_precond xh xl yh yl ->
  DWTimesDW_strong_precond xh xl yh yl.
Proof.
  intros (Hfxl & Hfyl & Hdwx & Hdwy & Hf2m & Hreal).
  repeat split; try assumption.
  exact (proj1 Hf2m).
Qed.

Lemma DWTimesDW_strong_precond_of_relative_precond
    (xh xl yh yl : ftype t) :
  DWTimesDW_relative_precond xh xl yh yl ->
  DWTimesDW_strong_precond xh xl yh yl.
Proof. intros [Hsafe _]. exact Hsafe. Qed.

End DWTimesDWCond.


Section DWDivFPCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin  := (SpecFloat.emin (fprec t) (femax t)).
Notation Omega := (bpow Zaux.radix2 (femax t)).

(* ------------------------------------------------------------------
   Whole range mixed tier for DWDivFP (Algorithm 15).
   Input condition decidable at runtime; no underflow floor on the quotient.
   ------------------------------------------------------------------ *)

(* Strong precondition for the whole-range guarantee on [DWDivFP].  It requires
   finite inputs, a double-word dividend, and a finite leading quotient; the
   latter also implies a nonzero divisor.  Upper bounds on [|xh|] and
   [|xh/y|] prevent overflow.  For a nonzero dividend, the lower bound on
   [|xh|] makes the division residual accurate enough for the [u^2] bound.
   The zero dividend is admitted separately: the double-word property then
   forces [xl] to zero, so the residual vanishes.  There is no lower bound on
   the quotient, so the condition admits subnormal results.  The pure relative
   bound additionally requires [DWDivFP_relative_precond].
   [dw_div_fp_strong_precond_check] establishes this condition. *)
Definition DWDivFP_strong_precond (xh xl y : ftype t) : Prop :=
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite y  = true /\
  double_word_prop xh xl /\
  is_finite (BDIV xh y) = true /\
  Rabs (FT2R xh)          <= bpow Zaux.radix2 (femax t - 2) /\
  Rabs (FT2R xh / FT2R y) <= bpow Zaux.radix2 (femax t - 2) /\
  (FT2R xh = 0 \/
   bpow Zaux.radix2 (emin + 2 * fprec t) <= Rabs (FT2R xh)).

(* Mathematical assumptions that must hold before the kernel is called. *)
Definition DWDivFP_weak_precond
    (xh xl y : ftype t) : Prop :=
  double_word_prop xh xl /\
  (FT2R xh = 0 \/
   bpow Zaux.radix2 (emin + 2 * fprec t) <= Rabs (FT2R xh)).

(* Output validity: the computed pair is finite. *)
Definition DWDivFP_finite_post_cond
    (xh xl y : ftype t) : Prop :=
  is_finite_p (DWDivFP xh xl y).

Definition DWDivFP_weak_pre_and_finite_post_cond
    (xh xl y : ftype t) : Prop :=
  DWDivFP_weak_precond xh xl y /\
  DWDivFP_finite_post_cond xh xl y.

(* ------------------------------------------------------------------
   Normal range pure relative tier for DWDivFP.
   ------------------------------------------------------------------ *)

(* Normal range condition for the pure relative bound on [DWDivFP].  It
   requires a normal leading quotient and either a zero correction or a normal
   correction quotient.  The zero case preserves exact division.  These are
   properties of computed nodes, not conditions that an input guard can check. *)
Definition DWDivFP_relative_regime_cond (xh xl y : ftype t) : Prop :=
  bpow Zaux.radix2 (emin + fprec t - 1) <= Rabs (FT2R xh / FT2R y) /\
  (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                       (Fast2Mult_err (BDIV xh y) y)) xl) = 0 \/
   bpow Zaux.radix2 (emin + fprec t - 1)
     <= Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                  (Fast2Mult_err (BDIV xh y) y)) xl)
              / FT2R y)).

(* Input condition for the sharp normal range relative bound
   |(zh+zl) - (xh+xl)/y| <= 3u^2 |(xh+xl)/y|
   (DWDivFP_relative_acc.DWDivFP_relative_accuracy): the strong precondition
   for the whole range,
   condition -- which supplies overflow headroom, the input double-word,
   y <> 0 and the product node floor -- plus normality of the operations. *)
Definition DWDivFP_relative_precond (xh xl y : ftype t) : Prop :=
  DWDivFP_strong_precond xh xl y /\
  DWDivFP_relative_regime_cond xh xl y.

Lemma DWDivFP_strong_precond_of_relative_precond
    (xh xl y : ftype t) :
  DWDivFP_relative_precond xh xl y ->
  DWDivFP_strong_precond xh xl y.
Proof. intros [Hsafe _]; exact Hsafe. Qed.

End DWDivFPCond.


Section DWDivDWCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin  := (SpecFloat.emin (fprec t) (femax t)).

(* ------------------------------------------------------------------
   Whole range mixed tier for DWDivDW (Algorithm 18).
   ------------------------------------------------------------------ *)

(** Strong precondition for the whole-range guarantee on [DWDivDW].  It requires
    finite double-word operands, a divisor window, and a quotient ceiling.
    There is no lower bound on the quotient.  The upper divisor bound implies
    [eta*|yh| <= u^2/4], which pays for the reciprocal reconstruction floor
    after multiplication by the dividend.  The lower divisor bound provides
    reciprocal overflow headroom, implies [eta <= u^2], and supports exactness
    of the FMA residual.  [DWDivDW_weak_precond] retains the divisor window
    but relies on [DWDivDW_finite_post_cond] for output overflow information.
    [dw_div_dw_strong_precond_check] establishes this strong precondition. *)
Definition DWDivDW_strong_precond (xh xl yh yl : ftype t) : Prop :=
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite yh = true /\
  is_finite yl = true /\
  double_word_prop xh xl /\
  double_word_prop yh yl /\
  Rabs (FT2R yh) <= bpow Zaux.radix2 (femax t - fprec t - 5) /\
  bpow Zaux.radix2 (emin + 2 * fprec t) <= Rabs (FT2R yh) /\
  Rabs (FT2R xh / FT2R yh) <= bpow Zaux.radix2 (femax t - 2).

Definition DWDivDW_weak_precond
    (xh xl yh yl : ftype t) : Prop :=
  double_word_prop xh xl /\
  double_word_prop yh yl /\
  Rabs (FT2R yh) <= bpow Zaux.radix2 (femax t - fprec t - 5) /\
  bpow Zaux.radix2 (emin + 2 * fprec t) <= Rabs (FT2R yh).

(* Output validity: the computed pair is finite. *)
Definition DWDivDW_finite_post_cond
    (xh xl yh yl : ftype t) : Prop :=
  is_finite_p (DWDivDW xh xl yh yl).

Definition DWDivDW_weak_pre_and_finite_post_cond
    (xh xl yh yl : ftype t) : Prop :=
  DWDivDW_weak_precond xh xl yh yl /\
  DWDivDW_finite_post_cond xh xl yh yl.

End DWDivDWCond.


(* Normal range condition for the pure relative bound on [DWDivDW].
   [DWDivDW_relative_regime_cond] records the nine node bounds needed to identify the FLT
   computation with the FLX model.  These bounds do not follow from input
   magnitudes, and the nodes may be zero.  The mixed tier therefore permits
   their underflow and includes an absolute floor term. *)
Section DWDivDWNormal.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (SpecFloat.emin (fprec t) (femax t)).

Variables (xh xl yh yl : ftype t).

Notation th  := (BDIV (Zconst t 1) yh).
Notation rh  := (BFMA (BOPP yh) th (Zconst t 1)).
Notation rl  := (BOPP (BMULT yl th)).
Notation eh  := (fst (Fast2Sum rh rl)).
Notation el  := (snd (Fast2Sum rh rl)).
Notation dh  := (fst (DWTimesFP eh el th)).
Notation dl  := (snd (DWTimesFP eh el th)).
Notation mh  := (fst (DWPlusFP dh dl th)).
Notation ml  := (snd (DWPlusFP dh dl th)).

Definition DWDivDW_relative_regime_cond : Prop :=
  bpow Zaux.radix2 (emin + fprec t - 1) <= Rabs (1 - FT2R yh * FT2R th) /\
  bpow Zaux.radix2 (emin + fprec t - 1) <= Rabs (FT2R yl * FT2R th) /\
  bpow Zaux.radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R eh * FT2R th) /\
  bpow Zaux.radix2 (emin + fprec t - 1)
    <= Rabs (FT2R el * FT2R th + FT2R (Fast2Mult_err eh th)) /\
  bpow Zaux.radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R mh) /\
  bpow Zaux.radix2 (emin + fprec t - 1) <= Rabs (FT2R xl * FT2R ml) /\
  bpow Zaux.radix2 (emin + fprec t - 1)
    <= Rabs (FT2R xh * FT2R ml + FT2R (BMULT xl ml)) /\
  bpow Zaux.radix2 (emin + fprec t - 1)
    <= Rabs (FT2R (BFMA xh ml (BMULT xl ml)) + FT2R xl * FT2R mh) /\
  bpow Zaux.radix2 (emin + fprec t - 1)
    <= Rabs (FT2R (Fast2Mult_err xh mh)
             + FT2R (BFMA xl mh (BFMA xh ml (BMULT xl ml)))).

End DWDivDWNormal.


Section DWDivDWRelativeCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

(* Input condition for the sharp normal range relative bound
   |(zh+zl) - (xh+xl)/(yh+yl)| <= 9.8 u^2 |Q|
   (DWDivDW_relative_acc.DWDivDW_relative_accuracy): the strong precondition
   for the whole range,
   condition -- overflow headroom, the divisor window, both input double-words
   -- plus normality of the operations.  It contains no quotient magnitude
   window designed to absorb eta; the relative bound is proved in the normal
   regime, not by charging a physical floor against a large quotient. *)
Definition DWDivDW_relative_precond (xh xl yh yl : ftype t) : Prop :=
  DWDivDW_strong_precond xh xl yh yl /\
  DWDivDW_relative_regime_cond xh xl yh yl.

Lemma DWDivDW_strong_precond_of_relative_precond
    (xh xl yh yl : ftype t) :
  DWDivDW_relative_precond xh xl yh yl ->
  DWDivDW_strong_precond xh xl yh yl.
Proof. intros [Hsafe _]; exact Hsafe. Qed.

End DWDivDWRelativeCond.
