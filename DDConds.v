(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* This file contains the preconditions for the floating-point functional
   models in DDModels.v. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs common.
Require Export DDModels.


Section TwoSumCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation fexp  := (SpecFloat.fexp (fprec t) (femax t)).
Notation Omega := (bpow Zaux.radix2 (femax t)).

(* Sufficient conditions for the two returned components to reconstruct a+b
   exactly and form a valid double word. *)
Definition TwoSum_exact_cond (a b : ftype t) : Prop :=
  is_finite (BPLUS a b) = true /\
  is_finite (BMINUS a b) = true /\
  Rabs (FT2R b) < Ulp.pred Zaux.radix2 fexp Omega.

End TwoSumCond.


Section Fast2SumCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

(* Sufficient condition for fast_2sum(a,b) to be correct (s + t = a + b,
   with s = round(a+b)).  Stated with ulp, which is well-behaved at 0
   (ulp 0 = bpow emin, the minimum):
     - ulp b <= ulp a   covers both the Dekker case |b| <= |a| (ulp_le) and
                        Boldo's exponent case (ulp b <= ulp a <-> cexp b <=
                        cexp a for nonzero b,a).  It also subsumes b = 0,
                        since ulp 0 <= ulp a always.
     - a = 0            (Fast2Sum0f: fast_2sum(0,b) is exact).
   The old `|b| <= |a|` precondition implies `ulp b <= ulp a` by ulp_le, so
   any caller that established it still discharges this by `left; ulp_le`. *)
Definition Fast2Sum_exact_cond (a b : ftype t) : Prop :=
  is_finite (BPLUS a b) = true /\
  ((Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (FT2R b) <=
    Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (FT2R a))%R \/
   FT2R a = 0%R).

End Fast2SumCond.


Section Fast2MultCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

(* Sufficient conditions for the two returned components to reconstruct a*b
   exactly and form a valid double word. *)
Definition Fast2Mult_exact_cond (a b : ftype t) : Prop :=
  is_finite (BMULT a b) = true /\
  (FT2R a * FT2R b = 0 \/
   bpow Zaux.radix2 (SpecFloat.emin (fprec t) (femax t) + 2 * fprec t - 1)
   <= Rabs (FT2R a * FT2R b)).

(* Fast2Mult_acc_only_cond requires only that the rounded product be finite.
   Compared with Fast2Mult_exact_cond, it drops the underflow condition (the `a*b = 0 \/
   threshold <= |a*b|` disjunction).  By itself it suffices for the bound
   |Fast2Mult_err a b| <= 1/2 ulp(a*b) — which holds in every regime — but does
   not prove that mul + err = a*b or that (mul, err) is a valid double word.
   Those conclusions need the underflow disjunct of the full Fast2Mult_exact_cond.
   See Fast2Mult_acc.v:
   Fast2Mult_accuracy_from_acc_only_cond (this cond) vs Fast2Mult_correct_from_exact_cond
   (the full cond). *)
Definition Fast2Mult_acc_only_cond (a b : ftype t) : Prop :=
  is_finite (BMULT a b) = true.

Lemma Fast2Mult_acc_only_cond_of_exact_cond (a b : ftype t) :
  Fast2Mult_exact_cond a b -> Fast2Mult_acc_only_cond a b.
Proof. intros [Hfin _]; exact Hfin. Qed.

End Fast2MultCond.


Section DWPlusDWCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation Omega := (bpow Zaux.radix2 (femax t)).

(** Input-only sufficient condition used by the guarded C interface. *)
Definition DWPlusDW_safe_input_cond (xh xl yh yl : ftype t) : Prop :=
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite yh = true /\
  is_finite yl = true /\
  double_word_prop xh xl /\
  double_word_prop yh yl /\
  Rabs (FT2R xh) <= /4 * Omega /\
  Rabs (FT2R yh) <= /4 * Omega.

(* Mathematical assumptions that must hold before the kernel is called. *)
Definition DWPlusDW_input_cond
    (xh xl yh yl : ftype t) : Prop :=
  double_word_prop xh xl /\
  double_word_prop yh yl.

Definition DWPlusDW_output_finite_cond
    (xh xl yh yl : ftype t) : Prop :=
  is_finite_p (AccurateDWPlusDW xh xl yh yl).

Definition DWPlusDW_cond
    (xh xl yh yl : ftype t) : Prop :=
  DWPlusDW_input_cond xh xl yh yl /\
  DWPlusDW_output_finite_cond xh xl yh yl.

End DWPlusDWCond.


Section DWPlusFPCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation Omega := (bpow Zaux.radix2 (femax t)).

(* This condition bounds only the high part of the double word, matching the
   shape of DWPlusDW_safe_input_cond.
   The DW relation forces |xl| <= ulp(xh)/2, so no separate magnitude bound
   on xl is required.  is_finite xl is NOT implied by double_word_prop
   (which lives in R via FT2R), so it must be asserted explicitly. *)
(** Input-only sufficient condition used by the guarded C interface. *)
Definition DWPlusFP_safe_input_cond (xh xl y : ftype t) : Prop :=
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite y  = true /\
  double_word_prop xh xl /\
  Rabs (FT2R xh) <= /4 * Omega /\
  Rabs (FT2R y)  <= /4 * Omega.

(* Mathematical assumptions that must hold before the kernel is called. *)
Definition DWPlusFP_input_cond
    (xh xl y : ftype t) : Prop :=
  double_word_prop xh xl.

Definition DWPlusFP_output_finite_cond
    (xh xl y : ftype t) : Prop :=
  is_finite_p (DWPlusFP xh xl y).

Definition DWPlusFP_cond
    (xh xl y : ftype t) : Prop :=
  DWPlusFP_input_cond xh xl y /\
  DWPlusFP_output_finite_cond xh xl y.

End DWPlusFPCond.


Section DWTimesFPCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation Omega := (bpow Zaux.radix2 (femax t)).

(* Safe input condition for the relative bound on [DWTimesFP3].
   [Fast2Mult_exact_cond] makes the leading product finite and excludes its
   underflow gap.  The other conjuncts make [xl] finite, require a double-word
   input, and keep the product below [Omega/2] so that the cross term and final
   [Fast2Sum] remain finite. *)
Definition DWTimesFP_relative_error_input_cond (xh xl y : ftype t) : Prop :=
  is_finite xl = true /\
  double_word_prop xh xl /\
  Fast2Mult_exact_cond xh y /\
  Rabs (FT2R xh * FT2R y) <= /2 * Omega.

(* Safe input condition for the mixed guarantee on [DWTimesFP3].  It uses
   [Fast2Mult_acc_only_cond], so it permits the leading-product underflow gap.
   Together with input finiteness, the double-word relation, and the product
   ceiling, it proves result finiteness and hence the mixed error bound and
   output validity.  [dw_mult_fp_check] establishes this condition.  The pure
   relative bound instead requires [DWTimesFP_relative_error_input_cond]. *)
Definition DWTimesFP_mixed_safe_input_cond (xh xl y : ftype t) : Prop :=
  is_finite xl = true /\
  double_word_prop xh xl /\
  Fast2Mult_acc_only_cond xh y /\
  Rabs (FT2R xh * FT2R y) <= /2 * Omega.

Definition DWTimesFP_mixed_input_cond
    (xh xl y : ftype t) : Prop :=
  double_word_prop xh xl.

Definition DWTimesFP_result_finite
    (xh xl y : ftype t) : Prop :=
  is_finite_p (DWTimesFP3 xh xl y).

Definition DWTimesFP_mixed_cond
    (xh xl y : ftype t) : Prop :=
  DWTimesFP_mixed_input_cond xh xl y /\
  DWTimesFP_result_finite xh xl y.

Lemma DWTimesFP_mixed_safe_input_cond_of_relative_error_input_cond
    (xh xl y : ftype t) :
  DWTimesFP_relative_error_input_cond xh xl y ->
  DWTimesFP_mixed_safe_input_cond xh xl y.
Proof.
  intros (Hfxl & Hdwp & Hf2m & Hreal).
  repeat split; try assumption.
  exact (Fast2Mult_acc_only_cond_of_exact_cond xh y Hf2m).
Qed.

End DWTimesFPCond.


Section DWTimesDWCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation Omega := (bpow Zaux.radix2 (femax t)).

(* Exact leading-product condition used by the closing multiplication in
   [DWDivDW3].  It excludes the [Fast2Mult] underflow gap, requires finite
   double-word inputs, and keeps [|xh*yh|] below [Omega/2] so that the final
   [Fast2Sum] remains finite. *)
Definition DWTimesDW_exact_leading_product_input_cond (xh xl yh yl : ftype t) : Prop :=
  is_finite xl = true /\
  is_finite yl = true /\
  double_word_prop xh xl /\
  double_word_prop yh yl /\
  Fast2Mult_exact_cond xh yh /\
  Rabs (FT2R xh * FT2R yh) <= /2 * Omega.

(* Safe input condition for the mixed guarantee on [DWTimesDW3].  It uses
   [Fast2Mult_acc_only_cond], so it permits the leading-product underflow gap.
   The remaining conjuncts require finite double-word inputs and enough
   overflow headroom to prove result finiteness.  The mixed guarantee then
   supplies the [4u^2|P| + 5/2*eta] bound and output validity.
   [dw_mult_dw_check] establishes this condition. *)
Definition DWTimesDW_mixed_safe_input_cond (xh xl yh yl : ftype t) : Prop :=
  is_finite xl = true /\
  is_finite yl = true /\
  double_word_prop xh xl /\
  double_word_prop yh yl /\
  Fast2Mult_acc_only_cond xh yh /\
  Rabs (FT2R xh * FT2R yh) <= /2 * Omega.

(* Input-only condition for the sharp normal-range relative bound.  The mixed
   safe-input condition supplies overflow headroom and input double-word
   properties.  Normality of the leading product and the low-low product is
   sufficient: the remaining low-order nodes are then either exact on the
   physical FLT lattice or normal. *)
Definition DWTimesDW_relative_error_input_cond
    (xh xl yh yl : ftype t) : Prop :=
  DWTimesDW_mixed_safe_input_cond xh xl yh yl /\
  bpow Zaux.radix2 (@common.emin t + 2 * fprec t - 1) <=
    Rabs (FT2R xh * FT2R yh) /\
  bpow Zaux.radix2 (@common.emin t + fprec t - 1) <=
    Rabs (FT2R xl * FT2R yl).

Definition DWTimesDW_mixed_input_cond
    (xh xl yh yl : ftype t) : Prop :=
  double_word_prop xh xl /\
  double_word_prop yh yl.

Definition DWTimesDW_result_finite
    (xh xl yh yl : ftype t) : Prop :=
  is_finite_p (DWTimesDW3 xh xl yh yl).

Definition DWTimesDW_mixed_cond
    (xh xl yh yl : ftype t) : Prop :=
  DWTimesDW_mixed_input_cond xh xl yh yl /\
  DWTimesDW_result_finite xh xl yh yl.

Lemma DWTimesDW_mixed_safe_input_cond_of_exact_leading_product_input_cond
    (xh xl yh yl : ftype t) :
  DWTimesDW_exact_leading_product_input_cond xh xl yh yl ->
  DWTimesDW_mixed_safe_input_cond xh xl yh yl.
Proof.
  intros (Hfxl & Hfyl & Hdwx & Hdwy & Hf2m & Hreal).
  repeat split; try assumption.
  exact (Fast2Mult_acc_only_cond_of_exact_cond xh yh Hf2m).
Qed.

Lemma DWTimesDW_mixed_safe_input_cond_of_relative_error_input_cond
    (xh xl yh yl : ftype t) :
  DWTimesDW_relative_error_input_cond xh xl yh yl ->
  DWTimesDW_mixed_safe_input_cond xh xl yh yl.
Proof. intros [Hsafe _]. exact Hsafe. Qed.

End DWTimesDWCond.


Section DWDivFPCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin  := (SpecFloat.emin (fprec t) (femax t)).
Notation Omega := (bpow Zaux.radix2 (femax t)).

(* ------------------------------------------------------------------
   WHOLE-RANGE MIXED TIER for DWDivFP3 (Algorithm 15).
   Input-only, runtime-checkable; no underflow floor on the quotient.
   ------------------------------------------------------------------ *)

(* Safe input condition for the mixed guarantee on [DWDivFP3].  It requires
   finite inputs, a double-word dividend, and a finite leading quotient; the
   latter also implies a nonzero divisor.  Upper bounds on [|xh|] and
   [|xh/y|] prevent overflow.  The lower bound on [|xh|] makes the division
   residual accurate enough for the [u^2] bound.  There is no lower bound on
   the quotient, so the condition admits subnormal results.  The pure relative
   bound additionally requires [DWDivFP_relative_error_input_cond].
   [dw_div_fp_check] establishes this condition. *)
Definition DWDivFP_mixed_safe_input_cond (xh xl y : ftype t) : Prop :=
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite y  = true /\
  double_word_prop xh xl /\
  is_finite (BDIV xh y) = true /\
  Rabs (FT2R xh)          <= bpow Zaux.radix2 (femax t - 2) /\
  Rabs (FT2R xh / FT2R y) <= bpow Zaux.radix2 (femax t - 2) /\
  bpow Zaux.radix2 (emin + 2 * fprec t) <= Rabs (FT2R xh).

(* Mathematical assumptions that must hold before the kernel is called. *)
Definition DWDivFP_mixed_input_cond
    (xh xl y : ftype t) : Prop :=
  double_word_prop xh xl /\
  bpow Zaux.radix2 (emin + 2 * fprec t) <= Rabs (FT2R xh).

(* Output validity: the computed pair is finite. *)
Definition DWDivFP_result_finite
    (xh xl y : ftype t) : Prop :=
  is_finite_p (DWDivFP3 xh xl y).

Definition DWDivFP_mixed_cond
    (xh xl y : ftype t) : Prop :=
  DWDivFP_mixed_input_cond xh xl y /\
  DWDivFP_result_finite xh xl y.

(* ------------------------------------------------------------------
   NORMAL-RANGE PURE RELATIVE TIER for DWDivFP3.
   ------------------------------------------------------------------ *)

(* Normal-range condition for the pure relative bound on [DWDivFP3].  It
   requires a normal leading quotient and either a zero correction or a normal
   correction quotient.  The zero case preserves exact division.  These are
   properties of computed nodes, not conditions that an input guard can check. *)
Definition DWDivFP_normal (xh xl y : ftype t) : Prop :=
  bpow Zaux.radix2 (emin + fprec t - 1) <= Rabs (FT2R xh / FT2R y) /\
  (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                       (Fast2Mult_err (BDIV xh y) y)) xl) = 0 \/
   bpow Zaux.radix2 (emin + fprec t - 1)
     <= Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                  (Fast2Mult_err (BDIV xh y) y)) xl)
              / FT2R y)).

(* Input condition for the sharp normal-range relative bound
   |(zh+zl) - (xh+xl)/y| <= 3u^2 |(xh+xl)/y|
   (DWDivFP_relative_acc.DWDivFP_relative_accuracy): the whole-range safe-input
   condition -- which supplies overflow headroom, the input double word,
   y <> 0 and the product-node floor -- plus normality of the operations. *)
Definition DWDivFP_relative_error_input_cond (xh xl y : ftype t) : Prop :=
  DWDivFP_mixed_safe_input_cond xh xl y /\
  DWDivFP_normal xh xl y.

Lemma DWDivFP_mixed_safe_input_cond_of_relative_error_input_cond
    (xh xl y : ftype t) :
  DWDivFP_relative_error_input_cond xh xl y ->
  DWDivFP_mixed_safe_input_cond xh xl y.
Proof. intros [Hsafe _]; exact Hsafe. Qed.

End DWDivFPCond.


Section DWDivDWCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin  := (SpecFloat.emin (fprec t) (femax t)).

(* ------------------------------------------------------------------
   WHOLE-RANGE MIXED TIER for DWDivDW3 (Algorithm 18).
   ------------------------------------------------------------------ *)

(** Safe input condition for the mixed guarantee on [DWDivDW3].  It requires
    finite double-word operands, a divisor window, and a quotient ceiling.
    There is no lower bound on the quotient.  The upper divisor bound implies
    [eta*|yh| <= u^2/4], which pays for the reciprocal reconstruction floor
    after multiplication by the dividend.  The lower divisor bound provides
    reciprocal overflow headroom, implies [eta <= u^2], and supports exactness
    of the FMA residual.  [DWDivDW_mixed_input_cond] retains the divisor window
    but relies on [DWDivDW_result_finite] for output overflow information.
    [dw_div_dw_check] establishes the safe input condition. *)
Definition DWDivDW_mixed_safe_input_cond (xh xl yh yl : ftype t) : Prop :=
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite yh = true /\
  is_finite yl = true /\
  double_word_prop xh xl /\
  double_word_prop yh yl /\
  Rabs (FT2R yh) <= bpow Zaux.radix2 (femax t - fprec t - 5) /\
  bpow Zaux.radix2 (emin + 2 * fprec t) <= Rabs (FT2R yh) /\
  Rabs (FT2R xh / FT2R yh) <= bpow Zaux.radix2 (femax t - 2).

Definition DWDivDW_mixed_input_cond
    (xh xl yh yl : ftype t) : Prop :=
  double_word_prop xh xl /\
  double_word_prop yh yl /\
  Rabs (FT2R yh) <= bpow Zaux.radix2 (femax t - fprec t - 5) /\
  bpow Zaux.radix2 (emin + 2 * fprec t) <= Rabs (FT2R yh).

(* Output validity: the computed pair is finite. *)
Definition DWDivDW_result_finite
    (xh xl yh yl : ftype t) : Prop :=
  is_finite_p (DWDivDW3 xh xl yh yl).

Definition DWDivDW_mixed_cond
    (xh xl yh yl : ftype t) : Prop :=
  DWDivDW_mixed_input_cond xh xl yh yl /\
  DWDivDW_result_finite xh xl yh yl.

End DWDivDWCond.


(* Normal-range condition for the pure relative bound on [DWDivDW3].
   [DWDivDW_normal] records the nine node bounds needed to identify the FLT
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
Notation dh  := (fst (DWTimesFP3 eh el th)).
Notation dl  := (snd (DWTimesFP3 eh el th)).
Notation mh  := (fst (DWPlusFP dh dl th)).
Notation ml  := (snd (DWPlusFP dh dl th)).

Definition DWDivDW_normal : Prop :=
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

(* Input condition for the sharp normal-range relative bound
   |(zh+zl) - (xh+xl)/(yh+yl)| <= 9.8 u^2 |Q|
   (DWDivDW_relative_acc.DWDivDW_relative_accuracy): the whole-range safe-input
   condition -- overflow headroom, the divisor window, both input double words
   -- plus normality of the operations.  It contains no quotient magnitude
   window designed to absorb eta; the relative bound is proved in the normal
   regime, not by charging a physical floor against a large quotient. *)
Definition DWDivDW_relative_error_input_cond (xh xl yh yl : ftype t) : Prop :=
  DWDivDW_mixed_safe_input_cond xh xl yh yl /\
  DWDivDW_normal xh xl yh yl.

Lemma DWDivDW_mixed_safe_input_cond_of_relative_error_input_cond
    (xh xl yh yl : ftype t) :
  DWDivDW_relative_error_input_cond xh xl yh yl ->
  DWDivDW_mixed_safe_input_cond xh xl yh yl.
Proof. intros [Hsafe _]; exact Hsafe. Qed.

End DWDivDWRelativeCond.
