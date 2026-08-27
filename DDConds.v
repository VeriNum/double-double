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

(* Precondition for DWTimesFP3 (Algorithm 9).  Minimal, non-redundant form:
     - Fast2Mult_exact_cond xh y : the leading product satisfies the leaf condition
       (finiteness of BMULT xh y + the underflow disjunction) needed to make the
       two components returned by Fast2Mult reconstruct xh*y exactly and to obtain
       the relative accuracy bound.  Via
       BMULT_finite_e this ALSO supplies is_finite xh and is_finite y, so those
       are not listed separately;
     - is_finite xl and the double-word relation on (xh, xl);
     - the product-magnitude bound |xh*y| <= Omega/2 = 2^(femax-1).  This is the
       overflow headroom that keeps the cross term and the closing Fast2Sum
       finite (Fast2Mult_exact_cond alone only gives |xh*y| < Omega, under which the
       closing Fast2Sum can still overflow).  Omega/2 is the largest clean
       power-of-two that is provably sufficient: at |xh*y| ~ Omega the closing
       correction (a few ulp) tips RN(ch.s + c3) over Omega.  A caller may
       establish it from the square-root-scale factor bounds |xh|,|y| <=
       2^(femax/2-1), which give the stronger |xh*y| <= Omega/4. *)
Definition DWTimesFP_relative_error_input_cond (xh xl y : ftype t) : Prop :=
  is_finite xl = true /\
  double_word_prop xh xl /\
  Fast2Mult_exact_cond xh y /\
  Rabs (FT2R xh * FT2R y) <= /2 * Omega.

(* DWTimesFP_mixed_safe_input_cond is used to prove, throughout the admitted
   floating-point range, both the mixed error bound for DWTimesFP3 and that its
   output is a valid double word.  It weakens Fast2Mult_exact_cond to
   Fast2Mult_acc_only_cond, i.e. it drops the underflow disjunct
   (FT2R xh * FT2R y = 0 \/ 2^(emin+2*p-1) <= |FT2R xh * FT2R y|) and keeps
   only overflow safety.  Exactly the DWTimesFP analogue of
   Fast2Mult_acc_only_cond vs Fast2Mult_exact_cond above.

   It suffices for the whole-range MIXED bound

     |(zh+zl) - (xh+xl)*y| <= 2u^2 |(xh+xl)*y| + 2.51*eta

   (DWMulFP_mixed_acc.DWTimesFP_mixed_guarantee_from_cond), together with output
   double-word closure.  Both conclusions hold in
   every regime given only the input double-word relation and finiteness of the
   computed pair.  The three conjuncts below are what a runtime guard needs to
   establish that finiteness.
   It does NOT suffice for the pure 2u^2 relative bound, which is available only
   when the nonzero underflow gap is excluded; that remains the province of the
   full DWTimesFP_relative_error_input_cond (see DWMulFP_relative_acc.DWTimesFP_cond_no_gap).

   This is the cond discharged by the runtime guard dw_mult_fp_check and carried
   by the exported funspec dw_mult_fp9_guarded_spec. *)
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

(* Exact-leading-product condition retained for the closing multiplication
   inside DWDivDW.  It excludes the Fast2Mult underflow gap, but permits
   subnormal low-order multiplication nodes and therefore is not the public
   normal-range relative-error condition for DWTimesDW3.

   Its conjuncts are:
     - Fast2Mult_exact_cond xh yh : leaf condition on the high product (also supplies
       is_finite xh and is_finite yh via BMULT_finite_e, so those are not listed);
     - is_finite xl, is_finite yl and the double-word relations on both pairs;
     - the product-magnitude bound |xh*yh| <= Omega/2 = 2^(femax-1) for overflow
       headroom (Omega/2 is the largest clean power-of-two that keeps the closing
       Fast2Sum finite; callers may establish it from separate factor bounds,
       which imply the stronger |xh*yh| <= Omega/4). *)
Definition DWTimesDW_exact_leading_product_input_cond (xh xl yh yl : ftype t) : Prop :=
  is_finite xl = true /\
  is_finite yl = true /\
  double_word_prop xh xl /\
  double_word_prop yh yl /\
  Fast2Mult_exact_cond xh yh /\
  Rabs (FT2R xh * FT2R yh) <= /2 * Omega.

(* DWTimesDW_mixed_safe_input_cond is used to prove, throughout the admitted
   floating-point range, both the mixed error bound for DWTimesDW3 and that its
   output is a valid double word.  It is the exact analogue of
   DWTimesFP_mixed_safe_input_cond above.  It weakens Fast2Mult_exact_cond to
   Fast2Mult_acc_only_cond, dropping the underflow disjunct
   (FT2R xh * FT2R yh = 0 \/ 2^(emin+2*p-1) <= |FT2R xh * FT2R yh|) and keeping
   only overflow safety.

   It suffices for the whole-range MIXED bound

     |(zh+zl) - (xh+xl)*(yh+yl)| <= 4u^2 |(xh+xl)*(yh+yl)| + 5/2*eta

   and proves that the output is a valid double word.  Both conclusions hold in
   every regime given only the two input double-word relations and finiteness of
   the computed pair.  The conjuncts below are what a runtime guard needs to
   establish that finiteness
   (DWMulDW_mixed_acc.DWTimesDW_mixed_cond_of_safe_input_cond).

   This is the cond discharged by the runtime guard dw_mult_dw_check and carried
   by the exported funspec dw_mult_dw12_guarded_spec, exactly as
   DWTimesFP_mixed_safe_input_cond is for dw_mult_fp_check and
   dw_mult_fp9_guarded_spec.  DWTimesDW_exact_leading_product_input_cond remains in use
   inside DWDivDW_relative_acc, whose reciprocal refinement needs the underflow disjunct
   for the exact product step. *)
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

(* DWDivFP_mixed_safe_input_cond is used to prove, throughout the admitted
   floating-point range, the mixed error bound for DWDivFP3, that its output is
   a valid double word, and that the computed pair is finite.  Its conjuncts
   are:

     - finiteness of the three inputs and the double-word relation on (xh,xl);

     - finiteness of the leading quotient node th = BDIV xh y.  That conjunct
       is the division analogue of Fast2Mult_acc_only_cond (which is likewise
       just `is_finite (BMULT a b) = true`), and it does double duty: it forces
       FT2R y <> 0, and it supplies the th-node finiteness that would otherwise
       have to be derived from a quotient ceiling together with y <> 0;

     - the two no-overflow bounds, both referencing only xh and y.  The
       QUOTIENT ceiling |xh/y| <= Omega/4 = bpow(femax-2) covers the nodes
       whose magnitude is the quotient (th = round(xh/y), tl = d/y and the
       closing th+tl); the |xh| ceiling covers the intermediate product node
       pih = round(th*y) ~ xh, which can overflow even under the quotient bound
       (e.g. xh = Omega, y = 4).  Unlike the mul-style split into two
       square-root bounds on xh and 1/y (which would exclude valid
       small-magnitude or large-matched divisions), this is the precise
       no-overflow condition and rejects only inputs that actually overflow;

     - the product-node floor 2^(emin+2p) <= |xh|.  This one is NOT removable:
       it is what makes the division residual representable to relative
       accuracy u, hence what makes DWDivFP3 a double-word algorithm at all.
       Dropping it costs the u^2 bound outright -- xh = 7*eta, y = 3*eta is a
       double word with a perfectly normal quotient 7/3 on which the algorithm
       returns zl = 0 and a relative error of u/2, violating 3u^2|Q| + c*eta
       for every constant c.  It is also what forces |y| > 2^(p+1), without
       which the closing division node has no bound.

   The cond admits a SUBNORMAL quotient.  The mixed bound

     |(zh+zl) - (xh+xl)/y| <= 3u^2 |(xh+xl)/y| + 2^emin

   survives with the same u^2 constant, because once |xh/y| < 2^(emin+p-1) the
   whole computation sits on the 2^emin lattice: the correction tl rounds
   within half an ulp of the exact one, and the closing Fast2Sum is exact
   because th + tl is again a lattice point.  The error bound, output
   double-word closure and finiteness are established in DWDivFP_subnormal.v.
   Its public ladder is DWDivFP_mixed_accuracy_from_cond /
   DWDivFP_double_word_from_cond / DWDivFP_mixed_guarantee_from_cond; the
   safe-input guarantee is a corollary after the precondition proves result
   finiteness.

   It does NOT suffice for the pure 3u^2 relative bound, which exists only in
   the normal regime; that is the province of
   DWDivFP_relative_error_input_cond below.

   This is the cond discharged by the runtime guard dw_div_fp_check. *)
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

(* DWDivFP_normal is the algorithmic normal-range predicate: it states that the
   two nodes whose roundings the 3u^2 analysis charges at relative accuracy u
   really do sit in the FLT normal range, so that DWDivFP3 coincides with the
   paper's unbounded-exponent FLX model.

     - the leading quotient xh/y is normal.  This is what lets
       th = BDIV xh y be read as the FLX rounding of the quotient;

     - the closing correction d = (xh - th*y) - pil + xl is EITHER exactly zero
       OR its quotient d/y is normal.  The zero disjunct is not decoration: it
       is the exact-division case, where the correction vanishes and nothing is
       lost, and a bare floor `2^(emin+p-1) <= |d/y|` would exclude it.

   Neither conjunct follows from magnitude bounds on xh, xl, y alone -- these
   are facts about the computation, which is why they live here rather than in
   the runtime-checkable input tier above.  Contrast the old formulation, whose
   quotient window 2^(emin+2p-1) <= |xh/y| existed only so that one floor ulp
   could be charged against a large quotient; nothing here absorbs eta. *)
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

(** [DWDivDW_mixed_safe_input_cond] is used to prove, throughout the admitted
    floating-point range, both the mixed error bound for [DWDivDW3] and that
    its output is a valid double word.  It is the DW/DW analogue of
    [DWDivFP_mixed_safe_input_cond] above, and carries NO underflow floor on
    the quotient: for Tdouble it admits every quotient below 2^-969, i.e. the
    entire underflowing-quotient range the mixed bound was built to cover.

    The exported results are

      |(zh+zl) - (xh+xl)/(yh+yl)| <= 9.8 u^2 |Q| + 5/2 eta

    ([DWDivDW_mixed_acc.DWDivDW_mixed_accuracy_from_cond]) together with output
    double-word closure ([DWDivDW_double_word_from_cond]) and their bundle
    ([DWDivDW_mixed_guarantee_from_cond]).  The safe-input condition reaches
    the same bundle through [DWDivDW_mixed_guarantee_from_safe_input_cond].
    The [5/2*eta] is not an
    artifact of a missing guard: the closing block routes through
    [DWMulDW_mixed_acc.DWTimesDW_mixed_accuracy_from_cond], which covers the WHOLE
    range from double-word inputs and finiteness alone, and whose sub-threshold
    gap arm spends five half-ulps.  The residual nodes that floor comes from
    may legitimately be zero, which is exactly why this cond deliberately does
    not bound them below.

    NO-OVERFLOW BOUNDS: only the quotient ceiling survives.  This cond used to
    carry three [<= 2^(femax-2)] conjuncts, on |xh|, |yh| and |xh/yh|.  Two of
    them are gone.

    - |yh| <= 2^(femax-2) was REDUNDANT.  Conjunct 7 below is an upper bound on
      |yh|, and a strictly stronger one: it is the same bound tightened by p
      binades and therefore also implies the weaker quarter-overflow bound.
      The runtime guard [dw_div_dw_check] already
      exploited this -- it tests |y->s| <= 2^969 and derived |y->s| <= 2^1022
      from it -- so the two conjuncts were never independent.

    - |xh| <= 2^(femax-2) was UNUSED.  It is not implied by anything, but no
      theorem in DWDivDW_relative_acc.v ever read it, finiteness
      ([DWDivDW3_finite_from_cond]) included, and the reason is structural: xh
      only ever enters the algorithm multiplied by mh ~ 1/yh (the closing
      ch = BMULT xh mh, tl1 = BFMA xh ml tl0, and xl likewise), so the quotient
      ceiling below already bounds every node xh reaches.  Accuracy, output
      double-word closure and finiteness were all re-verified without it.  The
      guard's xh_hi test is consequently dead and can be deleted whenever
      clightgen is next re-run.

    WHY CONJUNCTS 7 AND 8 STAY, AND WHERE CONJUNCT 7's EXPONENT COMES FROM.

    Conjuncts 7 and 8 are the two sides of one window on the divisor,

      2^(emin+2p) <= |yh| <= 2^(femax-p-5)        (Tdouble: 2^-968 .. 2^966),

    and neither is an underflow floor on a residual node.  Conjunct 7 used to
    be written as [2^(emin+2p-1) <= |1/yh|], which for yh <> 0 is the same
    kind of statement one exponent looser; it is now stated directly on |yh|,
    so the cond never mentions 1/FT2R yh and the guard needs no rounded-to-
    exact reciprocal transfer.  Nonzero-ness comes from conjunct 8.

    CONJUNCT 7 IS THE EXPORTED COEFFICIENT.  Since eta = 2^emin and u = 2^-p,
    conjunct 7 says exactly

      eta * |yh| <= u^2 / 4.

    The reciprocal reconstruction (mh,ml) carries an absolute underflow floor
    of its own, |M - 1/Y| <= a u^2/|Y| + fr*eta
    ([DWDivDW_reciprocal_error_scaled_floor_param]), so the closing
    multiplication by X contributes fr*eta*|X|; and since |X| = |Q|*|Y|
    identically,

      eta*|X| <= c u^2 |Q|   <->   eta*|Y| <= c u^2

    whenever Q <> 0, with |Y| = |yh|(1+O(u)).  Conjunct 7 IS that inequality,
    not merely a sufficient condition for it, so its exponent and the exported
    u^2 coefficient move together:

      |yh| <= 2^(femax-p-2-k)  ==>  charge = fr * 2^(1-k),   fr = 1 or 2.

    At k = 0 the charge is 2.0 on the ordered arm and 4.0 on the unordered one,
    and the exported coefficient was 12.33.  Nothing rearranges that away: the
    floor fr is REPRESENTATIONAL, not algorithmic.  At the window's edge
    |th| ~ 2^(emin+2p-1), so the refinement product eh*th sits one binade above
    the smallest normal and its exact value needs bits below 2^emin -- ANY
    double-word D misses E*th by up to eta/2, whatever algorithm produces it.
    With the paper's own FLX budget assembled from 5 (closing DWTimesDW12,
    relaxed from its actual <4u^2) + 2.298 (Newton residual) + 0.5 (rl
    rounding) + 2 (DWPlusFP) = 9.798, the only slack a runtime proof has over
    9.8 is the 5 -> 4 closing gain, i.e. 1.0 -- less than the charge.  So 9.8
    is out of reach at k <= 1 however the analysis is arranged, and k = 3 is
    what this cond takes: charge 0.25, arm budgets 9.56 (ordered) and 7.60
    (unordered), exported 9.8 with slack.

    The price is 3 binades off the TOP of the divisor range, an overflow-side
    restriction.  Underflow whole-range coverage is untouched: there is no
    floor on the quotient anywhere in this cond.

    Conjunct 8, [2^(emin+2p) <= |yh|], is likewise not an underflow floor.
    Since emin = 3 - femax - p it is literally

      |1/yh| <= 2^(femax-p-3),

    the p+3 binades of overflow headroom that the reciprocal node
    th = BDIV 1 yh and everything scaled by it (dh ~ u*th, mh ~ th) require;
    [DWDivDW_cond_reciprocal_upper_tight] uses it at exactly that strength.
    It does double duty twice more:

      - together with conjunct 7 it forces emin+2p <= femax-p-5, hence
        p <= femax-4 and so [emin+2p <= 0], hence [eta <= u^2]
        ([DWDivDW_cond_eta_le_u2]).  That is what lets the reciprocal
        residual's one rounding be charged at 1.001*u^2 with no floor ulp at
        all (only [p < femax] is available otherwise, giving eta <= 4u^2,
        which does not fit).
      - it is what makes the FMA residual rh = 1 - yh*th exactly
        representable ([DWDivDW_rh_exact_from_cond], via
        [DWDivDW_cond_emin_le]).

    Only ~3 of those p+3 binades of headroom are structurally needed (mh is
    th*(1+3u), and every other th-scaled node is far smaller), so conjunct 8
    could in principle come down to "yh is normal", 2^(emin+p-1) -- 54 binades
    lower for Tdouble.  What blocks it is the eta <= u^2 derivation above,
    which would then have to become an explicit format side condition
    p + 3 <= femax on every theorem in the chain.  That is a separate change;
    the lower bound never enters the error budget either way.

    Replacing conjunct 8 by finiteness of th in the style of
    [DWDivFP_mixed_safe_input_cond] would recover yh <> 0 and th-finiteness but
    none of those uses -- and unlike DW/FP division, which forms
    th = BDIV xh y and is therefore covered by its quotient ceiling, DW/DW has
    an explicit reciprocal node.  Thus the lower bound on |yh| remains in
    [DWDivDW_mixed_input_cond].  The quotient ceiling is omitted there because
    [DWDivDW_result_finite], checked after the kernel, supplies the required
    overflow information.

    This is the cond the runtime guard [dw_div_dw_check] discharges. *)
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


(* ------------------------------------------------------------------
   NORMAL-RANGE PURE RELATIVE TIER for DWDivDW3.

   [DWDivDW_normal] bundles the nine residual/product normal-range facts that
   the 9.8u^2 analysis needs in order to identify each rounded node of the
   reciprocal-bootstrap prologue and of the closing multiplication with its FLX
   counterpart.  All nine fail in the worst-case type (emin+2p = 2), so none is
   derivable from input magnitudes, and each of the underlying nodes may
   legitimately be zero -- which is precisely why the whole-range mixed tier
   above does not bound them below and pays a physical floor instead.

   It gets its own section so the algorithm's node names can be Notations, as
   in DDModels.DWDivDW3 itself.
   ------------------------------------------------------------------ *)
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
