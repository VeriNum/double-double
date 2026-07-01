(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** This file contains accuracy proofs for the multiplication of two
    double-word numbers: the algorithm DWTimesDW3 (Algorithm 12), which is the
    functional model of the C routine dw_mult_dw12 (dd_lib/dw_mult_dw.c).

    ============================================================================
    SKELETON.  This file mirrors the section layout of DWMulFP_acc.v (the DW x FP
    accuracy proof) for the DW x DW case.  Every proof body is [Admitted]; the
    statements, notations, section structure and the Layer-2 corollary are in
    place so the file typechecks end-to-end and can be filled in incrementally.

    Correspondences with the DW x FP template:
      - 4 inputs (xh xl yh yl) instead of 3;  y -> double word (yh, yl);
      - the FLT model DWTimesDW3 has five rounded ops
          Fast2Mult xh yh ; BMULT xl yl ; BFMA xh yl _ ; BFMA xl yh _ ; BPLUS _ _
        then a closing Fast2Sum  (vs. two ops for DW x FP);
      - the relative-error bound is 4*u^2 (the paper proves the strict
          DWTimesDW.DWTimesDW12_correct : Rabs ((zh+zl-xy)/xy) < 4*(u*u));
      - the precision hypothesis is  5 <= fprec t  (paper's Hp5), not 3;
      - the FLX/paper model is DWTimesDW.DWTimesDW12 (paper_proofs/DWTimesDW.v).
    ============================================================================ *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common.
Require Import DWTimesFP DWTimesDW DDModels DWord_defs Fast2Mult_acc TwoSum_acc Fast2Sum_acc.
Require Import DWPlusFP_acc_helpers.
From Flocq Require Import Pff2Flocq Core.

From Stdlib Require Import Reals.Reals.

Require Import mathcomp.ssreflect.ssreflect.

(* for choice functions : choice = fun x0 : Z => negb (Z.even x0) *)
From Stdlib Require Import Logic.FunctionalExtensionality.

Set Bullet Behavior "Strict Subproofs".

(* Keep the paper's two-product folded; proofs expose it via TwoProdE. *)
Opaque DWTimesFP.TwoProd.
Arguments DWTimesFP.TwoProd : simpl never.


Lemma let_pair_eta {A B C} (p : A*B) (k : A -> B -> C) :
  (let '(a,b) := p in k a b) = k (fst p) (snd p).
Proof. destruct p; reflexivity. Qed.

(* No-overflow of an FMA implies finiteness (converse of
   is_finite_fma_no_overflow); mirrors no_overflow_sum_is_finite for BPLUS.
   Re-declared file-local (as in DWMulFP_acc.v). *)
Lemma no_overflow_fma_is_finite {NANS: Nans} {t : type} {STD: is_standard t} :
  forall (a b c : ftype t),
  is_finite a = true -> is_finite b = true -> is_finite c = true ->
  Rabs (rounded t (FT2R a * FT2R b + FT2R c)) < bpow Zaux.radix2 (femax t) ->
  is_finite (BFMA a b c) = true.
Proof. Admitted.


(* ============================================================
   Section 1: extract per-operation finiteness from
   FIN : is_finite_p (DWTimesDW3 xh xl yh yl).
   ============================================================ *)
Section CorrectDWMulDW.
  Context {NANS: Nans} {t : type} {STD: is_standard t}.

  Variables (xh xl yh yl : ftype t).

  Hypothesis FIN : is_finite_p (DWTimesDW3 xh xl yh yl).

  Ltac prove_finite :=
    move: FIN;
    rewrite /DWTimesDW3/is_finite_p //=;
    move => [] //=;
    subexpr_finite => //
  .

  Fact FINxh : is_finite xh = true.
  Proof. Admitted.

  Fact FINxl : is_finite xl = true.
  Proof. Admitted.

  Fact FINyh : is_finite yh = true.
  Proof. Admitted.

  Fact FINyl : is_finite yl = true.
  Proof. Admitted.

  (* ch = fst (Fast2Mult xh yh) = BMULT xh yh *)
  Fact FINmul : is_finite (BMULT xh yh) = true.
  Proof. Admitted.

  Fact FIN1 : is_finite_p (Fast2Mult xh yh).
  Proof. Admitted.

  Let cl1 := snd (Fast2Mult xh yh).
  Let tl0 := BMULT xl yl.
  Let tl1 := BFMA xh yl tl0.
  Let cl2 := BFMA xl yh tl1.
  Let cl3 := BPLUS cl1 cl2.

  Fact FINtl0 : is_finite tl0 = true.
  Proof. Admitted.

  Fact FINtl1 : is_finite tl1 = true.
  Proof. Admitted.

  Fact FINcl2 : is_finite cl2 = true.
  Proof. Admitted.

  Fact FINcl3 : is_finite cl3 = true.
  Proof. Admitted.

End CorrectDWMulDW.


(* ============================================================
   Section 2: FLX TwoProd = FLT Fast2Mult, for the high product (xh, yh).
   Identical in content to DWMulFP_acc.v's Fast2Mult_correct (concerns a
   two-FP product only, no DW specifics).
   ============================================================ *)
Section CorrectDWMulDW'.
  Context {NANS: Nans} {t : type} {STD: is_standard t}.

  Notation emin := (common.emin (t:=t)).

  Variables (a b : ftype t).

  Hypothesis (Fast2Mult_overflow_condition : is_finite (BMULT a b) = true).
  Hypothesis (Fast2Mult_underflow_condition_strict : (FT2R a * FT2R b) <> 0 ->
    bpow Zaux.radix2 (emin + 3 * fprec t) <= Rabs (FT2R a * FT2R b)).

  Lemma Fast2Mult_correct :
    DWTimesFP.Fast2Mult (fprec t) choice (FT2R a) (FT2R b) = F2Rp (Fast2Mult a b).
  Proof. Admitted.

End CorrectDWMulDW'.

(* Weak variant under the minimal underflow threshold emin + 2*fprec - 1. *)
Section CorrectDWMulDW_weak.
  Context {NANS: Nans} {t : type} {STD: is_standard t}.

  Notation emin := (common.emin (t:=t)).

  Variables (a b : ftype t).

  Hypothesis (Fast2Mult_overflow_condition : is_finite (BMULT a b) = true).
  Hypothesis (Fast2Mult_underflow_condition : (FT2R a * FT2R b) <> 0 ->
    bpow Zaux.radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R a * FT2R b)).

  Lemma Fast2Mult_correct_weak :
    DWTimesFP.Fast2Mult (fprec t) choice (FT2R a) (FT2R b) = F2Rp (Fast2Mult a b).
  Proof. Admitted.

End CorrectDWMulDW_weak.


(* ============================================================
   Section 3: the load-bearing FLX -> FLT bridge for DWTimesDW3.
     DWTimesDW.DWTimesDW12 (fprec t) choice (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl)
       = F2Rp (DWTimesDW3 xh xl yh yl).
   Analog of DWMulFP_acc.v's DWTimesFP3_FLX_FLT: each of the five rounded ops
   agrees with its FLX counterpart (round_FLT_FLX + representability), and the
   closing Fast2Sum is exact via the magnitude ordering |cl3| <= |ch|.
   ============================================================ *)
Section CorrectDWMulDW_bridge.

Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (common.emin (t:=t)).
Notation u   := (bpow radix2 (- fprec t)).
Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).

Let ulp := (Ulp.ulp radix2 (SpecFloat.fexp (fprec t) (femax t))).

Variables (xh xl yh yl : ftype t).

Hypothesis xE : double_word xh xl.
Hypothesis yE : double_word yh yl.

(* cl3 = BPLUS cl1 cl2, with cl1 = Fast2Mult_err xh yh and
   cl2 = BFMA xl yh (BFMA xh yl (BMULT xl yl)).  Magnitude ordering for the
   closing Fast2Sum (ch <> 0): |cl3| <= |ch| = |Fast2Mult_mul xh yh|.
   FLT counterpart of the paper's F2Sum_correct_abs precondition inside
   DWTimesDW12_correct. *)
Lemma DWTimesDW3_cl3_le_ch :
  is_finite (BPLUS (Fast2Mult_mul xh yh)
               (BPLUS (Fast2Mult_err xh yh)
                      (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) = true ->
  FT2R (Fast2Mult_mul xh yh) <> 0 ->
  Rabs (FT2R (BPLUS (Fast2Mult_err xh yh)
                    (BFMA xl yh (BFMA xh yl (BMULT xl yl)))))
    <= Rabs (FT2R (Fast2Mult_mul xh yh)).
Proof. Admitted.

(* snd-output finiteness follows from fst-output finiteness via the closing
   Fast2Sum ulp-ordering precondition (is_finite_FastSum_ulp). *)
Lemma is_finite_DWTimesDW3 :
  is_finite (fst (DWTimesDW3 xh xl yh yl)) = true ->
  is_finite (snd (DWTimesDW3 xh xl yh yl)) = true.
Proof. Admitted.

Hypothesis FIN : is_finite_p (DWTimesDW3 xh xl yh yl).
Hypothesis Hp5 : (5 <= fprec t)%Z.
Hypothesis DWTimesDWUnderflowHyp1:
  bpow radix2 (emin + 3 * fprec t) <= Rabs (FT2R xh * FT2R yh).
Hypothesis DWTimesDWUnderflowHyp2:
  bpow radix2 (emin + fprec t - 1) +
  / 2 * Ulp.ulp radix2 fexp (FT2R xh * FT2R yh)
    <= Rabs (FT2R xl * FT2R yh).

Theorem DWTimesDW3_FLX_FLT :
  DWTimesDW.DWTimesDW12 (fprec t) choice
    (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl)
    = F2Rp (DWTimesDW3 xh xl yh yl).
Proof. Admitted.

End CorrectDWMulDW_bridge.

(* Weak FLX->FLT bridge under the minimal thresholds (emin+2*fprec-1 product,
   normal accumulated low term), surviving in the [emin+2p-1, emin+3p) band. *)
Section CorrectDWMulDW_weak_bridge.

Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (common.emin (t:=t)).

Variables (xh xl yh yl : ftype t).

Hypothesis xE : double_word xh xl.
Hypothesis yE : double_word yh yl.
Hypothesis FIN : is_finite_p (DWTimesDW3 xh xl yh yl).
Hypothesis Hp5 : (5 <= fprec t)%Z.
Hypothesis Hbig :
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh).

Theorem DWTimesDW3_FLX_FLT_weak :
  DWTimesDW.DWTimesDW12 (fprec t) choice
    (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl)
    = F2Rp (DWTimesDW3 xh xl yh yl).
Proof. Admitted.

End CorrectDWMulDW_weak_bridge.


(* ============================================================
   Section 4: finiteness of DWTimesDW3 from DWTimesDW_cond.
     fst (DWTimesDW3 xh xl yh yl) = BPLUS ch cl3, where
       ch  = Fast2Mult_mul xh yh   (= BMULT xh yh),
       cl3 = BPLUS (Fast2Mult_err xh yh) (BFMA xl yh (BFMA xh yl (BMULT xl yl))).
   The cond's product bound |round(xh*yh)| <= Omega/4 keeps |ch| small; the two
   double-word relations keep cl3 small; the closing Fast2Sum stays finite.
   ============================================================ *)
Section DWTimesDW_Finite.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin  := (@common.emin t).
Notation fexp  := (SpecFloat.fexp (fprec t) (femax t)).
Notation ulp   := (Ulp.ulp Zaux.radix2 fexp).
Notation Omega := (bpow Zaux.radix2 (femax t)).

Local Instance valid_fexp_inst : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.

(* --- Generic auxiliary bounds (identical to DWMulFP_acc.v) --- *)

Lemma aux_dwu (a b : ftype t) :
  double_word_prop a b -> Rabs (FT2R b) <= /2 * ulp (FT2R a).
Proof. Admitted.

Lemma aux_format_half_Omega : generic_format radix2 fexp (/2 * Omega).
Proof. Admitted.

Lemma aux_xhy_bnd (a b : ftype t) :
  is_finite (BMULT a b) = true ->
  Rabs (FT2R (BMULT a b)) <= /4 * Omega ->
  Rabs (FT2R a * FT2R b) <= /2 * Omega.
Proof. Admitted.

Lemma aux_round_ub (v : R) :
  Rabs (round radix2 fexp (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) v)
    <= Rabs v + /2 * ulp v.
Proof. Admitted.

Lemma aux_ulp_real (v : R) :
  Rabs v < Omega -> ulp v <= bpow radix2 (femax t - fprec t).
Proof. Admitted.

Lemma aux_format_small_0 (x : R) :
  generic_format radix2 fexp x -> Rabs x < bpow radix2 emin -> x = 0.
Proof. Admitted.

Lemma aux_dwu_rel (a b : ftype t) :
  double_word_prop a b ->
  Rabs (FT2R b) <= bpow radix2 (- fprec t) * Rabs (FT2R a).
Proof. Admitted.

(* --- DW x DW-specific term bounds (new; the extra products / FMAs) --- *)

(* |xh*yl| and |xl*yh| are ~u-small relative to |xh*yh| (one low word each);
   |xl*yl| is ~u^2-small (both low words).  Each stays well under Omega. *)
Lemma aux_xhyl_bnd (xh xl yh yl : ftype t) :
  double_word_prop yh yl ->
  Rabs (FT2R xh * FT2R yh) <= /2 * Omega ->
  Rabs (FT2R xh * FT2R yl) <= /2 * bpow radix2 (femax t - fprec t).
Proof. Admitted.

Lemma aux_xlyh_bnd (xh xl yh yl : ftype t) :
  double_word_prop xh xl ->
  Rabs (FT2R xh * FT2R yh) <= /2 * Omega ->
  Rabs (FT2R xl * FT2R yh) <= /2 * bpow radix2 (femax t - fprec t).
Proof. Admitted.

Lemma aux_xlyl_bnd (xh xl yh yl : ftype t) :
  double_word_prop xh xl ->
  double_word_prop yh yl ->
  Rabs (FT2R xh * FT2R yh) <= /2 * Omega ->
  Rabs (FT2R xl * FT2R yl) <= /2 * bpow radix2 (femax t - fprec t).
Proof. Admitted.

(* Magnitude ordering |cl3| <= |ch| for the closing Fast2Sum, in the normal
   product regime |xh*yh| >= bpow(emin+2p-1). *)
Lemma aux_cl3_le_ch (xh xl yh yl : ftype t) :
  double_word_prop xh xl ->
  double_word_prop yh yl ->
  is_finite (BMULT xh yh) = true ->
  is_finite (BPLUS (Fast2Mult_err xh yh)
                   (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) = true ->
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh) ->
  Rabs (FT2R (BPLUS (Fast2Mult_err xh yh)
                    (BFMA xl yh (BFMA xh yl (BMULT xl yl)))))
    <= Rabs (FT2R (Fast2Mult_mul xh yh)).
Proof. Admitted.

(* MAIN: the closing Fast2Sum of DWTimesDW3 stays finite under the cond. *)
Lemma DWTimesDW3_fst_finite (xh xl yh yl : ftype t) :
  DWTimesDW_cond xh xl yh yl ->
  is_finite (fst (DWTimesDW3 xh xl yh yl)) = true.
Proof. Admitted.

(* Finiteness of the snd output from the cond, via the closing Fast2Sum
   ulp-ordering precondition (ch = 0 when xh*yh = 0, else aux_cl3_le_ch). *)
Lemma DWTimesDW3_snd_finite (xh xl yh yl : ftype t) :
  DWTimesDW_cond xh xl yh yl ->
  is_finite (snd (DWTimesDW3 xh xl yh yl)) = true.
Proof. Admitted.

End DWTimesDW_Finite.


(* ============================================================
   Section 5: Layer-1 / Layer-2 accuracy for DWTimesDW3 (Algorithm 12).

   The Layer-1 theorem DWTimesDW_relerr_bound is to be proved by:
     - the underflow leg (xh*yh = 0): the exact product xr*yr is 0, so
       relerr = 0 (relerr_0_of_xryr0 + xryr0_of_prod0);
     - the normal leg: the FLX->FLT bridge DWTimesDW3_FLX_FLT(_weak) lifts the
       paper's tight FLX bound DWTimesDW.DWTimesDW12_correct (< 4*(u*u)) to the
       FLT conclusion.
   The corollary DWTimesDW_accuracy_from_cond is the Layer-2 interface used by
   the VST guarded wrapper spec (verif_proofs/verif_dw_mult_dw.v).
   ============================================================ *)
Section DWTimesDW_Accuracy.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation u      := (bpow Zaux.radix2 (- fprec t)).
Notation fexp   := (SpecFloat.fexp (fprec t) (femax t)).
Notation eminA  := (SpecFloat.emin (fprec t) (femax t)).
Notation ulp    := (Ulp.ulp Zaux.radix2 fexp).
Notation OmegaA := (bpow Zaux.radix2 (femax t)).

Local Instance valid_fexp_inst_acc : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.

Variables (xh xl yh yl : ftype t).

Let zh := FT2R (fst (DWTimesDW3 xh xl yh yl)).
Let zl := FT2R (snd (DWTimesDW3 xh xl yh yl)).
Let xr := (FT2R xh + FT2R xl).
Let yr := (FT2R yh + FT2R yl).

Definition relative_error_DWTimesDW : R :=
  Rabs (((zh + zl) - xr * yr) / (xr * yr)).

(* When the exact product xr*yr is 0 the relative error is 0 (Coq's _/0 = 0). *)
Lemma relerr_0_of_xryr0 : xr * yr = 0 -> relative_error_DWTimesDW = 0.
Proof. Admitted.

(* xh*yh = 0 forces xr*yr = 0: FT2R xh = 0 -> FT2R xl = 0 (double_word), and
   symmetrically for yh, yl. *)
Lemma xryr0_of_prod0 :
  double_word_prop xh xl ->
  double_word_prop yh yl ->
  FT2R xh * FT2R yh = 0 -> xr * yr = 0.
Proof. Admitted.

(* Load-bearing Layer-1 theorem.  Carries the underflow disjunction (same shape
   as DWTimesDW_cond's) and dispatches on it.  Bound is 4*u^2 (the paper proves
   the strict < 4*(u*u); we state the non-strict form here). *)
Theorem DWTimesDW_relerr_bound :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  (FT2R xh * FT2R yh = 0 \/
   bpow Zaux.radix2 (SpecFloat.emin (fprec t) (femax t) + 2 * fprec t - 1)
   <= Rabs (FT2R xh * FT2R yh)) ->
  relative_error_DWTimesDW <= 4 * u ^ 2.
Proof. Admitted.

(* Layer-2 corollary: a thin wrapper over DWTimesDW_relerr_bound.  Pulls the
   Layer-1 hypotheses out of DWTimesDW_cond (verified at the spec interface):
     - double_word          <- the cond's double_word_prop (convertible);
     - is_finite_p          <- DWTimesDW3_fst_finite / DWTimesDW3_snd_finite;
     - the underflow disjunction is passed through verbatim.
   The 5 <= fprec t hypothesis is threaded by the caller (true for Tdouble). *)
Corollary DWTimesDW_accuracy_from_cond :
  (5 <= fprec t)%Z ->
  DWTimesDW_cond xh xl yh yl ->
  relative_error_DWTimesDW <= 4 * u ^ 2.
Proof. Admitted.

End DWTimesDW_Accuracy.
