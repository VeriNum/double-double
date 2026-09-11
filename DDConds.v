(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Preconditions and postconditions for the double-word functional models. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs common.
Require Export DDModels.


Section Fast2SumCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

(** Sufficient condition for [Fast2Sum] to reconstruct the exact sum. *)
Definition Fast2Sum_exact_cond (a b : ftype t) : Prop :=
  is_finite (BPLUS a b) = true /\
  ((Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (FT2R b) <=
    Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (FT2R a))%R \/
   FT2R a = 0%R).

End Fast2SumCond.


Section Fast2MultCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

(** Requires the leading rounded product to be finite. *)
Definition Fast2Mult_product_finite_cond (a b : ftype t) : Prop :=
  is_finite (BMULT a b) = true.

(** Sufficient condition for [Fast2Mult] to reconstruct the exact product. *)
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

(** Sufficient input condition used by the strong C interface. *)
Definition DWPlusFP_strong_precond (xh xl y : ftype t) : Prop :=
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite y  = true /\
  double_word_prop xh xl /\
  Rabs (FT2R xh) <= /4 * Omega /\
  Rabs (FT2R y)  <= /4 * Omega.

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

(** Preconditions for the relative error bound on [DWTimesFP]. *)
Definition DWTimesFP_relative_precond (xh xl y : ftype t) : Prop :=
  is_finite xl = true /\
  double_word_prop xh xl /\
  Fast2Mult_exact_cond xh y /\
  Rabs (FT2R xh * FT2R y) <= /2 * Omega.

(** Input-only precondition ensuring a finite [DWTimesFP] result. *)
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

(** Preconditions for an exact leading product in [DWTimesDW]. *)
Definition DWTimesDW_exact_leading_product_precond (xh xl yh yl : ftype t) : Prop :=
  is_finite xl = true /\
  is_finite yl = true /\
  double_word_prop xh xl /\
  double_word_prop yh yl /\
  Fast2Mult_exact_cond xh yh /\
  Rabs (FT2R xh * FT2R yh) <= /2 * Omega.

(** Input-only precondition ensuring a finite [DWTimesDW] result. *)
Definition DWTimesDW_strong_precond (xh xl yh yl : ftype t) : Prop :=
  is_finite xl = true /\
  is_finite yl = true /\
  double_word_prop xh xl /\
  double_word_prop yh yl /\
  is_finite (BMULT xh yh) = true /\
  Rabs (FT2R xh * FT2R yh) <= /2 * Omega.

(** Preconditions for the relative error bound on [DWTimesDW]. *)
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

(** Input-only precondition ensuring a finite [DWDivFP] result. *)
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

Definition DWDivFP_weak_precond
    (xh xl y : ftype t) : Prop :=
  double_word_prop xh xl /\
  (FT2R xh = 0 \/
   bpow Zaux.radix2 (emin + 2 * fprec t) <= Rabs (FT2R xh)).

Definition DWDivFP_finite_post_cond
    (xh xl y : ftype t) : Prop :=
  is_finite_p (DWDivFP xh xl y).

Definition DWDivFP_weak_pre_and_finite_post_cond
    (xh xl y : ftype t) : Prop :=
  DWDivFP_weak_precond xh xl y /\
  DWDivFP_finite_post_cond xh xl y.

(** Normal-range condition for the relative error bound on [DWDivFP]. *)
Definition DWDivFP_relative_regime_cond (xh xl y : ftype t) : Prop :=
  bpow Zaux.radix2 (emin + fprec t - 1) <= Rabs (FT2R xh / FT2R y) /\
  (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                       (Fast2Mult_err (BDIV xh y) y)) xl) = 0 \/
   bpow Zaux.radix2 (emin + fprec t - 1)
     <= Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                  (Fast2Mult_err (BDIV xh y) y)) xl)
              / FT2R y)).

(** Preconditions for the relative error bound on [DWDivFP]. *)
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

(** Input-only precondition ensuring a finite [DWDivDW] result. *)
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

Definition DWDivDW_finite_post_cond
    (xh xl yh yl : ftype t) : Prop :=
  is_finite_p (DWDivDW xh xl yh yl).

Definition DWDivDW_weak_pre_and_finite_post_cond
    (xh xl yh yl : ftype t) : Prop :=
  DWDivDW_weak_precond xh xl yh yl /\
  DWDivDW_finite_post_cond xh xl yh yl.

End DWDivDWCond.


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

(** Normal-range conditions for the relative error bound on [DWDivDW]. *)
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

(** Preconditions for the relative error bound on [DWDivDW]. *)
Definition DWDivDW_relative_precond (xh xl yh yl : ftype t) : Prop :=
  DWDivDW_strong_precond xh xl yh yl /\
  DWDivDW_relative_regime_cond xh xl yh yl.

Lemma DWDivDW_strong_precond_of_relative_precond
    (xh xl yh yl : ftype t) :
  DWDivDW_relative_precond xh xl yh yl ->
  DWDivDW_strong_precond xh xl yh yl.
Proof. intros [Hsafe _]; exact Hsafe. Qed.

End DWDivDWRelativeCond.
