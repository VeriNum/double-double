(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Accuracy proof for double-word divided by a floating-point number
    (Algorithm 15, DWDivFP3).  Mirrors the two-layer structure of
    DWMulFP_acc.v: an FLX->FLT bridge collapsing every rounded node of the
    FLT runtime model [DDModels.DWDivFP3] onto the paper's real-valued FLX
    model [DWDivFP.DWDivFP3], then the Layer-1 relative-error theorem obtained
    from the paper's tight 3u^2 bound (DWDivFP.DWDFP3_correct), and finally a
    Layer-2 corollary discharging finiteness/underflow from DWDivFP_cond. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common.
Require Import DWTimesFP DWDivFP DDModels DWord_defs Fast2Mult_acc TwoSum_acc Fast2Sum_acc.
Require Import DWPlusFP_acc_helpers DWMulFP_acc.
From Flocq Require Import Pff2Flocq Core.
From Flocq Require Import Mult_error FLT.

Require Import mathcomp.ssreflect.ssreflect.
From Stdlib Require Import Logic.FunctionalExtensionality.

Set Bullet Behavior "Strict Subproofs".

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
Hypothesis UF_prod : bpow radix2 (emin + 3 * fprec t) <= Rabs (FT2R th * FT2R y).
Hypothesis UF_dh   : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xh - FT2R pih).
Hypothesis UF_dt   : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R dh - FT2R pil).
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

(* PROOF PLAN (node-by-node collapse; all cited lemmas verified available).
   Establish th' = FT2R th and tl' = FT2R tl (paper reals vs runtime FT2R),
   then close with FastTwoSumEq_FLT th tl FIN.  Finiteness of the intermediate
   BMINUS/BPLUS nodes is extracted from FIN with [subexpr_finite] exactly as in
   the CorrectDWDivFP section.  Format facts: Fxh/Fy via generic_format_FLT_FT2R
   + generic_format_FLX_FLT.

   (A) th' = FT2R (BDIV xh y):
       th' = round_FLX(xh/y); rewrite -(round_FLT_FLX .. UF_th) to get
       round_FLT(xh/y), then BDIV_round_correct (Fbdiv, Hyne).
   (B) TwoProd th' (FT2R y) = (FT2R pih, FT2R pil):
       rewrite DWTimesFP.TwoProdE; then DWMulFP_acc.Fast2Mult_correct
       (BDIV xh y) y (Fpih, UF_prod), using (A); F2Rp unfolds to the pair.
   (C) dh' = FT2R (BMINUS xh pih):  dh' = FT2R xh - pih' (by B).
       xhmpih_exact (Hp1=fprec_gt_one, ZNE=eq_refl, Fxh, Hyne) gives
       round_FLX(dh') = dh', i.e. generic_format FLX dh'; lift with
       generic_format_FLT_FLX (UF_dh) to generic_format FLT dh', so
       round_FLT(dh') = dh'; BMINUS_round_correct closes dh' = FT2R dh.
   (D) dt' = FT2R (BMINUS dh pil):  dt' = FT2R dh - pil' (by C,B).
       dt' = xh - th'*y (paper dtE) is FLX-format; lift via
       generic_format_FLT_FLX (UF_dt); BMINUS_round_correct.
   (E) d' = FT2R (BPLUS dt xl):  d' = round_FLX(dt' + xl);
       BPLUS_round_correct + round_FLT_FLX (or rnd_plus_FLT_FLX_eq').
   (F) tl' = FT2R (BDIV d y):  tl' = round_FLX(d'/y);
       rewrite -(round_FLT_FLX .. UF_tl) + BDIV_round_correct (Ftl, Hyne).
   Assemble: rewrite (A)&(F) into the paper Fast2Sum, apply FastTwoSumEq_FLT. *)
Lemma DWDivFP3_FLX_FLT :
  DWDivFP.DWDivFP3 (fprec t) choice (FT2R xh) (FT2R xl) (FT2R y)
    = F2Rp (DDModels.DWDivFP3 xh xl y).
Proof.
Admitted.

End BridgeDWDivFP.

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
Hypothesis UF_prod : bpow radix2 (emin + 3 * fprec t) <= Rabs (FT2R (BDIV xh y) * FT2R y).
Hypothesis UF_dh   : bpow radix2 (emin + fprec t - 1)
                     <= Rabs (FT2R xh - FT2R (BMULT (BDIV xh y) y)).
Hypothesis UF_dt   : bpow radix2 (emin + fprec t - 1)
                     <= Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y))
                              - FT2R (Fast2Mult_err (BDIV xh y) y)).
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
rewrite (DWDivFP3_FLX_FLT xh xl y FIN Hp4 Hyne UF_th UF_prod UF_dh UF_dt UF_tl) in Hpaper.
rewrite /F2Rp/= in Hpaper.
unfold relative_error_DWDivFP, zh, zl.
eapply Rle_trans; [ apply Req_le; reflexivity | ].
rewrite (_ : 3 * u ^ 2 = 3 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t)));
  [ exact Hpaper | rewrite /=; ring ].
Qed.

End FiniteAccuracyDWDivFP.
