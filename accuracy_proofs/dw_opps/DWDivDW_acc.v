(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Accuracy proof for double-word divided by a double-word number
    (Algorithm 18, DWDivDW3).  LAYER-1 SKELETON.

    DWDivDW3 is *compositional* (see DDModels.v): a reciprocal-bootstrap
    prologue

        th := BDIV 1 yh ; rh := BFMA (-yh) th 1 ; rl := -(BMULT yl th) ;
        (eh,el) := Fast2Sum rh rl ;
        (dh,dl) := DWTimesFP3 eh el th ;
        (mh,ml) := DWPlusFP  dh dl th ;
        (zh,zl) := DWTimesDW3 xh xl mh ml

    whose closing block is exactly the DW*DW multiply whose bridge/accuracy
    live in DWMulDW_acc.v.  The paper's FLX model (paper_proofs/DWDivDW.v) has
    the identical shape and its tight relative-error bound is
    DWDivDW.DWDDW3_correct : Rabs ((zh+zl - (x/y))/(x/y)) <= 98/10*u^2
    (requires 14 <= p, both operands double_word, yh <> 0).

    This file mirrors the two-layer structure of DWDivFP_acc.v / DWMulDW_acc.v:
      - Section CorrectDWDivDW : extract per-node finiteness from
        FIN : is_finite_p (DWDivDW3 xh xl yh yl).
      - Section BridgeDWDivDW : the FLX->FLT bridge DWDivDW3_FLX_FLT, obtained
        by *composing* the prologue leaf bridges with the already-proven
        sub-block bridges (DWMulDW_acc.DWTimesDW3_FLX_FLT for the closing
        multiply, plus the DWTimesFP3 / DWPlusFP bridges), under a strong-
        underflow discipline placing every rounded node in the normal range.
      - Section FiniteAccuracyDWDivDW : the Layer-1 relative-error theorem
        (<= 98/10*u^2) obtained from DWDDW3_correct via the bridge.

    LAYER-1 status: the substantive obligations are [admit]ed with a one-line
    comment naming the paper lemma / sub-block bridge that discharges them in
    the Layer-2 pass.  Deferred: (a) the mechanical per-node finiteness
    decomposition; (b) the compositional bridge and its prologue leaves;
    (c) instantiating DWDDW3_correct -- this additionally requires discharging
    the paper's abstract two-product hypotheses (Fast2Mult_correct, TwoProdE),
    which the (un-refactored) paper_proofs/DWDivDW.v still carries. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common.
Require Import DWTimesFP DWTimesDW DWDivFP DDModels DWord_defs
               Fast2Mult_acc TwoSum_acc Fast2Sum_acc.
(* NOTE: paper_proofs/DWDivDW.v (which holds the target bound DWDDW3_correct)
   is intentionally NOT required here.  That file was never compiled and needs
   proof repair (see the LAYER-2 note on relative_errorDWDivDW3_correct below);
   the Layer-1 skeleton is deliberately decoupled from it so it builds green. *)
Require Import DWPlusFP_acc_helpers DWMulFP_acc DWPlusFP_acc DWMulDW_acc
               DW_acc_lemmas.
From Flocq Require Import Pff2Flocq Core.
From Flocq Require Import Mult_error FLT Div_sqrt_error.

Require Import mathcomp.ssreflect.ssreflect.
From Stdlib Require Import Logic.FunctionalExtensionality.

Set Bullet Behavior "Strict Subproofs".

(* Keep the paper's two-product folded; proofs expose it via DWTimesFP.TwoProdE. *)
Opaque DWTimesFP.TwoProd.
Arguments DWTimesFP.TwoProd : simpl never.

(* ============================================================
   Section 1: extract per-operation finiteness from
   FIN : is_finite_p (DWDivDW3 xh xl yh yl).

   Runtime shape (DDModels.DWDivDW3):
     th := BDIV (Zconst t 1) yh
     rh := BFMA (BOPP yh) th (Zconst t 1)
     rl := BOPP (BMULT yl th)
     (eh,el) := Fast2Sum rh rl
     (dh,dl) := DWTimesFP3 eh el th
     (mh,ml) := DWPlusFP  dh dl th
     (zh,zl) := DWTimesDW3 xh xl mh ml
   ============================================================ *)
Section CorrectDWDivDW.
  Context {NANS: Nans} {t : type} {STD: is_standard t}.

  Variables (xh xl yh yl : ftype t).

  Hypothesis FIN : is_finite_p (DWDivDW3 xh xl yh yl).

  Notation th  := (BDIV (Zconst t 1) yh).
  Notation rh  := (BFMA (BOPP yh) th (Zconst t 1)).
  Notation rl  := (BOPP (BMULT yl th)).
  Notation eh  := (fst (Fast2Sum rh rl)).
  Notation el  := (snd (Fast2Sum rh rl)).
  Notation dh  := (fst (DWTimesFP3 eh el th)).
  Notation dl  := (snd (DWTimesFP3 eh el th)).
  Notation mh  := (fst (DWPlusFP dh dl th)).
  Notation ml  := (snd (DWPlusFP dh dl th)).

  (* The closing DWTimesDW3 xh xl mh ml is finite as a pair; its per-node
     finiteness follows from DWMulDW_acc's CorrectDWMulDW facts applied at
     (xh, xl, mh, ml).  The prologue nodes (th, rh, rl, eh, el, dh, dl, mh, ml)
     are finite by a BPLUS/BFMA/BMULT finite-elimination pass on FIN, exactly
     as in DWMulDW_acc.v's [prove_finite]. *)

  Fact FIN_th : is_finite th = true.
  Proof.
    (* LAYER-2: unfold DWDivDW3 through DWTimesDW3, then repeated
       BPLUS_finite_e / BFMA_finite_e / BMULT_finite_e; th appears in every
       leaf via mh, ml.  Mechanical (cf. DWMulDW_acc.v:123). *)
  Admitted.

  Fact FIN_mul : is_finite_p (DWTimesDW3 xh xl mh ml).
  Proof.
    (* LAYER-2: fst/snd of DWDivDW3 are exactly fst/snd of this DWTimesDW3;
       split FIN and re-pair. *)
  Admitted.

  Fact FIN_mh : is_finite mh = true.
  Proof.
    (* LAYER-2: mh is the high operand of the closing DWTimesDW3; extract via
       DWMulDW_acc.CorrectDWMulDW.FINyh applied at (xh,xl,mh,ml). *)
  Admitted.

  Fact FIN_ml : is_finite ml = true.
  Proof.
    (* LAYER-2: as FIN_mh via CorrectDWMulDW.FINyl. *)
  Admitted.

End CorrectDWDivDW.

(* ============================================================
   Section 2: FLX -> FLT bridge for DWDivDW3.

   Collapses the FLT runtime model DDModels.DWDivDW3 onto the paper's
   real-valued FLX model, node by node, under a strong-underflow discipline:
   every rounded node carries a lower bound placing it in the normal range so
   round_FLT agrees with round_FLX (round_FLT_FLX), and the closing DW*DW
   multiply is discharged by DWMulDW_acc.DWTimesDW3_FLX_FLT.

   The paper's FLX reciprocal prologue (paper_proofs/DWDivDW.v:1937-1949):
     th_r := rnd_p (/ yh)
     rh_r := 1 - yh * th_r
     rl_r := - rnd_p (yl * th_r)
     eh_r := rnd_p (rh_r + rl_r) ; el_r := snd (Fast2Sum rh_r rl_r)
     (dh_r,dl_r) := DWTimesFP9 eh_r el_r th_r
     (mh_r,ml_r) := DWPlusFP   dh_r dl_r th_r
     DWDivDW3_FLX := DWTimesDW12 xh xl mh_r ml_r
   ============================================================ *)
Section BridgeDWDivDW.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (common.emin (t:=t)).
Notation rnd_p := (round radix2 (FLX_exp (fprec t)) (Znearest choice)).

Variables (xh xl yh yl : ftype t).

Hypothesis FIN  : is_finite_p (DWDivDW3 xh xl yh yl).
Hypothesis Hp14 : (14 <= fprec t)%Z.
Hypothesis Hyhne : FT2R yh <> 0.

(* Runtime prologue nodes (see DDModels.DWDivDW3). *)
Notation th  := (BDIV (Zconst t 1) yh).
Notation rh  := (BFMA (BOPP yh) th (Zconst t 1)).
Notation rl  := (BOPP (BMULT yl th)).
Notation eh  := (fst (Fast2Sum rh rl)).
Notation el  := (snd (Fast2Sum rh rl)).
Notation dh  := (fst (DWTimesFP3 eh el th)).
Notation dl  := (snd (DWTimesFP3 eh el th)).
Notation mh  := (fst (DWPlusFP dh dl th)).
Notation ml  := (snd (DWPlusFP dh dl th)).

(* per-node normal-range hypotheses (strong-underflow discipline).  One family
   for each prologue node; the closing DWTimesDW3 delegates to the underflow
   family of DWMulDW_acc.DWTimesDW3_FLX_FLT (Nprod, N0..N3) at (xh,xl,mh,ml). *)
Hypothesis UF_th   : bpow radix2 (emin + fprec t - 1) <= Rabs (1 / FT2R yh).
Hypothesis UF_rl   : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R yl * FT2R th).
Hypothesis UF_eh   : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R rh + FT2R rl).
(* the DWTimesFP3 / DWPlusFP sub-blocks and the closing DWTimesDW3 carry their
   own per-node families, delegated to their respective bridges. *)

(* The FLX->FLT bridge.  RHS is the paper's FLX DWTimesDW12 evaluated at the
   FLX-reconstructed reciprocal prologue (mh_r, ml_r), written with exported
   operators so it matches the inlined Let in DWDDW3_correct up to conversion. *)
Lemma DWDivDW3_FLX_FLT :
  F2Rp (DWDivDW3 xh xl yh yl)
    = (let th_r := rnd_p (1 / FT2R yh) in
       let rh_r := (1 - FT2R yh * th_r)%R in
       let rl_r := (- rnd_p (FT2R yl * th_r))%R in
       let eh_r := rnd_p (rh_r + rl_r) in
       let el_r := snd (F2Sum.Fast2Sum (fprec t) choice rh_r rl_r) in
       let dhl  := DWTimesFP.DWTimesFP9 (fprec t) choice eh_r el_r th_r in
       let mhl  := DWPlus.DWPlusFP (fprec t) choice (fst dhl) (snd dhl) th_r in
       DWTimesDW.DWTimesDW12 (fprec t) choice
         (FT2R xh) (FT2R xl) (fst mhl) (snd mhl)).
Proof.
  (* LAYER-2 composition:
       1. prologue leaf bridges: th (BDIV_round_correct + round_FLT_FLX, UF_th),
          rh (BFMA round-identity, exact by Sterbenz-style cancellation),
          rl (BMULT + round_FLT_FLX, UF_rl), (eh,el) (FastTwoSumEq_FLT, UF_eh);
       2. sub-block bridges: DWTimesFP3 = DWTimesFP9 (FLX) and DWPlusFP
          (FLT->FLX) for (dh,dl),(mh,ml);
       3. closing multiply: DWMulDW_acc.DWTimesDW3_FLX_FLT at (xh,xl,mh,ml). *)
Admitted.

End BridgeDWDivDW.

(* ============================================================
   Section 3: Layer-1 relative-error theorem for DWDivDW3.
   Mirrors DWDivFP_acc.v:274-321 (relative_errorDWDivFP3_correct): instantiate
   the paper's tight bound DWDivDW.DWDDW3_correct (98/10*u^2), rewrite the FLX
   model via the bridge, and read off the numeric bound.
   ============================================================ *)
Section FiniteAccuracyDWDivDW.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (common.emin (t:=t)).
Notation u   := (bpow radix2 (- fprec t)).

Variables (xh xl yh yl : ftype t).
Let zh := FT2R (fst (DWDivDW3 xh xl yh yl)).
Let zl := FT2R (snd (DWDivDW3 xh xl yh yl)).

Hypothesis DWx  : double_word xh xl.
Hypothesis DWy  : double_word yh yl.
Hypothesis FIN  : is_finite_p (DWDivDW3 xh xl yh yl).
Hypothesis Hp14 : (14 <= fprec t)%Z.
Hypothesis Hyhne : FT2R yh <> 0.
(* the strong-underflow families for every rounded node, as consumed by
   DWDivDW3_FLX_FLT (prologue) and by the sub-block/closing bridges. *)

Definition relative_error_DWDivDW :=
  Rabs ((zh + zl - (FT2R xh + FT2R xl) / (FT2R yh + FT2R yl))
        / ((FT2R xh + FT2R xl) / (FT2R yh + FT2R yl))).

Theorem relative_errorDWDivDW3_correct :
  relative_error_DWDivDW <= 98/10 * u ^ 2.
Proof.
  (* LAYER-2:
       have HDWx : DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl)
         by apply (dw_word_DWdouble xh xl yh); exact DWx.
       have HDWy : DWPlus.double_word (fprec t) choice (FT2R yh) (FT2R yl)
         by apply (dw_word_DWdouble yh yl yh); exact DWy.
       pose proof (@DWDivDW.DWDDW3_correct (fprec t) (fprec_gt_one t) choice
                     eq_refl F2Mult_disch TwoProdE_disch
                     (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl)
                     HDWx HDWy Hp14 Hyhne) as Hpaper.
       rewrite (DWDivDW3_FLX_FLT xh xl yh yl FIN Hp14 Hyhne ...) in Hpaper.
       rewrite /F2Rp/= in Hpaper.
       unfold relative_error_DWDivDW, zh, zl.
       (* then the 98/10*u^2 = 98/10*(bpow*bpow) numeric collapse, cf.
          DWDivFP_acc.v:317. *)
     The instantiation additionally requires discharging the paper's abstract
     two-product hypotheses Fast2Mult_correct / TwoProdE (F2Mult_disch,
     TwoProdE_disch); TwoProdE is DWTimesFP.TwoProdE, Fast2Mult_correct is the
     FLX Dekker exactness of the concrete two-product.

     PREREQUISITE (blocks this whole path): paper_proofs/DWDivDW.v must first be
     compiled -- it was never built and is absent from _CoqProject.  Findings
     from the Layer-1 pass:
       * DWDivDW.v line 14 imports the stale paper_proofs/DWTimesDW_original.v.
         DWTimesDW_original.v does not compile: each of its 3 sections (Algo10/
         11/12) is MISSING [Notation TwoProd := (TwoProd p choice)] beside its
         [Notation Fast2Mult := (Fast2Mult p choice)], and after adding those a
         further proof-rot surfaces ([rewrite TwoProdE] "LHS does not match").
       * The maintained paper_proofs/DWTimesDW.v already provides ALL symbols
         DWDivDW.v needs (DWTimesDW12, DWTimesDW12_correct, DWTimesDW12_Asym_l/r,
         DWTimesDW12Sy) and its DWTimesDW12_correct no longer carries the
         abstract two-product hypotheses.  Repointing DWDivDW.v's import to
         DWTimesDW builds further but then fails inside DWDivDW.v's own proofs
         with an arg-order mismatch (a lemma is applied with ZNE where a Z is
         expected), because those proofs are coupled to _original's API.
     So Layer-2 begins by choosing one of: (a) repair DWTimesDW_original.v's
     proof rot, or (b) repoint to DWTimesDW.v and fix DWDivDW.v's arg-order
     mismatches; then add paper_proofs/DWDivDW.v to _CoqProject and re-require it
     here. *)
Admitted.

End FiniteAccuracyDWDivDW.
