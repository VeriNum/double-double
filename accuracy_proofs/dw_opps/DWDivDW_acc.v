(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Accuracy and representation results for [DWDivDW3], the implementation
    model of Algorithm 18 for dividing one double-word number by another.

    A double-word value is represented by a pair [(xh,xl)] whose sum denotes
    the represented real number.  [DWDivDW3] first constructs an approximation
    [(mh,ml)] to the reciprocal of the divisor [(yh,yl)], then multiplies the
    dividend [(xh,xl)] by that approximation.

    DWDivDW3 is *compositional* (see DDModels.v): a reciprocal-bootstrap
    prologue

        th := BDIV 1 yh ; rh := BFMA (-yh) th 1 ; rl := -(BMULT yl th) ;
        (eh,el) := Fast2Sum rh rl ;
        (dh,dl) := DWTimesFP3 eh el th ;
        (mh,ml) := DWPlusFP  dh dl th ;
        (zh,zl) := DWTimesDW3 xh xl mh ml

    The closing block is the double-word multiplication analyzed in
    [DWMulDW_acc.v].  This file connects three views of the algorithm:

      - [DDModels.DWDivDW3], the finite-precision runtime model used by the
        verification of [dw_div_dw18];
      - [DWDivDW.DWDivDW3], the idealized FLX model analyzed in the paper;
      - the relative-error statement for the real value represented by the
        pair returned by the runtime model.

    FLT below means the runtime floating-point model, including its bounded
    exponent range.  FLX means the paper's idealized model with the same
    precision but an unbounded exponent range.  A bridge theorem proves that
    the two models agree when the relevant operations do not underflow.

    The paper's tight relative-error bound is
    DWDivDW.DWDDW3_correct : Rabs ((zh+zl - (x/y))/(x/y)) <= 98/10*u^2
    (requires 14 <= p, both operands double_word, yh <> 0).

    Main results:

      - [FIN_mul], [FIN_mh], [FIN_ml], and [FIN_th] recover useful finiteness
        facts about intermediate computations from finiteness of the result.
      - [DWTimesDW3_double_word] proves that the multiplication subroutine
        returns a valid double-word under finiteness and normal-range
        assumptions.
      - [DWDivDW3_double_word] applies that representation result to the final
        multiplication performed by division.
      - [DWDivDW3_FLX_FLT] identifies the runtime result with the paper's FLX
        result under explicit no-underflow assumptions.
      - [relative_errorDWDivDW3_correct] transfers the paper's analysis to the
        runtime model, giving relative error at most [(98/10) * u^2].

    Proof status: [DWDivDW3_FLX_FLT] is currently admitted.  Consequently,
    [relative_errorDWDivDW3_correct], although terminated by [Qed], depends
    transitively on an admitted result. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common.
Require Import DWTimesFP DWTimesDW DWDivFP DDModels DWord_defs
               Fast2Mult_acc TwoSum_acc Fast2Sum_acc.
(* paper_proofs/DWDivDW.v now compiles and is in _CoqProject, so its tight FLX
   bound DWDivDW.DWDDW3_correct is available and instantiated below.  DWDivDW.v
   sets [Opaque DWTimesDW.DWTimesDW12] at top level; guard against that leaking
   into this file's proofs by re-asserting transparency after the Require. *)
Require Import DWDivDW.
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
   Finiteness of intermediate operations

   Extract per-operation finiteness from
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

  (** If the complete division returns finite components, then its final
      double-word multiplication also returns finite components.  This fact
      lets multiplication lemmas be applied directly to the final stage of
      [DWDivDW3]. *)
  Fact FIN_mul : is_finite_p (DWTimesDW3 xh xl mh ml).
  Proof. exact FIN. Qed.

  (** The high component of the reconstructed reciprocal is finite whenever
      the complete division result is finite. *)
  Fact FIN_mh : is_finite mh = true.
  Proof. exact (DWMulDW_acc.FINyh xh xl mh ml FIN_mul). Qed.

  (** The low component of the reconstructed reciprocal is finite whenever
      the complete division result is finite. *)
  Fact FIN_ml : is_finite ml = true.
  Proof. exact (DWMulDW_acc.FINyl xh xl mh ml FIN_mul). Qed.

  (** The initial rounded reciprocal [1/yh] is finite whenever the complete
      division result is finite.  This is useful when reasoning backward from
      the final result to the reciprocal-construction steps. *)
  Fact FIN_th : is_finite th = true.
  Proof.
    have Hmh := FIN_mh.
    change (is_finite (BPLUS (BPLUS dh th) (BPLUS dl (snd (TwoSumF dh th)))) = true)
      in Hmh.
    destruct (BPLUS_finite_e t _ _ Hmh) as [Hsh _].
    destruct (BPLUS_finite_e t _ _ Hsh) as [_ Hth].
    exact Hth.
  Qed.

End CorrectDWDivDW.

(* ============================================================
   Double-word representation of the multiplication result

   The closing operation of DWTimesDW3 is Fast2Sum ch cl3, with high product
   ch = BMULT xh yh and correction cl3 = BPLUS (Fast2Mult_err xh yh)
   (BFMA xl yh (BFMA xh yl (BMULT xl yl))).  A Fast2Sum output is a double-word
   once (a) the high sum BPLUS ch cl3 is finite and (b) the operands are ordered
   |cl3| <= |ch| (Fast2Sum_is_DW).  The ordering is DWMulDW_acc.aux_cl3_le_ch.

   NOTE (contrast with DWPlusFP_double_word, which is unconditional): the
   ordering here needs the product to be in the NORMAL range,
   bpow(emin+2p-1) <= |xh*yh| -- in deep underflow the correction is not forced
   below the (subnormal) high product, so a Fast2Sum-of-a-multiply result is
   NOT unconditionally a double-word.  This normal-range fact is exactly what
   DWDivDW_cond's quotient bound supplies for the closing multiply.
   ============================================================ *)
(** [DWTimesDW3] returns a nonoverlapping double-word representation provided
    both operands satisfy [double_word_prop], the computed result is finite,
    and the leading product is large enough to avoid deep underflow.

    The normal-range assumption ensures that the correction supplied to the
    final [Fast2Sum] is no larger than its leading component.  This lemma is
    used below for the final multiplication in [DWDivDW3].  The premise uses
    the Prop-valued [double_word_prop], while the conclusion uses the
    Type-valued [double_word]; both express the same nonoverlap equation. *)
Lemma DWTimesDW3_double_word {NANS: Nans} {t : type} {STD: is_standard t}
      (xh xl yh yl : ftype t) :
  (3 <= fprec t)%Z ->
  double_word_prop xh xl ->
  double_word_prop yh yl ->
  bpow radix2 (@common.emin t + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh) ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  double_word (fst (DWTimesDW3 xh xl yh yl)) (snd (DWTimesDW3 xh xl yh yl)).
Proof.
intros Hp3 DWx DWy Hnorm FIN.
have Hch  := DWMulDW_acc.FINmul  xh xl yh yl FIN.
have Hcl3 := DWMulDW_acc.FINcl3  xh xl yh yl FIN.
have Hle  := DWMulDW_acc.aux_cl3_le_ch xh xl yh yl Hp3 DWx DWy Hch Hcl3 Hnorm.
change (double_word
          (Fast2Sum_sum (BMULT xh yh)
             (BPLUS (Fast2Mult_err xh yh)
                    (BFMA xl yh (BFMA xh yl (BMULT xl yl)))))
          (Fast2Sum_err (BMULT xh yh)
             (BPLUS (Fast2Mult_err xh yh)
                    (BFMA xl yh (BFMA xh yl (BMULT xl yl)))))).
apply Fast2Sum_is_DW; [ exact (proj1 FIN) | exact Hle ].
Qed.

(* ============================================================
   Double-word representation of the division result

   fst/snd (DWDivDW3 xh xl yh yl) are, by definition, fst/snd of the closing
   DWTimesDW3 xh xl mh ml (where (mh,ml) is the refined reciprocal), so result-DW
   reduces directly to DWTimesDW3_double_word at (xh, xl, mh, ml).

   Its three obligations are the honest remaining content:
     - double_word_prop xh xl : the dividend is a DW (a cond field);
     - double_word_prop mh ml : the refined reciprocal (mh,ml) = DWPlusFP dh dl th
       is a DW.  DWPlusFP's result is a DW unconditionally (DWPlusFP_double_word),
       given its DW input (dh,dl) = DWTimesFP3 eh el th -- so this unfolds to the
       reciprocal-reconstruction DW cascade (DWTimesFP3 -> Fast2Sum(rh,rl)), each
       level a multiply-Fast2Sum needing its own normal-range, as in
       DWTimesDW3_double_word;
     - the closing-multiply normal range bpow(emin+2p-1) <= |xh*mh| (mh ~ 1/yh,
       so this is the quotient normal-range that DWDivDW_cond's bound (ii)
       supplies once the reciprocal error mh - 1/yh is controlled).
   Both DW-ness and the normal range are taken here as explicit hypotheses, the
   same "split-line" discipline the DWDivFP development uses for UF_tl.
   ============================================================ *)
Section ResultDWDivDW.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Variables (xh xl yh yl : ftype t).

Notation th  := (BDIV (Zconst t 1) yh).
Notation eh  := (fst (Fast2Sum (BFMA (BOPP yh) th (Zconst t 1)) (BOPP (BMULT yl th)))).
Notation el  := (snd (Fast2Sum (BFMA (BOPP yh) th (Zconst t 1)) (BOPP (BMULT yl th)))).
Notation dh  := (fst (DWTimesFP3 eh el th)).
Notation dl  := (snd (DWTimesFP3 eh el th)).
Notation mh  := (fst (DWPlusFP dh dl th)).
Notation ml  := (snd (DWPlusFP dh dl th)).

Hypothesis Hp3   : (3 <= fprec t)%Z.
Hypothesis FIN   : is_finite_p (DWDivDW3 xh xl yh yl).
Hypothesis DWx   : double_word_prop xh xl.
Hypothesis DWm   : double_word_prop mh ml.
Hypothesis Hnorm : bpow radix2 (@common.emin t + 2 * fprec t - 1)
                   <= Rabs (FT2R xh * FT2R mh).

(** The two components returned by [DWDivDW3] form a valid double-word.

    Besides finiteness and a double-word dividend, the theorem assumes that
    the reconstructed reciprocal [(mh,ml)] satisfies [double_word_prop] and
    that the final product [xh*mh] avoids deep underflow.  Separate range
    analysis can establish these assumptions from a public precondition for
    the division operation. *)
Lemma DWDivDW3_double_word :
  double_word (fst (DWDivDW3 xh xl yh yl)) (snd (DWDivDW3 xh xl yh yl)).
Proof.
have FINmul : is_finite_p (DWTimesDW3 xh xl mh ml) by exact FIN.
exact (DWTimesDW3_double_word xh xl mh ml Hp3 DWx DWm Hnorm FINmul).
Qed.

End ResultDWDivDW.

(* ============================================================
   Agreement between the FLX paper model and the FLT runtime model

   Collapses the FLT runtime model DDModels.DWDivDW3 onto the paper's
   real-valued FLX model, node by node, under no-underflow assumptions: the
   relevant rounded prologue nodes carry lower bounds placing them in the
   normal range, so round_FLT agrees with round_FLX (round_FLT_FLX).  The
   intended completed proof also composes bridges for the two reciprocal
   refinement sub-blocks and the closing double-word multiplication.

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

(* Normal-range hypotheses for the reciprocal, low-product, and error-sum
   nodes represented explicitly by the current theorem signature. *)
Hypothesis UF_th   : bpow radix2 (emin + fprec t - 1) <= Rabs (1 / FT2R yh).
Hypothesis UF_rl   : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R yl * FT2R th).
Hypothesis UF_eh   : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R rh + FT2R rl).
(* A completed compositional proof may require further hypotheses for the
   DWTimesFP3 and DWPlusFP sub-blocks and the closing DWTimesDW3.  Those
   hypotheses are not yet represented in this admitted theorem's interface. *)

(** The finite-precision runtime computation [DDModels.DWDivDW3] denotes the
    same real pair as the paper's FLX computation.

    The lower-bound hypotheses exclude underflow at the reciprocal,
    low-product, and error-sum nodes, allowing FLT rounding to be replaced by
    FLX rounding.  This equality is the link used by
    [relative_errorDWDivDW3_correct] to reuse the paper-level error bound.

    This result is currently admitted; its final interface may need additional
    no-underflow hypotheses for the composed sub-blocks. *)
Lemma DWDivDW3_FLX_FLT :
  F2Rp (DWDivDW3 xh xl yh yl)
    = (let th_r := rnd_p (/ FT2R yh) in
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
   Relative-error bound for DWDivDW3
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
(* No-underflow assumptions currently exposed by [DWDivDW3_FLX_FLT]. *)
Hypothesis UF_th : bpow radix2 (emin + fprec t - 1) <= Rabs (1 / FT2R yh).
Hypothesis UF_rl : bpow radix2 (emin + fprec t - 1)
                   <= Rabs (FT2R yl * FT2R (BDIV (Zconst t 1) yh)).
Hypothesis UF_eh : bpow radix2 (emin + fprec t - 1)
                   <= Rabs (FT2R (BFMA (BOPP yh) (BDIV (Zconst t 1) yh) (Zconst t 1))
                            + FT2R (BOPP (BMULT yl (BDIV (Zconst t 1) yh)))).

(** Absolute relative error of the real number [zh+zl] returned by the
    algorithm, measured against the exact quotient
    [(xh+xl)/(yh+yl)]. *)
Definition relative_error_DWDivDW :=
  Rabs ((zh + zl - (FT2R xh + FT2R xl) / (FT2R yh + FT2R yl))
        / ((FT2R xh + FT2R xl) / (FT2R yh + FT2R yl))).

(** Under the double-word, finiteness, precision, nonzero-divisor, and
    no-underflow assumptions above, [DWDivDW3] computes the quotient with
    relative error at most [9.8*u^2], where [u = 2^(-p)].

    The proof transfers [DWDivDW.DWDDW3_correct] from the paper's FLX model to
    the runtime FLT model through [DWDivDW3_FLX_FLT].  It therefore currently
    depends on the admitted bridge theorem. *)
Theorem relative_errorDWDivDW3_correct :
  relative_error_DWDivDW <= 98/10 * u ^ 2.
Proof.
(* Instantiate the paper's tight FLX bound directly.  Its abstract
   two-product hypotheses reduce to concrete lemmas: the round-to-nearest-even
   [choice] equation is [eq_refl], and [TwoProd = Fast2Mult] is
   DWTimesFP.TwoProdE.  The FLX->FLT reconciliation is the compositional bridge
   DWDivDW3_FLX_FLT. *)
have HDWx : DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl)
  by apply (dw_word_DWdouble xh xl yh); exact DWx.
have HDWy : DWPlus.double_word (fprec t) choice (FT2R yh) (FT2R yl)
  by apply (dw_word_DWdouble yh yl yh); exact DWy.
pose proof (@DWDivDW.DWDDW3_correct (fprec t) (fprec_gt_one t) choice eq_refl
              (DWTimesFP.TwoProdE (fprec t) choice)
              (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl)
              HDWx HDWy Hp14 Hyhne) as Hpaper.
cbv beta in Hpaper.
pose proof (DWDivDW3_FLX_FLT xh xl yh yl FIN Hp14 Hyhne UF_th UF_rl UF_eh) as Hbr.
cbv zeta in Hbr.
rewrite -Hbr in Hpaper.
rewrite /F2Rp in Hpaper.
cbv beta iota in Hpaper.
unfold relative_error_DWDivDW, zh, zl.
exact Hpaper.
Qed.

End FiniteAccuracyDWDivDW.
