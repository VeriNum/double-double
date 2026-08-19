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
      - [relative_errorDWDivDW3_from_cond_combined] gives the
        regime-independent bound, including underflow, of [(165/10) * u^2].

    Both the bridge and the transferred relative-error theorem are proved
    below from explicit normal-range premises for every rounding node that
    must be reconciled with the FLX model. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common FLT_helpers.
Require Import DWTimesFP DWTimesDW DWDivFP DDModels DWord_defs
               Fast2Mult_acc TwoSum_acc Fast2Sum_acc.
(* paper_proofs/DWDivDW.v now compiles and is in _CoqProject, so its tight FLX
   bound DWDivDW.DWDDW3_correct is available and instantiated below.  DWDivDW.v
   sets [Opaque DWTimesDW.DWTimesDW12] at top level; guard against that leaking
   into this file's proofs by re-asserting transparency after the Require. *)
Require Import DWDivDW.
Require Import DWPlusFP_acc_helpers DWMulFP_acc DWPlusFP_acc DWMulDW_acc
               DWDivFP_acc DWPlusDW_acc_helpers DW_acc_lemmas.
From Flocq Require Import Pff2Flocq Core.
From Flocq Require Import Mult_error FLT Div_sqrt_error.

Require Import mathcomp.ssreflect.ssreflect.
From Stdlib Require Import Logic.FunctionalExtensionality.

Set Bullet Behavior "Strict Subproofs".
Lemma no_overflow_fma_is_finite {NANS: Nans} {t : type} {STD: is_standard t} :
  forall (a b c : ftype t),
  is_finite a = true -> is_finite b = true -> is_finite c = true ->
  Rabs (rounded t (FT2R a * FT2R b + FT2R c)) < bpow Zaux.radix2 (femax t) ->
  is_finite (BFMA a b c) = true.
Proof.
  intros a b c Ha Hb Hc Hov.
  rewrite !is_finite_Binary in Ha, Hb, Hc.
  rewrite is_finite_Binary /BFMA float_of_ftype_of_float.
  pose proof (Binary.Bfma_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan (fprec t) (femax t) (fprec_gt_one t))
    BinarySingleNaN.mode_NE (float_of_ftype a) (float_of_ftype b) (float_of_ftype c)
    Ha Hb Hc) as H.
  cbv zeta in H.
  rewrite !B2R_float_of_ftype in H.
  unfold rounded in Hov.
  apply Rlt_bool_true in Hov.
  rewrite Hov in H.
  destruct H as (_ & HF & _).
  exact HF.
Qed.

(* Analog of no_overflow_fma_is_finite for BMULT: a real product whose rounded
   value stays below the overflow threshold yields a finite BMULT. *)
Lemma no_overflow_mult_is_finite {NANS: Nans} {t : type} {STD: is_standard t} :
  forall (a b : ftype t),
  is_finite a = true -> is_finite b = true ->
  Rabs (rounded t (FT2R a * FT2R b)) < bpow Zaux.radix2 (femax t) ->
  is_finite (BMULT a b) = true.
Proof.
  intros a b Ha Hb Hov.
  rewrite !is_finite_Binary in Ha, Hb.
  rewrite is_finite_Binary /BMULT/BINOP float_of_ftype_of_float.
  pose proof (Binary.Bmult_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (mult_nan (fprec t) (femax t) (fprec_gt_one t))
    BinarySingleNaN.mode_NE (float_of_ftype a) (float_of_ftype b)) as H.
  cbv zeta in H.
  rewrite !B2R_float_of_ftype in H.
  unfold rounded in Hov.
  apply Rlt_bool_true in Hov.
  rewrite Hov in H.
  destruct H as (_ & HF & _).
  rewrite HF Ha Hb //.
Qed.

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

  (** Pair finiteness of the reciprocal-renormalization block. *)
  Fact FIN_plus : is_finite_p (DWPlusFP dh dl th).
  Proof. split; [exact FIN_mh | exact FIN_ml]. Qed.

  (** The two components produced by the reciprocal-times-error block are
      finite.  These are recovered through the finite-input projections of
      the enclosing [DWPlusFP]. *)
  Fact FIN_dh : is_finite dh = true.
  Proof. exact (DWPlusFP_acc_helpers.FINxh dh dl th FIN_plus). Qed.

  Fact FIN_dl : is_finite dl = true.
  Proof. exact (DWPlusFP_acc_helpers.FINxl dh dl th FIN_plus). Qed.

  Fact FIN_timesfp : is_finite_p (DWTimesFP3 eh el th).
  Proof. split; [exact FIN_dh | exact FIN_dl]. Qed.

  (** The Fast2Sum components of the reciprocal residual are finite, obtained
      by projecting backward through [DWTimesFP3]. *)
  Fact FIN_eh : is_finite eh = true.
  Proof. exact (DWMulFP_acc.FINxh eh el th FIN_timesfp). Qed.

  Fact FIN_el : is_finite el = true.
  Proof. exact (DWMulFP_acc.FINxl eh el th FIN_timesfp). Qed.

  Fact FIN_fast2sum : is_finite_p (Fast2Sum rh rl).
  Proof. split; [exact FIN_eh | exact FIN_el]. Qed.

  (** Finiteness of the two explicit reciprocal-residual operands. *)
  Fact FIN_rh : is_finite rh = true.
  Proof.
    have Hsum := FIN_eh.
    change (is_finite (BPLUS rh rl) = true) in Hsum.
    exact (proj1 (BPLUS_finite_e t rh rl Hsum)).
  Qed.

  Fact FIN_rl : is_finite rl = true.
  Proof.
    have Hsum := FIN_eh.
    change (is_finite (BPLUS rh rl) = true) in Hsum.
    exact (proj2 (BPLUS_finite_e t rh rl Hsum)).
  Qed.

  (** Finiteness of the denominator components, exposed for the leaf rounding
      bridges. *)
  Fact FIN_yh : is_finite yh = true.
  Proof.
    destruct (BFMA_finite_e t (BOPP yh) th (Zconst t 1) FIN_rh)
      as [Hyh_opp _].
    exact (proj1 (BOPP_is_finite t yh) Hyh_opp).
  Qed.

  Fact FIN_yl : is_finite yl = true.
  Proof.
    have Hmul : is_finite (BMULT yl th) = true.
    { exact (proj1 (BOPP_is_finite t (BMULT yl th)) FIN_rl). }
    exact (proj1 (BMULT_finite_e t yl th Hmul)).
  Qed.

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

  (** Structural bridge for the residual [Fast2Sum].  Finiteness alone cannot
      imply nonoverlap: the required magnitude ordering is exposed explicitly
      for the later normal-range analysis. *)
  Fact DW_e
      (Hord : Rabs (FT2R rl) <= Rabs (FT2R rh)) :
    double_word eh el.
  Proof. exact (Fast2Sum_is_DW rh rl FIN_eh Hord). Qed.

  (** Structural bridge for [DWTimesFP3].  Its closing correction ordering is
      likewise an explicit premise, to be discharged by the bridge's range
      hypotheses rather than hidden in the finiteness layer. *)
  Fact DW_d
      (Hord :
         Rabs (FT2R (BFMA el th (Fast2Mult_err eh th)))
           <= Rabs (FT2R (Fast2Mult_mul eh th))) :
    double_word dh dl.
  Proof.
    exact (DWMulFP_acc.DWTimesFP3_double_word_from_pre eh el th
             (proj1 FIN_timesfp) Hord).
  Qed.

  (** Once [(dh,dl)] is a double word, [DWPlusFP] renormalizes its result into
      the double-word pair [(mh,ml)]. *)
  Fact DW_m (Hp3 : (3 <= fprec t)%Z) (DWd : double_word dh dl) :
    double_word mh ml.
  Proof.
    exact (DWPlusFP_acc_helpers.DWPlusFP_double_word dh dl th
             DWd FIN_plus Hp3).
  Qed.

End CorrectDWDivDW.

(* Small, reusable overflow combinators for the forward cascade.  A
   representable power-of-two envelope is preserved by round-to-nearest, so
   it simultaneously proves operation finiteness and a bound on its result. *)
Lemma BPLUS_finite_bpow_bound {NANS: Nans} {t : type} {STD: is_standard t}
      (a b : ftype t) (k : Z) :
  is_finite a = true -> is_finite b = true ->
  (SpecFloat.emin (fprec t) (femax t) <= k)%Z ->
  (k < femax t)%Z ->
  Rabs (FT2R a + FT2R b) <= bpow radix2 k ->
  is_finite (BPLUS a b) = true /\
  Rabs (FT2R (BPLUS a b)) <= bpow radix2 k.
Proof.
move => Fa Fb Hlow Hk Hab.
have Hfmt : generic_format radix2 (SpecFloat.fexp (fprec t) (femax t))
              (bpow radix2 k).
{ apply generic_format_bpow.
  unfold SpecFloat.fexp. apply Z.max_lub;
    [pose proof (fprec_lb t); lia | exact Hlow]. }
have Hrnd : Rabs (rounded t (FT2R a + FT2R b)) <= bpow radix2 k.
{ unfold rounded. apply abs_round_le_generic;
    first [exact valid_fexp_inst | apply valid_rnd_N | exact Hfmt | exact Hab]. }
have Fsum : is_finite (BPLUS a b) = true.
{ apply no_overflow_sum_is_finite; [exact Fa | exact Fb |].
  unfold Bplus_no_overflow.
  eapply Rle_lt_trans; [exact Hrnd | apply bpow_lt; exact Hk]. }
split; [exact Fsum |].
rewrite -(BPLUS_round_correct t a b Fsum). exact Hrnd.
Qed.

Lemma BMINUS_finite_bpow_bound {NANS: Nans} {t : type} {STD: is_standard t}
      (a b : ftype t) (k : Z) :
  is_finite a = true -> is_finite b = true ->
  (SpecFloat.emin (fprec t) (femax t) <= k)%Z ->
  (k < femax t)%Z ->
  Rabs (FT2R a - FT2R b) <= bpow radix2 k ->
  is_finite (BMINUS a b) = true /\
  Rabs (FT2R (BMINUS a b)) <= bpow radix2 k.
Proof.
move => Fa Fb Hlow Hk Hab.
have Hfmt : generic_format radix2 (SpecFloat.fexp (fprec t) (femax t))
              (bpow radix2 k).
{ apply generic_format_bpow.
  unfold SpecFloat.fexp. apply Z.max_lub;
    [pose proof (fprec_lb t); lia | exact Hlow]. }
have Hrnd : Rabs (rounded t (FT2R a - FT2R b)) <= bpow radix2 k.
{ unfold rounded. apply abs_round_le_generic;
    first [exact valid_fexp_inst | apply valid_rnd_N | exact Hfmt | exact Hab]. }
have Fdiff : is_finite (BMINUS a b) = true.
{ apply no_overflow_minus_is_finite; [exact Fa | exact Fb |].
  unfold Bminus_no_overflow.
  eapply Rle_lt_trans; [exact Hrnd | apply bpow_lt; exact Hk]. }
split; [exact Fdiff |].
rewrite -(BMINUS_round_correct t a b Fdiff). exact Hrnd.
Qed.

Lemma BMULT_finite_bpow_bound {NANS: Nans} {t : type} {STD: is_standard t}
      (a b : ftype t) (k : Z) :
  is_finite a = true -> is_finite b = true ->
  (SpecFloat.emin (fprec t) (femax t) <= k)%Z ->
  (k < femax t)%Z ->
  Rabs (FT2R a * FT2R b) <= bpow radix2 k ->
  is_finite (BMULT a b) = true /\
  Rabs (FT2R (BMULT a b)) <= bpow radix2 k.
Proof.
move => Fa Fb Hlow Hk Hab.
have Hfmt : generic_format radix2 (SpecFloat.fexp (fprec t) (femax t))
              (bpow radix2 k).
{ apply generic_format_bpow. unfold SpecFloat.fexp. apply Z.max_lub;
    [pose proof (fprec_lb t); lia | exact Hlow]. }
have Hrnd : Rabs (rounded t (FT2R a * FT2R b)) <= bpow radix2 k.
{ unfold rounded. apply abs_round_le_generic;
    first [exact valid_fexp_inst | apply valid_rnd_N | exact Hfmt | exact Hab]. }
have Fmul : is_finite (BMULT a b) = true.
{ apply no_overflow_mult_is_finite; [exact Fa | exact Fb |].
  eapply Rle_lt_trans; [exact Hrnd | apply bpow_lt; exact Hk]. }
split; [exact Fmul |].
rewrite -(BMULT_round_correct t a b Fmul). exact Hrnd.
Qed.

Lemma BFMA_finite_bpow_bound {NANS: Nans} {t : type} {STD: is_standard t}
      (a b c : ftype t) (k : Z) :
  is_finite a = true -> is_finite b = true -> is_finite c = true ->
  (SpecFloat.emin (fprec t) (femax t) <= k)%Z ->
  (k < femax t)%Z ->
  Rabs (FT2R a * FT2R b + FT2R c) <= bpow radix2 k ->
  is_finite (BFMA a b c) = true /\
  Rabs (FT2R (BFMA a b c)) <= bpow radix2 k.
Proof.
move => Fa Fb Fc Hlow Hk Hab.
have Hfmt : generic_format radix2 (SpecFloat.fexp (fprec t) (femax t))
              (bpow radix2 k).
{ apply generic_format_bpow. unfold SpecFloat.fexp. apply Z.max_lub;
    [pose proof (fprec_lb t); lia | exact Hlow]. }
have Hrnd : Rabs (rounded t (FT2R a * FT2R b + FT2R c)) <= bpow radix2 k.
{ unfold rounded. apply abs_round_le_generic;
    first [exact valid_fexp_inst | apply valid_rnd_N | exact Hfmt | exact Hab]. }
have Ffma : is_finite (BFMA a b c) = true.
{ apply no_overflow_fma_is_finite;
    [exact Fa | exact Fb | exact Fc |].
  eapply Rle_lt_trans; [exact Hrnd | apply bpow_lt; exact Hk]. }
split; [exact Ffma |].
rewrite -(BFMA_round_correct t a b c Ffma). exact Hrnd.
Qed.

(* The generic Algorithm-9 / Fast2Mult / Fast2Sum underflow-floor lemmas that
   used to sit here now live in DWMulFP_acc.v, where they belong: they are
   statements about DWTimesFP3 (Algorithm 9), they were already built on top of
   DWMulFP_acc.DWTimesFP_relerr_bound, and nothing about them is division
   specific.  Moving them upstream removed a layering inversion and relaxed
   their p >= 14 hypothesis to p >= 3.  The operation-independent rounding
   lemmas arrive through FLT_helpers; the Algorithm-9 lemmas arrive unqualified
   through the Require Import DWMulFP_acc above:

     round_FLT_error_rel_emin        round_abs_le_relative_plus_half_emin
     Fast2Mult_sum_error_floor       DWTimesFP_core_error_floor_gap
     Fast2Sum_sum_exact_of_sum_small (replaces Fast2Sum_sum_exact_floor_small)
     DWTimesFP3_sum_exact_of_ord     DWTimesFP3_double_word_of_sum
     Fast2Sum_double_word_of_sum     DWTimesFP3_error_floor_gap
     DWTimesFP3_error_mixed          DWTimesFP3_error_mixed_flat
     DWTimesFP3_double_word_mixed

   DWMulFP_acc also exports the assembled public form DWTimesFP3_error_mixed. *)

(** Absolute form of the paper-tight DWPlusFP theorem, including the zero-sum
    case through its multiplicative-error witness. *)
Lemma DWPlusFP_error_paper_tight {NANS : Nans} {t : type}
    {STD : is_standard t} (ah al b : ftype t) :
  (3 <= fprec t)%Z -> double_word_prop ah al ->
  is_finite_p (DWPlusFP ah al b) ->
  Rabs ((FT2R (fst (DWPlusFP ah al b))+
         FT2R (snd (DWPlusFP ah al b)))-
        (FT2R ah+FT2R al+FT2R b))
    <= 2*bpow radix2 (-fprec t)^2*
         Rabs (FT2R ah+FT2R al+FT2R b).
Proof.
move => Hp3 DWa FIN.
have H := @DWPlusFP_acc.relative_errorDWPlusFP_correct'
  NANS t STD ah al b DWa FIN Hp3.
destruct H as [del [Heq Hdel]].
cbv zeta in Heq.
set q := (FT2R ah+FT2R al+FT2R b)%R.
set u := bpow radix2 (-fprec t).
fold q in Heq. fold u in Hdel.
change (Rabs ((FT2R (fst (DWPlusFP ah al b))+
  FT2R (snd (DWPlusFP ah al b)))-q)<=2*u^2*Rabs q).
rewrite Heq.
replace (q*(1+del)-q)%R with (q*del)%R by ring.
rewrite Rabs_mult.
have Hmul := Rmult_le_compat_l (Rabs q) _ _ (Rabs_pos q) Hdel.
eapply Rle_trans; [exact Hmul|]. right; ring.
Qed.

(* ============================================================
   Immediate consequences of the public division condition
   ============================================================ *)
Section DWDivDWCondFacts.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (SpecFloat.emin (fprec t) (femax t)).

Lemma DWDivDW_cond_yh_nonzero (xh xl yh yl : ftype t) :
  DWDivDW_cond xh xl yh yl -> FT2R yh <> 0.
Proof.
move => [_ [_ [_ [_ [_ [_ [_ [_ [Hyhlo _]]]]]]]]].
intro Hyh0.
rewrite Hyh0 Rabs_R0 in Hyhlo.
have Hb := bpow_gt_0 radix2 (emin + 2 * fprec t).
lra.
Qed.

(** [DWDivDW_cond] pins [|yh|] between [2^(emin+2p)] and, via the reciprocal
    clause, [2^(1-emin-2p)].  A nonempty window forces [2*emin+4p <= 1], and
    the left side is even while the right is odd, so in fact [emin+2p <= 0].
    Every scale conversion below inherits this: the underflow floor is at most
    [u^2], not the format-generic [4*u^2]. *)
Lemma DWDivDW_cond_emin_le (xh xl yh yl : ftype t) :
  DWDivDW_cond xh xl yh yl ->
  (emin + 2 * fprec t <= 0)%Z.
Proof.
move => COND.
move: (COND) => [_ [_ [_ [_ [_ [_ [Hrecip [_ [Hyh _]]]]]]]]].
have Hyhne := DWDivDW_cond_yh_nonzero xh xl yh yl COND.
have Hprod : Rabs (1 / FT2R yh) * Rabs (FT2R yh) = 1.
{ rewrite -Rabs_mult.
  replace (1 / FT2R yh * FT2R yh)%R with 1 by (field; exact Hyhne).
  exact Rabs_R1. }
have Hmul : bpow radix2 (emin + 2 * fprec t - 1) *
            bpow radix2 (emin + 2 * fprec t) <= 1.
{ rewrite -Hprod. apply Rmult_le_compat;
    [apply bpow_ge_0 | apply bpow_ge_0 | exact Hrecip | exact Hyh]. }
rewrite -bpow_plus in Hmul.
have H1 : (1:R) = bpow radix2 0 by reflexivity.
rewrite H1 in Hmul.
have := le_bpow radix2 _ _ Hmul. lia.
Qed.

(** Hence the physical underflow ulp is itself a second-order quantity on the
    unit scale.  This is what makes the residual-scale floor [eta*|Q|] cost
    [1*u^2*|Q|] instead of the [4*u^2*|Q|] charged by the generic bound in
    [DWDivDW_eta_scales_from_cond_tight]. *)
Lemma DWDivDW_cond_eta_le_u2 (xh xl yh yl : ftype t) :
  DWDivDW_cond xh xl yh yl ->
  bpow radix2 emin <= bpow radix2 (- fprec t) ^ 2.
Proof.
move => COND.
have Hemin := DWDivDW_cond_emin_le xh xl yh yl COND.
replace (bpow radix2 (- fprec t) ^ 2)
  with (bpow radix2 (- fprec t) * bpow radix2 (- fprec t))%R by ring.
rewrite -bpow_plus. apply bpow_le. lia.
Qed.

Lemma DWDivDW_cond_UF_th (xh xl yh yl : ftype t) :
  DWDivDW_cond xh xl yh yl ->
  bpow radix2 (emin + fprec t - 1) <= Rabs (1 / FT2R yh).
Proof.
move => [_ [_ [_ [_ [_ [_ [Hrec _]]]]]]].
eapply Rle_trans; [| exact Hrec].
apply bpow_le. pose proof (fprec_lb t). unfold emin. lia.
Qed.

(** The public lower bound on [|yh|] also keeps the initial reciprocal far
    below overflow. *)
Lemma DWDivDW_cond_reciprocal_upper (xh xl yh yl : ftype t) :
  DWDivDW_cond xh xl yh yl ->
  Rabs (1 / FT2R yh) <= bpow radix2 (femax t - 2).
Proof.
move => [_ [_ [_ [_ [_ [_ [_ [_ [Hyhlo _]]]]]]]]].
have Hyhne : FT2R yh <> 0.
{ intro Hyh0.
  rewrite Hyh0 Rabs_R0 in Hyhlo.
  have Hb := bpow_gt_0 radix2 (emin + 2 * fprec t).
  lra. }
have Hyhpos : 0 < Rabs (FT2R yh) by apply Rabs_pos_lt; exact Hyhne.
have Hbpos : 0 < bpow radix2 (emin + 2 * fprec t)
  by apply bpow_gt_0.
rewrite Rdiv_1_l Rabs_inv.
eapply Rle_trans.
- apply Rinv_le_contravar; [exact Hbpos | exact Hyhlo].
- rewrite -bpow_opp.
  apply bpow_le.
  unfold emin, SpecFloat.emin; pose proof (fprec_lb t); lia.
Qed.

Lemma DWDivDW_cond_reciprocal_upper_tight (xh xl yh yl : ftype t) :
  DWDivDW_cond xh xl yh yl ->
  Rabs (1 / FT2R yh) <= bpow radix2 (femax t - fprec t - 3).
Proof.
move => [_ [_ [_ [_ [_ [_ [_ [_ [Hyhlo _]]]]]]]]].
have Hyhne : FT2R yh <> 0.
{ intro Hyh0. rewrite Hyh0 Rabs_R0 in Hyhlo.
  have Hb := bpow_gt_0 radix2 (emin + 2 * fprec t); lra. }
have Hbpos : 0 < bpow radix2 (emin + 2 * fprec t) by apply bpow_gt_0.
rewrite Rdiv_1_l Rabs_inv.
eapply Rle_trans.
- apply Rinv_le_contravar; [exact Hbpos | exact Hyhlo].
- rewrite -bpow_opp.
  apply Req_le; f_equal. unfold emin, SpecFloat.emin; lia.
Qed.

(** Finiteness of the reciprocal bootstrap node, obtained by reusing the
    quotient-node proof from DW/FP division at numerator [1]. *)
Lemma DWDivDW_th_finite_from_cond (xh xl yh yl : ftype t) :
  DWDivDW_cond xh xl yh yl ->
  is_finite (BDIV (Zconst t 1) yh) = true.
Proof.
move => COND.
have Honefin : is_finite (Zconst t 1) = true.
{ rewrite /Zconst is_finite_Binary float_of_ftype_of_float.
  have Hpow : (0 < 2 ^ fprec t)%Z.
  { apply Z.pow_pos_nonneg; pose proof (fprec_lb t); lia. }
  have Hrange : (- 2 ^ fprec t <= 1 <= 2 ^ fprec t)%Z by lia.
  exact (proj1 (proj2 (IEEE754_extra.BofZ_exact
                         (fprec t) (femax t) _ _ 1 Hrange))). }
have Hone : FT2R (Zconst t 1) = 1%R.
{ rewrite /Zconst FT2R_ftype_of_float.
  have Hpow : (0 < 2 ^ fprec t)%Z.
  { apply Z.pow_pos_nonneg; pose proof (fprec_lb t); lia. }
  have Hrange : (- 2 ^ fprec t <= 1 <= 2 ^ fprec t)%Z by lia.
  have Hexact := proj1 (IEEE754_extra.BofZ_exact
                          (fprec t) (femax t) _ _ 1 Hrange).
  rewrite Hexact; reflexivity. }
apply DWDivFP_acc.th_finite.
- exact Honefin.
- exact (DWDivDW_cond_yh_nonzero xh xl yh yl COND).
- rewrite Hone; exact (DWDivDW_cond_reciprocal_upper xh xl yh yl COND).
Qed.

Lemma DWDivDW_th_abs_upper_tight (xh xl yh yl : ftype t) :
  DWDivDW_cond xh xl yh yl ->
  Rabs (FT2R (BDIV (Zconst t 1) yh))
    <= bpow radix2 (femax t - fprec t - 3).
Proof.
move => COND.
have Fth := DWDivDW_th_finite_from_cond xh xl yh yl COND.
have Hyhne := DWDivDW_cond_yh_nonzero xh xl yh yl COND.
have Hone : FT2R (Zconst t 1) = 1%R.
{ rewrite /Zconst FT2R_ftype_of_float.
  have Hpow : (0 < 2 ^ fprec t)%Z.
  { apply Z.pow_pos_nonneg; pose proof (fprec_lb t); lia. }
  have Hrange : (- 2 ^ fprec t <= 1 <= 2 ^ fprec t)%Z by lia.
  have Hexact := proj1 (IEEE754_extra.BofZ_exact
                          (fprec t) (femax t) _ _ 1 Hrange).
  rewrite Hexact; reflexivity. }
rewrite -(BDIV_round_correct t (Zconst t 1) yh Hyhne Fth) Hone.
apply abs_round_le_generic.
- exact valid_fexp_inst.
- apply valid_rnd_N.
- apply generic_format_bpow. unfold SpecFloat.fexp.
  apply Z.max_lub.
  + pose proof (fprec_lb t); lia.
  + unfold SpecFloat.emin; pose proof (femax_lb t); lia.
- exact (DWDivDW_cond_reciprocal_upper_tight xh xl yh yl COND).
Qed.

Lemma DWDivDW_th_yh_residual_from_cond (xh xl yh yl : ftype t) :
  DWDivDW_cond xh xl yh yl ->
  Rabs (FT2R (BDIV (Zconst t 1) yh) * FT2R yh - 1)
    <= bpow radix2 (- fprec t).
Proof.
move => COND.
have Fth := DWDivDW_th_finite_from_cond xh xl yh yl COND.
have Hyhne := DWDivDW_cond_yh_nonzero xh xl yh yl COND.
have UFth := DWDivDW_cond_UF_th xh xl yh yl COND.
have Hone : FT2R (Zconst t 1) = 1%R.
{ rewrite /Zconst FT2R_ftype_of_float.
  have Hpow : (0 < 2 ^ fprec t)%Z.
  { apply Z.pow_pos_nonneg; pose proof (fprec_lb t); lia. }
  have Hrange : (- 2 ^ fprec t <= 1 <= 2 ^ fprec t)%Z by lia.
  have Hexact := proj1 (IEEE754_extra.BofZ_exact
                          (fprec t) (femax t) _ _ 1 Hrange).
  rewrite Hexact; reflexivity. }
have Hres := DWDivFP_acc.thy_residual (Zconst t 1) yh Fth Hyhne.
rewrite Hone in Hres. specialize (Hres UFth).
rewrite Rabs_R1 Rmult_1_l in Hres. exact Hres.
Qed.

Lemma DWDivDW_th_relative_bounds_from_cond (xh xl yh yl : ftype t) :
  (4 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let u := bpow radix2 (- fprec t) in
  let eta := bpow radix2 (@common.emin t) in
  0 < Rabs (FT2R th) /\
  Rabs (FT2R th) <= (1 + u) * Rabs (1 / FT2R yh) /\
  eta <= u /\ eta <= u * Rabs (FT2R th).
Proof.
move => Hp4 COND.
set th := BDIV (Zconst t 1) yh.
set u := bpow radix2 (- fprec t).
set eta := bpow radix2 (@common.emin t).
have Hyhne := DWDivDW_cond_yh_nonzero xh xl yh yl COND.
have HY : 0 < Rabs (FT2R yh) by apply Rabs_pos_lt; exact Hyhne.
have Hres := DWDivDW_th_yh_residual_from_cond xh xl yh yl COND.
fold th u in Hres.
have Hres' : Rabs (1-FT2R yh*FT2R th) <= u.
{ rewrite (Rabs_minus_sym 1 (FT2R yh*FT2R th)).
  replace (FT2R yh*FT2R th-1)%R with (FT2R th*FT2R yh-1)%R by ring.
  exact Hres. }
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu16 : u <= /16.
{ unfold u. have -> : (/16:R) = bpow radix2 (-4) by (simpl; lra).
  apply bpow_le; lia. }
have Hprod_abs : Rabs (FT2R th * FT2R yh) =
                   Rabs (FT2R th) * Rabs (FT2R yh) by apply Rabs_mult.
have Hprod_up : Rabs (FT2R th * FT2R yh) <= 1 + u.
{ have Htri := Rabs_triang (FT2R th * FT2R yh - 1) 1.
  have Heq : (FT2R th * FT2R yh - 1 + 1)%R = FT2R th * FT2R yh by ring.
  rewrite Heq Rabs_R1 in Htri; lra. }
have Hprod_lo : 1 - u <= Rabs (FT2R th * FT2R yh).
{ have Hrev := Rabs_triang_inv 1 (FT2R th * FT2R yh).
  rewrite Rabs_R1 (Rabs_minus_sym 1 (FT2R th * FT2R yh)) in Hrev.
  lra. }
have Hq : Rabs (1 / FT2R yh) = / Rabs (FT2R yh).
{ rewrite Rdiv_1_l Rabs_inv; reflexivity. }
have Hth_up : Rabs (FT2R th) <= (1 + u) * Rabs (1 / FT2R yh).
{ rewrite Hq. rewrite Hprod_abs in Hprod_up.
  apply (Rmult_le_reg_r (Rabs (FT2R yh))); [exact HY |].
  rewrite Rmult_assoc Rinv_l ?Rmult_1_r; [exact Hprod_up | lra]. }
have Hth_q_lo : /2 * Rabs (1 / FT2R yh) <= Rabs (FT2R th).
{ rewrite Hq. rewrite Hprod_abs in Hprod_lo.
  have Hhalf : /2 <= 1 - u by lra.
  apply (Rmult_le_reg_r (Rabs (FT2R yh))); [exact HY |].
  rewrite Rmult_assoc Rinv_l ?Rmult_1_r; [|lra].
  eapply Rle_trans; [exact Hhalf | exact Hprod_lo]. }
have Hqcond : bpow radix2 (@common.emin t + 2 * fprec t - 1)
                   <= Rabs (1 / FT2R yh).
{ move: (COND) => [_ [_ [_ [_ [_ [_ [H _]]]]]]]. exact H. }
have Hth_lo : bpow radix2 (@common.emin t + 2 * fprec t - 2)
                  <= Rabs (FT2R th).
{ eapply Rle_trans; [| exact Hth_q_lo].
  have Heq : bpow radix2 (@common.emin t + 2 * fprec t - 2) =
      /2 * bpow radix2 (@common.emin t + 2 * fprec t - 1).
  { change (bpow radix2 (@common.emin t + 2 * fprec t - 2) =
      bpow radix2 (-1) * bpow radix2 (@common.emin t + 2 * fprec t - 1)).
    rewrite -bpow_plus; f_equal; lia. }
  rewrite Heq. apply Rmult_le_compat_l; [lra | exact Hqcond]. }
have Heta_u : eta <= u.
{ unfold eta, u. apply bpow_le. unfold common.emin, SpecFloat.emin.
  pose proof (femax_lb t); lia. }
have Heta_uT : eta <= u * Rabs (FT2R th).
{ eapply Rle_trans.
  - have Heq : eta <= u * bpow radix2 (@common.emin t + 2 * fprec t - 2).
    { unfold eta, u. rewrite -bpow_plus. apply bpow_le. lia. }
    exact Heq.
  - apply Rmult_le_compat_l; [apply Rlt_le; exact Hu0 | exact Hth_lo]. }
repeat split.
- eapply Rlt_le_trans; [apply bpow_gt_0 | exact Hth_lo].
- exact Hth_up.
- exact Heta_u.
- exact Heta_uT.
Qed.

Lemma DWDivDW_yl_th_abs_from_cond (xh xl yh yl : ftype t) :
  DWDivDW_cond xh xl yh yl ->
  Rabs (FT2R yl * FT2R (BDIV (Zconst t 1) yh))
    <= bpow radix2 (- fprec t) * (1 + bpow radix2 (- fprec t)).
Proof.
move => COND.
move: (COND) => [_ [_ [_ [_ [_ [DWy _]]]]]].
set th := BDIV (Zconst t 1) yh.
have Hres := DWDivDW_th_yh_residual_from_cond xh xl yh yl COND.
fold th in Hres.
have Hyl : Rabs (FT2R yl) <= bpow radix2 (- fprec t) * Rabs (FT2R yh) :=
  @DWMulFP_acc.aux_dwu_rel t STD yh yl DWy.
have Hu0 : 0 <= bpow radix2 (- fprec t) by apply bpow_ge_0.
have Hthy : Rabs (FT2R th * FT2R yh)
             <= 1 + bpow radix2 (- fprec t).
{ have Htri := Rabs_triang (FT2R th * FT2R yh - 1) 1.
  have Heq : (FT2R th * FT2R yh - 1 + 1)%R = FT2R th * FT2R yh by ring.
  rewrite Heq Rabs_R1 in Htri. lra. }
rewrite Rabs_mult.
have Hswap : Rabs (FT2R yh) * Rabs (FT2R th)
             = Rabs (FT2R th * FT2R yh).
{ rewrite Rabs_mult; ring. }
eapply Rle_trans.
- apply Rmult_le_compat_r; [apply Rabs_pos | exact Hyl].
- rewrite Rmult_assoc Hswap.
  apply Rmult_le_compat_l; [exact Hu0 | exact Hthy].
Qed.

(** The exact FMA residual [1-yh*th] is at most one unit roundoff, hence its
    rounded value cannot overflow. *)
Lemma DWDivDW_rh_finite_from_cond (xh xl yh yl : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivDW_cond xh xl yh yl ->
  is_finite (BFMA (BOPP yh) (BDIV (Zconst t 1) yh) (Zconst t 1)) = true.
Proof.
move => Hp4 COND.
move: (COND) => [_ [_ [Hfyh _]]].
set th := BDIV (Zconst t 1) yh.
have Fth : is_finite th = true
  by exact (DWDivDW_th_finite_from_cond xh xl yh yl COND).
have Hyhne := DWDivDW_cond_yh_nonzero xh xl yh yl COND.
have UFth := DWDivDW_cond_UF_th xh xl yh yl COND.
have Hone : FT2R (Zconst t 1) = 1%R.
{ rewrite /Zconst FT2R_ftype_of_float.
  have Hpow : (0 < 2 ^ fprec t)%Z.
  { apply Z.pow_pos_nonneg; pose proof (fprec_lb t); lia. }
  have Hrange : (- 2 ^ fprec t <= 1 <= 2 ^ fprec t)%Z by lia.
  have Hexact := proj1 (IEEE754_extra.BofZ_exact
                          (fprec t) (femax t) _ _ 1 Hrange).
  rewrite Hexact; reflexivity. }
have Honefin : is_finite (Zconst t 1) = true.
{ rewrite /Zconst is_finite_Binary float_of_ftype_of_float.
  have Hpow : (0 < 2 ^ fprec t)%Z.
  { apply Z.pow_pos_nonneg; pose proof (fprec_lb t); lia. }
  have Hrange : (- 2 ^ fprec t <= 1 <= 2 ^ fprec t)%Z by lia.
  exact (proj1 (proj2 (IEEE754_extra.BofZ_exact
                         (fprec t) (femax t) _ _ 1 Hrange))). }
have Hres := DWDivFP_acc.thy_residual (Zconst t 1) yh Fth Hyhne.
rewrite Hone in Hres.
specialize (Hres UFth).
have Hu1 : bpow radix2 (- fprec t) <= 1.
{ have -> : (1:R) = bpow radix2 0 by reflexivity.
  apply bpow_le; pose proof (fprec_lb t); lia. }
have Hoppfin : is_finite (BOPP yh) = true
  by exact (proj2 (BOPP_is_finite t yh) Hfyh).
apply no_overflow_fma_is_finite;
  [exact Hoppfin | exact Fth | exact Honefin |].
have Hopp : (- FT2R yh = FT2R (BOPP yh))%R :=
  @BOPP_binary t NANS STD yh (or_intror Hfyh).
rewrite -Hopp Hone.
set v := (- FT2R yh * FT2R th + 1)%R.
have Hv : Rabs v <= bpow radix2 (- fprec t).
{ have Heq : v = - (FT2R th * FT2R yh - 1) by (unfold v; ring).
  rewrite Heq Rabs_Ropp.
  unfold th; rewrite Rabs_R1 Rmult_1_l in Hres; exact Hres. }
have HO : 8 <= bpow radix2 (femax t).
{ have -> : (8:R) = bpow radix2 3 by reflexivity.
  apply bpow_le; exact (femax_lb t). }
have Hvlt : Rabs v < bpow radix2 (femax t) by lra.
eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp |].
have Hulp := ulp_below_overflow v Hvlt.
have Hquarter : bpow radix2 (femax t - fprec t)
                <= /4 * bpow radix2 (femax t).
{ have -> : (/4 * bpow radix2 (femax t))%R =
      bpow radix2 (femax t - 2).
  { symmetry; exact (@DWDivFP_acc.aux_quarter_Omega t). }
  apply bpow_le; lia. }
lra.
Qed.

(** The low divisor product is of order [u]: double-word nonoverlap gives
    [|yl| <= u|yh|], while reciprocal rounding gives [|th*yh| <= 1+u]. *)
Lemma DWDivDW_yl_th_finite_from_cond (xh xl yh yl : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivDW_cond xh xl yh yl ->
  is_finite (BMULT yl (BDIV (Zconst t 1) yh)) = true.
Proof.
move => Hp4 COND.
move: (COND) => [_ [_ [_ [Hfyl [_ [DWy _]]]]]].
set th := BDIV (Zconst t 1) yh.
have Fth : is_finite th = true
  by exact (DWDivDW_th_finite_from_cond xh xl yh yl COND).
have Hyhne := DWDivDW_cond_yh_nonzero xh xl yh yl COND.
have UFth := DWDivDW_cond_UF_th xh xl yh yl COND.
have Hone : FT2R (Zconst t 1) = 1%R.
{ rewrite /Zconst FT2R_ftype_of_float.
  have Hpow : (0 < 2 ^ fprec t)%Z.
  { apply Z.pow_pos_nonneg; pose proof (fprec_lb t); lia. }
  have Hrange : (- 2 ^ fprec t <= 1 <= 2 ^ fprec t)%Z by lia.
  have Hexact := proj1 (IEEE754_extra.BofZ_exact
                          (fprec t) (femax t) _ _ 1 Hrange).
  rewrite Hexact; reflexivity. }
have Hres := DWDivFP_acc.thy_residual (Zconst t 1) yh Fth Hyhne.
rewrite Hone in Hres.
specialize (Hres UFth).
rewrite Rabs_R1 Rmult_1_l in Hres.
fold th in Hres.
have Hyl : Rabs (FT2R yl) <= bpow radix2 (- fprec t) * Rabs (FT2R yh) :=
  @DWMulFP_acc.aux_dwu_rel t STD yh yl DWy.
have Hu0 : 0 <= bpow radix2 (- fprec t) by apply bpow_ge_0.
have Hu16 : bpow radix2 (- fprec t) <= /16.
{ have -> : (/16:R) = bpow radix2 (-4) by (simpl; lra).
  apply bpow_le; lia. }
have Hthy : Rabs (FT2R th * FT2R yh)
             <= 1 + bpow radix2 (- fprec t).
{ have Htri := Rabs_triang (FT2R th * FT2R yh - 1) 1.
  have Heq : (FT2R th * FT2R yh - 1 + 1)%R = FT2R th * FT2R yh by ring.
  rewrite Heq Rabs_R1 in Htri. lra. }
have Hprod : Rabs (FT2R yl * FT2R th)
              <= bpow radix2 (- fprec t) *
                   (1 + bpow radix2 (- fprec t)).
{ rewrite Rabs_mult.
  have Hswap : Rabs (FT2R yh) * Rabs (FT2R th)
               = Rabs (FT2R th * FT2R yh).
  { rewrite Rabs_mult; ring. }
  eapply Rle_trans.
  - apply Rmult_le_compat_r; [apply Rabs_pos | exact Hyl].
  - rewrite Rmult_assoc Hswap.
    apply Rmult_le_compat_l; [exact Hu0 | exact Hthy]. }
apply no_overflow_mult_is_finite; [exact Hfyl | exact Fth |].
have HO : 8 <= bpow radix2 (femax t).
{ have -> : (8:R) = bpow radix2 3 by reflexivity.
  apply bpow_le; exact (femax_lb t). }
have Hvlt : Rabs (FT2R yl * FT2R th) < bpow radix2 (femax t) by nra.
eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp |].
have Hulp := ulp_below_overflow (FT2R yl * FT2R th) Hvlt.
have Hquarter : bpow radix2 (femax t - fprec t)
                <= /4 * bpow radix2 (femax t).
{ rewrite -(@DWDivFP_acc.aux_quarter_Omega t).
  apply bpow_le; lia. }
nra.
Qed.

Lemma DWDivDW_rl_finite_from_cond (xh xl yh yl : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivDW_cond xh xl yh yl ->
  is_finite (BOPP (BMULT yl (BDIV (Zconst t 1) yh))) = true.
Proof.
move => Hp4 COND.
apply (proj2 (BOPP_is_finite t _)).
exact (DWDivDW_yl_th_finite_from_cond xh xl yh yl Hp4 COND).
Qed.

Lemma DWDivDW_rh_abs_le_one (xh xl yh yl : ftype t) :
  (4 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  Rabs (FT2R (BFMA (BOPP yh) (BDIV (Zconst t 1) yh) (Zconst t 1))) <= 1.
Proof.
move => Hp4 COND.
move: (COND) => [_ [_ [Hfyh _]]].
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
have Frh : is_finite rh = true
  by exact (DWDivDW_rh_finite_from_cond xh xl yh yl Hp4 COND).
have Hres := DWDivDW_th_yh_residual_from_cond xh xl yh yl COND.
fold th in Hres.
have Hu1 : bpow radix2 (- fprec t) <= 1.
{ have -> : (1:R) = bpow radix2 0 by reflexivity.
  apply bpow_le; pose proof (fprec_lb t); lia. }
have Hopp : (- FT2R yh = FT2R (BOPP yh))%R :=
  @BOPP_binary t NANS STD yh (or_intror Hfyh).
have Hone : FT2R (Zconst t 1) = 1%R.
{ rewrite /Zconst FT2R_ftype_of_float.
  have Hpow : (0 < 2 ^ fprec t)%Z.
  { apply Z.pow_pos_nonneg; pose proof (fprec_lb t); lia. }
  have Hrange : (- 2 ^ fprec t <= 1 <= 2 ^ fprec t)%Z by lia.
  have Hexact := proj1 (IEEE754_extra.BofZ_exact
                          (fprec t) (femax t) _ _ 1 Hrange).
  rewrite Hexact; reflexivity. }
unfold rh.
rewrite -(BFMA_round_correct t (BOPP yh) th (Zconst t 1) Frh) -Hopp Hone.
apply abs_round_le_generic.
- exact valid_fexp_inst.
- apply valid_rnd_N.
- change (generic_format radix2 (SpecFloat.fexp (fprec t) (femax t))
            (bpow radix2 0)).
  apply generic_format_bpow. unfold SpecFloat.fexp.
  apply Z.max_lub; [pose proof (fprec_lb t); lia |].
  unfold SpecFloat.emin; pose proof (femax_lb t); pose proof (fprec_lb t); lia.
- have Heq : (- FT2R yh * FT2R th + 1)%R
             = - (FT2R th * FT2R yh - 1) by ring.
  rewrite Heq Rabs_Ropp. lra.
Qed.

Lemma DWDivDW_rl_abs_le_one (xh xl yh yl : ftype t) :
  (4 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  Rabs (FT2R (BOPP (BMULT yl (BDIV (Zconst t 1) yh)))) <= 1.
Proof.
move => Hp4 COND.
set th := BDIV (Zconst t 1) yh.
set q := BMULT yl th.
have Fq : is_finite q = true
  by exact (DWDivDW_yl_th_finite_from_cond xh xl yh yl Hp4 COND).
have Frl : is_finite (BOPP q) = true
  by exact (DWDivDW_rl_finite_from_cond xh xl yh yl Hp4 COND).
have Hq := DWDivDW_yl_th_abs_from_cond xh xl yh yl COND.
fold th in Hq.
have Hu0 : 0 <= bpow radix2 (- fprec t) by apply bpow_ge_0.
have Hu16 : bpow radix2 (- fprec t) <= /16.
{ have -> : (/16:R) = bpow radix2 (-4) by (simpl; lra).
  apply bpow_le; lia. }
have Hopp : (- FT2R q = FT2R (BOPP q))%R :=
  @BOPP_binary t NANS STD q (or_introl Frl).
rewrite -Hopp Rabs_Ropp.
unfold q.
rewrite -(BMULT_round_correct t yl th Fq).
apply abs_round_le_generic.
- exact valid_fexp_inst.
- apply valid_rnd_N.
- change (generic_format radix2 (SpecFloat.fexp (fprec t) (femax t))
            (bpow radix2 0)).
  apply generic_format_bpow. unfold SpecFloat.fexp.
  apply Z.max_lub; [pose proof (fprec_lb t); lia |].
  unfold SpecFloat.emin; pose proof (femax_lb t); pose proof (fprec_lb t); lia.
- nra.
Qed.

(** The low residual remains strictly below [2u], including in the
    subnormal regime.  This sharper exponent fact, rather than a magnitude
    ordering between [rh] and [rl], is what the paper's Fast2Sum proof uses. *)
Lemma DWDivDW_rl_abs_lt_two_u (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  Rabs (FT2R (BOPP (BMULT yl (BDIV (Zconst t 1) yh)))) <
    2*bpow radix2 (-fprec t).
Proof.
move => Hp14 COND.
set th := BDIV (Zconst t 1) yh.
set q := BMULT yl th.
set rl := BOPP q.
set u := bpow radix2 (-fprec t).
set eta := bpow radix2 (@common.emin t).
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /16384.
{ unfold u. have -> : (/16384:R)=bpow radix2 (-14) by (simpl;lra).
  apply bpow_le; lia. }
have Harg := DWDivDW_yl_th_abs_from_cond xh xl yh yl COND.
fold th u in Harg.
have Fq := DWDivDW_yl_th_finite_from_cond
  xh xl yh yl ltac:(lia) COND.
fold th q in Fq.
have Frl := DWDivDW_rl_finite_from_cond
  xh xl yh yl ltac:(lia) COND.
fold th q rl in Frl.
have Hqr : FT2R q = round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
    (FT2R yl*FT2R th).
{ unfold q. symmetry; apply BMULT_round_correct; exact Fq. }
have Herr := round_FLT_error_rel_emin (t:=t) (FT2R yl*FT2R th).
fold u eta in Herr.
have Heta : eta <= 4*u^2.
{ unfold eta, u, common.emin, SpecFloat.emin.
  replace (4*bpow radix2 (-fprec t)^2)%R with
    (bpow radix2 (2-2*fprec t))%R.
  - apply bpow_le. pose proof (fprec_lt_femax t); lia.
  - replace (bpow radix2 (-fprec t)^2)%R with
      (bpow radix2 (-fprec t)*bpow radix2 (-fprec t))%R by ring.
    rewrite -bpow_plus.
    have -> : (4:R)=bpow radix2 2 by reflexivity.
    rewrite -bpow_plus. f_equal; lia. }
have Hqerr : Rabs (FT2R q-(FT2R yl*FT2R th)) <=
    u*(u*(1+u))+/2*eta.
{ rewrite Hqr. eapply Rle_trans; [exact Herr|].
  apply Rplus_le_compat_r.
  apply Rmult_le_compat_l; [lra|exact Harg]. }
have Hqabs : Rabs (FT2R q) <=
    u*(u*(1+u))+/2*eta+u*(1+u).
{ have H := Rabs_triang
    (FT2R q-(FT2R yl*FT2R th)) (FT2R yl*FT2R th).
  replace (FT2R q-(FT2R yl*FT2R th)+FT2R yl*FT2R th)%R
    with (FT2R q) in H by ring.
  nra. }
have Hop : FT2R rl = -FT2R q.
{ symmetry; exact (@BOPP_binary t NANS STD q (or_introl Frl)). }
rewrite Hop Rabs_Ropp. eapply Rle_lt_trans; [exact Hqabs|]. nra.
Qed.

Lemma DWDivDW_rl_cexp_le (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let rl := BOPP (BMULT yl th) in
  FT2R rl <> 0 ->
  (cexp radix2 (FLX_exp (fprec t)) (FT2R rl) <=
     1-2*fprec t)%Z.
Proof.
move => Hp14 COND /=.
set th := BDIV (Zconst t 1) yh.
set rl := BOPP (BMULT yl th).
move => Hrl0.
have Hrl := DWDivDW_rl_abs_lt_two_u xh xl yh yl Hp14 COND.
fold th rl in Hrl.
cbv [Generic_fmt.cexp FLX_exp].
suff Hmag : (mag radix2 (FT2R rl) <= 1-fprec t)%Z.
  { have Hsub := proj1 (Z.sub_le_mono_r
      (mag radix2 (FT2R rl)) (1-fprec t) (fprec t)) Hmag.
  have Heq : ((1-fprec t)-fprec t = 1-2*fprec t)%Z by ring.
  rewrite Heq in Hsub. exact Hsub. }
apply mag_le_bpow; [exact Hrl0|].
eapply Rlt_le_trans; [exact Hrl|].
replace (2*bpow radix2 (-fprec t))%R with
  (bpow radix2 (1-fprec t))%R.
- apply Rle_refl.
- have -> : (2:R)=bpow radix2 1 by reflexivity.
  rewrite -bpow_plus. f_equal; lia.
Qed.

(** All three operations of the residual [Fast2Sum] stay within tiny
    power-of-two envelopes.  This proof does not require the Fast2Sum
    magnitude-ordering condition. *)
Lemma DWDivDW_fast2sum_cascade_from_cond (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let e := Fast2Sum
       (BFMA (BOPP yh) (BDIV (Zconst t 1) yh) (Zconst t 1))
       (BOPP (BMULT yl (BDIV (Zconst t 1) yh))) in
  is_finite_p e /\
  Rabs (FT2R (fst e)) <= 2 /\
  Rabs (FT2R (snd e)) <= 8.
Proof.
move => Hp14 COND.
set rh := BFMA (BOPP yh) (BDIV (Zconst t 1) yh) (Zconst t 1).
set rl := BOPP (BMULT yl (BDIV (Zconst t 1) yh)).
set s := BPLUS rh rl.
set z := BMINUS s rh.
have Hp4 : (4 <= fprec t)%Z by lia.
have Frh : is_finite rh = true
  by exact (DWDivDW_rh_finite_from_cond xh xl yh yl Hp4 COND).
have Frl : is_finite rl = true
  by exact (DWDivDW_rl_finite_from_cond xh xl yh yl Hp4 COND).
have Hrh : Rabs (FT2R rh) <= 1
  by exact (DWDivDW_rh_abs_le_one xh xl yh yl Hp4 COND).
have Hrl : Rabs (FT2R rl) <= 1
  by exact (DWDivDW_rl_abs_le_one xh xl yh yl Hp4 COND).
have Hlow (k : Z) (Hk : (0 <= k)%Z) :
    (SpecFloat.emin (fprec t) (femax t) <= k)%Z.
{ unfold SpecFloat.emin; pose proof (femax_lb t); pose proof (fprec_lb t); lia. }
have Hhigh (k : Z) (Hk : (k <= 3)%Z) : (k < femax t)%Z.
{ pose proof (fprec_lt_femax t); lia. }
have Hs_in : Rabs (FT2R rh + FT2R rl) <= bpow radix2 1.
{ change (bpow radix2 1) with 2%R.
  eapply Rle_trans; [apply Rabs_triang |]; lra. }
have [Fs Hs] := BPLUS_finite_bpow_bound rh rl 1 Frh Frl
                   (Hlow 1%Z ltac:(lia)) (Hhigh 1%Z ltac:(lia)) Hs_in.
fold s in Fs, Hs.
have Hz_in : Rabs (FT2R s - FT2R rh) <= bpow radix2 2.
{ change (bpow radix2 2) with 4%R.
  change (Rabs (FT2R s) <= 2) in Hs.
  have Htri := Rabs_triang (FT2R s) (- FT2R rh).
  replace (FT2R s + - FT2R rh)%R with (FT2R s - FT2R rh)%R in Htri by ring.
  rewrite Rabs_Ropp in Htri; lra. }
have [Fz Hz] := BMINUS_finite_bpow_bound s rh 2 Fs Frh
                   (Hlow 2%Z ltac:(lia)) (Hhigh 2%Z ltac:(lia)) Hz_in.
fold z in Fz, Hz.
have He_in : Rabs (FT2R rl - FT2R z) <= bpow radix2 3.
{ change (bpow radix2 3) with 8%R.
  change (Rabs (FT2R z) <= 4) in Hz.
  have Htri := Rabs_triang (FT2R rl) (- FT2R z).
  replace (FT2R rl + - FT2R z)%R with (FT2R rl - FT2R z)%R in Htri by ring.
  rewrite Rabs_Ropp in Htri; lra. }
have [Fe He] := BMINUS_finite_bpow_bound rl z 3 Frl Fz
                 (Hlow 3%Z ltac:(lia)) (Hhigh 3%Z ltac:(lia)) He_in.
change ((is_finite s = true /\ is_finite (BMINUS rl z) = true) /\
        Rabs (FT2R s) <= 2 /\ Rabs (FT2R (BMINUS rl z)) <= 8).
change (Rabs (FT2R s) <= 2) in Hs.
change (Rabs (FT2R (BMINUS rl z)) <= 8) in He.
exact (conj (conj Fs Fe) (conj Hs He)).
Qed.

Corollary DWDivDW_fast2sum_finite_from_cond (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  is_finite_p
    (Fast2Sum
       (BFMA (BOPP yh) (BDIV (Zconst t 1) yh) (Zconst t 1))
       (BOPP (BMULT yl (BDIV (Zconst t 1) yh)))).
Proof.
move => Hp14 COND.
exact (proj1 (DWDivDW_fast2sum_cascade_from_cond xh xl yh yl Hp14 COND)).
Qed.

(** Forward overflow cascade for the reciprocal-times-residual block.  The
    deliberately coarse [|eh| <= 2], [|el| <= 8] bounds are sufficient because
    [th] is at scale [2^(femax-p-3)]. *)
Lemma DWDivDW_timesfp_cascade_from_cond (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let e := Fast2Sum
       (BFMA (BOPP yh) th (Zconst t 1)) (BOPP (BMULT yl th)) in
  let d := DWTimesFP3 (fst e) (snd e) th in
  is_finite_p d /\
  Rabs (FT2R (fst d)) <= bpow radix2 (femax t - fprec t + 2) /\
  Rabs (FT2R (snd d)) <= bpow radix2 (femax t - fprec t + 4).
Proof.
move => Hp14 COND.
set th := BDIV (Zconst t 1) yh.
set e := Fast2Sum (BFMA (BOPP yh) th (Zconst t 1)) (BOPP (BMULT yl th)).
set eh := fst e; set el := snd e.
set ch := BMULT eh th.
set cl1 := Fast2Mult_err eh th.
set cl3 := BFMA el th cl1.
set s := BPLUS ch cl3.
set z := BMINUS s ch.
have Fth := DWDivDW_th_finite_from_cond xh xl yh yl COND.
fold th in Fth.
have Hth := DWDivDW_th_abs_upper_tight xh xl yh yl COND.
fold th in Hth.
have Hec := DWDivDW_fast2sum_cascade_from_cond xh xl yh yl Hp14 COND.
fold e in Hec. destruct Hec as [[Feh Fel] [Heh Hel]].
fold eh in Feh, Heh; fold el in Fel, Hel.
have Hlow (k : Z) (Hk : (femax t - fprec t - 2 <= k)%Z) :
    (SpecFloat.emin (fprec t) (femax t) <= k)%Z.
{ unfold SpecFloat.emin; pose proof (femax_lb t); lia. }
have Hhigh (k : Z) (Hk : (k <= femax t - fprec t + 4)%Z) :
    (k < femax t)%Z.
{ pose proof (fprec_lb t); lia. }
have H2 (k : Z) :
    2 * bpow radix2 k = bpow radix2 (k + 1).
{ change (bpow radix2 1 * bpow radix2 k = bpow radix2 (k + 1)).
  rewrite -bpow_plus; f_equal; lia. }
have H8 (k : Z) :
    8 * bpow radix2 k = bpow radix2 (k + 3).
{ change (bpow radix2 3 * bpow radix2 k = bpow radix2 (k + 3)).
  rewrite -bpow_plus; f_equal; lia. }
have Hch_in : Rabs (FT2R eh * FT2R th)
  <= bpow radix2 (femax t - fprec t - 2).
{ rewrite Rabs_mult.
  eapply Rle_trans.
  - apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Heh | exact Hth].
  - rewrite H2. apply Req_le; f_equal; lia. }
have [Fch Hch] := BMULT_finite_bpow_bound eh th
  (femax t - fprec t - 2) Feh Fth
  (Hlow (femax t - fprec t - 2)%Z ltac:(lia))
  (Hhigh (femax t - fprec t - 2)%Z ltac:(lia)) Hch_in.
fold ch in Fch, Hch.
have Ffast := Fast2Mult_acc_helpers.Fast2Mult_finite_unconditional eh th Fch.
have Fcl1 : is_finite cl1 = true by exact (proj2 Ffast).
have Hprodlt : Rabs (FT2R eh * FT2R th) < bpow radix2 (femax t).
{ eapply Rle_lt_trans; [exact Hch_in | apply bpow_lt; lia]. }
have Hcl1u := Fast2Mult_acc.Fast2Mult_accuracy_norm eh th Fch.
have Hulp := ulp_below_overflow (FT2R eh * FT2R th) Hprodlt.
have Hcl1 : Rabs (FT2R cl1) <= bpow radix2 (femax t - fprec t - 1).
{ eapply Rle_trans; [exact Hcl1u |].
  eapply Rle_trans; [apply Rmult_le_compat_l; [lra | exact Hulp] |].
  have Heq : (/2 * bpow radix2 (femax t - fprec t))%R
      = bpow radix2 (femax t - fprec t - 1).
  { change (bpow radix2 (-1) * bpow radix2 (femax t - fprec t) =
              bpow radix2 (femax t - fprec t - 1)).
    rewrite -bpow_plus; f_equal; lia. }
  rewrite Heq; lra. }
have Helth : Rabs (FT2R el * FT2R th)
    <= bpow radix2 (femax t - fprec t).
{ rewrite Rabs_mult.
  eapply Rle_trans.
  - apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hel | exact Hth].
  - rewrite H8. apply Req_le; f_equal; lia. }
have Hcl3_in : Rabs (FT2R el * FT2R th + FT2R cl1)
    <= bpow radix2 (femax t - fprec t + 1).
{ eapply Rle_trans; [apply Rabs_triang |].
  have Hcl1' : Rabs (FT2R cl1) <= bpow radix2 (femax t - fprec t).
  { eapply Rle_trans; [exact Hcl1 |]. apply bpow_le; lia. }
  rewrite -(H2 (femax t - fprec t)%Z). lra. }
have [Fcl3 Hcl3] := BFMA_finite_bpow_bound el th cl1
  (femax t - fprec t + 1) Fel Fth Fcl1
  (Hlow (femax t - fprec t + 1)%Z ltac:(lia))
  (Hhigh (femax t - fprec t + 1)%Z ltac:(lia)) Hcl3_in.
fold cl3 in Fcl3, Hcl3.
have Hch' : Rabs (FT2R ch) <= bpow radix2 (femax t - fprec t + 1).
{ eapply Rle_trans; [exact Hch |]. apply bpow_le; lia. }
have Hs_in : Rabs (FT2R ch + FT2R cl3)
    <= bpow radix2 (femax t - fprec t + 2).
{ eapply Rle_trans; [apply Rabs_triang |].
  replace (femax t - fprec t + 2)%Z with
    ((femax t - fprec t + 1) + 1)%Z by lia.
  rewrite -(H2 (femax t - fprec t + 1)%Z); lra. }
have [Fs Hs] := BPLUS_finite_bpow_bound ch cl3
  (femax t - fprec t + 2) Fch Fcl3
  (Hlow (femax t - fprec t + 2)%Z ltac:(lia))
  (Hhigh (femax t - fprec t + 2)%Z ltac:(lia)) Hs_in.
fold s in Fs, Hs.
have Hz_in : Rabs (FT2R s - FT2R ch)
    <= bpow radix2 (femax t - fprec t + 3).
{ have Htri := Rabs_triang (FT2R s) (- FT2R ch).
  replace (FT2R s + - FT2R ch)%R with (FT2R s - FT2R ch)%R in Htri by ring.
  rewrite Rabs_Ropp in Htri.
  have Hch'' : Rabs (FT2R ch) <= bpow radix2 (femax t - fprec t + 2).
  { eapply Rle_trans; [exact Hch |]. apply bpow_le; lia. }
  replace (femax t - fprec t + 3)%Z with
    ((femax t - fprec t + 2) + 1)%Z by lia.
  rewrite -(H2 (femax t - fprec t + 2)%Z).
  replace (2 * bpow radix2 (femax t - fprec t + 2))%R with
    (bpow radix2 (femax t - fprec t + 2) +
     bpow radix2 (femax t - fprec t + 2))%R by ring.
  eapply Rle_trans; [exact Htri |].
  exact (Rplus_le_compat _ _ _ _ Hs Hch''). }
have [Fz Hz] := BMINUS_finite_bpow_bound s ch
  (femax t - fprec t + 3) Fs Fch
  (Hlow (femax t - fprec t + 3)%Z ltac:(lia))
  (Hhigh (femax t - fprec t + 3)%Z ltac:(lia)) Hz_in.
fold z in Fz, Hz.
have He_in : Rabs (FT2R cl3 - FT2R z)
    <= bpow radix2 (femax t - fprec t + 4).
{ have Htri := Rabs_triang (FT2R cl3) (- FT2R z).
  replace (FT2R cl3 + - FT2R z)%R with (FT2R cl3 - FT2R z)%R in Htri by ring.
  rewrite Rabs_Ropp in Htri.
  have Hcl3' : Rabs (FT2R cl3) <= bpow radix2 (femax t - fprec t + 3).
  { eapply Rle_trans; [exact Hcl3 |]. apply bpow_le; lia. }
  replace (femax t - fprec t + 4)%Z with
    ((femax t - fprec t + 3) + 1)%Z by lia.
  rewrite -(H2 (femax t - fprec t + 3)%Z); lra. }
have [Ferr Herr] := BMINUS_finite_bpow_bound cl3 z
  (femax t - fprec t + 4) Fcl3 Fz
  (Hlow (femax t - fprec t + 4)%Z ltac:(lia))
  (Hhigh (femax t - fprec t + 4)%Z ltac:(lia)) He_in.
change ((is_finite s = true /\ is_finite (BMINUS cl3 z) = true) /\
  Rabs (FT2R s) <= bpow radix2 (femax t - fprec t + 2) /\
  Rabs (FT2R (BMINUS cl3 z)) <= bpow radix2 (femax t - fprec t + 4)).
split; [exact (conj Fs Ferr) |].
exact (conj Hs Herr).
Qed.

(** Forward overflow cascade for the reciprocal renormalization [DWPlusFP]. *)
Lemma DWDivDW_plusfp_cascade_from_cond (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let e := Fast2Sum
       (BFMA (BOPP yh) th (Zconst t 1)) (BOPP (BMULT yl th)) in
  let d := DWTimesFP3 (fst e) (snd e) th in
  let m := DWPlusFP (fst d) (snd d) th in
  is_finite_p m /\
  Rabs (FT2R (fst m)) <= bpow radix2 (femax t - fprec t + 8) /\
  Rabs (FT2R (snd m)) <= bpow radix2 (femax t - fprec t + 10).
Proof.
move => Hp14 COND.
set th := BDIV (Zconst t 1) yh.
set e := Fast2Sum (BFMA (BOPP yh) th (Zconst t 1)) (BOPP (BMULT yl th)).
set d := DWTimesFP3 (fst e) (snd e) th.
set dh := fst d; set dl := snd d.
set ts := TwoSumF dh th.
set sh := fst ts; set sl := snd ts.
set v := BPLUS dl sl.
set mh := BPLUS sh v.
set z := BMINUS mh sh.
have Fth := DWDivDW_th_finite_from_cond xh xl yh yl COND; fold th in Fth.
have Hth := DWDivDW_th_abs_upper_tight xh xl yh yl COND; fold th in Hth.
have Hdc := DWDivDW_timesfp_cascade_from_cond xh xl yh yl Hp14 COND.
fold th e d in Hdc. destruct Hdc as [[Fdh Fdl] [Hdh Hdl]].
fold dh in Fdh, Hdh; fold dl in Fdl, Hdl.
have Hlow (k : Z) (Hk : (femax t - fprec t - 3 <= k)%Z) :
    (SpecFloat.emin (fprec t) (femax t) <= k)%Z.
{ unfold SpecFloat.emin; pose proof (femax_lb t); lia. }
have Hhigh (k : Z) (Hk : (k <= femax t - fprec t + 10)%Z) :
    (k < femax t)%Z.
{ pose proof (fprec_lb t); lia. }
have H2 (k : Z) : 2 * bpow radix2 k = bpow radix2 (k + 1).
{ change (bpow radix2 1 * bpow radix2 k = bpow radix2 (k + 1)).
  rewrite -bpow_plus; f_equal; lia. }
have Hth' : Rabs (FT2R th) <= bpow radix2 (femax t - fprec t + 2).
{ eapply Rle_trans; [exact Hth |]. apply bpow_le; lia. }
have Hsum_in : Rabs (FT2R dh + FT2R th)
    <= bpow radix2 (femax t - fprec t + 3).
{ eapply Rle_trans; [apply Rabs_triang |].
  replace (femax t - fprec t + 3)%Z with
    ((femax t - fprec t + 2) + 1)%Z by lia.
  rewrite -(H2 (femax t - fprec t + 2)%Z).
  replace (2 * bpow radix2 (femax t - fprec t + 2))%R with
    (bpow radix2 (femax t - fprec t + 2) +
     bpow radix2 (femax t - fprec t + 2))%R by ring.
  exact (Rplus_le_compat _ _ _ _ Hdh Hth'). }
have [Fsh Hsh] := BPLUS_finite_bpow_bound dh th
  (femax t - fprec t + 3) Fdh Fth
  (Hlow (femax t - fprec t + 3)%Z ltac:(lia))
  (Hhigh (femax t - fprec t + 3)%Z ltac:(lia)) Hsum_in.
fold sh in Fsh, Hsh.
have Hminus_in : Rabs (FT2R dh - FT2R th)
    <= bpow radix2 (femax t - fprec t + 3).
{ have Htri := Rabs_triang (FT2R dh) (- FT2R th).
  replace (FT2R dh + - FT2R th)%R with (FT2R dh - FT2R th)%R in Htri by ring.
  rewrite Rabs_Ropp in Htri.
  replace (femax t - fprec t + 3)%Z with
    ((femax t - fprec t + 2) + 1)%Z by lia.
  rewrite -(H2 (femax t - fprec t + 2)%Z).
  replace (2 * bpow radix2 (femax t - fprec t + 2))%R with
    (bpow radix2 (femax t - fprec t + 2) +
     bpow radix2 (femax t - fprec t + 2))%R by ring.
  eapply Rle_trans; [exact Htri |].
  exact (Rplus_le_compat _ _ _ _ Hdh Hth'). }
have [Fminus _] := BMINUS_finite_bpow_bound dh th
  (femax t - fprec t + 3) Fdh Fth
  (Hlow (femax t - fprec t + 3)%Z ltac:(lia))
  (Hhigh (femax t - fprec t + 3)%Z ltac:(lia)) Hminus_in.
have Hthq : Rabs (FT2R th) <= /4 * bpow radix2 (femax t).
{ rewrite -(@DWDivFP_acc.aux_quarter_Omega t).
  eapply Rle_trans; [exact Hth |]. apply bpow_le; lia. }
have Hthpred : Rabs (FT2R th) <
    Ulp.pred radix2 (SpecFloat.fexp (fprec t) (femax t)) (bpow radix2 (femax t)).
{ eapply Rle_lt_trans; [exact Hthq |].
  apply (@DWPlusDW_acc_helpers.Omega4_lt_predOmega t); lia. }
have Tcond : TwoSum_cond dh th := conj Fsh (conj Fminus Hthpred).
have Fts : is_finite_p ts.
{ fold ts. split; [exact Fsh |].
  apply TwoSum_acc_helpers.is_finite_TwoSum;
    [exact Fsh | exact Fminus | exact Hthpred]. }
have Fsl : is_finite sl = true by exact (proj2 Fts).
have Hsl_u := TwoSum_acc.TwoSum_accuracy dh th Fts.
have Hsumlt : Rabs (FT2R dh + FT2R th) < bpow radix2 (femax t).
{ eapply Rle_lt_trans; [exact Hsum_in | apply bpow_lt; lia]. }
have Hulp := ulp_below_overflow (FT2R dh + FT2R th) Hsumlt.
have Hsl : Rabs (FT2R sl) <= bpow radix2 (femax t - fprec t - 1).
{ eapply Rle_trans; [exact Hsl_u |].
  eapply Rle_trans; [apply Rmult_le_compat_l; [lra | exact Hulp] |].
  have Heq : (/2 * bpow radix2 (femax t - fprec t))%R =
      bpow radix2 (femax t - fprec t - 1).
  { change (bpow radix2 (-1) * bpow radix2 (femax t - fprec t) =
              bpow radix2 (femax t - fprec t - 1)).
    rewrite -bpow_plus; f_equal; lia. }
  rewrite Heq; lra. }
have Hsl' : Rabs (FT2R sl) <= bpow radix2 (femax t - fprec t + 4).
{ eapply Rle_trans; [exact Hsl |]. apply bpow_le; lia. }
have Hv_in : Rabs (FT2R dl + FT2R sl)
    <= bpow radix2 (femax t - fprec t + 5).
{ eapply Rle_trans; [apply Rabs_triang |].
  replace (femax t - fprec t + 5)%Z with
    ((femax t - fprec t + 4) + 1)%Z by lia.
  rewrite -(H2 (femax t - fprec t + 4)%Z).
  replace (2 * bpow radix2 (femax t - fprec t + 4))%R with
    (bpow radix2 (femax t - fprec t + 4) +
     bpow radix2 (femax t - fprec t + 4))%R by ring.
  exact (Rplus_le_compat _ _ _ _ Hdl Hsl'). }
have [Fv Hv] := BPLUS_finite_bpow_bound dl sl
  (femax t - fprec t + 5) Fdl Fsl
  (Hlow (femax t - fprec t + 5)%Z ltac:(lia))
  (Hhigh (femax t - fprec t + 5)%Z ltac:(lia)) Hv_in.
fold v in Fv, Hv.
have Hsh' : Rabs (FT2R sh) <= bpow radix2 (femax t - fprec t + 5).
{ eapply Rle_trans; [exact Hsh |]. apply bpow_le; lia. }
have Hmh_in : Rabs (FT2R sh + FT2R v)
    <= bpow radix2 (femax t - fprec t + 6).
{ eapply Rle_trans; [apply Rabs_triang |].
  replace (femax t - fprec t + 6)%Z with
    ((femax t - fprec t + 5) + 1)%Z by lia.
  rewrite -(H2 (femax t - fprec t + 5)%Z); lra. }
have [Fmh Hmh] := BPLUS_finite_bpow_bound sh v
  (femax t - fprec t + 6) Fsh Fv
  (Hlow (femax t - fprec t + 6)%Z ltac:(lia))
  (Hhigh (femax t - fprec t + 6)%Z ltac:(lia)) Hmh_in.
fold mh in Fmh, Hmh.
have Hz_in : Rabs (FT2R mh - FT2R sh)
    <= bpow radix2 (femax t - fprec t + 7).
{ have Htri := Rabs_triang (FT2R mh) (- FT2R sh).
  replace (FT2R mh + - FT2R sh)%R with (FT2R mh - FT2R sh)%R in Htri by ring.
  rewrite Rabs_Ropp in Htri.
  have Hsh'' : Rabs (FT2R sh) <= bpow radix2 (femax t - fprec t + 6).
  { eapply Rle_trans; [exact Hsh |]. apply bpow_le; lia. }
  replace (femax t - fprec t + 7)%Z with
    ((femax t - fprec t + 6) + 1)%Z by lia.
  rewrite -(H2 (femax t - fprec t + 6)%Z); lra. }
have [Fz Hz] := BMINUS_finite_bpow_bound mh sh
  (femax t - fprec t + 7) Fmh Fsh
  (Hlow (femax t - fprec t + 7)%Z ltac:(lia))
  (Hhigh (femax t - fprec t + 7)%Z ltac:(lia)) Hz_in.
fold z in Fz, Hz.
have Hml_in : Rabs (FT2R v - FT2R z)
    <= bpow radix2 (femax t - fprec t + 8).
{ have Htri := Rabs_triang (FT2R v) (- FT2R z).
  replace (FT2R v + - FT2R z)%R with (FT2R v - FT2R z)%R in Htri by ring.
  rewrite Rabs_Ropp in Htri.
  have Hv' : Rabs (FT2R v) <= bpow radix2 (femax t - fprec t + 7).
  { eapply Rle_trans; [exact Hv |]. apply bpow_le; lia. }
  replace (femax t - fprec t + 8)%Z with
    ((femax t - fprec t + 7) + 1)%Z by lia.
  rewrite -(H2 (femax t - fprec t + 7)%Z); lra. }
have [Fml Hml] := BMINUS_finite_bpow_bound v z
  (femax t - fprec t + 8) Fv Fz
  (Hlow (femax t - fprec t + 8)%Z ltac:(lia))
  (Hhigh (femax t - fprec t + 8)%Z ltac:(lia)) Hml_in.
change ((is_finite mh = true /\ is_finite (BMINUS v z) = true) /\
  Rabs (FT2R mh) <= bpow radix2 (femax t - fprec t + 8) /\
  Rabs (FT2R (BMINUS v z)) <= bpow radix2 (femax t - fprec t + 10)).
split; [exact (conj Fmh Fml) |].
split.
- eapply Rle_trans; [exact Hmh |]. apply bpow_le; lia.
- eapply Rle_trans; [exact Hml |]. apply bpow_le; lia.
Qed.

(** Relational reconstruction bounds.  Unlike the coarse exponent envelopes
    used only for overflow, these bounds retain the scale of [th]. *)
Lemma DWDivDW_reciprocal_relative_from_cond (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let rh := BFMA (BOPP yh) th (Zconst t 1) in
  let rl := BOPP (BMULT yl th) in
  let e := Fast2Sum rh rl in
  let d := DWTimesFP3 (fst e) (snd e) th in
  let m := DWPlusFP (fst d) (snd d) th in
  (1 - 86 * bpow radix2 (- fprec t)) * Rabs (FT2R th)
      <= Rabs (FT2R (fst m)) /\
  Rabs (FT2R (fst m)) <=
      (1 + 89 * bpow radix2 (- fprec t)) * Rabs (FT2R th) /\
  Rabs (FT2R (snd m)) <=
      2 * bpow radix2 (- fprec t) * Rabs (FT2R th) /\
  double_word_prop (fst m) (snd m) /\
  let ts := TwoSumF (fst d) th in
  let v := BPLUS (snd d) (snd ts) in
  Rabs (FT2R v) <= Rabs (FT2R (fst ts)).
Proof.
move => Hp14 COND.
set u := bpow radix2 (- fprec t).
set eta := bpow radix2 (@common.emin t).
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
set ql := BMULT yl th.
set rl := BOPP ql.
set e := Fast2Sum rh rl; set eh := fst e; set el := snd e.
set d := DWTimesFP3 eh el th; set dh := fst d; set dl := snd d.
set ts := TwoSumF dh th; set sh := fst ts; set sl := snd ts.
set v := BPLUS dl sl.
set m := Fast2Sum sh v; set mh := fst m; set ml := snd m.
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /16384.
{ unfold u. have -> : (/16384:R) = bpow radix2 (-14) by (simpl; lra).
  apply bpow_le; lia. }
have Htb := DWDivDW_th_relative_bounds_from_cond xh xl yh yl ltac:(lia) COND.
fold th u eta in Htb. destruct Htb as [HT0 [HTup [Heta HetaT]]].
set T := Rabs (FT2R th).
fold T in HT0, HTup, HetaT.
have Hround_u : forall (x C : R),
    Rabs x <= C*u -> C*u*u <= /2*u ->
    Rabs (round radix2 (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
                      (Znearest choice) x) <= (C+1)*u.
{ move => x C Hx HCu.
  eapply Rle_trans; [apply round_abs_le_relative_plus_half_emin |].
  have Hfac0 : 0 <= 1 + u by nra.
  have Hmul : (1+u)*Rabs x <= (1+u)*(C*u).
  { apply Rmult_le_compat_l; assumption. }
  eapply Rle_trans with (r2 := (C + /2)*u + /2*u).
  - apply Rplus_le_compat.
    + eapply Rle_trans; [exact Hmul |]. nra.
    + apply Rmult_le_compat_l; [lra | exact Heta].
  - nra. }
have Hround_uT : forall (x C : R),
    Rabs x <= C*u*T -> C*u*u <= /2*u ->
    Rabs (round radix2 (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
                      (Znearest choice) x) <= (C+1)*u*T.
{ move => x C Hx HCu.
  eapply Rle_trans; [apply round_abs_le_relative_plus_half_emin |].
  have Hfac0 : 0 <= 1 + u by nra.
  have Hmul : (1+u)*Rabs x <= (1+u)*(C*u*T).
  { apply Rmult_le_compat_l; assumption. }
  have HTnonneg : 0 <= T by lra.
  have HCuT : (C*u*u)*T <= (/2*u)*T.
  { apply Rmult_le_compat_r; assumption. }
  eapply Rle_trans with (r2 := (C + /2)*u*T + /2*(u*T)).
  - apply Rplus_le_compat.
    + eapply Rle_trans; [exact Hmul |]. nra.
    + apply Rmult_le_compat_l; [lra | exact HetaT].
  - nra. }
have Fth := DWDivDW_th_finite_from_cond xh xl yh yl COND; fold th in Fth.
have Frh := DWDivDW_rh_finite_from_cond xh xl yh yl ltac:(lia) COND; fold th rh in Frh.
have Fql := DWDivDW_yl_th_finite_from_cond xh xl yh yl ltac:(lia) COND;
  fold th ql in Fql.
have Frl := DWDivDW_rl_finite_from_cond xh xl yh yl ltac:(lia) COND;
  fold th ql rl in Frl.
have Hres := DWDivDW_th_yh_residual_from_cond xh xl yh yl COND;
  fold th u in Hres.
have Hylth := DWDivDW_yl_th_abs_from_cond xh xl yh yl COND;
  fold th u in Hylth.
have Hec := DWDivDW_fast2sum_cascade_from_cond xh xl yh yl Hp14 COND;
  fold th rh rl e in Hec; destruct Hec as [[Feh Fel] _].
fold eh in Feh; fold el in Fel.
have Hdc := DWDivDW_timesfp_cascade_from_cond xh xl yh yl Hp14 COND;
  fold th rh rl e eh el d in Hdc; destruct Hdc as [[Fdh Fdl] _].
fold dh in Fdh; fold dl in Fdl.
have Hmc := DWDivDW_plusfp_cascade_from_cond xh xl yh yl Hp14 COND;
  fold th rh rl e eh el d dh dl m in Hmc; destruct Hmc as [[Fmh Fml] _].
fold mh in Fmh; fold ml in Fml.
have Hopp_yh : (- FT2R yh = FT2R (BOPP yh))%R.
{ move: (COND) => [_ [_ [Fyh _]]].
  exact (@BOPP_binary t NANS STD yh (or_intror Fyh)). }
have Hone : FT2R (Zconst t 1) = 1%R.
{ rewrite /Zconst FT2R_ftype_of_float.
  have Hpow : (0 < 2 ^ fprec t)%Z.
  { apply Z.pow_pos_nonneg; pose proof (fprec_lb t); lia. }
  have Hrange : (- 2 ^ fprec t <= 1 <= 2 ^ fprec t)%Z by lia.
  have Hexact := proj1 (IEEE754_extra.BofZ_exact
                          (fprec t) (femax t) _ _ 1 Hrange).
  rewrite Hexact; reflexivity. }
have Hrh : Rabs (FT2R rh) <= 2*u.
{ unfold rh. rewrite -(BFMA_round_correct t (BOPP yh) th (Zconst t 1) Frh).
  rewrite -Hopp_yh Hone.
  eapply Rle_trans; [apply round_abs_le_relative_plus_half_emin |].
  have Heq : (- FT2R yh * FT2R th + 1)%R =
      - (FT2R th * FT2R yh - 1) by ring.
  rewrite Heq Rabs_Ropp.
  have Hu2 : u*u <= /2*u by nra.
  have Hfac0 : 0 <= 1 + u by nra.
  have Hmul : (1 + u) * Rabs (FT2R th * FT2R yh - 1)
                  <= (1 + u) * u.
  { apply Rmult_le_compat_l; assumption. }
  eapply Rle_trans with (r2 := /2*3*u + /2*u).
  - apply Rplus_le_compat.
    + eapply Rle_trans; [exact Hmul |]. nra.
    + apply Rmult_le_compat_l; [lra | exact Heta].
  - lra. }
have Hopp_ql : (- FT2R ql = FT2R rl)%R.
{ exact (@BOPP_binary t NANS STD ql (or_introl Frl)). }
have Hrl : Rabs (FT2R rl) <= 2*u.
{ rewrite -Hopp_ql Rabs_Ropp. unfold ql.
  rewrite -(BMULT_round_correct t yl th Fql).
  eapply Rle_trans; [apply round_abs_le_relative_plus_half_emin |].
  have Hfac0 : 0 <= 1 + u by nra.
  have Hmul : (1 + u) * Rabs (FT2R yl * FT2R th)
                  <= (1 + u) * (u * (1 + u)).
  { apply Rmult_le_compat_l; assumption. }
  have Hu3 : u*u*u <= /4*u by nra.
  eapply Rle_trans with (r2 := /2*3*u + /2*u).
  - apply Rplus_le_compat.
    + eapply Rle_trans; [exact Hmul |]. nra.
    + apply Rmult_le_compat_l; [lra | exact Heta].
  - lra. }
have Feh_sum : is_finite (BPLUS rh rl) = true.
{ change (is_finite (BPLUS rh rl) = true) in Feh. exact Feh. }
have Heh : Rabs (FT2R eh) <= 5*u.
{ unfold eh, e, Fast2Sum, fst.
  rewrite -(BPLUS_round_correct t rh rl Feh_sum).
  eapply Rle_trans; [apply round_abs_le_relative_plus_half_emin |].
  have Htri := Rabs_triang (FT2R rh) (FT2R rl).
  have Hin : Rabs (FT2R rh + FT2R rl) <= 4*u by lra.
  have Hfac0 : 0 <= 1 + u by nra.
  have Hmul : (1+u)*Rabs (FT2R rh + FT2R rl) <= (1+u)*(4*u).
  { apply Rmult_le_compat_l; assumption. }
  have Hu4 : 4*u*u <= /2*u by nra.
  eapply Rle_trans with (r2 := /2*9*u + /2*u).
  - apply Rplus_le_compat.
    + eapply Rle_trans; [exact Hmul |]. nra.
    + apply Rmult_le_compat_l; [lra | exact Heta].
  - lra. }
set ez := BMINUS eh rh.
have Fez : is_finite ez = true.
{ move: Fel. unfold el, e, Fast2Sum, snd. set z0 := BMINUS (BPLUS rh rl) rh.
  move => H. have Hz := proj2 (BMINUS_finite_e t rl z0 H).
  fold eh in Hz. fold ez. exact Hz. }
have Hez : Rabs (FT2R ez) <= 8*u.
{ unfold ez. rewrite -(BMINUS_round_correct t eh rh Fez).
  eapply Rle_trans; [apply Hround_u with (C := 7) | nra].
  have Htri := Rabs_triang (FT2R eh) (-FT2R rh).
  replace (FT2R eh + -FT2R rh)%R with (FT2R eh - FT2R rh)%R in Htri by ring.
  rewrite Rabs_Ropp in Htri; lra.
  nra. }
have Hel : Rabs (FT2R el) <= 12*u.
{ unfold el, e, Fast2Sum, snd.
  fold eh ez. rewrite -(BMINUS_round_correct t rl ez Fel).
  eapply Rle_trans; [apply Hround_u with (C := 10) |]; [|nra|nra].
  have Htri := Rabs_triang (FT2R rl) (-FT2R ez).
  replace (FT2R rl + -FT2R ez)%R with (FT2R rl - FT2R ez)%R in Htri by ring.
  rewrite Rabs_Ropp in Htri; lra. }
set ch := BMULT eh th.
set cl1 := Fast2Mult_err eh th.
set cl3 := BFMA el th cl1.
have Fch := DWMulFP_acc.FIN3 eh el th (conj Fdh Fdl); fold ch in Fch.
have Ffast := DWMulFP_acc.FIN1 eh el th (conj Fdh Fdl).
have Fcl1 : is_finite cl1 = true by exact (proj2 Ffast).
have Fcl3 := DWMulFP_acc.FIN2 eh el th (conj Fdh Fdl); fold cl1 cl3 in Fcl3.
have Hch : Rabs (FT2R ch) <= 6*u*T.
{ unfold ch. rewrite -(BMULT_round_correct t eh th Fch).
  eapply Rle_trans; [apply Hround_uT with (C := 5) | nra].
  - rewrite Rabs_mult. fold T. nra.
  - nra. }
have Hcl1u := Fast2Mult_acc.Fast2Mult_accuracy_norm eh th Fch.
have Hulp := ulp_le_relative_plus_emin (t:=t) (FT2R eh * FT2R th).
fold u eta in Hulp.
have Hcl1 : Rabs (FT2R cl1) <= u*T.
{ have Hprod : Rabs (FT2R eh * FT2R th) <= 5*u*T.
  { rewrite Rabs_mult; fold T; nra. }
  have Hu5 : 5*u*u <= /2*u by nra.
  have HTnonneg : 0 <= T by lra.
  have Hu5T : (5*u*u)*T <= (/2*u)*T.
  { apply Rmult_le_compat_r; assumption. }
  have Huprod : u * Rabs (FT2R eh * FT2R th) <= u * (5*u*T).
  { apply Rmult_le_compat_l; [lra | exact Hprod]. }
  eapply Rle_trans; [exact Hcl1u |].
  eapply Rle_trans with
      (r2 := u * Rabs (FT2R eh * FT2R th) + /2*eta).
  - nra.
  - eapply Rle_trans with (r2 := /2*(u*T) + /2*(u*T)).
    + apply Rplus_le_compat.
      * eapply Rle_trans; [exact Huprod |]. nra.
      * apply Rmult_le_compat_l; [lra | exact HetaT].
    + nra. }
have Hcl3 : Rabs (FT2R cl3) <= 15*u*T.
{ unfold cl3. rewrite -(BFMA_round_correct t el th cl1 Fcl3).
  eapply Rle_trans; [apply Hround_uT with (C := 13) | nra].
  have Htri := Rabs_triang (FT2R el * FT2R th) (FT2R cl1).
  - rewrite Rabs_mult in Htri; fold T in Htri; nra.
  - nra. }
have Fdh_sum : is_finite (BPLUS ch cl3) = true.
{ change (is_finite (BPLUS ch cl3) = true) in Fdh. exact Fdh. }
have Hdh : Rabs (FT2R dh) <= 23*u*T.
{ unfold dh, d, DWTimesFP3, Fast2Sum, fst, Fast2Mult_mul, Fast2Mult.
  fold ch cl1 cl3. rewrite -(BPLUS_round_correct t ch cl3 Fdh_sum).
  eapply Rle_trans; [apply Hround_uT with (C := 21) | nra].
  - have Htri := Rabs_triang (FT2R ch) (FT2R cl3); nra.
  - nra. }
set dz := BMINUS dh ch.
have Fdz : is_finite dz = true.
{ move: Fdl. unfold dl, d, DWTimesFP3, Fast2Sum, snd,
    Fast2Mult_mul, Fast2Mult. fold ch cl1 cl3 dh.
  set z0 := BMINUS dh ch. move => H.
  have Hz := proj2 (BMINUS_finite_e t cl3 z0 H). fold dz; exact Hz. }
have Hdz : Rabs (FT2R dz) <= 32*u*T.
{ unfold dz. rewrite -(BMINUS_round_correct t dh ch Fdz).
  eapply Rle_trans; [apply Hround_uT with (C := 29) | nra].
  have Htri := Rabs_triang (FT2R dh) (-FT2R ch).
  replace (FT2R dh + -FT2R ch)%R with (FT2R dh - FT2R ch)%R in Htri by ring.
  - rewrite Rabs_Ropp in Htri; nra.
  - nra. }
have Hdl : Rabs (FT2R dl) <= 51*u*T.
{ unfold dl, d, DWTimesFP3, Fast2Sum, snd, Fast2Mult_mul, Fast2Mult.
  fold ch cl1 cl3 dh dz. rewrite -(BMINUS_round_correct t cl3 dz Fdl).
  eapply Rle_trans; [apply Hround_uT with (C := 47) | nra].
  have Htri := Rabs_triang (FT2R cl3) (-FT2R dz).
  replace (FT2R cl3 + -FT2R dz)%R with (FT2R cl3 - FT2R dz)%R in Htri by ring.
  - rewrite Rabs_Ropp in Htri; nra.
  - nra. }
have Fts := DWPlusFP_acc_helpers.FIN1 dh dl th (conj Fmh Fml).
fold ts in Fts.
have Fsh : is_finite sh = true by exact (proj1 Fts).
have Fsl : is_finite sl = true by exact (proj2 Fts).
have Harg : Rabs (FT2R dh + FT2R th) <= (1 + 23*u)*T.
{ eapply Rle_trans; [apply Rabs_triang |]. fold T; nra. }
have Hsh : Rabs (FT2R sh) <= (1 + 28*u)*T.
{ unfold sh, ts, TwoSumF, fst.
  rewrite -(BPLUS_round_correct t dh th Fsh).
  eapply Rle_trans; [apply round_abs_le_relative_plus_half_emin |].
  have Hfac0 : 0 <= 1 + u by nra.
  have Hmul : (1+u)*Rabs (FT2R dh + FT2R th)
      <= (1+u)*((1+23*u)*T).
  { apply Rmult_le_compat_l; assumption. }
  have Hscalar : (1+u)*(1+23*u) + /2*u <= 1+28*u by nra.
  have HTnonneg : 0 <= T by lra.
  have HscalarT : ((1+u)*(1+23*u) + /2*u)*T <= (1+28*u)*T.
  { apply Rmult_le_compat_r; assumption. }
  have Hetahalf : /2*eta <= /2*(u*T).
  { apply Rmult_le_compat_l; [lra | exact HetaT]. }
  eapply Rle_trans with
      (r2 := (1+u)*((1+23*u)*T) + /2*(u*T)).
  - apply Rplus_le_compat; assumption.
  - eapply Rle_trans; [| exact HscalarT].
    right; ring. }
have Hsherr := round_FLT_error_rel_emin (t:=t) (FT2R dh + FT2R th).
fold u eta in Hsherr.
have Hsherr' : Rabs (FT2R sh - (FT2R dh + FT2R th)) <= 3*u*T.
{ unfold sh, ts, TwoSumF, fst.
  rewrite -(BPLUS_round_correct t dh th Fsh).
  have Huarg : u*Rabs (FT2R dh + FT2R th)
      <= u*((1+23*u)*T).
  { apply Rmult_le_compat_l; [lra | exact Harg]. }
  have Hu23 : 23*u*u <= /2*u by nra.
  have HTnonneg : 0 <= T by lra.
  have Hu23T : (23*u*u)*T <= (/2*u)*T.
  { apply Rmult_le_compat_r; assumption. }
  have Hetahalf : /2*eta <= /2*(u*T).
  { apply Rmult_le_compat_l; [lra | exact HetaT]. }
  have Huarg2 : u*Rabs (FT2R dh + FT2R th) <= /2*3*u*T.
  { eapply Rle_trans; [exact Huarg |].
    have Hscalar2 : u*(1+23*u) <= /2*3*u by nra.
    have Hscalar2T : (u*(1+23*u))*T <= (/2*3*u)*T.
    { apply Rmult_le_compat_r; assumption. }
    eapply Rle_trans; [| exact Hscalar2T]. right; ring. }
  eapply Rle_trans; [exact Hsherr |].
  eapply Rle_trans with (r2 := /2*3*u*T + /2*(u*T)).
  - apply Rplus_le_compat; assumption.
  - nra. }
have Hsh_lo : (1 - 26*u)*T <= Rabs (FT2R sh).
{ have Hrev := Rabs_triang_inv (FT2R th) (FT2R sh).
  have Htri_d := Rabs_triang (FT2R sh - (FT2R dh + FT2R th)) (FT2R dh).
  have Heq : (FT2R sh - (FT2R dh + FT2R th) + FT2R dh)%R =
      FT2R sh - FT2R th by ring.
  rewrite Heq in Htri_d.
  rewrite (Rabs_minus_sym (FT2R th) (FT2R sh)) in Hrev.
  fold T in Hrev. nra. }
have Hslu := TwoSum_acc.TwoSum_accuracy dh th Fts.
have Hulparg := ulp_le_relative_plus_emin (t:=t) (FT2R dh + FT2R th).
fold u eta in Hulparg.
have Hsl : Rabs (FT2R sl) <= 3*u*T.
{ have Huarg : u*Rabs (FT2R dh + FT2R th) <= u*((1+23*u)*T).
  { apply Rmult_le_compat_l; [lra | exact Harg]. }
  have Hscalar : u*(1+23*u) <= /2*3*u by nra.
  have HTnonneg : 0 <= T by lra.
  have HscalarT : (u*(1+23*u))*T <= (/2*3*u)*T.
  { apply Rmult_le_compat_r; assumption. }
  have Huarg2 : u*Rabs (FT2R dh + FT2R th) <= /2*3*u*T.
  { eapply Rle_trans; [exact Huarg |].
    eapply Rle_trans; [| exact HscalarT]. right; ring. }
  have Hetahalf : /2*eta <= /2*(u*T).
  { apply Rmult_le_compat_l; [lra | exact HetaT]. }
  eapply Rle_trans; [exact Hslu |].
  eapply Rle_trans with
      (r2 := u*Rabs (FT2R dh + FT2R th) + /2*eta).
  - nra.
  - eapply Rle_trans with (r2 := /2*3*u*T + /2*(u*T)).
    + apply Rplus_le_compat; assumption.
    + nra. }
have Fv := DWPlusFP_acc_helpers.FIN2 dh dl th (conj Fmh Fml); fold sl v in Fv.
have Hv : Rabs (FT2R v) <= 58*u*T.
{ unfold v. rewrite -(BPLUS_round_correct t dl sl Fv).
  eapply Rle_trans; [apply Hround_uT with (C := 54) | nra].
  - have Htri := Rabs_triang (FT2R dl) (FT2R sl); nra.
  - nra. }
have Hord : Rabs (FT2R v) <= Rabs (FT2R sh).
{ eapply Rle_trans; [exact Hv |].
  eapply Rle_trans; [| exact Hsh_lo]. nra. }
have Fmh_sum : is_finite (BPLUS sh v) = true.
{ unfold mh, m, Fast2Sum, fst in Fmh. exact Fmh. }
have Hsv : Rabs (FT2R sh + FT2R v) <= (1 + 86*u)*T.
{ eapply Rle_trans; [apply Rabs_triang |]. nra. }
have Hmh : Rabs (FT2R mh) <= (1 + 89*u)*T.
{ unfold mh, m, Fast2Sum, fst.
  rewrite -(BPLUS_round_correct t sh v Fmh_sum).
  eapply Rle_trans; [apply round_abs_le_relative_plus_half_emin |].
  have Hfac0 : 0 <= 1+u by nra.
  have Hmul : (1+u)*Rabs (FT2R sh + FT2R v)
      <= (1+u)*((1+86*u)*T).
  { apply Rmult_le_compat_l; assumption. }
  have Hscalar : (1+u)*(1+86*u) + /2*u <= 1+89*u by nra.
  have HTnonneg : 0 <= T by lra.
  have HscalarT : ((1+u)*(1+86*u) + /2*u)*T <= (1+89*u)*T.
  { apply Rmult_le_compat_r; assumption. }
  have Hetahalf : /2*eta <= /2*(u*T).
  { apply Rmult_le_compat_l; [lra | exact HetaT]. }
  eapply Rle_trans with
      (r2 := (1+u)*((1+86*u)*T) + /2*(u*T)).
  - apply Rplus_le_compat; assumption.
  - eapply Rle_trans; [| exact HscalarT]. right; ring. }
have Hmlu := FastTwoSum_accuracy sh v Fmh_sum Hord.
have Hulpm := ulp_le_relative_plus_emin (t:=t) (FT2R sh + FT2R v).
fold u eta in Hulpm.
have Hml : Rabs (FT2R ml) <= 2*u*T.
{ eapply Rle_trans; [exact Hmlu |].
  have Huarg : u*Rabs (FT2R sh + FT2R v) <= u*((1+86*u)*T).
  { apply Rmult_le_compat_l; [lra | exact Hsv]. }
  have Hscalar : u*(1+86*u) <= /2*3*u by nra.
  have HTnonneg : 0 <= T by lra.
  have HscalarT : (u*(1+86*u))*T <= (/2*3*u)*T.
  { apply Rmult_le_compat_r; assumption. }
  have Huarg2 : u*Rabs (FT2R sh + FT2R v) <= /2*3*u*T.
  { eapply Rle_trans; [exact Huarg |].
    eapply Rle_trans; [| exact HscalarT]. right; ring. }
  have Hetahalf : /2*eta <= /2*(u*T).
  { apply Rmult_le_compat_l; [lra | exact HetaT]. }
  eapply Rle_trans with
      (r2 := u*Rabs (FT2R sh + FT2R v) + /2*eta).
  - nra.
  - eapply Rle_trans with (r2 := /2*3*u*T + /2*(u*T)).
    + apply Rplus_le_compat; assumption.
    + nra. }
have HDW : double_word mh ml.
{ exact (Fast2Sum_is_DW sh v Fmh_sum Hord). }
have Hsvlo : (1-84*u)*T <= Rabs (FT2R sh + FT2R v).
{ have Hrev := Rabs_triang_inv (FT2R sh) (- FT2R v).
  replace (FT2R sh - - FT2R v)%R with (FT2R sh + FT2R v)%R in Hrev by ring.
  rewrite Rabs_Ropp in Hrev; nra. }
have Hcorr := FastTwoSum_correct sh v Fmh_sum Hord.
fold m mh ml in Hcorr.
change (FT2R ml = FT2R sh + FT2R v - FT2R mh) in Hcorr.
have Hsum : FT2R mh + FT2R ml = FT2R sh + FT2R v by lra.
have Hmsum := Rabs_triang (FT2R mh) (FT2R ml).
rewrite Hsum in Hmsum.
have Hmhlo : (1-86*u)*T <= Rabs (FT2R mh) by nra.
repeat split; [exact Hmhlo | exact Hmh | exact Hml | exact HDW | exact Hord].
Qed.

Lemma DWDivDW_zprod_lower_from_cond (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let rh := BFMA (BOPP yh) th (Zconst t 1) in
  let rl := BOPP (BMULT yl th) in
  let e := Fast2Sum rh rl in
  let d := DWTimesFP3 (fst e) (snd e) th in
  let m := DWPlusFP (fst d) (snd d) th in
  /2 * Rabs (FT2R xh / FT2R yh)
    <= Rabs (FT2R xh * FT2R (fst m)).
Proof.
move => Hp14 COND.
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
set rl := BOPP (BMULT yl th).
set e := Fast2Sum rh rl.
set d := DWTimesFP3 (fst e) (snd e) th.
set m := DWPlusFP (fst d) (snd d) th.
set mh := fst m.
set u := bpow radix2 (- fprec t).
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /16384.
{ unfold u. have -> : (/16384:R) = bpow radix2 (-14) by (simpl; lra).
  apply bpow_le; lia. }
have Hrel := DWDivDW_reciprocal_relative_from_cond xh xl yh yl Hp14 COND.
fold th rh rl e d m in Hrel. destruct Hrel as [Hmhlo _].
fold mh u in Hmhlo.
have Hres := DWDivDW_th_yh_residual_from_cond xh xl yh yl COND.
fold th u in Hres.
have Hprodlo : 1-u <= Rabs (FT2R th) * Rabs (FT2R yh).
{ rewrite -Rabs_mult.
  have Hrev := Rabs_triang_inv 1 (FT2R th * FT2R yh).
  rewrite Rabs_R1 (Rabs_minus_sym 1 (FT2R th * FT2R yh)) in Hrev.
  lra. }
have Hyhne := DWDivDW_cond_yh_nonzero xh xl yh yl COND.
have HY : 0 < Rabs (FT2R yh) by apply Rabs_pos_lt; exact Hyhne.
have HmhY : /2 <= Rabs (FT2R mh) * Rabs (FT2R yh).
{ have H := Rmult_le_compat_r (Rabs (FT2R yh)) _ _
      (Rlt_le _ _ HY) Hmhlo.
  have Hcoef : /2 <= (1-86*u)*(1-u) by nra.
  eapply Rle_trans; [exact Hcoef |].
  eapply Rle_trans.
  - apply Rmult_le_compat_l; [nra | exact Hprodlo].
  - eapply Rle_trans; [| exact H]. right; ring. }
have Hscaled : /2 * Rabs (FT2R xh)
    <= Rabs (FT2R xh) * (Rabs (FT2R mh) * Rabs (FT2R yh)).
{ have := Rmult_le_compat_l (Rabs (FT2R xh)) _ _ (Rabs_pos _) HmhY.
  nra. }
apply (Rmult_le_reg_r (Rabs (FT2R yh))); [exact HY |].
rewrite Rabs_mult Rmult_assoc.
have Hratio : Rabs (FT2R xh / FT2R yh) * Rabs (FT2R yh)
                = Rabs (FT2R xh).
{ rewrite -Rabs_mult. f_equal. field; exact Hyhne. }
rewrite Rmult_assoc Hratio.
exact Hscaled.
Qed.

Lemma DWDivDW_eta_scales_from_cond_tight (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let u := bpow radix2 (- fprec t) in
  let eta := bpow radix2 (@common.emin t) in
  eta <= 4*u^2 /\ eta <= (201/100)*u^2*Rabs (FT2R th).
Proof.
move => Hp14 COND.
set th := BDIV (Zconst t 1) yh.
set u := bpow radix2 (- fprec t).
set eta := bpow radix2 (@common.emin t).
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /16384.
{ unfold u. have -> : (/16384:R) = bpow radix2 (-14) by (simpl; lra).
  apply bpow_le; lia. }
have Heta_u2 : eta <= 4*u^2.
{ replace (4*u^2) with (4*(u*u)) by nra.
  have H4 : (4:R) = bpow radix2 2 by reflexivity.
  unfold eta, u. rewrite H4.
  replace (bpow radix2 2 *
      (bpow radix2 (- fprec t) * bpow radix2 (- fprec t)))
    with (bpow radix2 (2 + - fprec t + - fprec t)).
  2: { rewrite bpow_plus bpow_plus; ring. }
  apply bpow_le.
  unfold common.emin, SpecFloat.emin.
  pose proof (fprec_lt_femax t); lia. }
have Hres := DWDivDW_th_yh_residual_from_cond xh xl yh yl COND.
fold th u in Hres.
have Hprodlo : 1-u <= Rabs (FT2R th) * Rabs (FT2R yh).
{ rewrite -Rabs_mult.
  have Hrev := Rabs_triang_inv 1 (FT2R th * FT2R yh).
  rewrite Rabs_R1 (Rabs_minus_sym 1 (FT2R th * FT2R yh)) in Hrev.
  lra. }
move: (COND) => [_ [_ [_ [_ [_ [_ [Hq _]]]]]]].
have Hyhne := DWDivDW_cond_yh_nonzero xh xl yh yl COND.
have HY : 0 < Rabs (FT2R yh) by apply Rabs_pos_lt; exact Hyhne.
have Hqeq : Rabs (1 / FT2R yh) * Rabs (FT2R yh) = 1.
{ rewrite -Rabs_mult. replace (1 / FT2R yh * FT2R yh)%R with 1 by (field; exact Hyhne).
  rewrite Rabs_R1; reflexivity. }
have Hthq : (1-u)*Rabs (1/FT2R yh) <= Rabs (FT2R th).
{ apply (Rmult_le_reg_r (Rabs (FT2R yh))); [exact HY |].
  rewrite Rmult_assoc Hqeq Rmult_1_r.
  eapply Rle_trans; [exact Hprodlo |]. right; ring. }
have Hthlo : (1-u)*bpow radix2 (@common.emin t + 2*fprec t-1)
    <= Rabs (FT2R th).
{ eapply Rle_trans; [| exact Hthq].
  apply Rmult_le_compat_l.
  - nra.
  - exact Hq. }
have Hcoef0 : 0 <= (201/100)*u^2 by
  (apply Rmult_le_pos; [lra | apply pow_le; lra]).
have Hmul := Rmult_le_compat_l ((201/100)*u^2) _ _ Hcoef0 Hthlo.
have Heq : eta = 2*u^2 *
    bpow radix2 (@common.emin t + 2*fprec t-1).
{ have He : u*u*bpow radix2 (@common.emin t + 2*fprec t-1) =
      bpow radix2 (@common.emin t-1).
  { unfold u. rewrite -!bpow_plus; f_equal; lia. }
  have Het : eta = 2*bpow radix2 (@common.emin t-1).
  { unfold eta. have H2 : (2:R) = bpow radix2 1 by reflexivity.
    rewrite H2 -bpow_plus; f_equal; lia. }
  rewrite Het.
  replace (2*u^2*bpow radix2 (@common.emin t+2*fprec t-1))
    with (2*(u*u*bpow radix2 (@common.emin t+2*fprec t-1))) by nra.
  rewrite He; reflexivity. }
have Hcoef : 2 <= (201/100)*(1-u) by nra.
have Hbase := bpow_ge_0 radix2 (@common.emin t+2*fprec t-1).
split; [exact Heta_u2 |].
rewrite Heq.
eapply Rle_trans; [| exact Hmul].
have Hu2 := pow2_ge_0 u.
replace ((201/100)*u^2*((1-u)*bpow radix2 (@common.emin t+2*fprec t-1)))
  with (((201/100)*u^2*(1-u))*bpow radix2
    (@common.emin t+2*fprec t-1)) by ring.
apply Rmult_le_compat_r; [exact Hbase |].
nra.
Qed.

(** Compatibility form with the older factor [3]. *)
Lemma DWDivDW_eta_scales_from_cond (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let u := bpow radix2 (- fprec t) in
  let eta := bpow radix2 (@common.emin t) in
  eta <= 4*u^2 /\ eta <= 3*u^2*Rabs (FT2R th).
Proof.
move => Hp14 COND.
have H := DWDivDW_eta_scales_from_cond_tight xh xl yh yl Hp14 COND.
cbv zeta in H |- *. destruct H as [Hu Ht]. split; [exact Hu|].
have Hnonneg : 0 <= bpow radix2 (-fprec t)^2 *
    Rabs (FT2R (BDIV (Zconst t 1) yh)).
{ apply Rmult_le_pos; [apply pow_le; apply bpow_ge_0|apply Rabs_pos]. }
eapply Rle_trans; [exact Ht|]. nra.
Qed.

(** One absolute underflow ulp costs at most [2.01] [u^2] units on the
    exact quotient scale.  This is the conversion needed by the eventual
    FLT/FLX perturbation theorem; unlike [DWDivDW_eta_absorbed_by_zprod], it
    does not lose a factor through the reconstructed reciprocal product. *)
Lemma DWDivDW_eta_absorbed_by_quotient_tight (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  bpow radix2 (@common.emin t) <=
    (201/100) * bpow radix2 (- fprec t) ^ 2 *
      Rabs ((FT2R xh + FT2R xl) / (FT2R yh + FT2R yl)).
Proof.
move => Hp14 COND.
set u := bpow radix2 (- fprec t).
set eta := bpow radix2 (@common.emin t).
set X := FT2R xh + FT2R xl.
set Y := FT2R yh + FT2R yl.
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /16384.
{ unfold u. have -> : (/16384:R) = bpow radix2 (-14) by (simpl; lra).
  apply bpow_le; lia. }
move: (COND) => [_ [_ [_ [_ [DWx [DWy [_ [Hq _]]]]]]]].
have Hyhne : FT2R yh <> 0.
{ intro H0. move: Hq; rewrite H0 /Rdiv Rinv_0 Rmult_0_r Rabs_R0.
  have := bpow_gt_0 radix2
    (SpecFloat.emin (fprec t) (femax t) + 2 * fprec t - 1); lra. }
have Hxhne : FT2R xh <> 0.
{ intro H0. move: Hq; rewrite H0 /Rdiv Rmult_0_l Rabs_R0.
  have := bpow_gt_0 radix2
    (SpecFloat.emin (fprec t) (femax t) + 2 * fprec t - 1); lra. }
have Hxl := @DWMulFP_acc.aux_dwu_rel t STD xh xl DWx.
have Hyl := @DWMulFP_acc.aux_dwu_rel t STD yh yl DWy.
fold u in Hxl, Hyl.
have HXlo : (1-u)*Rabs (FT2R xh) <= Rabs X.
{ unfold X. have H := Rabs_triang_inv (FT2R xh) (-FT2R xl).
  rewrite Rabs_Ropp in H.
  replace (FT2R xh - -FT2R xl)%R with
    (FT2R xh + FT2R xl)%R in H by ring. nra. }
have HYup : Rabs Y <= (1+u)*Rabs (FT2R yh).
{ unfold Y. have H := Rabs_triang (FT2R yh) (FT2R yl). nra. }
have HYne : Y <> 0.
{ intro H0.
  have Hrev := Rabs_triang_inv (FT2R yh) (-FT2R yl).
  rewrite Rabs_Ropp in Hrev.
  replace (FT2R yh - -FT2R yl)%R with Y in Hrev by (unfold Y; ring).
  rewrite H0 Rabs_R0 in Hrev.
  have Hypos : 0 < Rabs (FT2R yh) by apply Rabs_pos_lt; exact Hyhne.
  nra. }
have HY0 : 0 < Rabs Y by apply Rabs_pos_lt; exact HYne.
have Hlead : Rabs (FT2R xh / FT2R yh) * Rabs (FT2R yh)
               = Rabs (FT2R xh).
{ rewrite -Rabs_mult. f_equal. field; exact Hyhne. }
have HQY : Rabs (X/Y) * Rabs Y = Rabs X.
{ rewrite -Rabs_mult. f_equal. field; exact HYne. }
have Hscale : (1-u)/(1+u) * Rabs (FT2R xh / FT2R yh)
                <= Rabs (X/Y).
{ apply (Rmult_le_reg_r (Rabs Y)); [exact HY0|].
  rewrite HQY.
  have Hfac0 : 0 <= (1-u)/(1+u) * Rabs (FT2R xh / FT2R yh)
  .
  { apply Rmult_le_pos; [|apply Rabs_pos].
    unfold Rdiv. apply Rmult_le_pos; [nra|].
    apply Rlt_le, Rinv_0_lt_compat; nra. }
  have Hmul := Rmult_le_compat_l
    ((1-u)/(1+u) * Rabs (FT2R xh / FT2R yh)) _ _ Hfac0 HYup.
  eapply Rle_trans; [exact Hmul|].
  replace (((1-u)/(1+u) * Rabs (FT2R xh / FT2R yh)) *
      ((1+u)*Rabs (FT2R yh)))%R with
    ((1-u)*(Rabs (FT2R xh / FT2R yh)*Rabs (FT2R yh)))%R
      by (field; nra).
  rewrite Hlead. exact HXlo. }
have Hbase : (1-u)/(1+u) *
    bpow radix2 (@common.emin t + 2*fprec t-1) <= Rabs (X/Y).
{ eapply Rle_trans; [|exact Hscale].
  apply Rmult_le_compat_l; [|exact Hq].
  unfold Rdiv. apply Rmult_le_pos; [nra|].
  apply Rlt_le, Rinv_0_lt_compat; nra. }
have Heta : eta = 2*u^2 *
    bpow radix2 (@common.emin t + 2*fprec t-1).
{ have He : u*u*bpow radix2 (@common.emin t+2*fprec t-1) =
      bpow radix2 (@common.emin t-1).
  { unfold u. rewrite -!bpow_plus; f_equal; lia. }
  have Het : eta = 2*bpow radix2 (@common.emin t-1).
  { unfold eta. have H2 : (2:R) = bpow radix2 1 by reflexivity.
    rewrite H2 -bpow_plus; f_equal; lia. }
  rewrite Het. replace (2*u^2*bpow radix2
    (@common.emin t+2*fprec t-1)) with
    (2*(u*u*bpow radix2 (@common.emin t+2*fprec t-1))) by nra.
  rewrite He; reflexivity. }
have Hmul := Rmult_le_compat_l ((201/100)*u^2) _ _ ltac:(nra) Hbase.
rewrite Heta. eapply Rle_trans; [|exact Hmul].
have Hb := bpow_ge_0 radix2 (@common.emin t+2*fprec t-1).
replace (2*u^2*bpow radix2 (@common.emin t+2*fprec t-1)) with
  ((2*u^2)*bpow radix2 (@common.emin t+2*fprec t-1)) by ring.
replace ((201/100)*u^2*((1-u)/(1+u)*
  bpow radix2 (@common.emin t+2*fprec t-1))) with
  (((201/100)*u^2*((1-u)/(1+u)))*
  bpow radix2 (@common.emin t+2*fprec t-1)) by ring.
apply Rmult_le_compat_r; [exact Hb|].
have Hcoef : 2 <= (201/100)*(1-u)/(1+u).
{ apply (Rmult_le_reg_r (1+u)); [nra|].
  have Heq : ((201/100)*(1-u)/(1+u))*(1+u) = (201/100)*(1-u)
    by (field; nra).
  rewrite Heq; nra. }
nra.
Qed.

Lemma DWDivDW_residual_value_error_floor (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let rh := BFMA (BOPP yh) th (Zconst t 1) in
  let rl := BOPP (BMULT yl th) in
  let e := Fast2Sum rh rl in
  Rabs ((FT2R (fst e) + FT2R (snd e)) -
    (1 - (FT2R yh + FT2R yl)*FT2R th))
      <= 8*bpow radix2 (-fprec t)^2 +
         2*bpow radix2 (@common.emin t) /\
  Rabs (FT2R (fst e)) <= 6*bpow radix2 (-fprec t) /\
  Rabs (FT2R (snd e)) <= 16*bpow radix2 (-fprec t)^2.
Proof.
move => Hp14 COND.
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
set ql := BMULT yl th.
set rl := BOPP ql.
set e := Fast2Sum rh rl.
set eh := fst e; set el := snd e.
set u := bpow radix2 (-fprec t).
set eta := bpow radix2 (@common.emin t).
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /16384.
{ unfold u. have -> : (/16384:R)=bpow radix2 (-14) by (simpl;lra).
  apply bpow_le; lia. }
have Hsc := DWDivDW_eta_scales_from_cond xh xl yh yl Hp14 COND.
fold th u eta in Hsc. destruct Hsc as [Heta _].
have Fth := DWDivDW_th_finite_from_cond xh xl yh yl COND; fold th in Fth.
have Frh := DWDivDW_rh_finite_from_cond xh xl yh yl ltac:(lia) COND;
  fold th rh in Frh.
have Fql := DWDivDW_yl_th_finite_from_cond xh xl yh yl ltac:(lia) COND;
  fold th ql in Fql.
have Frl := DWDivDW_rl_finite_from_cond xh xl yh yl ltac:(lia) COND;
  fold th ql rl in Frl.
have Fe := DWDivDW_fast2sum_finite_from_cond xh xl yh yl Hp14 COND.
fold th rh rl e in Fe. destruct Fe as [Feh Fel].
fold eh in Feh; fold el in Fel.
have Hres := DWDivDW_th_yh_residual_from_cond xh xl yh yl COND.
fold th u in Hres.
have Hylth := DWDivDW_yl_th_abs_from_cond xh xl yh yl COND.
fold th u in Hylth.
have Hres' : Rabs (1-FT2R yh*FT2R th) <= u.
{ rewrite (Rabs_minus_sym 1 (FT2R yh*FT2R th)).
  replace (FT2R yh*FT2R th-1)%R with (FT2R th*FT2R yh-1)%R by ring.
  exact Hres. }
have Hopp_yh : (-FT2R yh=FT2R (BOPP yh))%R.
{ move: (COND)=>[_ [_ [Fyh _]]]. exact (@BOPP_binary t NANS STD yh (or_intror Fyh)). }
have Hone : FT2R (Zconst t 1)=1%R.
{ rewrite /Zconst FT2R_ftype_of_float.
  have Hpow : (0 < 2^fprec t)%Z by (apply Z.pow_pos_nonneg; pose proof (fprec_lb t); lia).
  have Hrange : (-2^fprec t <= 1 <= 2^fprec t)%Z by lia.
  rewrite (proj1 (IEEE754_extra.BofZ_exact (fprec t) (femax t) _ _ 1 Hrange)); reflexivity. }
have Hrhr : FT2R rh = round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
    (1-FT2R yh*FT2R th).
{ unfold rh. rewrite -(BFMA_round_correct t (BOPP yh) th (Zconst t 1) Frh).
  rewrite -Hopp_yh Hone. f_equal; ring. }
have Herh : Rabs (FT2R rh-(1-FT2R yh*FT2R th)) <= u^2+/2*eta.
{ rewrite Hrhr. eapply Rle_trans; [apply round_FLT_error_rel_emin |].
  have Huabs : u*Rabs (1-FT2R yh*FT2R th) <= u^2.
  { eapply Rle_trans.
    - apply Rmult_le_compat_l; [lra | exact Hres'].
    - nra. }
  apply Rplus_le_compat; [exact Huabs|apply Rle_refl]. }
have Hrh : Rabs (FT2R rh) <= 2*u.
{ have Ha := Rabs_triang (FT2R rh-(1-FT2R yh*FT2R th))
    (1-FT2R yh*FT2R th).
  replace (FT2R rh-(1-FT2R yh*FT2R th)+(1-FT2R yh*FT2R th))%R
    with (FT2R rh) in Ha by ring.
  nra. }
have Hqlr : FT2R ql = round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
    (FT2R yl*FT2R th).
{ unfold ql. symmetry; apply BMULT_round_correct; exact Fql. }
have Heql : Rabs (FT2R ql-FT2R yl*FT2R th) <= 2*u^2+/2*eta.
{ rewrite Hqlr. eapply Rle_trans; [apply round_FLT_error_rel_emin |].
  have Harg : Rabs (FT2R yl*FT2R th) <= 2*u by nra.
  have Huarg : u*Rabs (FT2R yl*FT2R th) <= 2*u^2.
  { eapply Rle_trans.
    - apply Rmult_le_compat_l; [lra | exact Harg].
    - nra. }
  apply Rplus_le_compat; [exact Huarg|apply Rle_refl]. }
have Hoppql : (-FT2R ql=FT2R rl)%R.
{ exact (@BOPP_binary t NANS STD ql (or_introl Frl)). }
have Herl : Rabs (FT2R rl + FT2R yl*FT2R th) <= 2*u^2+/2*eta.
{ rewrite -Hoppql. replace (-FT2R ql+FT2R yl*FT2R th)%R
    with (-(FT2R ql-FT2R yl*FT2R th))%R by ring.
  rewrite Rabs_Ropp; exact Heql. }
have Hrl : Rabs (FT2R rl) <= 3*u.
{ have Ha := Rabs_triang (FT2R rl+FT2R yl*FT2R th)
    (-FT2R yl*FT2R th).
  replace (FT2R rl+FT2R yl*FT2R th+-FT2R yl*FT2R th)%R
    with (FT2R rl) in Ha by ring.
  have Hoppabs : Rabs (-FT2R yl*FT2R th)=Rabs(FT2R yl*FT2R th).
  { replace (-FT2R yl*FT2R th)%R with (-(FT2R yl*FT2R th))%R by ring.
    rewrite Rabs_Ropp; reflexivity. }
  rewrite Hoppabs in Ha; nra. }
set z := BMINUS eh rh.
have Fz : is_finite z=true.
{ move: Fel. unfold el,e,Fast2Sum,snd. fold eh. move=>H.
  exact (proj2 (BMINUS_finite_e t rl (BMINUS eh rh) H)). }
have Hehr : FT2R eh=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
    (FT2R rh+FT2R rl).
{ unfold eh,e,Fast2Sum,fst. symmetry; apply BPLUS_round_correct; exact Feh. }
have Hehs : Rabs (FT2R eh-(FT2R rh+FT2R rl)) <= 5*u^2+/2*eta.
{ rewrite Hehr. eapply Rle_trans; [apply round_FLT_error_rel_emin |].
  have Ha:=Rabs_triang (FT2R rh) (FT2R rl).
  have Harg : Rabs (FT2R rh+FT2R rl)<=5*u by nra.
  have Huarg : u*Rabs (FT2R rh+FT2R rl) <= 5*u^2.
  { eapply Rle_trans.
    - apply Rmult_le_compat_l; [lra | exact Harg].
    - nra. }
  apply Rplus_le_compat; [exact Huarg|apply Rle_refl]. }
have Heh : Rabs (FT2R eh)<=6*u.
{ have Ha:=Rabs_triang (FT2R eh-(FT2R rh+FT2R rl)) (FT2R rh+FT2R rl).
  replace (FT2R eh-(FT2R rh+FT2R rl)+(FT2R rh+FT2R rl))%R
    with (FT2R eh) in Ha by ring.
  have Hb:=Rabs_triang (FT2R rh) (FT2R rl). nra. }
have Hzr : FT2R z=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
    (FT2R eh-FT2R rh).
{ unfold z. symmetry; apply BMINUS_round_correct; exact Fz. }
have Hza : Rabs (FT2R eh-FT2R rh)<=4*u.
{ have Heq:FT2R eh-FT2R rh=
    (FT2R eh-(FT2R rh+FT2R rl))+FT2R rl by ring.
  rewrite Heq;eapply Rle_trans;[apply Rabs_triang|];nra. }
have Hez : Rabs (FT2R z-(FT2R eh-FT2R rh))<=4*u^2+/2*eta.
{ rewrite Hzr. eapply Rle_trans; [apply round_FLT_error_rel_emin |].
  have Huarg : u*Rabs (FT2R eh-FT2R rh)<=4*u^2.
  { eapply Rle_trans.
    - apply Rmult_le_compat_l; [lra|exact Hza].
    - nra. }
  apply Rplus_le_compat; [exact Huarg|apply Rle_refl]. }
have Hz : Rabs (FT2R z)<=5*u.
{ have Ha:=Rabs_triang (FT2R z-(FT2R eh-FT2R rh)) (FT2R eh-FT2R rh).
  replace (FT2R z-(FT2R eh-FT2R rh)+(FT2R eh-FT2R rh))%R
    with (FT2R z) in Ha by ring. nra. }
have Helr : FT2R el=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
    (FT2R rl-FT2R z).
{ unfold el,e,Fast2Sum,snd. fold eh z.
  symmetry; apply BMINUS_round_correct; exact Fel. }
have Hela : Rabs (FT2R rl-FT2R z)<=13*u^2.
{ have Heq:FT2R rl-FT2R z=
    -(FT2R eh-(FT2R rh+FT2R rl))+
    -(FT2R z-(FT2R eh-FT2R rh)) by ring.
  rewrite Heq;eapply Rle_trans;[apply Rabs_triang|].
  rewrite !Rabs_Ropp;nra. }
have Heel : Rabs (FT2R el-(FT2R rl-FT2R z))<=13*u^3+/2*eta.
{ rewrite Helr. eapply Rle_trans; [apply round_FLT_error_rel_emin |].
  have Huarg:u*Rabs(FT2R rl-FT2R z)<=13*u^3.
  { eapply Rle_trans.
    - apply Rmult_le_compat_l; [lra|exact Hela].
    - ring_simplify;lra. }
  apply Rplus_le_compat; [exact Huarg|apply Rle_refl]. }
have Hel : Rabs (FT2R el)<=16*u^2.
{ have Ha:=Rabs_triang (FT2R el-(FT2R rl-FT2R z)) (FT2R rl-FT2R z).
  replace (FT2R el-(FT2R rl-FT2R z)+(FT2R rl-FT2R z))%R
    with (FT2R el) in Ha by ring. nra. }
have Hfserr : Rabs ((FT2R eh+FT2R el)-(FT2R rh+FT2R rl))
    <=4*u^2+13*u^3+eta.
{ have Heq:(FT2R eh+FT2R el)-(FT2R rh+FT2R rl)=
    (FT2R el-(FT2R rl-FT2R z))-(FT2R z-(FT2R eh-FT2R rh)) by ring.
  rewrite Heq. have Ha:=Rabs_triang
    (FT2R el-(FT2R rl-FT2R z)) (-(FT2R z-(FT2R eh-FT2R rh))).
  replace ((FT2R el-(FT2R rl-FT2R z))+-(FT2R z-(FT2R eh-FT2R rh)))%R
    with ((FT2R el-(FT2R rl-FT2R z))-(FT2R z-(FT2R eh-FT2R rh)))%R
    in Ha by ring. rewrite Rabs_Ropp in Ha; nra. }
have Htotal : Rabs ((FT2R eh+FT2R el)-
    (1-(FT2R yh+FT2R yl)*FT2R th))<=8*u^2+2*eta.
{ have Heq:(FT2R eh+FT2R el)-(1-(FT2R yh+FT2R yl)*FT2R th)=
    ((FT2R eh+FT2R el)-(FT2R rh+FT2R rl))+
    (FT2R rh-(1-FT2R yh*FT2R th))+
    (FT2R rl+FT2R yl*FT2R th) by ring.
  rewrite Heq.
  have Ha:=Rabs_triang
    (((FT2R eh+FT2R el)-(FT2R rh+FT2R rl))+
      (FT2R rh-(1-FT2R yh*FT2R th)))
    (FT2R rl+FT2R yl*FT2R th).
  have Hb:=Rabs_triang ((FT2R eh+FT2R el)-(FT2R rh+FT2R rl))
    (FT2R rh-(1-FT2R yh*FT2R th)). nra. }
repeat split; [exact Htotal|exact Heh|exact Hel].
Qed.

(** Compatibility form obtained by absorbing the two explicit residual-floor
    terms.  New denormal proofs should use
    [DWDivDW_residual_value_error_floor] instead. *)
Lemma DWDivDW_residual_value_error (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let rh := BFMA (BOPP yh) th (Zconst t 1) in
  let rl := BOPP (BMULT yl th) in
  let e := Fast2Sum rh rl in
  Rabs ((FT2R (fst e) + FT2R (snd e)) -
    (1 - (FT2R yh + FT2R yl)*FT2R th))
      <= 16*bpow radix2 (-fprec t)^2 /\
  Rabs (FT2R (fst e)) <= 6*bpow radix2 (-fprec t) /\
  Rabs (FT2R (snd e)) <= 16*bpow radix2 (-fprec t)^2.
Proof.
move => Hp14 COND.
cbv zeta.
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
set rl := BOPP (BMULT yl th).
set e := Fast2Sum rh rl.
set u := bpow radix2 (-fprec t).
set eta := bpow radix2 (@common.emin t).
have Hfloor := DWDivDW_residual_value_error_floor
  xh xl yh yl Hp14 COND.
fold th rh rl e u eta in Hfloor.
destruct Hfloor as [Hvalue [Heh Hel]].
change (Rabs ((FT2R (fst e)+FT2R (snd e))-
  (1-(FT2R yh+FT2R yl)*FT2R th)) <= 8*u^2+2*eta) in Hvalue.
change (Rabs (FT2R (fst e)) <= 6*u) in Heh.
change (Rabs (FT2R (snd e)) <= 16*u^2) in Hel.
have Hsc := DWDivDW_eta_scales_from_cond xh xl yh yl Hp14 COND.
fold th u eta in Hsc. destruct Hsc as [Heta _].
change (Rabs ((FT2R (fst e)+FT2R (snd e))-
  (1-(FT2R yh+FT2R yl)*FT2R th)) <= 16*u^2 /\
  Rabs (FT2R (fst e)) <= 6*u /\
  Rabs (FT2R (snd e)) <= 16*u^2).
split.
- nra.
- split; [exact Heh|exact Hel].
Qed.

(** Two-arm compensated refinement-product estimate.  When the closing
    Fast2Sum is ordered, its sum is exact and the refinement costs one floor
    ulp.  Otherwise the general two-floor bound holds and the Newton residual
    is itself second order. *)
Lemma DWDivDW_refinement_product_value_error_tight_floor
    (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let rh := BFMA (BOPP yh) th (Zconst t 1) in
  let rl := BOPP (BMULT yl th) in
  let e := Fast2Sum rh rl in
  let d := DWTimesFP3 (fst e) (snd e) th in
  let Y := FT2R yh+FT2R yl in
  Rabs ((FT2R (fst d)+FT2R (snd d))-
        (FT2R (fst e)+FT2R (snd e))*FT2R th)
        <= 36*bpow radix2 (-fprec t)^3*Rabs (FT2R th) +
           1*bpow radix2 (@common.emin t)
  \/ (Rabs ((FT2R (fst d)+FT2R (snd d))-
        (FT2R (fst e)+FT2R (snd e))*FT2R th)
        <= 140*bpow radix2 (-fprec t)^3*Rabs (FT2R th) +
           2*bpow radix2 (@common.emin t)
      /\ Rabs (1-Y*FT2R th) <= 72*bpow radix2 (-fprec t)^2).
Proof.
move => Hp14 COND.
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
set rl := BOPP (BMULT yl th).
set e := Fast2Sum rh rl; set eh := fst e; set el := snd e.
set d := DWTimesFP3 eh el th; set dh := fst d; set dl := snd d.
set u := bpow radix2 (-fprec t); set eta := bpow radix2 (@common.emin t).
set T := Rabs (FT2R th).
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /16384.
{ unfold u. have -> : (/16384:R)=bpow radix2 (-14) by (simpl;lra).
  apply bpow_le; lia. }
have HT0 : 0 < T.
{ have Htb := DWDivDW_th_relative_bounds_from_cond
    xh xl yh yl ltac:(lia) COND.
  fold th u eta in Htb. fold T in Htb. exact (proj1 Htb). }
have HTn : 0 <= T by exact (Rlt_le _ _ HT0).
have Heta0 : 0 < eta by apply bpow_gt_0.
have Hsc := DWDivDW_eta_scales_from_cond xh xl yh yl Hp14 COND.
fold th u eta in Hsc. destruct Hsc as [_ HetaT]. fold T in HetaT.
have Hr := DWDivDW_residual_value_error xh xl yh yl Hp14 COND.
fold th rh rl e u in Hr. destruct Hr as [_ [Heh Hel]].
fold eh in Heh; fold el in Hel.
have Fd := DWDivDW_timesfp_cascade_from_cond xh xl yh yl Hp14 COND.
fold th e d in Fd. destruct Fd as [[Fdh Fdl] _].
fold eh el dh dl in Fdh, Fdl.
set ch := BMULT eh th; set cl1 := Fast2Mult_err eh th.
set cl3 := BFMA el th cl1; set z := BMINUS dh ch.
have Fch := DWMulFP_acc.FIN3 eh el th (conj Fdh Fdl); fold ch in Fch.
have Ffast := DWMulFP_acc.FIN1 eh el th (conj Fdh Fdl).
have Fcl1 : is_finite cl1=true by exact (proj2 Ffast).
have Fcl3 := DWMulFP_acc.FIN2 eh el th (conj Fdh Fdl);
  fold cl1 cl3 in Fcl3.
have Fz : is_finite z=true.
{ move: Fdl. unfold dl,d,DWTimesFP3,Fast2Sum,snd,
    Fast2Mult_mul,Fast2Mult. fold ch cl1 cl3 dh.
  move => H. exact (proj2 (BMINUS_finite_e t cl3 z H)). }
have Herr (v : R) :
  Rabs (round radix2 (SpecFloat.fexp (fprec t) (femax t))
    (Znearest choice) v-v) <= u*Rabs v+/2*eta.
{ have H := round_FLT_error_rel_emin (t:=t) v.
  fold u eta in H. exact H. }
have Hchr : FT2R ch=round radix2
    (SpecFloat.fexp(fprec t)(femax t)) (Znearest choice)
    (FT2R eh*FT2R th).
{ unfold ch; symmetry; apply BMULT_round_correct; exact Fch. }
have Hech : Rabs (FT2R ch-FT2R eh*FT2R th)
    <= 6*u^2*T+/2*eta.
{ rewrite Hchr. eapply Rle_trans; [apply Herr|].
  rewrite Rabs_mult. fold T.
  have HehT := Rmult_le_compat_r T _ _ (Rlt_le _ _ HT0) Heh.
  apply Rplus_le_compat_r.
  replace (6*u^2*T)%R with (u*(6*u*T))%R by ring.
  apply Rmult_le_compat_l; [exact (Rlt_le _ _ Hu0)|exact HehT]. }
have Hoppch : (-FT2R ch=FT2R(BOPP ch))%R.
{ exact (@BOPP_binary t NANS STD ch (or_intror Fch)). }
have Hcl1r : FT2R cl1=round radix2
    (SpecFloat.fexp(fprec t)(femax t)) (Znearest choice)
    (FT2R eh*FT2R th-FT2R ch).
{ unfold cl1,Fast2Mult_err,Fast2Mult,snd.
  rewrite -(BFMA_round_correct t eh th (BOPP(BMULT eh th)) Fcl1).
  fold ch; rewrite -Hoppch; f_equal; ring. }
have He1 : Rabs (FT2R cl1-(FT2R eh*FT2R th-FT2R ch))
    <= 8*u^3*T+/2*eta.
{ rewrite Hcl1r. eapply Rle_trans; [apply Herr|].
  rewrite Rabs_minus_sym.
  have Hmul := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Hech.
  have Hueta := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) HetaT.
  nra. }
have Hcl1 : Rabs (FT2R cl1) <= 12*u^2*T.
{ have Ha := Rabs_triang
    (FT2R cl1-(FT2R eh*FT2R th-FT2R ch))
    (FT2R eh*FT2R th-FT2R ch).
  replace (FT2R cl1-(FT2R eh*FT2R th-FT2R ch)+
    (FT2R eh*FT2R th-FT2R ch))%R with(FT2R cl1)in Ha by ring.
  rewrite Rabs_minus_sym in Hech. nra. }
have Hcl3r : FT2R cl3=round radix2
    (SpecFloat.fexp(fprec t)(femax t)) (Znearest choice)
    (FT2R el*FT2R th+FT2R cl1).
{ unfold cl3; symmetry; apply BFMA_round_correct; exact Fcl3. }
have Harg3 : Rabs (FT2R el*FT2R th+FT2R cl1) <= 28*u^2*T.
{ eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rabs_mult. fold T.
  have Helt := Rmult_le_compat_r T _ _ (Rlt_le _ _ HT0) Hel.
  replace (28*u^2*T)%R with (16*u^2*T+12*u^2*T)%R by ring.
  apply Rplus_le_compat.
  - eapply Rle_trans; [exact Helt|]. right; ring.
  - exact Hcl1. }
have He3 : Rabs (FT2R cl3-(FT2R el*FT2R th+FT2R cl1))
    <= 28*u^3*T+/2*eta.
{ rewrite Hcl3r. eapply Rle_trans; [apply Herr|].
  have Hmul := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Harg3.
  nra. }
have Hcl3 : Rabs (FT2R cl3) <= 32*u^2*T.
{ have Ha := Rabs_triang
    (FT2R cl3-(FT2R el*FT2R th+FT2R cl1))
    (FT2R el*FT2R th+FT2R cl1).
  replace (FT2R cl3-(FT2R el*FT2R th+FT2R cl1)+
    (FT2R el*FT2R th+FT2R cl1))%R with(FT2R cl3)in Ha by ring.
  nra. }
have Hcore : Rabs ((FT2R ch+FT2R cl3)-
    (FT2R eh+FT2R el)*FT2R th) <= 36*u^3*T+eta.
{ have Heq : (FT2R ch+FT2R cl3)-
      (FT2R eh+FT2R el)*FT2R th =
    (FT2R cl1-(FT2R eh*FT2R th-FT2R ch))+
    (FT2R cl3-(FT2R el*FT2R th+FT2R cl1)) by ring.
  rewrite Heq. eapply Rle_trans; [apply Rabs_triang|]. nra. }
have Hdhr : FT2R dh=round radix2
    (SpecFloat.fexp(fprec t)(femax t)) (Znearest choice)
    (FT2R ch+FT2R cl3).
{ unfold dh,d,DWTimesFP3,Fast2Sum,fst,Fast2Mult_mul,Fast2Mult.
  fold ch cl1 cl3; symmetry; apply BPLUS_round_correct; exact Fdh. }
have Hch : Rabs (FT2R ch) <= 7*u*T.
{ have Ha := Rabs_triang (FT2R ch-FT2R eh*FT2R th)
      (FT2R eh*FT2R th).
  replace (FT2R ch-FT2R eh*FT2R th+FT2R eh*FT2R th)%R
    with(FT2R ch)in Ha by ring.
  rewrite Rabs_mult in Ha. fold T in Ha.
  have HehT := Rmult_le_compat_r T _ _ (Rlt_le _ _ HT0) Heh.
  have Hsmall : 6*u^2*T+/2*eta <= u*T by nra.
  eapply Rle_trans; [exact Ha|].
  eapply Rle_trans.
  - apply Rplus_le_compat; [exact Hech|exact HehT].
  - lra. }
have Hsumarg : Rabs (FT2R ch+FT2R cl3) <= 8*u*T.
{ eapply Rle_trans; [apply Rabs_triang|]. nra. }
have Hes : Rabs (FT2R dh-(FT2R ch+FT2R cl3))
    <= 8*u^2*T+/2*eta.
{ rewrite Hdhr. eapply Rle_trans; [apply Herr|].
  have Hmul := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Hsumarg.
  nra. }
have Hza : Rabs (FT2R dh-FT2R ch) <= 42*u^2*T.
{ have Heq : FT2R dh-FT2R ch =
    (FT2R dh-(FT2R ch+FT2R cl3))+FT2R cl3 by ring.
  rewrite Heq. eapply Rle_trans; [apply Rabs_triang|]. nra. }
have Hzr : FT2R z=round radix2
    (SpecFloat.fexp(fprec t)(femax t)) (Znearest choice)
    (FT2R dh-FT2R ch).
{ unfold z; symmetry; apply BMINUS_round_correct; exact Fz. }
have Hez : Rabs (FT2R z-(FT2R dh-FT2R ch))
    <= 42*u^3*T+/2*eta.
{ rewrite Hzr. eapply Rle_trans; [apply Herr|].
  have Hmul := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Hza.
  nra. }
have Hdlarg : Rabs (FT2R cl3-FT2R z) <= 51*u^2*T+eta.
{ have Heq : FT2R cl3-FT2R z =
    -(FT2R dh-(FT2R ch+FT2R cl3))-
    (FT2R z-(FT2R dh-FT2R ch)) by ring.
  rewrite Heq. eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rabs_Ropp.
  have Hthird : 42*u^3*T <= u^2*T by nra.
  eapply Rle_trans.
  - apply Rplus_le_compat; [exact Hes|].
    rewrite Rabs_Ropp; exact Hez.
  - nra. }
have Hdlr : FT2R dl=round radix2
    (SpecFloat.fexp(fprec t)(femax t)) (Znearest choice)
    (FT2R cl3-FT2R z).
{ unfold dl,d,DWTimesFP3,Fast2Sum,snd,Fast2Mult_mul,Fast2Mult.
  fold ch cl1 cl3 dh z; symmetry; apply BMINUS_round_correct; exact Fdl. }
have Hedl : Rabs (FT2R dl-(FT2R cl3-FT2R z))
    <= 55*u^3*T+/2*eta.
{ rewrite Hdlr. eapply Rle_trans; [apply Herr|].
  have Hmul := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Hdlarg.
  have Hueta := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) HetaT.
  nra. }
have Hsum : Rabs ((FT2R dh+FT2R dl)-(FT2R ch+FT2R cl3))
    <= 97*u^3*T+eta.
{ have Heq : (FT2R dh+FT2R dl)-(FT2R ch+FT2R cl3) =
    (FT2R dl-(FT2R cl3-FT2R z))-
    (FT2R z-(FT2R dh-FT2R ch)) by ring.
  rewrite Heq. eapply Rle_trans.
  - have H := Rabs_triang
      (FT2R dl-(FT2R cl3-FT2R z))
      (-(FT2R z-(FT2R dh-FT2R ch))).
    rewrite Rabs_Ropp in H. exact H.
  - nra. }
have Heq : (FT2R dh+FT2R dl)-
    (FT2R eh+FT2R el)*FT2R th =
  ((FT2R dh+FT2R dl)-(FT2R ch+FT2R cl3))+
  ((FT2R ch+FT2R cl3)-(FT2R eh+FT2R el)*FT2R th) by ring.
have Hunc : Rabs ((FT2R dh+FT2R dl)-
    (FT2R eh+FT2R el)*FT2R th) <= 140*u^3*T+2*eta.
{ rewrite Heq. eapply Rle_trans; [apply Rabs_triang|].
  (* The displayed constants leave ample room at p >= 14. *)
  nra. }
change (Rabs ((FT2R dh+FT2R dl)-
        (FT2R eh+FT2R el)*FT2R th) <= 36*u^3*T+1*eta
  \/ (Rabs ((FT2R dh+FT2R dl)-
        (FT2R eh+FT2R el)*FT2R th) <= 140*u^3*T+2*eta
      /\ Rabs (1-(FT2R yh+FT2R yl)*FT2R th) <= 72*u^2)).
(* ---- the two refinement arms ----------------------------------------
   Ordered: Algorithm 9's closing Fast2Sum is exact
   ([DWTimesFP3_sum_exact_of_ord]), so [dh+dl = ch+cl3] and the bound is
   [Hcore] itself -- one floor ulp instead of two.

   Unordered: [|cl3| > |ch|] can only happen when [eh] is tiny.  With
   [|ch| >= |eh|*T - (6u^2 T + eta/2)] and [|cl3| <= 32u^2 T] that forces
   [|eh| < 39.5u^2], hence [|eh+el| <= 55.5u^2], hence the exact Newton
   residual [1-Y*th] is itself of order [u^2] -- which makes the Newton
   remainder fourth order in that arm (see
   [flx_newton_step_error_of_residual]). *)
destruct (Rle_dec (Rabs (FT2R cl3)) (Rabs (FT2R ch))) as [Hord|Hnord].
- left.
  have Hex := DWTimesFP3_sum_exact_of_ord eh el th (conj Fdh Fdl) Hord.
  change (FT2R dh+FT2R dl=FT2R ch+FT2R cl3) in Hex.
  rewrite Hex. eapply Rle_trans; [exact Hcore|lra].
- right. split; [exact Hunc|].
  have Hnord' : Rabs (FT2R ch) < Rabs (FT2R cl3) by (apply Rnot_le_lt; exact Hnord).
  have Hlo : Rabs (FT2R eh)*T-Rabs (FT2R ch-FT2R eh*FT2R th)
      <= Rabs (FT2R ch).
  { have H := Rabs_triang_inv (FT2R eh*FT2R th)
      (FT2R eh*FT2R th-FT2R ch).
    replace (FT2R eh*FT2R th-(FT2R eh*FT2R th-FT2R ch))%R
      with (FT2R ch) in H by ring.
    rewrite Rabs_mult in H. fold T in H.
    rewrite (Rabs_minus_sym (FT2R eh*FT2R th) (FT2R ch)) in H.
    exact H. }
  have Hech' : Rabs (FT2R ch-FT2R eh*FT2R th) <= 6*u^2*T+/2*eta
    by exact Hech.
  have HehT : Rabs (FT2R eh)*T < 395/10*u^2*T by nra.
  have Hehsmall : Rabs (FT2R eh) < 395/10*u^2.
  { apply (Rmult_lt_reg_r T); [exact HT0|].
    eapply Rlt_le_trans; [exact HehT|]. right; ring. }
  (* [Heh]/[Hel] arrive stated on the unfolded [Fast2Sum] terms, so restate
     them on the local abbreviations before handing them to [lra]. *)
  have Hel' : Rabs (FT2R el) <= 16*u^2 by exact Hel.
  have HE : Rabs (FT2R eh+FT2R el) <= 555/10*u^2.
  { eapply Rle_trans; [apply Rabs_triang|]. lra. }
  have Hres0 := proj1 (DWDivDW_residual_value_error
    xh xl yh yl Hp14 COND).
  cbv zeta in Hres0.
  have Hres : Rabs ((FT2R eh+FT2R el)-
      (1-(FT2R yh+FT2R yl)*FT2R th)) <= 16*u^2
    by exact Hres0.
  have Htri := Rabs_triang
    ((FT2R eh+FT2R el)-(1-(FT2R yh+FT2R yl)*FT2R th))
    (-(FT2R eh+FT2R el)).
  replace ((FT2R eh+FT2R el)-(1-(FT2R yh+FT2R yl)*FT2R th)+
    -(FT2R eh+FT2R el))%R with
    (-(1-(FT2R yh+FT2R yl)*FT2R th))%R in Htri by ring.
  rewrite Rabs_Ropp Rabs_Ropp in Htri.
  nra.
Qed.

Lemma DWDivDW_final_cond_from_cond_normal (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let rh := BFMA (BOPP yh) th (Zconst t 1) in
  let rl := BOPP (BMULT yl th) in
  let e := Fast2Sum rh rl in
  let d := DWTimesFP3 (fst e) (snd e) th in
  let m := DWPlusFP (fst d) (snd d) th in
  bpow radix2 (@common.emin t + 2 * fprec t - 1)
    <= Rabs (FT2R xh * FT2R (fst m)) ->
  DWTimesDW_cond xh xl (fst m) (snd m).
Proof.
move => Hp14 COND /= UFprod.
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
set rl := BOPP (BMULT yl th).
set e := Fast2Sum rh rl.
set d := DWTimesFP3 (fst e) (snd e) th.
set m := DWPlusFP (fst d) (snd d) th.
fold th rh rl e d m in UFprod.
move: (COND) =>
  [Fxh [Fxl [Fyh [Fyl [DWx [DWy [Hqlo [Hxqlo [Hylo
    [Hxhi [Hyhi Hratiohi]]]]]]]]]]].
have Hmc := DWDivDW_plusfp_cascade_from_cond xh xl yh yl Hp14 COND.
fold th rh rl e d m in Hmc.
destruct Hmc as [[Fmh Fml] _].
have Hrel := DWDivDW_reciprocal_relative_from_cond xh xl yh yl Hp14 COND.
fold th rh rl e d m in Hrel.
destruct Hrel as [_ [Hmh [Hml [DWm _]]]].
set u := bpow radix2 (- fprec t).
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /16384.
{ unfold u. have -> : (/16384:R) = bpow radix2 (-14) by (simpl; lra).
  apply bpow_le; lia. }
have Htb := DWDivDW_th_relative_bounds_from_cond xh xl yh yl ltac:(lia) COND.
fold th u in Htb. destruct Htb as [_ [HTup _]].
have Hyhne := DWDivDW_cond_yh_nonzero xh xl yh yl COND.
have Hratio : Rabs (FT2R xh) * Rabs (1 / FT2R yh)
                = Rabs (FT2R xh / FT2R yh).
{ rewrite -Rabs_mult. f_equal. field; exact Hyhne. }
have Hcoef : (1+89*u)*(1+u) <= 2 by nra.
have Hmhq : (1+89*u)*Rabs (FT2R th)
    <= (1+89*u)*((1+u)*Rabs (1 / FT2R yh)).
{ apply Rmult_le_compat_l; [nra | exact HTup]. }
have Hprod : Rabs (FT2R xh * FT2R (fst m))
                  <= bpow radix2 (femax t - 1).
{ rewrite Rabs_mult.
  eapply Rle_trans.
  - apply Rmult_le_compat_l; [apply Rabs_pos | exact Hmh].
  - eapply Rle_trans.
    + apply Rmult_le_compat_l; [apply Rabs_pos |].
      exact Hmhq.
    + replace (Rabs (FT2R xh) *
          ((1 + 89*u) * ((1 + u) * Rabs (1 / FT2R yh))))
        with ((1+89*u)*(1+u) *
          (Rabs (FT2R xh) * Rabs (1 / FT2R yh))) by ring.
      rewrite Hratio.
      eapply Rle_trans.
      * apply Rmult_le_compat_r; [apply Rabs_pos | exact Hcoef].
      * eapply Rle_trans; [apply Rmult_le_compat_l; [lra | exact Hratiohi] |].
        have Heq : 2 * bpow radix2 (femax t - 2)
                     = bpow radix2 (femax t - 1).
        { change (bpow radix2 1 * bpow radix2 (femax t - 2) =
                    bpow radix2 (femax t - 1)).
          rewrite -bpow_plus; f_equal; lia. }
        rewrite Heq; lra. }
have [Fprod _] := BMULT_finite_bpow_bound xh (fst m) (femax t - 1)
  Fxh Fmh ltac:(unfold SpecFloat.emin; pose proof (femax_lb t); lia)
  ltac:(lia) Hprod.
split; [exact Fxl |].
split; [exact Fml |].
split; [exact DWx |].
split; [exact DWm |].
split.
- split.
  + change (is_finite (BMULT xh (fst m)) = true); exact Fprod.
  + right. change (bpow radix2 (@common.emin t + 2 * fprec t - 1)
      <= Rabs (FT2R xh * FT2R (fst m))). exact UFprod.
- have Heq : /2 * bpow radix2 (femax t) = bpow radix2 (femax t - 1).
  { change (bpow radix2 (-1) * bpow radix2 (femax t) =
              bpow radix2 (femax t - 1)).
    rewrite -bpow_plus; f_equal; lia. }
  rewrite Heq; exact Hprod.
Qed.

(** In the complementary closing-product regime, all nodes of the final
    [DWTimesDW3] are absolutely small.  This supplies finiteness without the
    normal-product disjunct required by [DWTimesDW_cond]. *)
Lemma DWDivDW3_finite_from_cond_zprod_underflow (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let rh := BFMA (BOPP yh) th (Zconst t 1) in
  let rl := BOPP (BMULT yl th) in
  let e := Fast2Sum rh rl in
  let d := DWTimesFP3 (fst e) (snd e) th in
  let m := DWPlusFP (fst d) (snd d) th in
  Rabs (FT2R xh * FT2R (fst m)) <
    bpow radix2 (@common.emin t + 2 * fprec t - 1) ->
  is_finite_p (DWDivDW3 xh xl yh yl).
Proof.
move => Hp14 COND /= Hsmall.
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
set rl := BOPP (BMULT yl th).
set e := Fast2Sum rh rl.
set d := DWTimesFP3 (fst e) (snd e) th.
set m := DWPlusFP (fst d) (snd d) th.
set mh := fst m; set ml := snd m.
move: (COND) => [Fxh [Fxl [_ [_ [DWx [_ _]]]]]].
have Hmc := DWDivDW_plusfp_cascade_from_cond xh xl yh yl Hp14 COND.
fold th rh rl e d m in Hmc. destruct Hmc as [[Fmh Fml] _].
fold mh in Fmh; fold ml in Fml.
have Hrel := DWDivDW_reciprocal_relative_from_cond xh xl yh yl Hp14 COND.
fold th rh rl e d m in Hrel. destruct Hrel as [_ [_ [_ [DWm _]]]].
fold mh ml in DWm.
fold th rh rl e d m mh in Hsmall.
change (Rabs (FT2R xh * FT2R mh) <
  bpow radix2 (@common.emin t + 2 * fprec t - 1)) in Hsmall.
set u := bpow radix2 (- fprec t).
set eta := bpow radix2 (@common.emin t).
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu1 : u <= 1.
{ unfold u. have -> : (1:R) = bpow radix2 0 by reflexivity.
  apply bpow_le; lia. }
have Heta1 : eta <= 1.
{ unfold eta. have -> : (1:R) = bpow radix2 0 by reflexivity.
  apply bpow_le. unfold common.emin, SpecFloat.emin.
  pose proof (femax_lb t); pose proof (fprec_lb t); lia. }
have Hthreshold :
    bpow radix2 (@common.emin t + 2 * fprec t - 1) <= 2.
{ have -> : (2:R) = bpow radix2 1 by reflexivity.
  apply bpow_le. unfold common.emin, SpecFloat.emin.
  pose proof (fprec_lt_femax t); lia. }
have HP : Rabs (FT2R xh * FT2R mh) <= 2 by lra.
have Hxl := @DWMulFP_acc.aux_dwu_rel t STD xh xl DWx.
have Hmlr := @DWMulFP_acc.aux_dwu_rel t STD mh ml DWm.
fold u in Hxl, Hmlr.
have HPabs : Rabs (FT2R xh) * Rabs (FT2R mh) <= 2.
{ rewrite -Rabs_mult; exact HP. }
have HuP : u * (Rabs (FT2R xh) * Rabs (FT2R mh)) <= 2.
{ eapply Rle_trans.
  - apply Rmult_le_compat_l; [lra | exact HPabs].
  - nra. }
have Hxhml : Rabs (FT2R xh * FT2R ml) <= 2.
{ rewrite Rabs_mult.
  have H := Rmult_le_compat_l (Rabs (FT2R xh)) _ _
      (Rabs_pos _) Hmlr.
  eapply Rle_trans; [exact H |].
  eapply Rle_trans; [| exact HuP]. right; ring. }
have Hxlmh : Rabs (FT2R xl * FT2R mh) <= 2.
{ rewrite Rabs_mult.
  have H := Rmult_le_compat_r (Rabs (FT2R mh)) _ _
      (Rabs_pos _) Hxl.
  eapply Rle_trans; [exact H |].
  eapply Rle_trans; [| exact HuP]. right; ring. }
have Hxlml : Rabs (FT2R xl * FT2R ml) <= 2.
{ rewrite Rabs_mult.
  have H : Rabs (FT2R xl) * Rabs (FT2R ml) <=
      (u*Rabs (FT2R xh))*(u*Rabs (FT2R mh)).
  { apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hxl | exact Hmlr]. }
  eapply Rle_trans; [exact H |].
  have Huu : u*u <= 1 by nra.
  eapply Rle_trans with
    (r2 := (u*u)*(Rabs (FT2R xh)*Rabs (FT2R mh))).
  - right; ring.
  - eapply Rle_trans.
    + apply Rmult_le_compat_l; [nra | exact HPabs].
    + nra. }
set ch := BMULT xh mh.
have [Fch Hch] := BMULT_finite_bpow_bound xh mh 1 Fxh Fmh
  ltac:(unfold SpecFloat.emin; pose proof (femax_lb t); pose proof (fprec_lb t); lia)
  ltac:(pose proof (fprec_lt_femax t); lia)
  ltac:(change (Rabs (FT2R xh * FT2R mh) <= 2); exact HP).
fold ch in Fch, Hch.
change (Rabs (FT2R ch) <= 2) in Hch.
set cl1 := Fast2Mult_err xh mh.
have Ffast := Fast2Mult_acc_helpers.Fast2Mult_finite_unconditional xh mh Fch.
have Fcl1 : is_finite cl1 = true by exact (proj2 Ffast).
have Hcl1u := Fast2Mult_acc.Fast2Mult_accuracy_norm xh mh Fch.
fold cl1 in Hcl1u.
have Hulp := ulp_le_relative_plus_emin (t:=t) (FT2R xh * FT2R mh).
fold u eta in Hulp.
have Hcl1 : Rabs (FT2R cl1) <= 4 by nra.
set tl0 := BMULT xl ml.
have [Ftl0 Htl0] := BMULT_finite_bpow_bound xl ml 1 Fxl Fml
  ltac:(unfold SpecFloat.emin; pose proof (femax_lb t); pose proof (fprec_lb t); lia)
  ltac:(pose proof (fprec_lt_femax t); lia)
  ltac:(change (Rabs (FT2R xl * FT2R ml) <= 2); exact Hxlml).
fold tl0 in Ftl0, Htl0.
change (Rabs (FT2R tl0) <= 2) in Htl0.
set tl1 := BFMA xh ml tl0.
have Harg1 : Rabs (FT2R xh * FT2R ml + FT2R tl0) <= 4
  by (eapply Rle_trans; [apply Rabs_triang |]; nra).
have [Ftl1 Htl1] := BFMA_finite_bpow_bound xh ml tl0 2
  Fxh Fml Ftl0
  ltac:(unfold SpecFloat.emin; pose proof (femax_lb t); pose proof (fprec_lb t); lia)
  ltac:(pose proof (fprec_lt_femax t); lia)
  ltac:(change (Rabs (FT2R xh * FT2R ml + FT2R tl0) <= 4); exact Harg1).
fold tl1 in Ftl1, Htl1.
change (Rabs (FT2R tl1) <= 4) in Htl1.
set cl2 := BFMA xl mh tl1.
have Harg2 : Rabs (FT2R xl * FT2R mh + FT2R tl1) <= 8
  by (eapply Rle_trans; [apply Rabs_triang |]; nra).
have [Fcl2 Hcl2] := BFMA_finite_bpow_bound xl mh tl1 3
  Fxl Fmh Ftl1
  ltac:(unfold SpecFloat.emin; pose proof (femax_lb t); pose proof (fprec_lb t); lia)
  ltac:(pose proof (fprec_lt_femax t); lia)
  ltac:(change (Rabs (FT2R xl * FT2R mh + FT2R tl1) <= 8); exact Harg2).
fold cl2 in Fcl2, Hcl2.
change (Rabs (FT2R cl2) <= 8) in Hcl2.
set cl3 := BPLUS cl1 cl2.
have Harg3 : Rabs (FT2R cl1 + FT2R cl2) <= 16
  by (eapply Rle_trans; [apply Rabs_triang |]; nra).
have [Fcl3 Hcl3] := BPLUS_finite_bpow_bound cl1 cl2 4
  Fcl1 Fcl2
  ltac:(unfold SpecFloat.emin; pose proof (femax_lb t); pose proof (fprec_lb t); lia)
  ltac:(pose proof (fprec_lt_femax t); lia)
  ltac:(change (Rabs (FT2R cl1 + FT2R cl2) <= 16); exact Harg3).
fold cl3 in Fcl3, Hcl3.
change (Rabs (FT2R cl3) <= 16) in Hcl3.
set zh := BPLUS ch cl3.
have Hargz : Rabs (FT2R ch + FT2R cl3) <= 32
  by (eapply Rle_trans; [apply Rabs_triang |]; nra).
have [Fzh Hzh] := BPLUS_finite_bpow_bound ch cl3 5
  Fch Fcl3
  ltac:(unfold SpecFloat.emin; pose proof (femax_lb t); pose proof (fprec_lb t); lia)
  ltac:(pose proof (fprec_lt_femax t); lia)
  ltac:(change (Rabs (FT2R ch + FT2R cl3) <= 32); exact Hargz).
fold zh in Fzh, Hzh.
change (Rabs (FT2R zh) <= 32) in Hzh.
set z0 := BMINUS zh ch.
have Harg0 : Rabs (FT2R zh - FT2R ch) <= 64.
{ have Htri := Rabs_triang (FT2R zh) (- FT2R ch).
  replace (FT2R zh + - FT2R ch)%R with (FT2R zh - FT2R ch)%R in Htri by ring.
  rewrite Rabs_Ropp in Htri; nra. }
have [Fz0 Hz0] := BMINUS_finite_bpow_bound zh ch 6
  Fzh Fch
  ltac:(unfold SpecFloat.emin; pose proof (femax_lb t); pose proof (fprec_lb t); lia)
  ltac:(pose proof (fprec_lt_femax t); lia)
  ltac:(change (Rabs (FT2R zh - FT2R ch) <= 64); exact Harg0).
fold z0 in Fz0, Hz0.
change (Rabs (FT2R z0) <= 64) in Hz0.
set zl := BMINUS cl3 z0.
have Hargl : Rabs (FT2R cl3 - FT2R z0) <= 128.
{ have Htri := Rabs_triang (FT2R cl3) (- FT2R z0).
  replace (FT2R cl3 + - FT2R z0)%R with (FT2R cl3 - FT2R z0)%R in Htri by ring.
  rewrite Rabs_Ropp in Htri; nra. }
have [Fzl Hzl] := BMINUS_finite_bpow_bound cl3 z0 7
  Fcl3 Fz0
  ltac:(unfold SpecFloat.emin; pose proof (femax_lb t); pose proof (fprec_lb t); lia)
  ltac:(pose proof (fprec_lt_femax t); lia)
  ltac:(change (Rabs (FT2R cl3 - FT2R z0) <= 128); exact Hargl).
fold zl in Fzl, Hzl.
change (Rabs (FT2R zl) <= 128) in Hzl.
change (is_finite zh = true /\ is_finite zl = true).
exact (conj Fzh Fzl).
Qed.

Lemma DWDivDW3_finite_from_cond (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  is_finite_p (DWDivDW3 xh xl yh yl).
Proof.
move => Hp14 COND.
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
set rl := BOPP (BMULT yl th).
set e := Fast2Sum rh rl.
set d := DWTimesFP3 (fst e) (snd e) th.
set m := DWPlusFP (fst d) (snd d) th.
destruct (Rle_or_lt
  (bpow radix2 (@common.emin t + 2 * fprec t - 1))
  (Rabs (FT2R xh * FT2R (fst m)))) as [Hnormal | Hsmall].
- have Hfinal := DWDivDW_final_cond_from_cond_normal xh xl yh yl
    Hp14 COND Hnormal.
  split.
  + exact (DWMulDW_acc.DWTimesDW3_fst_finite xh xl (fst m) (snd m)
      ltac:(lia) Hfinal).
  + exact (DWMulDW_acc.DWTimesDW3_snd_finite xh xl (fst m) (snd m)
      ltac:(lia) Hfinal).
- exact (DWDivDW3_finite_from_cond_zprod_underflow xh xl yh yl
    Hp14 COND Hsmall).
Qed.

Lemma DWDivDW_eta_absorbed_by_zprod (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let rh := BFMA (BOPP yh) th (Zconst t 1) in
  let rl := BOPP (BMULT yl th) in
  let e := Fast2Sum rh rl in
  let d := DWTimesFP3 (fst e) (snd e) th in
  let m := DWPlusFP (fst d) (snd d) th in
  bpow radix2 (@common.emin t) <=
    4 * bpow radix2 (- fprec t) ^ 2 *
      Rabs (FT2R xh * FT2R (fst m)).
Proof.
move => Hp14 COND /=.
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
set rl := BOPP (BMULT yl th).
set e := Fast2Sum rh rl.
set d := DWTimesFP3 (fst e) (snd e) th.
set m := DWPlusFP (fst d) (snd d) th.
have Hq : bpow radix2 (@common.emin t + 2 * fprec t - 1)
    <= Rabs (FT2R xh / FT2R yh).
{ move: (COND) => [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]. exact H. }
have Hz := DWDivDW_zprod_lower_from_cond xh xl yh yl Hp14 COND.
fold th rh rl e d m in Hz.
change (/2 * Rabs (FT2R xh / FT2R yh) <=
  Rabs (FT2R xh * FT2R (fst m))) in Hz.
have Hlow : /2 * bpow radix2 (@common.emin t + 2 * fprec t - 1)
    <= Rabs (FT2R xh * FT2R (fst m)) by nra.
have Hu20 : 0 <= 4 * bpow radix2 (- fprec t) ^ 2.
{ apply Rmult_le_pos; [lra | apply pow_le; apply bpow_ge_0]. }
have Hmul := Rmult_le_compat_l
  (4 * bpow radix2 (- fprec t) ^ 2) _ _ Hu20 Hlow.
eapply Rle_trans; [| exact Hmul].
have He : bpow radix2 (- fprec t) * bpow radix2 (- fprec t) *
    bpow radix2 (@common.emin t + 2 * fprec t - 1) =
    bpow radix2 (@common.emin t - 1).
{ rewrite -!bpow_plus; f_equal; lia. }
have Heta : bpow radix2 (@common.emin t) =
    2 * bpow radix2 (@common.emin t - 1).
{ have H2 : (2:R) = bpow radix2 1 by reflexivity.
  rewrite H2 -bpow_plus; f_equal; lia. }
apply Req_le. rewrite Heta.
replace (4 * bpow radix2 (- fprec t) ^ 2 *
  (/2 * bpow radix2 (@common.emin t + 2 * fprec t - 1)))
  with (2 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t) *
    bpow radix2 (@common.emin t + 2 * fprec t - 1))) by nra.
rewrite He; reflexivity.
Qed.

End DWDivDWCondFacts.

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
Section PaperModelDWDivDW.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation rnd_p := (round radix2 (FLX_exp (fprec t)) (Znearest choice)).

(** Tight normalized bootstrap residual.  The reciprocal rounding contributes
    [(yh/2)u], while the double-word low part contributes [u/yh].  Their
    coefficients sum to at most [3/2] over [1,2], and the cross term is at
    most [u^2/2]. *)
Lemma flx_newton_residual_normalized (yh yl : R) :
  DWPlus.double_word (fprec t) choice yh yl ->
  1 <= yh <= 2-2*bpow radix2 (-fprec t) ->
  let th := rnd_p (/yh) in
  let Y := yh+yl in
  Rabs (Y*th-1) <=
    (3/2+bpow radix2 (-fprec t)/2)*bpow radix2 (-fprec t).
Proof.
move => DWy [Hy1 Hy2] /=.
set u := bpow radix2 (-fprec t).
set th := rnd_p (/yh).
set Y := yh+yl.
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu1 : u < 1.
{ unfold u. have -> : (1:R)=bpow radix2 0 by reflexivity.
  apply bpow_lt; pose proof (fprec_gt_one t); lia. }
have Hy0 : 0 < yh by lra.
have Hyne : yh<>0 by lra.
have Hyl : Rabs yl<=u.
{ apply (@DWTimesDW.double_lpart_u
    (fprec t) (fprec_gt_one t) choice yh yl DWy).
  split; [exact Hy1|].
  eapply Rle_lt_trans; [exact Hy2|]. fold u. nra. }
have Hinv : Rabs (/yh)<=1.
{ rewrite Rabs_pos_eq; [|apply Rlt_le, Rinv_0_lt_compat;exact Hy0].
  rewrite -Rinv_1. apply Rinv_le; lra. }
have Hth : Rabs (th-/yh)<=u/2.
{ unfold th, rnd_p.
  have H := @Bayleyaux.error_le_half_ulp'
    (fprec t) (fprec_gt_one t) choice (/yh) 0 Hinv.
  simpl in H. fold u in H.
  eapply Rle_trans; [exact H|].
  have HuE : /IZR (Z.pow_pos 2 (fprecp t))=u.
  { unfold u. rewrite bpow_opp. reflexivity. }
  rewrite HuE. lra. }
set a := (yh*(th-/yh))%R.
set s := (yl/yh)%R.
have Ha : Rabs a<=yh/2*u.
{ unfold a. rewrite Rabs_mult Rabs_pos_eq; [|lra].
  have H := Rmult_le_compat_l yh _ _ (Rlt_le _ _ Hy0) Hth.
  nra. }
have Hs : Rabs s<=u/yh.
{ unfold s, Rdiv. rewrite Rabs_mult Rabs_inv.
  rewrite (Rabs_pos_eq yh); [|lra].
  have H := Rmult_le_compat_r (/yh) _ _
    (Rlt_le _ _ (Rinv_0_lt_compat yh Hy0)) Hyl.
  nra. }
have Hfac : yh/2+1/yh<=3/2.
{ apply (Rmult_le_reg_r yh); [exact Hy0|].
  replace ((yh/2+1/yh)*yh)%R with (yh^2/2+1)%R
    by (field; exact Hyne).
  have Hy_le2 : yh <= 2.
  { eapply Rle_trans; [exact Hy2|]. fold u. nra. }
  nra. }
have Has : Rabs a+Rabs s<=3/2*u.
{ eapply Rle_trans; [apply Rplus_le_compat; [exact Ha|exact Hs]|].
  have H := Rmult_le_compat_r u _ _ (Rlt_le _ _ Hu0) Hfac.
  nra. }
have Hcross : Rabs (a*s)<=u^2/2.
{ rewrite Rabs_mult.
  have Hmul := Rmult_le_compat
    (Rabs a) (yh/2*u) (Rabs s) (u/yh)
    (Rabs_pos _) (Rabs_pos _) Ha Hs.
  eapply Rle_trans; [exact Hmul|].
  right. field; exact Hyne. }
have Heq : Y*th-1=a+s+a*s.
{ unfold Y,a,s. field; exact Hyne. }
rewrite Heq.
have Htri := Rabs_triang (a+s) (a*s).
have Htri2 := Rabs_triang a s.
eapply Rle_trans; [exact Htri|].
eapply Rle_trans.
- apply Rplus_le_compat; [exact Htri2|exact Hcross].
- eapply Rle_trans.
  + apply Rplus_le_compat; [exact Has|apply Rle_refl].
  + fold u. change (3/2*u+u^2/2 <= (3/2+u/2)*u)%R.
    right. field.
Qed.

(** Squaring the normalized residual recovers the Newton contribution used
    by the paper.  At the bridge's standing precision [p >= 14], the small
    [u/2] cross term fits below the paper constant [2.298]. *)
Lemma flx_newton_residual_normalized_sq (yh yl : R) :
  (14 <= fprec t)%Z ->
  DWPlus.double_word (fprec t) choice yh yl ->
  1 <= yh <= 2-2*bpow radix2 (-fprec t) ->
  let th := rnd_p (/yh) in
  let Y := yh+yl in
  Rabs (Y*th-1)^2 <=
    2298/1000*bpow radix2 (-fprec t)^2.
Proof.
move => Hp14 DWy Hy /=.
set u := bpow radix2 (-fprec t).
set th := rnd_p (/yh).
set Y := yh+yl.
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /16384.
{ unfold u. have -> : (/16384:R)=bpow radix2 (-14) by (simpl;lra).
  apply bpow_le; lia. }
have H := flx_newton_residual_normalized yh yl DWy Hy.
fold th Y u in H.
cbv zeta in H.
have HA0 : 0 <= Rabs (Y*th-1) by apply Rabs_pos.
have HC0 : 0 <= (3/2+u/2)*u by nra.
have Hsq : Rabs (Y*th-1)^2 <= ((3/2+u/2)*u)^2.
{ pose proof (pow2_ge_0 ((3/2+u/2)*u-Rabs (Y*th-1))). nra. }
eapply Rle_trans; [exact Hsq|].
have Hcoef : (3/2+u/2)^2 <= 2298/1000.
{ pose proof (pow2_ge_0 u). nra. }
have Hmul := Rmult_le_compat_r (u^2) _ _ (pow2_ge_0 u) Hcoef.
eapply Rle_trans; [|exact Hmul].
right. field.
Qed.

(** Scale- and sign-invariant form of the Newton bootstrap estimate.  The
    product [(yh+yl)*round(1/yh)] is unchanged by a power-of-two scaling of
    the divisor pair, so the normalized result applies to every nonzero
    double word. *)
Lemma flx_newton_residual_sq (yh yl : R) :
  (14 <= fprec t)%Z ->
  DWPlus.double_word (fprec t) choice yh yl -> yh <> 0 ->
  Rabs ((yh+yl)*rnd_p (/yh)-1)^2 <=
    2298/1000*bpow radix2 (-fprec t)^2.
Proof.
move => Hp14 DWy yhn0.
wlog ypos : yh yl DWy yhn0 / 0 < yh.
{ move => Hwlog.
  destruct (Rlt_le_dec 0 yh) as [Hy|Hy]; first by apply Hwlog.
  have Hny : 0 < -yh by lra.
  have DWny := @DWDivDW.DW_opp (fprec t) choice eq_refl yh yl DWy.
  have H := Hwlog (-yh) (-yl) DWny ltac:(lra) Hny.
  have Hinv : /(-yh) = -(/yh) by (field; exact yhn0).
  rewrite Hinv round_NE_opp in H.
  have Heq : ((-yh + -yl)*(-rnd_p (/yh))-1 =
      (yh+yl)*rnd_p (/yh)-1)%R by ring.
  rewrite Heq in H. exact H. }
destruct DWy as [[Fyh Fyl] Hyround].
destruct (DWPlus.scale_generic_12 (p:=fprec t) Fyh ypos)
  as [ey Hys].
have DWys : DWPlus.double_word (fprec t) choice
    (yh*bpow radix2 ey) (yl*bpow radix2 ey).
{ apply (@DWDivDW.dw_S (fprec t) (fprec_gt_one t) choice yh yl ey).
  split; [split; assumption|exact Hyround]. }
have Hys0 : yh*bpow radix2 ey<>0.
{ apply Rmult_integral_contrapositive_currified;
    [exact yhn0|apply Rgt_not_eq, bpow_gt_0]. }
have H := flx_newton_residual_normalized_sq
  (yh*bpow radix2 ey) (yl*bpow radix2 ey) Hp14 DWys Hys.
have Hinv : /(yh*bpow radix2 ey)=/yh*bpow radix2 (-ey).
{ apply (Rmult_eq_reg_r (bpow radix2 ey));
      [|apply Rgt_not_eq, bpow_gt_0].
  rewrite Rmult_assoc -bpow_plus.
  replace (-ey+ey)%Z with 0%Z by lia. simpl.
  field; split; [exact yhn0|apply Rgt_not_eq, bpow_gt_0]. }
rewrite Hinv Bayleyaux.round_bpow in H.
cbv zeta in H.
replace (((yh*bpow radix2 ey)+(yl*bpow radix2 ey))*
    (rnd_p (/yh)*bpow radix2 (-ey))-1)%R with
    ((yh+yl)*rnd_p (/yh)-1)%R in H.
- exact H.
- replace (((yh*bpow radix2 ey)+(yl*bpow radix2 ey))*
      (rnd_p (/yh)*bpow radix2 (-ey)))%R with
    ((yh+yl)*rnd_p (/yh)*
      (bpow radix2 ey*bpow radix2 (-ey)))%R by ring.
  rewrite -bpow_plus. replace (ey+-ey)%Z with 0%Z by lia.
  simpl; ring.
Qed.

Lemma flx_newton_step_error (yh yl : R) :
  (14 <= fprec t)%Z ->
  DWPlus.double_word (fprec t) choice yh yl -> yh <> 0 ->
  let th := rnd_p (/yh) in
  let Y := yh+yl in
  Rabs (th+(1-Y*th)*th-/Y) <=
    2298/1000*bpow radix2 (-fprec t)^2*Rabs (/Y).
Proof.
move => Hp14 DWy yhn0 /=.
set th := rnd_p (/yh).
set Y := yh+yl.
have HYne : Y<>0.
{ intro HY0. apply yhn0.
  move: DWy. rewrite /DWPlus.double_word -/Y HY0 round_0.
  by move => [[_ _] ->]. }
have Hsq := flx_newton_residual_sq yh yl Hp14 DWy yhn0.
fold th Y in Hsq.
have Heq : th+(1-Y*th)*th-/Y = -((Y*th-1)^2)*(/Y).
{ field; exact HYne. }
rewrite Heq Rabs_mult Rabs_Ropp.
have Habspow : Rabs ((Y*th-1)^2)=Rabs (Y*th-1)^2.
{ rewrite Rabs_pos_eq; [symmetry; apply pow2_abs|apply pow2_ge_0]. }
rewrite Habspow.
apply Rmult_le_compat_r; [apply Rabs_pos|exact Hsq].
Qed.

(** Residual-parameterized form of the Newton step.  The remainder is exactly
    [-(1-Y*th)^2/Y], so any bound on the residual transfers directly; the
    [2298/1000*u^2] of the previous lemma is just this with the generic
    [|1-Y*th| <= (3/2+u/2)*u].

    The unordered arm of the refinement split has [|1-Y*th|] of order [u^2]
    (the ordering of Algorithm 9's closing Fast2Sum can only fail when the
    residual is that small), which makes this contribution fourth order and
    removes the [2.298] term from that arm's ordinary budget.  No precision
    bound is needed -- this is pure algebra over the exact identity. *)
Lemma flx_newton_step_error_of_residual (yh yl r : R) :
  DWPlus.double_word (fprec t) choice yh yl -> yh <> 0 ->
  let th := rnd_p (/yh) in
  let Y := yh+yl in
  Rabs (1-Y*th) <= r ->
  Rabs (th+(1-Y*th)*th-/Y) <= r^2*Rabs (/Y).
Proof.
move => DWy yhn0 /=.
set th := rnd_p (/yh).
set Y := yh+yl.
move => Hr.
have HYne : Y<>0.
{ intro HY0. apply yhn0.
  move: DWy. rewrite /DWPlus.double_word -/Y HY0 round_0.
  by move => [[_ _] ->]. }
have Heq : th+(1-Y*th)*th-/Y = -((1-Y*th)^2)*(/Y).
{ field; exact HYne. }
rewrite Heq Rabs_mult Rabs_Ropp.
have Habspow : Rabs ((1-Y*th)^2)=Rabs (1-Y*th)^2.
{ rewrite Rabs_pos_eq; [symmetry; apply pow2_abs|apply pow2_ge_0]. }
rewrite Habspow.
apply Rmult_le_compat_r; [apply Rabs_pos|].
have H0 : 0 <= Rabs (1-Y*th) by apply Rabs_pos.
nra.
Qed.

(** A fixed-point representation of the leading operand is the precise
    structural premise needed by Fast2Sum when magnitude ordering is not
    available.  This is the form used by the paper for the reciprocal
    residual: [rh] lies on a [2*u^2] lattice even when [rl] is larger. *)
Lemma flx_f2s_sum_of_fix_left (a b : R) (e : Z) :
  generic_format radix2 (FLX_exp (fprec t)) a ->
  generic_format radix2 (FLX_exp (fprec t)) b ->
  generic_format radix2 (FIX_exp e) a ->
  (cexp radix2 (FLX_exp (fprec t)) b <= e)%Z ->
  let z := F2Sum.Fast2Sum (fprec t) choice a b in
  fst z + snd z = a + b.
Proof.
move => Fa Fb Fixa Hbe.
have Fixa' := FIX_format_generic radix2 e a Fixa.
destruct Fixa' as [fa Hfa Hexp].
have Hcorr := @F2SumFLX.F2Sum_correct_proof
  radix2 (fprec t) (fprec_gt_one t) choice.
specialize (Hcorr (fun x => round_NE_opp _ _ x) ltac:(simpl; lia)
  a b Fa Fb).
have Hrep : exists fa0 : float radix2,
    a = F2R fa0 /\
    (cexp radix2 (FLX_exp (fprec t)) b <= Fexp fa0)%Z.
{ exists fa. split; [exact Hfa|]. rewrite Hexp. exact Hbe. }
specialize (Hcorr Hrep).
unfold F2SumFLX.Fast2Sum_correct in Hcorr.
cbv zeta in Hcorr.
unfold F2Sum.Fast2Sum.
set z := F2SumFLX.Fast2Sum radix2 (fprec t) choice a b in Hcorr |- *.
destruct z as [s r].
change (r = a+b-s) in Hcorr.
change (s+r=a+b). lra.
Qed.

Lemma fix_format_lower (x : R) (e1 e2 : Z) :
  (e1<=e2)%Z ->
  generic_format radix2 (FIX_exp e2) x ->
  generic_format radix2 (FIX_exp e1) x.
Proof.
move => He Fx.
eapply (@generic_inclusion_mag radix2 (FIX_exp e2) (FIX_exp e1) x).
- move => _. unfold FIX_exp. exact He.
- exact Fx.
Qed.

(** The reciprocal residual is an integer multiple of [2*u^2], independently
    of the exponent of [y].  Scaling [y] into [1,2) also scales its reciprocal
    in the opposite direction, so their product—and hence the residual—is
    unchanged. *)
Lemma flx_reciprocal_residual_fix (y : R) :
  generic_format radix2 (FLX_exp (fprec t)) y -> y <> 0 ->
  generic_format radix2 (FIX_exp (1-2*fprec t))
    (1-y*rnd_p (/y)).
Proof.
move => Fy yn0.
wlog ypos : y Fy yn0 / 0 < y.
{ move => Hwlog.
  destruct (Rlt_le_dec 0 y) as [Hy|Hy]; first by apply Hwlog.
  have Hny : 0 < -y by lra.
  have Fny : generic_format radix2 (FLX_exp (fprec t)) (-y)
    by apply generic_format_opp.
  have H := Hwlog (-y) Fny ltac:(lra) Hny.
  have Hinv : /(-y) = -(/y) by (field; exact yn0).
  rewrite Hinv round_NE_opp in H.
  change (generic_format radix2 (FIX_exp (1-2*fprec t))
    (1-(-y)*(-rnd_p (/y)))) in H.
  replace (1- -y * -rnd_p (/y))%R with
    (1-y*rnd_p (/y))%R in H by ring.
  exact H. }
wlog Hy12 : y Fy yn0 ypos / 1 <= y <= 2-2*bpow radix2 (-fprec t).
{ move => Hwlog.
  destruct (DWPlus.scale_generic_12 (p:=fprec t) Fy ypos)
    as [ey Bys].
  have Fys := DWPlus.formatS (fprec_gt_one t) Fy ey.
  have Hys0 : y*bpow radix2 ey<>0.
  { apply Rmult_integral_contrapositive_currified;
      [exact yn0|apply Rgt_not_eq, bpow_gt_0]. }
  have Hysp : 0 < y*bpow radix2 ey.
  { apply Rmult_lt_0_compat; [exact ypos|apply bpow_gt_0]. }
  have H := Hwlog (y*bpow radix2 ey) Fys Hys0 Hysp Bys.
  have Hinv : /(y*bpow radix2 ey) = /y*bpow radix2 (-ey).
  { apply (Rmult_eq_reg_r (bpow radix2 ey));
      [|apply Rgt_not_eq, bpow_gt_0].
    rewrite Rmult_assoc -bpow_plus.
    replace (-ey+ey)%Z with 0%Z by lia. simpl.
    field; split; [exact yn0|apply Rgt_not_eq, bpow_gt_0]. }
  rewrite Hinv Bayleyaux.round_bpow in H.
  replace ((y*bpow radix2 ey)*(rnd_p (/y)*bpow radix2 (-ey)))%R
    with (y*rnd_p (/y))%R in H.
  - exact H.
  - replace ((y*bpow radix2 ey)*(rnd_p (/y)*bpow radix2 (-ey)))%R
      with (y*rnd_p (/y)*(bpow radix2 ey*bpow radix2 (-ey)))%R by ring.
    rewrite -bpow_plus. replace (ey+-ey)%Z with 0%Z by lia.
    simpl; ring. }
destruct Hy12 as [Hylo Hyhi].
set u := bpow radix2 (-fprec t).
set th := rnd_p (/y).
fold u in Hyhi.
have Hu0 : 0 < u by apply bpow_gt_0.
have Hhalf : /2 <= th.
{ have Hiy : /2 <= /y.
  { apply Rinv_le; [exact ypos|]. nra. }
  have Hr := round_le radix2 (FLX_exp (fprec t)) (Znearest choice)
    (/2) (/y) Hiy.
  have Hfmt : generic_format radix2 (FLX_exp (fprec t)) (/2).
  { change (generic_format radix2 (FLX_exp (fprec t))
      (bpow radix2 (-1))).
    apply generic_format_bpow. unfold FLX_exp.
    replace (-1+1-fprec t)%Z with (-fprec t)%Z by ring.
    exact (proj1 (Z.opp_le_mono 1 (fprec t))
      (Z.lt_le_incl _ _ (fprec_gt_one t))). }
  specialize (Hr ltac:(apply FLX_exp_valid; apply fprec_gt_0)
    ltac:(apply valid_rnd_N)).
  rewrite round_generic in Hr; [fold th in Hr; exact Hr|exact Hfmt]. }
have Hy1 : bpow radix2 0 <= Rabs y.
{ change (1<=Rabs y). rewrite Rabs_pos_eq; lra. }
have Hth1 : bpow radix2 (-1) <= Rabs th.
{ change (/2<=Rabs th). rewrite Rabs_pos_eq; lra. }
destruct (@DWTimesFP.ex_mul (fprec t) y 0 Hy1 Fy) as [my Hy].
have Fth : generic_format radix2 (FLX_exp (fprec t)) th.
{ unfold th, rnd_p. apply generic_format_round; typeclasses eauto. }
destruct (@DWTimesFP.ex_mul (fprec t) th (-1) Hth1 Fth) as [mt Hth].
fold u in Hy, Hth.
have Hy' : y=IZR my*(2*u).
{ rewrite Hy. simpl. ring. }
have Hth' : th=IZR mt*u.
{ rewrite Hth. have Hb : bpow radix2 (-1)=(/2)%R by reflexivity.
  rewrite Hb. field. }
pose fr := Float radix2 (2^(2*fprec t-1)-my*mt) (1-2*fprec t).
apply generic_format_FIX.
apply (FIX_spec radix2 (1-2*fprec t)
  (1-y*th) fr).
- unfold fr. rewrite /F2R /= Hy' Hth'.
  rewrite minus_IZR.
  have Hpos : (0<=2*fprec t-1)%Z.
  { pose proof (fprec_gt_one t); lia. }
  have Hzp := IZR_Zpower radix2 (2*fprec t-1) Hpos.
  rewrite Hzp.
  have Hscale : bpow radix2 (1-2*fprec t)=2*u^2.
  { replace (1-2*fprec t)%Z with
      (1+(-fprec t+-fprec t))%Z by ring.
    rewrite bpow_plus bpow_plus.
    change (bpow radix2 1 *
      (bpow radix2 (-fprec t)*bpow radix2 (-fprec t))=2*u^2).
    change (bpow radix2 1) with (2:R). unfold u. ring. }
  have Hunit : bpow radix2 (2*fprec t-1)*(2*u^2)=1.
  { rewrite -Hscale -bpow_plus.
    replace (2*fprec t-1+(1-2*fprec t))%Z with 0%Z by ring.
    reflexivity. }
  have HD0 : bpow radix2 (2*fprec t-1)<>0
    by apply Rgt_not_eq, bpow_gt_0.
  have HinvD : /bpow radix2 (2*fprec t-1)=2*u^2.
  { apply (Rmult_eq_reg_l (bpow radix2 (2*fprec t-1)));
    [|exact HD0].
    rewrite Rinv_r; [symmetry; exact Hunit|exact HD0]. }
  unfold Rdiv. rewrite HinvD mult_IZR Rmult_minus_distr_r Hunit.
  ring.
- reflexivity.
Qed.

(** Runtime residual Fast2Sum is exact once its leading residual is placed on
    the same [2*u^2] lattice used in the paper proof.  Notice that no
    magnitude ordering between [rh] and [rl] is assumed. *)
Lemma DWDivDW_residual_fast2sum_exact_from_fix
    (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let rh := BFMA (BOPP yh) th (Zconst t 1) in
  let rl := BOPP (BMULT yl th) in
  let e := Fast2Sum rh rl in
  generic_format radix2 (FIX_exp (1-2*fprec t)) (FT2R rh) ->
  FT2R (fst e)+FT2R (snd e)=FT2R rh+FT2R rl.
Proof.
move => Hp14 COND /=.
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
set rl := BOPP (BMULT yl th).
set e := Fast2Sum rh rl.
move => Frhfix.
have Fe := DWDivDW_fast2sum_finite_from_cond
  xh xl yh yl Hp14 COND.
specialize (Fe NANS STD).
fold th rh rl e in Fe.
destruct (Req_dec (FT2R rl) 0) as [Hrl0|Hrl0].
- have Hord : Rabs (FT2R rl)<=Rabs (FT2R rh).
  { rewrite Hrl0 Rabs_R0. apply Rabs_pos. }
  have Hsum := FastTwoSum_correct rh rl (proj1 Fe) Hord.
  change (FT2R (snd e)=FT2R rh+FT2R rl-FT2R (fst e)) in Hsum.
  change (FT2R (fst e)+FT2R (snd e)=FT2R rh+FT2R rl).
  rewrite Hsum. ring.
- have Frh : generic_format radix2 (FLX_exp (fprec t)) (FT2R rh).
  { apply (generic_format_FLX_FLT radix2
      (SpecFloat.emin (fprec t) (femax t)) (fprec t)).
    apply generic_format_FLT_FT2R. }
  have Frl : generic_format radix2 (FLX_exp (fprec t)) (FT2R rl).
  { apply (generic_format_FLX_FLT radix2
      (SpecFloat.emin (fprec t) (femax t)) (fprec t)).
    apply generic_format_FLT_FT2R. }
  have Hce := DWDivDW_rl_cexp_le xh xl yh yl Hp14 COND.
  specialize (Hce NANS STD).
  fold th rl in Hce. cbv zeta in Hce. specialize (Hce Hrl0).
  have Hp := flx_f2s_sum_of_fix_left
    (FT2R rh) (FT2R rl) (1-2*fprec t) Frh Frl Frhfix Hce.
  cbv zeta in Hp.
  have Hb := FastTwoSumEq_FLT rh rl Fe.
  rewrite Hb /F2Rp /= in Hp. fold e in Hp. exact Hp.
Qed.

(** The public condition makes the leading reciprocal normal, so this node is
    shared literally by the runtime FLT computation and the paper FLX model. *)
Lemma DWDivDW_th_FLT_FLX_from_cond (xh xl yh yl : ftype t) :
  DWDivDW_cond xh xl yh yl ->
  rnd_p (/ FT2R yh) = FT2R (BDIV (Zconst t 1) yh).
Proof.
move => COND.
have Fth := @DWDivDW_th_finite_from_cond NANS t STD xh xl yh yl COND.
have Hyhne := DWDivDW_cond_yh_nonzero xh xl yh yl COND.
have UFth := DWDivDW_cond_UF_th xh xl yh yl COND.
have Hone : FT2R (Zconst t 1) = 1%R.
{ rewrite /Zconst FT2R_ftype_of_float.
  have Hpow : (0 < 2 ^ fprec t)%Z.
  { apply Z.pow_pos_nonneg; pose proof (fprec_lb t); lia. }
  have Hrange : (- 2 ^ fprec t <= 1 <= 2 ^ fprec t)%Z by lia.
  have Hexact := proj1 (IEEE754_extra.BofZ_exact
                          (fprec t) (femax t) _ _ 1 Hrange).
  rewrite Hexact; reflexivity. }
rewrite -(BDIV_round_correct t (Zconst t 1) yh Hyhne Fth) Hone Rdiv_1_l.
symmetry; apply round_FLT_FLX. rewrite Rdiv_1_l in UFth; exact UFth.
Qed.

(** The runtime high residual remains on the paper's [2*u^2] lattice.
    If that lattice is inside the FLT range, the exact residual is already
    representable and the FMA does not round.  If the FLT minimum exponent is
    coarser, the rounded result lies on that coarser lattice, which is itself
    included in the [2*u^2] lattice. *)
Lemma DWDivDW_rh_fix_from_cond (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let rh := BFMA (BOPP yh) th (Zconst t 1) in
  generic_format radix2 (FIX_exp (1-2*fprec t)) (FT2R rh).
Proof.
move => Hp14 COND /=.
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
set v := (1-FT2R yh*FT2R th)%R.
set emin := @common.emin t.
set ef := (1-2*fprec t)%Z.
have Hth := DWDivDW_th_FLT_FLX_from_cond xh xl yh yl COND.
have Hyne := DWDivDW_cond_yh_nonzero xh xl yh yl COND.
have Fyh : generic_format radix2 (FLX_exp (fprec t)) (FT2R yh).
{ apply (generic_format_FLX_FLT radix2
    (SpecFloat.emin (fprec t) (femax t)) (fprec t)).
  apply generic_format_FLT_FT2R. }
have Hvfix := flx_reciprocal_residual_fix (FT2R yh) Fyh Hyne.
rewrite Hth in Hvfix. fold th v ef in Hvfix.
have Hvflx0 := @DWDivDW.Prop7_2 (fprec t) (fprec_gt_one t)
  choice eq_refl (FT2R yh) Fyh Hyne.
cbv zeta in Hvflx0. rewrite Hth in Hvflx0. fold th in Hvflx0.
have Hvflx : generic_format radix2 (FLX_exp (fprec t)) v.
{ unfold v. replace (1-FT2R yh*FT2R th)%R with
    (-(FT2R yh*FT2R th-1))%R by ring.
  apply generic_format_opp. exact Hvflx0. }
have Frh := DWDivDW_rh_finite_from_cond
  xh xl yh yl ltac:(lia) COND.
specialize (Frh NANS STD).
fold th rh in Frh.
move: (COND) => [_ [_ [Fyhr _]]].
have Hopp : FT2R (BOPP yh) = -FT2R yh.
{ symmetry; exact (@BOPP_binary t NANS STD yh (or_intror Fyhr)). }
have Hone : FT2R (Zconst t 1)=1%R.
{ rewrite /Zconst FT2R_ftype_of_float.
  have Hpow : (0<2^fprec t)%Z by
    (apply Z.pow_pos_nonneg; pose proof (fprec_lb t); lia).
  have Hrange : (-2^fprec t<=1<=2^fprec t)%Z by lia.
  rewrite (proj1 (IEEE754_extra.BofZ_exact
    (fprec t) (femax t) _ _ 1 Hrange)); reflexivity. }
have Hrnd : FT2R rh = round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) v.
{ unfold rh. rewrite -(BFMA_round_correct
    t (BOPP yh) th (Zconst t 1) Frh) Hopp Hone.
  unfold v. f_equal; ring. }
destruct (Z.leb_spec0 emin ef) as [Hemin|Hemin].
- have Hvflt : generic_format radix2
      (SpecFloat.fexp (fprec t) (femax t)) v.
  { destruct (Rle_dec (Rabs v) (bpow radix2 (emin+fprec t)))
      as [Hsmall|Hlarge].
    - have Hvfixemin := fix_format_lower v emin ef Hemin Hvfix.
      apply generic_format_FLT_FIX.
      + apply fprec_gt_0.
      + exact Hsmall.
      + exact Hvfixemin.
    - apply (generic_format_FLT_FLX radix2 emin (fprec t)).
      + eapply Rle_trans with
          (r2 := bpow radix2 (emin + fprec t)).
        * apply bpow_le.
          lia.
        * apply Rlt_le, Rnot_le_lt. exact Hlarge.
      + exact Hvflx. }
  rewrite Hrnd round_generic; [exact Hvfix|exact Hvflt].
- have Hrhflt : generic_format radix2
      (SpecFloat.fexp (fprec t) (femax t)) (FT2R rh)
    by apply generic_format_FLT_FT2R.
  have Hrhfixemin := generic_format_FIX_FLT radix2 emin (fprec t)
    (FT2R rh) Hrhflt.
  have Hefemin : (ef < emin)%Z by lia.
  exact (fix_format_lower (FT2R rh) ef emin
    (Z.lt_le_incl _ _ Hefemin) Hrhfixemin).
Qed.

(** The preceding lemma splits on whether the paper lattice [1-2p] is coarser
    than [emin].  Under [DWDivDW_cond] it never is: [DWDivDW_cond_emin_le]
    gives [emin <= -2p < 1-2p], so the exact residual is always an FLT value
    and the FMA does not round at all.

    This is the first of the node-exclusivity facts.  The [rh] node
    contributes no signed delta whatsoever -- neither an ordinary [u]-relative
    term nor an underflow floor -- so the [~UF_rh] arm of the regime cascade
    carries no error of its own. *)
Lemma DWDivDW_rh_exact_from_cond (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  FT2R (BFMA (BOPP yh) th (Zconst t 1)) = 1 - FT2R yh * FT2R th.
Proof.
move => Hp14 COND /=.
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
set v := (1-FT2R yh*FT2R th)%R.
set emin := @common.emin t.
set ef := (1-2*fprec t)%Z.
have Hemin : (emin <= ef)%Z.
{ have H := DWDivDW_cond_emin_le xh xl yh yl COND.
  unfold emin, ef, common.emin. lia. }
have Hth := DWDivDW_th_FLT_FLX_from_cond xh xl yh yl COND.
have Hyne := DWDivDW_cond_yh_nonzero xh xl yh yl COND.
have Fyh : generic_format radix2 (FLX_exp (fprec t)) (FT2R yh).
{ apply (generic_format_FLX_FLT radix2
    (SpecFloat.emin (fprec t) (femax t)) (fprec t)).
  apply generic_format_FLT_FT2R. }
have Hvfix := flx_reciprocal_residual_fix (FT2R yh) Fyh Hyne.
rewrite Hth in Hvfix. fold th v ef in Hvfix.
have Hvflx0 := @DWDivDW.Prop7_2 (fprec t) (fprec_gt_one t)
  choice eq_refl (FT2R yh) Fyh Hyne.
cbv zeta in Hvflx0. rewrite Hth in Hvflx0. fold th in Hvflx0.
have Hvflx : generic_format radix2 (FLX_exp (fprec t)) v.
{ unfold v. replace (1-FT2R yh*FT2R th)%R with
    (-(FT2R yh*FT2R th-1))%R by ring.
  apply generic_format_opp. exact Hvflx0. }
have Frh := DWDivDW_rh_finite_from_cond
  xh xl yh yl ltac:(lia) COND.
specialize (Frh NANS STD).
fold th rh in Frh.
move: (COND) => [_ [_ [Fyhr _]]].
have Hopp : FT2R (BOPP yh) = -FT2R yh.
{ symmetry; exact (@BOPP_binary t NANS STD yh (or_intror Fyhr)). }
have Hone : FT2R (Zconst t 1)=1%R.
{ rewrite /Zconst FT2R_ftype_of_float.
  have Hpow : (0<2^fprec t)%Z by
    (apply Z.pow_pos_nonneg; pose proof (fprec_lb t); lia).
  have Hrange : (-2^fprec t<=1<=2^fprec t)%Z by lia.
  rewrite (proj1 (IEEE754_extra.BofZ_exact
    (fprec t) (femax t) _ _ 1 Hrange)); reflexivity. }
have Hrnd : FT2R rh = round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) v.
{ unfold rh. rewrite -(BFMA_round_correct
    t (BOPP yh) th (Zconst t 1) Frh) Hopp Hone.
  unfold v. f_equal; ring. }
have Hvflt : generic_format radix2
    (SpecFloat.fexp (fprec t) (femax t)) v.
{ destruct (Rle_dec (Rabs v) (bpow radix2 (emin+fprec t)))
    as [Hsmall|Hlarge].
  - have Hvfixemin := fix_format_lower v emin ef Hemin Hvfix.
    apply generic_format_FLT_FIX.
    + apply fprec_gt_0.
    + exact Hsmall.
    + exact Hvfixemin.
  - apply (generic_format_FLT_FLX radix2 emin (fprec t)).
    + eapply Rle_trans with
        (r2 := bpow radix2 (emin + fprec t)).
      * apply bpow_le. lia.
      * apply Rlt_le, Rnot_le_lt. exact Hlarge.
    + exact Hvflx. }
rewrite Hrnd. exact (round_generic _ _ _ _ Hvflt).
Qed.

(** Under the division precondition the fixed-point premise above is
    automatic, so the residual Fast2Sum contributes no rounding error. *)
Lemma DWDivDW_residual_fast2sum_exact_from_cond
    (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let rh := BFMA (BOPP yh) th (Zconst t 1) in
  let rl := BOPP (BMULT yl th) in
  let e := Fast2Sum rh rl in
  FT2R (fst e)+FT2R (snd e)=FT2R rh+FT2R rl.
Proof.
move => Hp14 COND /=.
apply (DWDivDW_residual_fast2sum_exact_from_fix
  xh xl yh yl Hp14 COND).
exact (DWDivDW_rh_fix_from_cond xh xl yh yl Hp14 COND).
Qed.

(** Reciprocal-refinement multiplication with exactly the paper's [2*u^2]
    ordinary term and only the Fast2Mult-gap floor term. *)
Lemma DWDivDW_refinement_product_error_mixed_paper
    (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let rh := BFMA (BOPP yh) th (Zconst t 1) in
  let rl := BOPP (BMULT yl th) in
  let e := Fast2Sum rh rl in
  let d := DWTimesFP3 (fst e) (snd e) th in
  Rabs ((FT2R (fst d)+FT2R (snd d))-
        (FT2R (fst e)+FT2R (snd e))*FT2R th)
    <= 2*bpow radix2 (-fprec t)^2*
         Rabs ((FT2R (fst e)+FT2R (snd e))*FT2R th)+
       251/100*bpow radix2 (@common.emin t) /\
  double_word_prop (fst d) (snd d).
Proof.
move => Hp14 COND /=.
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
set rl := BOPP (BMULT yl th).
set e := Fast2Sum rh rl.
set d := DWTimesFP3 (fst e) (snd e) th.
have Fe0 := DWDivDW_fast2sum_cascade_from_cond
  xh xl yh yl Hp14 COND.
specialize (Fe0 NANS STD). fold th rh rl e in Fe0.
destruct Fe0 as [Fe _].
have Fd0 := DWDivDW_timesfp_cascade_from_cond
  xh xl yh yl Hp14 COND.
specialize (Fd0 NANS STD). fold th rh rl e d in Fd0.
destruct Fd0 as [Fd _].
have Hex := DWDivDW_residual_fast2sum_exact_from_cond
  xh xl yh yl Hp14 COND.
fold th rh rl e in Hex. cbv zeta in Hex.
have DWe := Fast2Sum_double_word_of_sum rh rl Fe Hex.
fold e in DWe.
split.
- have H := DWTimesFP3_error_mixed_flat
    (fst e) (snd e) th ltac:(lia) DWe Fd.
  fold d in H. exact H.
- exact (DWTimesFP3_double_word_mixed
    (fst e) (snd e) th ltac:(lia) DWe Fd).
Qed.

Lemma DWDivDW_reciprocal_plus_error_paper_tight
    (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let rh := BFMA (BOPP yh) th (Zconst t 1) in
  let rl := BOPP (BMULT yl th) in
  let e := Fast2Sum rh rl in
  let d := DWTimesFP3 (fst e) (snd e) th in
  let m := DWPlusFP (fst d) (snd d) th in
  Rabs ((FT2R (fst m)+FT2R (snd m))-
        (FT2R (fst d)+FT2R (snd d)+FT2R th))
    <= 2*bpow radix2 (-fprec t)^2*
         Rabs (FT2R (fst d)+FT2R (snd d)+FT2R th).
Proof.
move => Hp14 COND /=.
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
set rl := BOPP (BMULT yl th).
set e := Fast2Sum rh rl.
set d := DWTimesFP3 (fst e) (snd e) th.
set m := DWPlusFP (fst d) (snd d) th.
have Hd := DWDivDW_refinement_product_error_mixed_paper
  xh xl yh yl Hp14 COND.
fold th rh rl e d in Hd. cbv zeta in Hd.
destruct Hd as [_ DWd].
have Fm0 := DWDivDW_plusfp_cascade_from_cond
  xh xl yh yl Hp14 COND.
specialize (Fm0 NANS STD). fold th rh rl e d m in Fm0.
destruct Fm0 as [Fm _].
exact (DWPlusFP_error_paper_tight
  (fst d) (snd d) th ltac:(lia) DWd Fm).
Qed.

(** The low-divisor product is the second and only other reciprocal-prologue
    node that may initially differ; it also costs at most one floor ulp. *)
Lemma DWDivDW_rl_FLT_FLX_diff_from_cond (xh xl yh yl : ftype t) :
  (4 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  Rabs (FT2R (BOPP (BMULT yl th)) -
        (- rnd_p (FT2R yl * FT2R th)))
    <= bpow radix2 (@common.emin t).
Proof.
move => Hp4 COND.
set th := BDIV (Zconst t 1) yh.
have Frl := @DWDivDW_rl_finite_from_cond NANS t STD
  xh xl yh yl Hp4 COND.
have Fmul : is_finite (BMULT yl th) = true.
{ exact (proj1 (BOPP_is_finite t (BMULT yl th)) Frl). }
have Hrun := BMULT_round_correct t yl th Fmul.
change (Rabs (FT2R (BOPP (BMULT yl th)) -
  (- rnd_p (FT2R yl * FT2R th))) <=
  bpow radix2 (@common.emin t)).
rewrite -(@BOPP_binary t NANS STD (BMULT yl th) (or_introl Frl)).
rewrite -Hrun.
set vr := round radix2 (SpecFloat.fexp (fprec t) (femax t))
  (Znearest choice) (FT2R yl * FT2R th).
set vp := rnd_p (FT2R yl * FT2R th).
change (Rabs (- vr - - vp) <= bpow radix2 (@common.emin t)).
replace (- vr - - vp)%R with (- (vr-vp))%R by ring.
rewrite Rabs_Ropp.
unfold vr, vp.
exact (DWDivFP_acc.round_FLT_FLX_diff (t:=t) (FT2R yl * FT2R th)).
Qed.

(** Consequently the real sum entering reciprocal refinement differs from
    the paper input by at most two floor ulps.  This is the perturbation that
    must be propagated; the normal [u^2] analysis is deliberately absent. *)
Lemma DWDivDW_residual_sum_FLT_FLX_diff_from_cond
    (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let rh := BFMA (BOPP yh) th (Zconst t 1) in
  let rl := BOPP (BMULT yl th) in
  Rabs ((FT2R rh + FT2R rl) -
        ((1 - FT2R yh * rnd_p (/ FT2R yh)) -
         rnd_p (FT2R yl * rnd_p (/ FT2R yh))))
    <= 1 * bpow radix2 (@common.emin t).
Proof.
move => Hp4 COND.
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
set rl := BOPP (BMULT yl th).
have Hth := DWDivDW_th_FLT_FLX_from_cond xh xl yh yl COND.
(* The high residual does not round at all ([DWDivDW_rh_exact_from_cond]), so
   it coincides with the paper's high residual and contributes nothing.  Only
   the low double round survives, which is why the total is one floor ulp
   rather than the [3/2] this lemma used to charge. *)
have Hex := DWDivDW_rh_exact_from_cond xh xl yh yl Hp4 COND.
fold th rh in Hex. cbv zeta in Hex.
have Hrl := DWDivDW_rl_FLT_FLX_diff_from_cond xh xl yh yl
  ltac:(lia) COND.
fold th rl in Hrl. cbv zeta in Hrl.
rewrite Hth.
change (Rabs (FT2R rh + FT2R rl -
  ((1 - FT2R yh * FT2R th) - rnd_p (FT2R yl * FT2R th))) <=
  1 * bpow radix2 (@common.emin t)).
rewrite Hex.
replace (1 - FT2R yh * FT2R th + FT2R rl -
  ((1 - FT2R yh * FT2R th) - rnd_p (FT2R yl * FT2R th)))%R with
  (FT2R rl - (- rnd_p (FT2R yl * FT2R th)))%R by ring.
eapply Rle_trans; [exact Hrl|]. lra.
Qed.

(** The complete runtime residual pair therefore costs nothing for the exact
    residual projection ([DWDivDW_rh_exact_from_cond]) and at most one ulp for
    the low double round. *)
Lemma DWDivDW_fast2sum_sum_FLT_FLX_diff_from_cond
    (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let rh := BFMA (BOPP yh) th (Zconst t 1) in
  let rl := BOPP (BMULT yl th) in
  let e := Fast2Sum rh rl in
  Rabs ((FT2R (fst e)+FT2R (snd e)) -
        ((1 - FT2R yh * rnd_p (/ FT2R yh)) -
         rnd_p (FT2R yl * rnd_p (/ FT2R yh))))
    <= 1 * bpow radix2 (@common.emin t).
Proof.
move => Hp14 COND /=.
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
set rl := BOPP (BMULT yl th).
set e := Fast2Sum rh rl.
have Hex := DWDivDW_residual_fast2sum_exact_from_cond
  xh xl yh yl Hp14 COND.
have Hres := DWDivDW_residual_sum_FLT_FLX_diff_from_cond
  xh xl yh yl ltac:(lia) COND.
fold th rh rl e in Hex. fold th rh rl in Hres.
cbv zeta in Hex, Hres.
rewrite Hex. exact Hres.
Qed.

(** Tight distance from the runtime residual pair to the exact Newton
    residual.  The sole ordinary term is the FLX rounding of [yl*th]; the
    FLT-versus-FLX bridge contributes exactly the preceding single floor
    ulp. *)
Lemma DWDivDW_residual_value_error_tight_floor
    (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let rh := BFMA (BOPP yh) th (Zconst t 1) in
  let rl := BOPP (BMULT yl th) in
  let e := Fast2Sum rh rl in
  let Y := FT2R yh+FT2R yl in
  Rabs ((FT2R (fst e)+FT2R (snd e))-(1-Y*FT2R th)) <=
    1001/1000*bpow radix2 (-fprec t)^2+
    1*bpow radix2 (@common.emin t).
Proof.
move => Hp14 COND /=.
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
set rl := BOPP (BMULT yl th).
set e := Fast2Sum rh rl.
set Y := FT2R yh+FT2R yl.
set u := bpow radix2 (-fprec t).
set eta := bpow radix2 (@common.emin t).
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /16384.
{ unfold u. have -> : (/16384:R)=bpow radix2 (-14) by (simpl;lra).
  apply bpow_le; lia. }
have Hth := DWDivDW_th_FLT_FLX_from_cond xh xl yh yl COND.
have Hfloor := DWDivDW_fast2sum_sum_FLT_FLX_diff_from_cond
  xh xl yh yl Hp14 COND.
fold th rh rl e in Hfloor. cbv zeta in Hfloor.
rewrite Hth in Hfloor.
set v := (FT2R yl*FT2R th)%R.
have Hv := DWDivDW_yl_th_abs_from_cond xh xl yh yl COND.
specialize (Hv NANS STD).
fold th u in Hv. fold v in Hv.
have Hrnd0 := Relative.relative_error_N_FLX radix2 (fprec t)
  (fprec_gt_0 t) choice v.
have He : (/2*bpow radix2 (-fprec t+1))%R=u.
{ unfold u. replace (-fprec t+1)%Z with (1+-fprec t)%Z by ring.
  rewrite bpow_plus. change (bpow radix2 1) with (2:R). lra. }
rewrite He in Hrnd0.
have Hrnd : Rabs (v-rnd_p v)<=1001/1000*u^2.
{ rewrite Rabs_minus_sym.
  eapply Rle_trans; [exact Hrnd0|].
  have Hmul := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Hv.
  eapply Rle_trans; [exact Hmul|]. nra. }
change (Rabs ((FT2R (fst e)+FT2R (snd e))-(1-Y*FT2R th)) <=
  1001/1000*u^2+1*eta).
have Heq : (FT2R (fst e)+FT2R (snd e))-(1-Y*FT2R th) =
 ((FT2R (fst e)+FT2R (snd e))-
   ((1-FT2R yh*FT2R th)-rnd_p v))+(v-rnd_p v).
{ unfold Y,v. ring. }
rewrite Heq. eapply Rle_trans; [apply Rabs_triang|].
fold eta in Hfloor. fold v in Hfloor.
eapply Rle_trans.
- apply Rplus_le_compat; [exact Hfloor|exact Hrnd].
- right; ring.
Qed.

Lemma DWDivDW_newton_step_error_tight_from_cond
    (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let Y := FT2R yh+FT2R yl in
  Rabs (FT2R th+(1-Y*FT2R th)*FT2R th-/Y) <=
    2298/1000*bpow radix2 (-fprec t)^2*Rabs (/Y).
Proof.
move => Hp14 COND /=.
set th := BDIV (Zconst t 1) yh.
set Y := FT2R yh+FT2R yl.
move: (COND) => [_ [_ [_ [_ [_ [DWy _]]]]]].
have HDWy : DWPlus.double_word (fprec t) choice (FT2R yh) (FT2R yl).
{ apply (dw_word_DWdouble yh yl yh). exact DWy. }
have Hyhne := DWDivDW_cond_yh_nonzero xh xl yh yl COND.
have H := flx_newton_step_error (FT2R yh) (FT2R yl)
  Hp14 HDWy Hyhne.
have Hth := DWDivDW_th_FLT_FLX_from_cond xh xl yh yl COND.
fold th Y. cbv zeta in H. rewrite Hth in H. exact H.
Qed.

(** The exact scale that propagates a reciprocal-residual perturbation to the
    quotient is essentially one: [|(xh+xl)*th| <= 1.001*|Q|]. *)
Lemma DWDivDW_X_th_quotient_scale_from_cond
    (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let Q := (FT2R xh + FT2R xl)/(FT2R yh + FT2R yl) in
  Rabs ((FT2R xh + FT2R xl) * FT2R th) <= 1001/1000 * Rabs Q.
Proof.
move => Hp14 COND.
set th := BDIV (Zconst t 1) yh.
set X := FT2R xh + FT2R xl.
set Y := FT2R yh + FT2R yl.
set Q := X/Y.
set u := bpow radix2 (-fprec t).
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /16384.
{ unfold u. have -> : (/16384:R) = bpow radix2 (-14) by (simpl; lra).
  apply bpow_le; lia. }
move: (COND) => [_ [_ [_ [_ [_ [DWy _]]]]]].
have Hyl := @DWMulFP_acc.aux_dwu_rel t STD yh yl DWy.
fold u in Hyl.
have Hyhne := DWDivDW_cond_yh_nonzero xh xl yh yl COND.
have HYne : Y <> 0.
{ intro H0.
  have Hrev := Rabs_triang_inv (FT2R yh) (-FT2R yl).
  rewrite Rabs_Ropp in Hrev.
  replace (FT2R yh - -FT2R yl)%R with Y in Hrev by (unfold Y; ring).
  rewrite H0 Rabs_R0 in Hrev.
  have Hypos : 0 < Rabs (FT2R yh) by apply Rabs_pos_lt; exact Hyhne.
  nra. }
have Hy0 : 0 < Rabs (FT2R yh) by apply Rabs_pos_lt; exact Hyhne.
have HYup : Rabs Y <= (1+u)*Rabs (FT2R yh).
{ unfold Y. eapply Rle_trans; [apply Rabs_triang|]. nra. }
have Htb := DWDivDW_th_relative_bounds_from_cond
  (NANS:=NANS) (STD:=STD) (t:=t) xh xl yh yl ltac:(lia) COND.
destruct Htb as [_ [HTup _]]. fold th u in HTup.
have Hinv : Rabs (1/FT2R yh)*Rabs (FT2R yh)=1.
{ rewrite -Rabs_mult.
  replace (1/FT2R yh*FT2R yh)%R with 1 by (field; exact Hyhne).
  rewrite Rabs_R1; reflexivity. }
have HthYh : Rabs (FT2R th)*Rabs (FT2R yh) <= 1+u.
{ have H := Rmult_le_compat_r (Rabs (FT2R yh)) _ _
    (Rlt_le _ _ Hy0) HTup.
  rewrite Rmult_assoc Hinv Rmult_1_r in H. exact H. }
have HthY : Rabs (FT2R th)*Rabs Y <= (1+u)^2.
{ have H := Rmult_le_compat_l (Rabs (FT2R th)) _ _
    (Rabs_pos _) HYup.
  eapply Rle_trans; [exact H|].
  have H2 := Rmult_le_compat_l (1+u) _ _ ltac:(nra) HthYh.
  replace (Rabs (FT2R th)*((1+u)*Rabs (FT2R yh)))%R with
    ((1+u)*(Rabs (FT2R th)*Rabs (FT2R yh)))%R by ring.
  eapply Rle_trans; [exact H2|]. right; ring. }
have HQY : Rabs Q*Rabs Y=Rabs X.
{ unfold Q, Rdiv. rewrite Rabs_mult Rabs_inv.
  field. intro H; apply HYne, Rabs_eq_R0; exact H. }
have HY0 : 0 < Rabs Y by apply Rabs_pos_lt; exact HYne.
change (Rabs (X*FT2R th) <= 1001/1000*Rabs Q).
rewrite Rabs_mult.
apply (Rmult_le_reg_r (Rabs Y)); [exact HY0|].
replace ((Rabs X*Rabs (FT2R th))*Rabs Y)%R with
  (Rabs X*(Rabs (FT2R th)*Rabs Y))%R by ring.
replace ((1001/1000*Rabs Q)*Rabs Y)%R with
  (1001/1000*(Rabs Q*Rabs Y))%R by ring.
rewrite HQY.
eapply Rle_trans.
- apply Rmult_le_compat_l; [apply Rabs_pos|exact HthY].
- replace (Rabs X*(1+u)^2)%R with ((1+u)^2*Rabs X)%R by ring.
  apply Rmult_le_compat_r; [apply Rabs_pos|]. nra.
Qed.

(** Quotient-scaled interpretation of the compensated refinement block.
    Its ordinary rounding contribution is below [0.01*u^2*|Q|] at
    [p >= 14]; the only second-order denormal contribution is retained as
    the two actual floor ulps generated inside Algorithm 9. *)
(** Coefficient-parametric scaling of the refinement block onto the quotient
    scale.  The third-order coefficient [c3] is absorbed into [1/100*u^2] for
    any [c3 <= 140] at [p >= 14], so both arms of the refinement split share
    this step; only the floor coefficient [fl] is carried through. *)
Lemma DWDivDW_refinement_product_error_scaled_param
    (xh xl yh yl : ftype t) (c3 fl : R) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  0 <= c3 -> c3 <= 140 -> 0 <= fl ->
  let th := BDIV (Zconst t 1) yh in
  let rh := BFMA (BOPP yh) th (Zconst t 1) in
  let rl := BOPP (BMULT yl th) in
  let e := Fast2Sum rh rl in
  let d := DWTimesFP3 (fst e) (snd e) th in
  let X := FT2R xh + FT2R xl in
  let Q := X / (FT2R yh + FT2R yl) in
  Rabs ((FT2R (fst d) + FT2R (snd d)) -
        (FT2R (fst e) + FT2R (snd e))*FT2R th)
    <= c3 * bpow radix2 (-fprec t)^3 * Rabs (FT2R th) +
       fl * bpow radix2 (@common.emin t) ->
  Rabs (X * ((FT2R (fst d) + FT2R (snd d)) -
                  (FT2R (fst e) + FT2R (snd e))*FT2R th))
    <= 1/100 * bpow radix2 (-fprec t)^2 * Rabs Q +
       fl * bpow radix2 (@common.emin t) * Rabs X.
Proof.
move => Hp14 COND Hc30 Hc3 Hfl. cbv zeta.
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
set rl := BOPP (BMULT yl th).
set e := Fast2Sum rh rl.
set d := DWTimesFP3 (fst e) (snd e) th.
set X := FT2R xh + FT2R xl.
set Q := X/(FT2R yh + FT2R yl).
set u := bpow radix2 (-fprec t).
set eta := bpow radix2 (@common.emin t).
set T := Rabs (FT2R th).
move => Href.
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /16384.
{ unfold u. have -> : (/16384:R)=bpow radix2 (-14) by (simpl;lra).
  apply bpow_le; lia. }
have HT0 : 0 <= T by (unfold T; apply Rabs_pos).
have HX0 : 0 <= Rabs X by apply Rabs_pos.
have Heta0 : 0 <= eta by (unfold eta; apply bpow_ge_0).
have Hscale := DWDivDW_X_th_quotient_scale_from_cond
  xh xl yh yl Hp14 COND.
fold th X Q in Hscale. cbv zeta in Hscale.
rewrite Rabs_mult in Hscale. fold T in Hscale.
change (Rabs (X*((FT2R (fst d)+FT2R (snd d))-
  (FT2R (fst e)+FT2R (snd e))*FT2R th)) <=
  1/100*u^2*Rabs Q+fl*eta*Rabs X).
rewrite Rabs_mult.
have Hmul := Rmult_le_compat_l (Rabs X) _ _ HX0 Href.
eapply Rle_trans; [exact Hmul|].
have Hthird : Rabs X*(c3*u^3*T) <= 1/100*u^2*Rabs Q.
{ replace (Rabs X*(c3*u^3*T))%R with
      (c3*u^3*(Rabs X*T))%R by ring.
  have Hc : 0 <= c3*u^3.
  { apply Rmult_le_pos; [exact Hc30|apply pow_le; lra]. }
  have Hs := Rmult_le_compat_l (c3*u^3) _ _ Hc Hscale.
  eapply Rle_trans; [exact Hs|].
  have HQ0 : 0 <= Rabs Q by apply Rabs_pos.
  replace (c3*u^3*(1001/1000*Rabs Q))%R with
    ((c3*u^3*(1001/1000))*Rabs Q)%R by ring.
  replace (1/100*u^2*Rabs Q)%R with
    ((1/100*u^2)*Rabs Q)%R by ring.
  apply Rmult_le_compat_r; [exact HQ0|].
  (* [c3*1.001*u^3 <= 0.01*u^2] at [c3 <= 140], [u <= 2^-14]; give the two
     monomial comparisons explicitly, [nra] does not find them alone. *)
  have Hu2 : 0 <= u^2 by (apply pow_le; lra).
  have Hu3 : u^3 <= u^2*(/16384).
  { replace (u^3)%R with (u^2*u)%R by ring.
    apply Rmult_le_compat_l; [exact Hu2|exact Hu]. }
  have Hc3u : c3*u^3 <= 140*u^3.
  { apply Rmult_le_compat_r; [apply pow_le; lra|exact Hc3]. }
  nra. }
eapply Rle_trans with (r2:=
  Rabs X*(c3*u^3*T)+Rabs X*(fl*eta)).
- fold T; right; ring.
- eapply Rle_trans.
  + apply Rplus_le_compat; [exact Hthird|apply Rle_refl].
  + right; ring.
Qed.

(** Coefficient-parametric reciprocal reconstruction.  The refinement block's
    floor coefficient [fr] and the Newton remainder's coefficient [nw] are
    taken as inputs, so the two arms of the refinement split share this whole
    float-level assembly instead of each needing a copy.

    The conclusion is an exact identity in [fr] and [nw] -- nothing is rounded
    up here, which is what lets each arm keep its own sharp constants. *)
Lemma DWDivDW_reciprocal_error_scaled_floor_param
    (xh xl yh yl : ftype t) (fr nw : R) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  0 <= fr -> 0 <= nw ->
  let th := BDIV (Zconst t 1) yh in
  let rh := BFMA (BOPP yh) th (Zconst t 1) in
  let rl := BOPP (BMULT yl th) in
  let e := Fast2Sum rh rl in
  let d := DWTimesFP3 (fst e) (snd e) th in
  let m := DWPlusFP (fst d) (snd d) th in
  let X := FT2R xh+FT2R xl in
  let Y := FT2R yh+FT2R yl in
  let Q := X/Y in
  Rabs (X*((FT2R (fst d)+FT2R (snd d))-
        (FT2R (fst e)+FT2R (snd e))*FT2R th)) <=
    1/100*bpow radix2 (-fprec t)^2*Rabs Q+
    fr*bpow radix2 (@common.emin t)*Rabs X ->
  Rabs (X*(FT2R th+(1-Y*FT2R th)*FT2R th-/Y)) <=
    nw*bpow radix2 (-fprec t)^2*Rabs Q ->
  Rabs (X*((FT2R (fst m)+FT2R (snd m))-/Y)) <=
    (2+(nw+1013/1000)*(1+2*bpow radix2 (-fprec t)^2))*
      bpow radix2 (-fprec t)^2*Rabs Q+
    (fr*(1+2*bpow radix2 (-fprec t)^2))*
      bpow radix2 (@common.emin t)*Rabs X+
    (1001/1000*(1+2*bpow radix2 (-fprec t)^2))*
      bpow radix2 (@common.emin t)*Rabs Q.
Proof.
move => Hp14 COND Hfr Hnw. cbv zeta.
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
set rl := BOPP (BMULT yl th).
set e := Fast2Sum rh rl.
set d := DWTimesFP3 (fst e) (snd e) th.
set m := DWPlusFP (fst d) (snd d) th.
set X := FT2R xh+FT2R xl.
set Y := FT2R yh+FT2R yl.
set Q := X/Y.
set u := bpow radix2 (-fprec t).
set eta := bpow radix2 (@common.emin t).
set E := FT2R (fst e)+FT2R (snd e).
set D := FT2R (fst d)+FT2R (snd d).
set M := FT2R (fst m)+FT2R (snd m).
move => Href HnewX.
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /16384.
{ unfold u. have -> : (/16384:R)=bpow radix2 (-14) by (simpl;lra).
  apply bpow_le; lia. }
have HX0 : 0 <= Rabs X by apply Rabs_pos.
have HQ0 : 0 <= Rabs Q by apply Rabs_pos.
have Heta0 : 0 <= eta by (unfold eta; apply bpow_ge_0).
have HYne : Y<>0.
{ move: (COND) => [_ [_ [_ [_ [_ [DWy _]]]]]].
  have Hyhne := DWDivDW_cond_yh_nonzero xh xl yh yl COND.
  intro HY0; apply Hyhne.
  have Hyl := @DWMulFP_acc.aux_dwu_rel t STD yh yl DWy.
  fold u in Hyl.
  have Hrev := Rabs_triang_inv (FT2R yh) (-FT2R yl).
  rewrite Rabs_Ropp in Hrev.
  replace (FT2R yh- -FT2R yl)%R with Y in Hrev by (unfold Y;ring).
  rewrite HY0 Rabs_R0 in Hrev.
  have Hy0 : 0 <= Rabs (FT2R yh) by apply Rabs_pos.
  have Hz : Rabs (FT2R yh)=0 by nra.
  exact (Rabs_eq_R0 _ Hz). }
have HQX : Rabs X*Rabs (/Y)=Rabs Q.
{ unfold Q, Rdiv. rewrite Rabs_mult. reflexivity. }
have Hscale := DWDivDW_X_th_quotient_scale_from_cond
  xh xl yh yl Hp14 COND.
fold th Q in Hscale. cbv zeta in Hscale.
have Hres := DWDivDW_residual_value_error_tight_floor
  xh xl yh yl Hp14 COND.
fold th rh rl e Y u eta E in Hres. cbv zeta in Hres.
fold X Q in Hscale. fold E in Hres.
have Hresc : Rabs (X*((E-(1-Y*FT2R th))*FT2R th)) <=
    (1001/1000*Rabs Q)*(1001/1000*u^2+1*eta).
{ have Hfac : Rabs (X*((E-(1-Y*FT2R th))*FT2R th)) =
      Rabs (X*FT2R th)*Rabs (E-(1-Y*FT2R th)).
  { rewrite !Rabs_mult. ring. }
  rewrite Hfac.
  have Hmul := Rmult_le_compat _ _ _ _
    (Rabs_pos _) (Rabs_pos _) Hscale Hres.
  exact Hmul. }
have Hu2Q : 0 <= u^2*Rabs Q.
{ apply Rmult_le_pos; [apply pow_le; lra|exact HQ0]. }
have HetaX : 0 <= eta*Rabs X.
{ apply Rmult_le_pos; [exact Heta0|exact HX0]. }
have HetaQ : 0 <= eta*Rabs Q.
{ apply Rmult_le_pos; [exact Heta0|exact HQ0]. }
have Hpre : Rabs (X*((D+FT2R th)-/Y)) <=
    (nw+1013/1000)*u^2*Rabs Q+fr*eta*Rabs X+
    1001/1000*eta*Rabs Q.
{ have Heq : X*((D+FT2R th)-/Y) =
    X*(D-E*FT2R th)+X*((E-(1-Y*FT2R th))*FT2R th)+
    X*(FT2R th+(1-Y*FT2R th)*FT2R th-/Y) by ring.
  rewrite Heq.
  have Ht1 := Rabs_triang (X*(D-E*FT2R th))
    (X*((E-(1-Y*FT2R th))*FT2R th)).
  have Ht2 := Rabs_triang
    (X*(D-E*FT2R th)+X*((E-(1-Y*FT2R th))*FT2R th))
    (X*(FT2R th+(1-Y*FT2R th)*FT2R th-/Y)).
  eapply Rle_trans; [exact Ht2|].
  eapply Rle_trans.
  - apply Rplus_le_compat; [exact Ht1|exact HnewX].
  - eapply Rle_trans.
    + apply Rplus_le_compat.
      * apply Rplus_le_compat; [exact Href|exact Hresc].
      * apply Rle_refl.
    + nra. }
have Hplus := DWDivDW_reciprocal_plus_error_paper_tight
  xh xl yh yl Hp14 COND.
fold th rh rl e d m u D M in Hplus. cbv zeta in Hplus.
have HXS : Rabs (X*(D+FT2R th)) <= Rabs Q+
    ((nw+1013/1000)*u^2*Rabs Q+fr*eta*Rabs X+
     1001/1000*eta*Rabs Q).
{ have Heq : X*(D+FT2R th)=X/Y+X*((D+FT2R th)-/Y).
  { field; exact HYne. }
  rewrite Heq. eapply Rle_trans; [apply Rabs_triang|].
  fold Q. apply Rplus_le_compat_l. exact Hpre. }
have HplusX : Rabs (X*(M-(D+FT2R th))) <=
    2*u^2*(Rabs Q+
      ((nw+1013/1000)*u^2*Rabs Q+fr*eta*Rabs X+
       1001/1000*eta*Rabs Q)).
{ rewrite Rabs_mult.
  have Hx := Rmult_le_compat_l (Rabs X) _ _ HX0 Hplus.
  eapply Rle_trans; [exact Hx|].
  have Hfac : Rabs X*(2*u^2*Rabs (D+FT2R th)) =
      2*u^2*Rabs (X*(D+FT2R th)).
  { rewrite Rabs_mult. ring. }
  rewrite Hfac.
  apply Rmult_le_compat_l; [nra|exact HXS]. }
change (Rabs (X*(M-/Y)) <=
  (2+(nw+1013/1000)*(1+2*u^2))*u^2*Rabs Q+
  (fr*(1+2*u^2))*eta*Rabs X+
  (1001/1000*(1+2*u^2))*eta*Rabs Q).
have Heq : X*(M-/Y)=X*(M-(D+FT2R th))+X*((D+FT2R th)-/Y)
  by ring.
rewrite Heq. eapply Rle_trans; [apply Rabs_triang|].
eapply Rle_trans.
- apply Rplus_le_compat; [exact HplusX|exact Hpre].
- right; ring.
Qed.


(** Reciprocal reconstruction prefix of the paper computation. *)
Definition DWDivDW_reciprocal_FLX_model (yh yl : ftype t) : R * R :=
  let th_r := rnd_p (/ FT2R yh) in
  let rh_r := (1 - FT2R yh * th_r)%R in
  let rl_r := (- rnd_p (FT2R yl * th_r))%R in
  let eh_r := rnd_p (rh_r + rl_r) in
  let el_r := snd (F2Sum.Fast2Sum (fprec t) choice rh_r rl_r) in
  let dhl  := DWTimesFP.DWTimesFP9 (fprec t) choice eh_r el_r th_r in
  DWPlus.DWPlusFP (fprec t) choice (fst dhl) (snd dhl) th_r.

(** The real-valued, unbounded-exponent computation analyzed by the paper.
    Naming it separately lets the denormal proof compare the runtime result
    with this fixed reference value instead of re-analyzing normal rounding. *)
Definition DWDivDW3_FLX_model (xh xl yh yl : ftype t) : R * R :=
  let mhl := DWDivDW_reciprocal_FLX_model yh yl in
  DWTimesDW.DWTimesDW12 (fprec t) choice
    (FT2R xh) (FT2R xl) (fst mhl) (snd mhl).

(** Aggregate closing-block contract.  The proof performs the internal
    leading-product and low-order underflow case analysis directly, exposing
    only the mixed relative/floor estimate required by division. *)
Local Lemma DWDivDW3_closing_mixed_error_from_cond
    (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let th := BDIV (Zconst t 1) yh in
  let rh := BFMA (BOPP yh) th (Zconst t 1) in
  let rl := BOPP (BMULT yl th) in
  let e := Fast2Sum rh rl in
  let d := DWTimesFP3 (fst e) (snd e) th in
  let m := DWPlusFP (fst d) (snd d) th in
  let X := FT2R xh+FT2R xl in
  let M := FT2R (fst m)+FT2R (snd m) in
  let zr := FT2R (fst (DWDivDW3 xh xl yh yl))+
            FT2R (snd (DWDivDW3 xh xl yh yl)) in
  Rabs (zr-X*M) <=
    4*bpow radix2 (-fprec t)^2*Rabs (X*M)+
    2*bpow radix2 (@common.emin t).
Proof.
move => Hp14 COND /=.
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
set rl := BOPP (BMULT yl th).
set e := Fast2Sum rh rl.
set d := DWTimesFP3 (fst e) (snd e) th.
set m := DWPlusFP (fst d) (snd d) th.
set mh := fst m; set ml := snd m.
set X := FT2R xh+FT2R xl.
set M := FT2R mh+FT2R ml.
set zr := FT2R (fst (DWDivDW3 xh xl yh yl))+
          FT2R (snd (DWDivDW3 xh xl yh yl)).
set u := bpow radix2 (-fprec t).
set eta := bpow radix2 (@common.emin t).
set T := bpow radix2 (@common.emin t+2*fprec t-1).
set N := bpow radix2 (@common.emin t+fprec t-1).
set P0 := FT2R xh*FT2R mh.
set P := Rabs P0.
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /16384.
{ unfold u. have -> : (/16384:R)=bpow radix2 (-14) by (simpl;lra).
  apply bpow_le; lia. }
have Heta0 : 0 < eta by (unfold eta;apply bpow_gt_0).
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have HN0 : 0 < N by (unfold N;apply bpow_gt_0).
move: (COND) => [_ [_ [_ [_ [DWx _]]]]].
have Hrel := DWDivDW_reciprocal_relative_from_cond
  xh xl yh yl Hp14 COND.
specialize (Hrel NANS STD). fold th rh rl e d m in Hrel.
destruct Hrel as [_ [_ [_ [DWm _]]]]. fold m mh ml in DWm.
have FIN := DWDivDW3_finite_from_cond xh xl yh yl Hp14 COND.
specialize (FIN NANS STD). fold th rh rl e d m mh ml in FIN.
change (is_finite_p (DWTimesDW3 xh xl mh ml)) in FIN.
change (Rabs (zr-X*M) <= 4*u^2*Rabs (X*M)+2*eta).
destruct (Rle_or_lt P (9/8*T)) as [Hnear|Hfar].
- destruct (Rle_or_lt T P) as [Nprod|Hgap].
  + have Hmul := DWMulDW_acc.DWTimesDW_abs_normal_near_threshold
      xh xl mh ml DWx DWm FIN Hp14 Nprod Hnear.
    fold X M zr u eta in Hmul. cbv zeta in Hmul. exact Hmul.
  + have Heta := DWDivDW_eta_absorbed_by_zprod xh xl yh yl Hp14 COND.
specialize (Heta NANS STD).
fold th rh rl e d m in Heta. cbv zeta in Heta.
fold m mh u eta P0 P in Heta.
have HPlow0 := DWDivDW_zprod_lower_from_cond xh xl yh yl Hp14 COND.
specialize (HPlow0 NANS STD).
fold th rh rl e d m in HPlow0. cbv zeta in HPlow0.
fold m mh P0 P in HPlow0.
have Hq : T <= Rabs (FT2R xh/FT2R yh).
{ unfold T. move: (COND) => [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]. exact H. }
have HPlow : /2*T <= P.
{ have H := Rmult_le_compat_l (/2) _ _ ltac:(lra) Hq.
  eapply Rle_trans; [exact H|exact HPlow0]. }
have Hxl := @DWMulFP_acc.aux_dwu_rel t STD xh xl DWx.
have Hml := @DWMulFP_acc.aux_dwu_rel t STD mh ml DWm.
fold u in Hxl,Hml.
have Hxhml : Rabs (FT2R xh*FT2R ml) <= u*P.
{ unfold P,P0. rewrite !Rabs_mult.
  have H := Rmult_le_compat_l (Rabs (FT2R xh)) _ _
    (Rabs_pos _) Hml. eapply Rle_trans; [exact H|]. right;ring. }
have Hxlmh : Rabs (FT2R xl*FT2R mh) <= u*P.
{ unfold P,P0. rewrite !Rabs_mult.
  have H := Rmult_le_compat_r (Rabs (FT2R mh)) _ _
    (Rabs_pos _) Hxl. eapply Rle_trans; [exact H|]. right;ring. }
have Hxlml : Rabs (FT2R xl*FT2R ml) <= u^2*P.
{ unfold P,P0. rewrite !Rabs_mult.
  have H := Rmult_le_compat _ _ _ _ (Rabs_pos _) (Rabs_pos _) Hxl Hml.
  eapply Rle_trans; [exact H|]. right;ring. }
have HuT : u*T=N.
{ unfold u,T,N. rewrite -bpow_plus. f_equal;ring. }
have HuP_N : u*P < N.
{ have H := Rmult_lt_compat_l u _ _ Hu0 Hgap.
  rewrite HuT in H. exact H. }
have HtwoN : 2*N=bpow radix2 (@common.emin t+fprec t).
{ unfold N. transitivity
    (bpow radix2 1*bpow radix2 (@common.emin t+fprec t-1));
    [change (bpow radix2 1) with (2:R);ring|].
  rewrite -bpow_plus. f_equal;ring. }
have HfourN : 4*N=bpow radix2 (@common.emin t+fprec t+1).
{ unfold N. transitivity
    (bpow radix2 2*bpow radix2 (@common.emin t+fprec t-1));
    [change (bpow radix2 2) with (4:R);ring|].
  rewrite -bpow_plus. f_equal;ring. }
set ch := BMULT xh mh.
set cl1 := Fast2Mult_err xh mh.
set tl0 := BMULT xl ml.
set tl1 := BFMA xh ml tl0.
set cl2 := BFMA xl mh tl1.
set cl3 := BPLUS cl1 cl2.
have Fch : is_finite ch=true by
  (unfold ch;exact (DWMulDW_acc.FINmul xh xl mh ml FIN)).
have F0 : is_finite tl0=true by
  (unfold tl0;exact (DWMulDW_acc.FINtl0 xh xl mh ml FIN)).
have F1 : is_finite tl1=true by
  (unfold tl1,tl0;exact (DWMulDW_acc.FINtl1 xh xl mh ml FIN)).
have F2 : is_finite cl2=true by
  (unfold cl2,tl1,tl0;exact (DWMulDW_acc.FINcl2 xh xl mh ml FIN)).
have F3 : is_finite cl3=true by
  (unfold cl3,cl1,cl2,tl1,tl0;
   exact (DWMulDW_acc.FINcl3 xh xl mh ml FIN)).
have Ffast := Fast2Mult_acc_helpers.Fast2Mult_finite_unconditional xh mh Fch.
have Fcl1 : is_finite cl1=true by exact (proj2 Ffast).
have Htl00 := DWMulDW_acc.leading_product_gap_low_low_zero
  xh xl mh ml DWx DWm F0 Hgap.
fold tl0 in Htl00.
have Hdelta := Fast2Mult_sum_error_floor xh mh ltac:(lia) Ffast.
fold P0 ch cl1 eta in Hdelta.
have H1r : FT2R tl1=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
    (FT2R xh*FT2R ml).
{ unfold tl1. rewrite -(BFMA_round_correct t xh ml tl0 F1) Htl00.
  f_equal;ring. }
have He1 : Rabs (FT2R tl1-FT2R xh*FT2R ml) <= /2*eta.
{ rewrite H1r. eapply Rle_trans.
  - apply DWMulDW_acc.round_FLT_error_below_binade with(k:=0%Z);
      [lia|].
    replace (@common.emin t+fprec t+0)%Z with
      (@common.emin t+fprec t)%Z by ring.
    rewrite -HtwoN. nra.
  - right. unfold eta.
    replace (@common.emin t+0)%Z with (@common.emin t) by ring.
    reflexivity. }
have HNfmt : generic_format radix2
    (SpecFloat.fexp (fprec t) (femax t)) N.
{ unfold N. apply generic_format_bpow. unfold SpecFloat.fexp,FLT_exp.
  unfold common.emin,SpecFloat.emin. lia. }
have Htl1N : Rabs (FT2R tl1) <= N.
{ rewrite H1r -round_NE_abs.
  rewrite -(round_generic radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) N HNfmt).
  apply round_le; [exact valid_fexp_inst|apply valid_rnd_N|].
  eapply Rle_trans; [exact Hxhml|]. lra. }
set a2 := FT2R xl*FT2R mh+FT2R tl1.
have Ha2 : Rabs a2 < 2*N.
{ unfold a2. eapply Rle_lt_trans; [apply Rabs_triang|]. nra. }
have H2r : FT2R cl2=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) a2.
{ unfold cl2,a2. symmetry;exact (BFMA_round_correct t xl mh tl1 F2). }
have He2 : Rabs (FT2R cl2-a2) <= /2*eta.
{ rewrite H2r. eapply Rle_trans.
  - apply DWMulDW_acc.round_FLT_error_below_binade with(k:=0%Z);
      [lia|].
    replace (@common.emin t+fprec t+0)%Z with
      (@common.emin t+fprec t)%Z by ring.
    rewrite -HtwoN. exact Ha2.
  - right. unfold eta.
    replace (@common.emin t+0)%Z with (@common.emin t) by ring.
    reflexivity. }
have H2Nfmt : generic_format radix2
    (SpecFloat.fexp (fprec t) (femax t)) (2*N).
{ rewrite HtwoN. apply generic_format_bpow.
  unfold SpecFloat.fexp,FLT_exp,common.emin,SpecFloat.emin. lia. }
have Hcl2N : Rabs (FT2R cl2) <= 2*N.
{ rewrite H2r -round_NE_abs.
  rewrite -(round_generic radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) (2*N) H2Nfmt).
  apply round_le; [exact valid_fexp_inst|apply valid_rnd_N|]. lra. }
have Hcl1N : Rabs (FT2R cl1) <= /2*N.
{ have Hc := Fast2Mult_acc.Fast2Mult_accuracy_norm xh mh Fch.
  fold cl1 P0 in Hc.
  have HgapP : Rabs P0 <
      bpow radix2 (@common.emin t+fprec t+(fprec t-1)).
  { change (P < T) in Hgap. unfold T in Hgap.
    replace (@common.emin t+fprec t+(fprec t-1))%Z with
      (@common.emin t+2*fprec t-1)%Z by ring.
    exact Hgap. }
  have Hb := DWMulDW_acc.half_ulp_FLT_below_binade
    (t:=t) P0 (fprec t-1) ltac:(lia) HgapP.
  unfold N. eapply Rle_trans; [exact Hc|].
  replace (@common.emin t+fprec t-1)%Z with
    (@common.emin t+(fprec t-1))%Z by ring.
  exact Hb. }
set a3 := FT2R cl1+FT2R cl2.
have Ha3 : Rabs a3 < 4*N.
{ unfold a3. eapply Rle_lt_trans; [apply Rabs_triang|]. nra. }
have H3r : FT2R cl3=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) a3.
{ unfold cl3,a3. symmetry;exact (BPLUS_round_correct t cl1 cl2 F3). }
have He3 : Rabs (FT2R cl3-a3) <= eta.
{ rewrite H3r.
  have H := DWMulDW_acc.round_FLT_error_below_binade
    (t:=t) a3 1%Z ltac:(lia)
      ltac:(replace (@common.emin t+fprec t+1)%Z with
        (@common.emin t+fprec t+1)%Z by ring;
        rewrite -HfourN;exact Ha3).
  eapply Rle_trans; [exact H|]. unfold eta.
  rewrite (bpow_plus radix2 (@common.emin t) 1).
  change (bpow radix2 1) with (2:R). ring_simplify; lra. }
have H4Nfmt : generic_format radix2
    (SpecFloat.fexp (fprec t) (femax t)) (4*N).
{ rewrite HfourN. apply generic_format_bpow.
  unfold SpecFloat.fexp,FLT_exp,common.emin,SpecFloat.emin. lia. }
have Hcl3N : Rabs (FT2R cl3) <= 4*N.
{ rewrite H3r -round_NE_abs.
  rewrite -(round_generic radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) (4*N) H4Nfmt).
  apply round_le; [exact valid_fexp_inst|apply valid_rnd_N|]. lra. }
have Hcherr := round_FLT_error_rel_emin (t:=t) P0.
fold u eta in Hcherr.
have Hchr : FT2R ch=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) P0.
{ unfold ch. symmetry;exact (BMULT_round_correct t xh mh Fch). }
rewrite -Hchr in Hcherr.
fold P in Hcherr.
have HetaP : eta <= 4*u^2*P.
{ change (eta <= 4*u^2*P). unfold P,P0,mh.
  exact Heta. }
have Hchlo : (1-u-2*u^2)*P <= Rabs (FT2R ch).
{ have Htri := Rabs_triang (P0-FT2R ch) (FT2R ch).
  replace (P0-FT2R ch+FT2R ch) with P0 in Htri by ring.
  fold P in Htri.
  replace (P0-FT2R ch) with (-(FT2R ch-P0)) in Htri by ring.
  rewrite Rabs_Ropp in Htri.
  set A := u*P. set B := u^2*P.
  have HerrAB : Rabs (FT2R ch-P0) <= A+2*B.
  { unfold A,B. nra. }
  replace ((1-u-2*u^2)*P) with (P-A-2*B) by (unfold A,B;ring).
  nra. }
have HNP : N <= 2*u*P.
{ rewrite -HuT. replace (2*u*P) with (u*(2*P)) by ring.
  apply Rmult_le_compat_l; [lra|]. nra. }
have Hord : Rabs (FT2R cl3) <= Rabs (FT2R ch).
{ eapply Rle_trans; [exact Hcl3N|]. eapply Rle_trans; [|exact Hchlo].
  have H := Rmult_le_compat_l 4 _ _ ltac:(lra) HNP. nra. }
have Hsum := FastTwoSum_correct ch cl3 (proj1 FIN) Hord.
set zh := Fast2Sum_sum ch cl3.
set zl := Fast2Sum_err ch cl3.
fold zh zl in Hsum.
have HsumE : FT2R zh+FT2R zl=FT2R ch+FT2R cl3.
{ rewrite Hsum. ring. }
have Herr : Rabs ((FT2R ch+FT2R cl3)-X*M) <=
    5/2*eta+u^2*P.
{ fold ch in Hdelta.
  set A := FT2R ch+FT2R cl1-P0.
  set B := -FT2R xl*FT2R ml.
  set C := FT2R tl1-FT2R xh*FT2R ml.
  set D := FT2R cl2-a2.
  set E := FT2R cl3-a3.
  have Heq : (FT2R ch+FT2R cl3)-X*M = A+B+C+D+E.
  { unfold A,B,C,D,E,X,M,a2,a3,P0. ring. }
  rewrite Heq.
  have Ht1 := Rabs_triang (A+B+C+D) E.
  have Ht2 := Rabs_triang (A+B+C) D.
  have Ht3 := Rabs_triang (A+B) C.
  have Ht4 := Rabs_triang A B.
  have Htri : Rabs (A+B+C+D+E) <=
      Rabs A+Rabs B+Rabs C+Rabs D+Rabs E.
  { eapply Rle_trans; [exact Ht1|]. apply Rplus_le_compat_r.
    eapply Rle_trans; [exact Ht2|]. apply Rplus_le_compat_r.
    eapply Rle_trans; [exact Ht3|]. apply Rplus_le_compat_r.
    exact Ht4. }
  have Hlow : Rabs B <= u^2*P
    by unfold B; replace (-FT2R xl*FT2R ml) with (-(FT2R xl*FT2R ml)) by ring;
       rewrite Rabs_Ropp;exact Hxlml.
  fold A in Hdelta. fold C in He1. fold D in He2. fold E in He3.
  eapply Rle_trans; [exact Htri|].
  eapply Rle_trans.
  - apply Rplus_le_compat; [|exact He3].
    apply Rplus_le_compat; [|exact He2].
    apply Rplus_le_compat; [|exact He1].
    apply Rplus_le_compat; [exact Hdelta|exact Hlow].
  - ring_simplify. lra. }
have HXM := DWMulDW_acc.aux_dw_exact_product_lower xh xl mh ml DWx DWm.
fold u X M P0 P in HXM.
specialize (HXM STD).
change (Rabs (zr-X*M) <= 4*u^2*Rabs (X*M)+2*eta).
change (Rabs ((FT2R zh+FT2R zl)-X*M) <=
  4*u^2*Rabs (X*M)+2*eta).
rewrite HsumE. eapply Rle_trans; [exact Herr|].
have Hreserve : /2*eta+u^2*P <= 4*u^2*Rabs (X*M).
{ have Hbase : 3*u^2*P <= 4*u^2*((1-u)^2*P) by nra.
  eapply Rle_trans; [|eapply Rle_trans; [exact Hbase|]].
  - nra.
  - apply Rmult_le_compat_l; [nra|exact HXM]. }
nra.
- have Nprod : T <= P.
  { have HT0 : 0<T by (unfold T;apply bpow_gt_0).
    have Hcoef : T<=9/8*T by (clear -HT0;nra).
    eapply Rle_trans; [exact Hcoef|apply Rlt_le;exact Hfar]. }
  destruct (Rle_or_lt N (Rabs (FT2R xl*FT2R ml))) as [N0|U0].
  + have Hmul := DWMulDW_acc.DWTimesDW_abs_low0_normal
      xh xl mh ml DWx DWm FIN ltac:(lia) Nprod N0.
    fold X M zr u in Hmul. cbv zeta in Hmul.
    eapply Rle_trans; [exact Hmul|]. nra.
  + destruct (Rle_or_lt N
      (Rabs (FT2R (Fast2Mult_err xh mh)+
        FT2R (BFMA xl mh (BFMA xh ml (BMULT xl ml))))))
      as [N3|U3].
    * destruct (Rle_or_lt N
        (Rabs (FT2R xh*FT2R ml+FT2R (BMULT xl ml)))) as [N1|U1].
      -- destruct (Rle_or_lt N
          (Rabs (FT2R xl*FT2R mh+
            FT2R (BFMA xh ml (BMULT xl ml))))) as [N2|U2].
         ++ have Hmul := DWMulDW_acc.DWTimesDW_abs_low0_far
              xh xl mh ml DWx DWm FIN ltac:(lia)
              Hfar U0 N1 N2 N3.
            fold X M zr u eta in Hmul. cbv zeta in Hmul. exact Hmul.
         ++ have Hmul := DWMulDW_acc.DWTimesDW_abs_low0_low2_other_normal
              xh xl mh ml DWx DWm FIN Hp14 Nprod U0 N1 U2 N3.
            fold X M zr u eta in Hmul. cbv zeta in Hmul. exact Hmul.
      -- destruct (Rle_or_lt N
          (Rabs (FT2R xl*FT2R mh+
            FT2R (BFMA xh ml (BMULT xl ml))))) as [N2|U2].
         ++ have Hmul := DWMulDW_acc.DWTimesDW_abs_low0_low1_tail_normal
              xh xl mh ml DWx DWm FIN Hp14 Nprod U0 U1 N2 N3.
            fold X M zr u eta in Hmul. cbv zeta in Hmul. exact Hmul.
         ++ have Hmul := DWMulDW_acc.DWTimesDW_abs_low0_low1_low2_final_normal
              xh xl mh ml DWx DWm FIN Hp14 Nprod U0 U1 U2 N3.
            fold X M zr u eta in Hmul. cbv zeta in Hmul. exact Hmul.
    * have Hmul := DWMulDW_acc.DWTimesDW_abs_low0_final_underflow
        xh xl mh ml DWx DWm FIN Hp14 Nprod U0 U3.
      fold X M zr u eta in Hmul. cbv zeta in Hmul. exact Hmul.
Qed.

(** Coefficient-parametric form of the composition.  Pure real arithmetic: the
    reciprocal reconstruction's three coefficients stay symbolic, so the two
    arms of the refinement split can instantiate it with their own constants
    instead of each needing its own copy of the float-level assembly.  The
    conclusion is an exact identity in those coefficients -- nothing is
    rounded up here. *)
Lemma DWDivDW_mixed_closing_composition_param
    (u eta X Y Q M zr a bx bq : R) :
  0 <= u -> u <= /16384 -> 0 <= eta -> Y <> 0 -> Q = X/Y ->
  Rabs (X*(M-/Y)) <=
    a*u^2*Rabs Q+bx*eta*Rabs X+bq*eta*Rabs Q ->
  Rabs (zr-X*M) <= 4*u^2*Rabs (X*M)+2*eta ->
  Rabs (zr-Q) <=
    (4+a*(1+4*u^2))*u^2*Rabs Q+
    (bx*(1+4*u^2))*eta*Rabs X+
    (bq*(1+4*u^2))*eta*Rabs Q+2*eta.
Proof.
move => Hu0 Hu Heta0 HYne HQ Hrec Hclose.
have HX0 : 0 <= Rabs X by apply Rabs_pos.
have HQ0 : 0 <= Rabs Q by apply Rabs_pos.
have HXM : Rabs (X*M) <= Rabs Q+
    (a*u^2*Rabs Q+bx*eta*Rabs X+bq*eta*Rabs Q).
{ have Heq : X*M=Q+X*(M-/Y).
  { rewrite HQ. field; exact HYne. }
  rewrite Heq. eapply Rle_trans; [apply Rabs_triang|].
  apply Rplus_le_compat_l. exact Hrec. }
have Hclosing : Rabs (zr-X*M) <=
    4*u^2*(Rabs Q+
      (a*u^2*Rabs Q+bx*eta*Rabs X+bq*eta*Rabs Q))+2*eta.
{ eapply Rle_trans; [exact Hclose|].
  apply Rplus_le_compat_r.
  apply Rmult_le_compat_l; [nra|exact HXM]. }
have Heq : zr-Q=(zr-X*M)+X*(M-/Y).
{ rewrite HQ. field; exact HYne. }
rewrite Heq. eapply Rle_trans; [apply Rabs_triang|].
eapply Rle_trans.
- apply Rplus_le_compat; [exact Hclosing|exact Hrec].
- right; ring.
Qed.

(** Generic conversion of a mixed physical-floor estimate with symbolic
    coefficients into a pure relative bound.  Pure real arithmetic: each arm of
    the refinement split supplies its own [(a,bx,bq)] and its own budget
    check. *)
Lemma DWDivDW_relative_of_mixed_param
    (u eta X Q zr a bx bq c : R) :
  0 < u -> Q <> 0 ->
  0 <= bx -> 0 <= bq ->
  Rabs (zr-Q) <=
    a*u^2*Rabs Q+bx*eta*Rabs X+bq*eta*Rabs Q+2*eta ->
  eta*Rabs X <= 201/100*(1001/1000)*u^2*Rabs Q ->
  eta <= u^2 ->
  eta <= 201/100*u^2*Rabs Q ->
  a+bx*(201/100*(1001/1000))+bq+2*(201/100) <= c ->
  Rabs ((zr-Q)/Q) <= c*u^2.
Proof.
move => Hu0 HQne Hbx Hbq Habs HX Hetau2 Heta Hbud.
have HQabs : 0 < Rabs Q by apply Rabs_pos_lt.
have Hu2Q : 0 <= u^2*Rabs Q.
{ apply Rmult_le_pos; [apply pow_le; lra|lra]. }
have H1 : bx*(eta*Rabs X) <= bx*(201/100*(1001/1000)*(u^2*Rabs Q)).
{ apply Rmult_le_compat_l; [exact Hbx|].
  eapply Rle_trans; [exact HX|]. right; ring. }
have HQ' : eta*Rabs Q <= u^2*Rabs Q.
{ apply Rmult_le_compat_r; [lra|exact Hetau2]. }
have H2 : bq*(eta*Rabs Q) <= bq*(u^2*Rabs Q).
{ apply Rmult_le_compat_l; [exact Hbq|exact HQ']. }
have H3 : 2*eta <= 2*(201/100*(u^2*Rabs Q)).
{ apply Rmult_le_compat_l; [lra|].
  eapply Rle_trans; [exact Heta|]. right; ring. }
have H4 : (a+bx*(201/100*(1001/1000))+bq+2*(201/100))*(u^2*Rabs Q)
    <= c*(u^2*Rabs Q).
{ apply Rmult_le_compat_r; [exact Hu2Q|exact Hbud]. }
have Herr : Rabs (zr-Q) <= c*u^2*Rabs Q.
{ eapply Rle_trans; [exact Habs|]. nra. }
rewrite Rabs_mult Rabs_inv.
apply (Rmult_le_reg_r (Rabs Q)); [exact HQabs|].
rewrite Rmult_assoc Rinv_l; [rewrite Rmult_1_r; exact Herr|].
apply Rgt_not_eq; exact HQabs.
Qed.

(** Master two-arm theorem.  The refinement split of
    [DWDivDW_refinement_product_value_error_tight_floor] is destructed here,
    and each arm carries its own reciprocal coefficients through the shared
    parametric assembly:

    - ordered arm: Algorithm 9's closing Fast2Sum is exact, so the refinement
      floor is [eta] rather than [2*eta] ([fr = 1]), while the Newton
      remainder keeps its generic [2.298] coefficient;
    - unordered arm: the refinement floor stays at [2*eta] ([fr = 2]), but the
      reciprocal residual is itself [O(u^2)], so the Newton remainder is
      fourth order and its coefficient collapses.

    The arm-specific constants remain separate until the final relative-error
    conversion, yielding the regime-independent coefficient [16.5]. *)
Local Theorem relative_errorDWDivDW3_from_cond_arms
    (xh xl yh yl : ftype t) :
  (14 <= fprec t)%Z -> DWDivDW_cond xh xl yh yl ->
  let X := FT2R xh+FT2R xl in
  let Q := X/(FT2R yh+FT2R yl) in
  let zr := FT2R (fst (DWDivDW3 xh xl yh yl))+
            FT2R (snd (DWDivDW3 xh xl yh yl)) in
  Rabs ((zr-Q)/Q) <= 165/10*bpow radix2 (-fprec t)^2.
Proof.
move => Hp14 COND /=.
set th := BDIV (Zconst t 1) yh.
set rh := BFMA (BOPP yh) th (Zconst t 1).
set rl := BOPP (BMULT yl th).
set e := Fast2Sum rh rl.
set d := DWTimesFP3 (fst e) (snd e) th.
set m := DWPlusFP (fst d) (snd d) th.
set X := FT2R xh+FT2R xl.
set Y := FT2R yh+FT2R yl.
set Q := X/Y.
set zr := FT2R (fst (DWDivDW3 xh xl yh yl))+
          FT2R (snd (DWDivDW3 xh xl yh yl)).
set u := bpow radix2 (-fprec t).
set eta := bpow radix2 (@common.emin t).
set M := FT2R (fst m)+FT2R (snd m).
set D := FT2R (fst d)+FT2R (snd d).
set E := FT2R (fst e)+FT2R (snd e).
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /16384.
{ unfold u. have -> : (/16384:R)=bpow radix2 (-14) by (simpl;lra).
  apply bpow_le; lia. }
have Hu2b : u^2 <= /16384*(/16384).
{ replace (u^2) with (u*u) by ring. apply Rmult_le_compat; lra. }
have Heta0 : 0 <= eta by (unfold eta; apply bpow_ge_0).
have HX0 : 0 <= Rabs X by apply Rabs_pos.
have HQ0 : 0 <= Rabs Q by apply Rabs_pos.
have Hyhne := DWDivDW_cond_yh_nonzero xh xl yh yl COND.
move: (COND) => [_ [_ [_ [_ [DWx [DWy [_ [Hqwin _]]]]]]]].
have HYne : Y<>0.
{ intro HY0. apply Hyhne.
  move: DWy. rewrite /double_word_prop -/Y HY0 /rounded round_0.
  by move => ->. }
have HQX : Rabs X*Rabs (/Y)=Rabs Q.
{ unfold Q, Rdiv. rewrite Rabs_mult. reflexivity. }
have HQne : Q<>0.
{ have Hxhne : FT2R xh<>0.
  { intro H0. move: Hqwin.
    rewrite H0 /Rdiv Rmult_0_l Rabs_R0 => Hbad.
    have Hb := bpow_gt_0 radix2 (@common.emin t+2*fprec t-1).
    exact (Rlt_not_le _ _ Hb Hbad). }
  have HXne : X<>0.
  { intro HXzero. apply Hxhne.
    move: DWx. rewrite /double_word_prop -/X HXzero /rounded round_0.
    by move => ->. }
  unfold Q, Rdiv. apply Rmult_integral_contrapositive_currified;
    [exact HXne|apply Rinv_neq_0_compat; exact HYne]. }
(* ---- the closing block, identical in both arms ---------------------- *)
have Hclose : Rabs (zr-X*M) <= 4*u^2*Rabs (X*M)+2*eta.
{ have H := DWDivDW3_closing_mixed_error_from_cond
    xh xl yh yl Hp14 COND.
  fold th rh rl e d m in H. cbv zeta in H.
  fold X M zr u eta in H. exact H. }
(* ---- the three scale conversions, identical in both arms ------------ *)
have Hsc := DWDivDW_eta_scales_from_cond_tight xh xl yh yl Hp14 COND.
specialize (Hsc NANS STD). fold th u eta in Hsc.
destruct Hsc as [_ HetaT].
have Hscale := DWDivDW_X_th_quotient_scale_from_cond
  xh xl yh yl Hp14 COND.
fold th in Hscale. cbv zeta in Hscale. fold X Y Q in Hscale.
rewrite Rabs_mult in Hscale.
set T := Rabs (FT2R th) in HetaT, Hscale.
have HetaX : eta*Rabs X <= 201/100*(1001/1000)*u^2*Rabs Q.
{ have Hx := Rmult_le_compat_r (Rabs X) _ _ HX0 HetaT.
  eapply Rle_trans; [exact Hx|].
  replace ((201/100*u^2*T)*Rabs X)%R with
    (201/100*u^2*(Rabs X*T))%R by ring.
  have Hc : 0 <= 201/100*u^2 by nra.
  have Hs := Rmult_le_compat_l (201/100*u^2) _ _ Hc Hscale.
  eapply Rle_trans; [exact Hs|].
  apply Req_le. ring. }
have Hetau2 : eta <= u^2.
{ unfold eta, u, common.emin.
  exact (DWDivDW_cond_eta_le_u2 xh xl yh yl COND). }
have HetaOut := DWDivDW_eta_absorbed_by_quotient_tight
  xh xl yh yl Hp14 COND.
specialize (HetaOut STD). fold u eta in HetaOut.
fold X Y Q in HetaOut.
(* ---- destruct the refinement arms ---------------------------------- *)
have Harms := @DWDivDW_refinement_product_value_error_tight_floor
  NANS t STD xh xl yh yl Hp14 COND.
cbv zeta in Harms.
destruct Harms as [Htight|[Hcoarse Hsmall]].
- (* ===== ordered arm: fr = 1, nw = 2.298 ===== *)
  have Href := DWDivDW_refinement_product_error_scaled_param
    xh xl yh yl 36 1 Hp14 COND ltac:(lra) ltac:(lra) ltac:(lra).
  cbv zeta in Href. specialize (Href Htight).
  have Hnew := DWDivDW_newton_step_error_tight_from_cond
    xh xl yh yl Hp14 COND.
  fold th Y u in Hnew. cbv zeta in Hnew.
  have HnewX : Rabs (X*(FT2R th+(1-Y*FT2R th)*FT2R th-/Y)) <=
      2298/1000*u^2*Rabs Q.
  { rewrite Rabs_mult.
    have Hmul := Rmult_le_compat_l (Rabs X) _ _ HX0 Hnew.
    eapply Rle_trans; [exact Hmul|]. right.
    rewrite -HQX. ring. }
  have Hrec := DWDivDW_reciprocal_error_scaled_floor_param
    xh xl yh yl 1 (2298/1000) Hp14 COND ltac:(lra) ltac:(lra).
  cbv zeta in Hrec. specialize (Hrec Href HnewX).
  fold M in Hrec.
  have Hcomp := DWDivDW_mixed_closing_composition_param
    u eta X Y Q M zr
    (2+(2298/1000+1013/1000)*(1+2*u^2))
    (1*(1+2*u^2))
    (1001/1000*(1+2*u^2))
    ltac:(lra) Hu Heta0 HYne eq_refl Hrec Hclose.
  apply (DWDivDW_relative_of_mixed_param u eta X Q zr
    (4+(2+(2298/1000+1013/1000)*(1+2*u^2))*(1+4*u^2))
    ((1*(1+2*u^2))*(1+4*u^2))
    ((1001/1000*(1+2*u^2))*(1+4*u^2))
    (165/10) Hu0 HQne ltac:(nra) ltac:(nra)
    Hcomp HetaX Hetau2 HetaOut).
  nra.
- (* ===== unordered arm: fr = 2, nw collapses ===== *)
  have Href := DWDivDW_refinement_product_error_scaled_param
    xh xl yh yl 140 2 Hp14 COND ltac:(lra) ltac:(lra) ltac:(lra).
  cbv zeta in Href. specialize (Href Hcoarse).
  have HDWy : DWPlus.double_word (fprec t) choice (FT2R yh) (FT2R yl).
  { apply (dw_word_DWdouble yh yl yh). exact DWy. }
  have Hth := DWDivDW_th_FLT_FLX_from_cond xh xl yh yl COND.
  have Hnw0 := flx_newton_step_error_of_residual
    (FT2R yh) (FT2R yl) (72*u^2) HDWy Hyhne.
  cbv zeta in Hnw0. rewrite Hth in Hnw0.
  fold Y in Hnw0.
  have Hnw := Hnw0 Hsmall.
  have Hstep : (72*u^2)^2 <= 1/10*u^2.
  { replace ((72*u^2)^2)%R with ((5184*u^2)*u^2)%R by ring.
    have Hc : 0 <= 5184*u^2 by nra.
    have H := Rmult_le_compat_l (5184*u^2) _ _ Hc Hu2b.
    eapply Rle_trans; [exact H|]. nra. }
  have HnewX : Rabs (X*(FT2R th+(1-Y*FT2R th)*FT2R th-/Y)) <=
      1/10*u^2*Rabs Q.
  { rewrite Rabs_mult.
    have Hmul := Rmult_le_compat_l (Rabs X) _ _ HX0 Hnw.
    eapply Rle_trans; [exact Hmul|].
    have Hfac : Rabs X*((72*u^2)^2*Rabs (/Y)) =
        (72*u^2)^2*Rabs Q.
    { rewrite -HQX. ring. }
    rewrite Hfac.
    apply Rmult_le_compat_r; [exact HQ0|exact Hstep]. }
  have Hrec := DWDivDW_reciprocal_error_scaled_floor_param
    xh xl yh yl 2 (1/10) Hp14 COND ltac:(lra) ltac:(lra).
  cbv zeta in Hrec. specialize (Hrec Href HnewX).
  fold M in Hrec.
  have Hcomp := DWDivDW_mixed_closing_composition_param
    u eta X Y Q M zr
    (2+(1/10+1013/1000)*(1+2*u^2))
    (2*(1+2*u^2))
    (1001/1000*(1+2*u^2))
    ltac:(lra) Hu Heta0 HYne eq_refl Hrec Hclose.
  apply (DWDivDW_relative_of_mixed_param u eta X Q zr
    (4+(2+(1/10+1013/1000)*(1+2*u^2))*(1+4*u^2))
    ((2*(1+2*u^2))*(1+4*u^2))
    ((1001/1000*(1+2*u^2))*(1+4*u^2))
    (165/10) Hu0 HQne ltac:(nra) ltac:(nra)
    Hcomp HetaX Hetau2 HetaOut).
  nra.
Qed.

End PaperModelDWDivDW.

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
Hypothesis UF_rh   : bpow radix2 (emin + fprec t - 1)
  <= Rabs (1 - FT2R yh * FT2R th).
Hypothesis UF_rl   : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R yl * FT2R th).
(* Normal-range hypotheses consumed by the composed multiplication bridges. *)
Hypothesis UF_dprod : bpow radix2 (emin + 2 * fprec t - 1)
  <= Rabs (FT2R eh * FT2R th).
Hypothesis UF_dlow : bpow radix2 (emin + fprec t - 1)
  <= Rabs (FT2R el * FT2R th + FT2R (Fast2Mult_err eh th)).
Hypothesis UF_zprod : bpow radix2 (emin + 2 * fprec t - 1)
  <= Rabs (FT2R xh * FT2R mh).
Hypothesis UF_z0 : bpow radix2 (emin + fprec t - 1)
  <= Rabs (FT2R xl * FT2R ml).
Hypothesis UF_z1 : bpow radix2 (emin + fprec t - 1)
  <= Rabs (FT2R xh * FT2R ml + FT2R (BMULT xl ml)).
Hypothesis UF_z2 : bpow radix2 (emin + fprec t - 1)
  <= Rabs (FT2R (BFMA xh ml (BMULT xl ml)) + FT2R xl * FT2R mh).
Hypothesis UF_z3 : bpow radix2 (emin + fprec t - 1)
  <= Rabs (FT2R (Fast2Mult_err xh mh)
             + FT2R (BFMA xl mh (BFMA xh ml (BMULT xl ml)))).

(** The finite-precision runtime computation [DDModels.DWDivDW3] denotes the
    same real pair as the paper's FLX computation.

    The lower-bound hypotheses exclude underflow at the reciprocal,
    low-product, and error-sum nodes, allowing FLT rounding to be replaced by
    FLX rounding.  This equality is the link used by
    [relative_errorDWDivDW3_correct] to reuse the paper-level error bound.

    The hypotheses enumerate the normal-range obligations required by the
    reciprocal prologue and the two composed multiplication bridges. *)
Lemma DWDivDW3_FLX_FLT :
  F2Rp (DWDivDW3 xh xl yh yl)
    = DWDivDW3_FLX_model xh xl yh yl.
Proof.
unfold DWDivDW3_FLX_model, DWDivDW_reciprocal_FLX_model.
have Fth := FIN_th xh xl yh yl FIN.
have Frh := FIN_rh xh xl yh yl FIN.
have Frl := FIN_rl xh xl yh yl FIN.
have Fe := FIN_fast2sum xh xl yh yl FIN.
have Fd := FIN_timesfp xh xl yh yl FIN.
have Fm := FIN_plus xh xl yh yl FIN.
have Fz := FIN_mul xh xl yh yl FIN.
have Hyfmt : generic_format radix2 (FLX_exp (fprec t)) (FT2R yh).
{ apply (generic_format_FLX_FLT radix2
           (SpecFloat.emin (fprec t) (femax t)) (fprec t)).
  apply generic_format_FLT_FT2R. }
have Hth : rnd_p (/ FT2R yh) = FT2R th.
{ rewrite -(BDIV_round_correct t (Zconst t 1) yh Hyhne Fth).
  have Hone : FT2R (Zconst t 1) = 1%R.
  { rewrite /Zconst FT2R_ftype_of_float.
    have Hpow : (0 < 2 ^ fprec t)%Z.
    { apply Z.pow_pos_nonneg; lia. }
    have Hrange : (- 2 ^ fprec t <= 1 <= 2 ^ fprec t)%Z by lia.
    have Hexact := proj1 (IEEE754_extra.BofZ_exact
                            (fprec t) (femax t) _ _ 1 Hrange).
    rewrite Hexact; reflexivity. }
  rewrite Hone Rdiv_1_l.
  symmetry; apply round_FLT_FLX.
  have Hnormal := UF_th.
  rewrite Rdiv_1_l in Hnormal; exact Hnormal. }
have Hrh : (1 - FT2R yh * FT2R th)%R = FT2R rh.
{ have Hg := @DWDivDW.Prop7_2 (fprec t) (fprec_gt_one t) choice eq_refl
                 (FT2R yh) Hyfmt Hyhne.
  rewrite Hth in Hg.
  have Hg' : generic_format radix2 (FLX_exp (fprec t))
      (1 - FT2R yh * FT2R th).
  { replace (1 - FT2R yh * FT2R th)%R
      with (- (FT2R yh * FT2R th - 1))%R by ring.
    apply generic_format_opp; exact Hg. }
  rewrite -(BFMA_round_correct t (BOPP yh) th (Zconst t 1) Frh).
  have Hyhfin := FIN_yh xh xl yh yl FIN.
  have Hopp : (- FT2R yh = FT2R (BOPP yh))%R :=
    @BOPP_binary t NANS STD yh (or_intror Hyhfin).
  have Hone : FT2R (Zconst t 1) = 1%R.
  { rewrite /Zconst FT2R_ftype_of_float.
    have Hpow : (0 < 2 ^ fprec t)%Z.
    { apply Z.pow_pos_nonneg; lia. }
    have Hrange : (- 2 ^ fprec t <= 1 <= 2 ^ fprec t)%Z by lia.
    have Hexact := proj1 (IEEE754_extra.BofZ_exact
                            (fprec t) (femax t) _ _ 1 Hrange).
    rewrite Hexact; reflexivity. }
  rewrite -Hopp Hone.
  replace (- FT2R yh * FT2R th + 1)%R
    with (1 - FT2R yh * FT2R th)%R by ring.
  rewrite (round_FLT_FLX radix2 emin (fprec t) (Znearest choice)
             (1 - FT2R yh * FT2R th) UF_rh).
  symmetry; apply round_generic;
    [exact (Generic_fmt.valid_rnd_N choice) | exact Hg']. }
have Hrl : (- rnd_p (FT2R yl * FT2R th))%R = FT2R rl.
{ have Hmul : is_finite (BMULT yl th) = true.
  { exact (proj1 (BOPP_is_finite t (BMULT yl th)) Frl). }
  rewrite -(@BOPP_binary t NANS STD (BMULT yl th) (or_introl Frl)).
  rewrite -(BMULT_round_correct t yl th Hmul).
  f_equal.
  symmetry; apply round_FLT_FLX; exact UF_rl. }
have Heq : F2Sum.Fast2Sum (fprec t) choice (FT2R rh) (FT2R rl)
             = F2Rp (Fast2Sum rh rl).
{ exact (FastTwoSumEq_FLT rh rl Fe). }
have Hd : DWTimesFP.DWTimesFP9 (fprec t) choice
              (FT2R eh) (FT2R el) (FT2R th)
            = F2Rp (DWTimesFP3 eh el th).
{ exact (DWMulFP_acc.DWTimesFP3_FLX_FLT_weak eh el th Fd
           UF_dprod UF_dlow). }
have Hm : DWPlus.DWPlusFP (fprec t) choice
              (FT2R dh) (FT2R dl) (FT2R th)
            = F2Rp (DWPlusFP dh dl th).
{ exact (DWPlusFP_acc_helpers.DWPlusFP_eq dh dl th Fm). }
have Hz : DWTimesDW.DWTimesDW12 (fprec t) choice
              (FT2R xh) (FT2R xl) (FT2R mh) (FT2R ml)
            = F2Rp (DWTimesDW3 xh xl mh ml).
{ exact (DWMulDW_acc.DWTimesDW3_FLX_FLT xh xl mh ml Fz
           UF_zprod UF_z0 UF_z1 UF_z2 UF_z3). }
have Heh := f_equal fst Heq.
have Hel := f_equal snd Heq.
have Hdh := f_equal fst Hd.
have Hdl := f_equal snd Hd.
have Hmh := f_equal fst Hm.
have Hml := f_equal snd Hm.
rewrite /F2Rp /= in Heh Hel Hdh Hdl Hmh Hml.
rewrite Hth /= Hrh Hrl /=.
rewrite -Hz -Hmh -Hml -Hdh -Hdl -Heh -Hel.
reflexivity.
Qed.

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
Notation th  := (BDIV (Zconst t 1) yh).
Notation rh  := (BFMA (BOPP yh) th (Zconst t 1)).
Notation rl  := (BOPP (BMULT yl th)).
Notation eh  := (fst (Fast2Sum rh rl)).
Notation el  := (snd (Fast2Sum rh rl)).
Notation dh  := (fst (DWTimesFP3 eh el th)).
Notation dl  := (snd (DWTimesFP3 eh el th)).
Notation mh  := (fst (DWPlusFP dh dl th)).
Notation ml  := (snd (DWPlusFP dh dl th)).
(* No-underflow assumptions currently exposed by [DWDivDW3_FLX_FLT]. *)
Hypothesis UF_th : bpow radix2 (emin + fprec t - 1) <= Rabs (1 / FT2R yh).
Hypothesis UF_rh : bpow radix2 (emin + fprec t - 1)
                   <= Rabs (1 - FT2R yh * FT2R th).
Hypothesis UF_rl : bpow radix2 (emin + fprec t - 1)
                   <= Rabs (FT2R yl * FT2R th).
Hypothesis UF_dprod : bpow radix2 (emin + 2 * fprec t - 1)
                      <= Rabs (FT2R eh * FT2R th).
Hypothesis UF_dlow : bpow radix2 (emin + fprec t - 1)
  <= Rabs (FT2R el * FT2R th + FT2R (Fast2Mult_err eh th)).
Hypothesis UF_zprod : bpow radix2 (emin + 2 * fprec t - 1)
                      <= Rabs (FT2R xh * FT2R mh).
Hypothesis UF_z0 : bpow radix2 (emin + fprec t - 1)
                   <= Rabs (FT2R xl * FT2R ml).
Hypothesis UF_z1 : bpow radix2 (emin + fprec t - 1)
                   <= Rabs (FT2R xh * FT2R ml + FT2R (BMULT xl ml)).
Hypothesis UF_z2 : bpow radix2 (emin + fprec t - 1)
  <= Rabs (FT2R (BFMA xh ml (BMULT xl ml)) + FT2R xl * FT2R mh).
Hypothesis UF_z3 : bpow radix2 (emin + fprec t - 1)
  <= Rabs (FT2R (Fast2Mult_err xh mh)
           + FT2R (BFMA xl mh (BFMA xh ml (BMULT xl ml)))).

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
    the runtime FLT model through the proved [DWDivDW3_FLX_FLT] bridge. *)
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
pose proof (DWDivDW3_FLX_FLT xh xl yh yl FIN Hp14 Hyhne
              UF_th UF_rh UF_rl UF_dprod UF_dlow
              UF_zprod UF_z0 UF_z1 UF_z2 UF_z3) as Hbr.
cbv zeta in Hbr.
fold (DWDivDW_reciprocal_FLX_model yh yl) in Hpaper.
fold (DWDivDW3_FLX_model xh xl yh yl) in Hpaper.
rewrite -Hbr in Hpaper.
rewrite /F2Rp in Hpaper.
cbv beta iota in Hpaper.
unfold relative_error_DWDivDW, zh, zl.
exact Hpaper.
Qed.

End FiniteAccuracyDWDivDW.

(* ============================================================
   Forward finiteness through the closing multiplication

   Once the reciprocal reconstruction has established the public condition
   of the closing [DWTimesDW3] block, its existing componentwise finiteness
   theorems provide finiteness of the complete division result.  Keeping this
   as a separate lemma makes the remaining reciprocal-range proof expose the
   precise condition it must establish rather than a collection of internal
   output-finiteness facts.
   ============================================================ *)
Section FiniteDWDivDWFromFinalBlock.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

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

(** The complete division is finite as soon as its closing multiplication
    satisfies the already-proved [DWTimesDW_cond]. *)
Lemma DWDivDW3_finite_from_final_cond :
  (4 <= fprec t)%Z ->
  DWTimesDW_cond xh xl mh ml ->
  is_finite_p (DWDivDW3 xh xl yh yl).
Proof.
move => Hp4 Hfinal.
split.
- exact (DWMulDW_acc.DWTimesDW3_fst_finite xh xl mh ml Hp4 Hfinal).
- exact (DWMulDW_acc.DWTimesDW3_snd_finite xh xl mh ml Hp4 Hfinal).
Qed.

End FiniteDWDivDWFromFinalBlock.

(* ============================================================
   Normal-regime characterization for DWDivDW3

   The nine residual/product node lower bounds below all fail in the
   worst-case type (emin+2p=2), so none is derivable from [DWDivDW_cond]
   and none is exact.  Bundled here as the single normal-regime
   characterization [DWDivDW_normal] — the DWDivDW analogue of DWDivFP's
   [Hdyn] — so the normal-leg accuracy theorem takes the DWDivFP-style
   shape [COND -> DWDivDW_normal -> bound].  [UF_th] is NOT included: it
   is derived from [DWDivDW_cond] via [DWDivDW_cond_UF_th].
   ============================================================ *)
Section NormalCharDWDivDW.
Context {NANS: Nans} {t : type} {STD: is_standard t}.
Notation emin := (common.emin (t:=t)).
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
  bpow radix2 (emin + fprec t - 1) <= Rabs (1 - FT2R yh * FT2R th) /\
  bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R yl * FT2R th) /\
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R eh * FT2R th) /\
  bpow radix2 (emin + fprec t - 1)
    <= Rabs (FT2R el * FT2R th + FT2R (Fast2Mult_err eh th)) /\
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R mh) /\
  bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xl * FT2R ml) /\
  bpow radix2 (emin + fprec t - 1)
    <= Rabs (FT2R xh * FT2R ml + FT2R (BMULT xl ml)) /\
  bpow radix2 (emin + fprec t - 1)
    <= Rabs (FT2R (BFMA xh ml (BMULT xl ml)) + FT2R xl * FT2R mh) /\
  bpow radix2 (emin + fprec t - 1)
    <= Rabs (FT2R (Fast2Mult_err xh mh)
             + FT2R (BFMA xl mh (BFMA xh ml (BMULT xl ml)))).
End NormalCharDWDivDW.

(* ============================================================
   Layer 2: normal-regime accuracy from the public condition

   [DWDivDW_cond] supplies the double-word operands, the nonzero leading
   divisor, and normality of the initial reciprocal.  It deliberately does
   not lower-bound residual nodes, since any of them may be exactly zero.
   Their bounds below are therefore the genuine normal-regime split line.
   Result finiteness remains explicit until the separate overflow cascade for
   the complete reciprocal/refinement pipeline is established.
   ============================================================ *)
Section CondAccuracyDWDivDW.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (common.emin (t:=t)).
Notation u := (bpow radix2 (- fprec t)).

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

Hypothesis Hp14 : (14 <= fprec t)%Z.
Hypothesis COND : DWDivDW_cond xh xl yh yl.

(* The nine residual/product normality facts are bundled into the single
   [DWDivDW_normal] characterization (defined above), mirroring DWDivFP's
   [COND + Hdyn] normal-leg interface. *)
Hypothesis Hnormal : DWDivDW_normal xh xl yh yl.

(** Normal-regime form of the tight paper bound using only the public input
    condition plus the single normal-regime characterization [DWDivDW_normal]
    for residual computations. *)
Theorem relative_errorDWDivDW3_from_cond_normal :
  Rabs
    ((FT2R (fst (DWDivDW3 xh xl yh yl))
       + FT2R (snd (DWDivDW3 xh xl yh yl))
       - (FT2R xh + FT2R xl) / (FT2R yh + FT2R yl))
     / ((FT2R xh + FT2R xl) / (FT2R yh + FT2R yl)))
  <= 98 / 10 * u ^ 2.
Proof.
move: (COND) =>
  [Hfxh [Hfxl [Hfyh [Hfyl [DWx [DWy _]]]]]].
move: Hnormal =>
  [UF_rh [UF_rl [UF_dprod [UF_dlow [UF_zprod
    [UF_z0 [UF_z1 [UF_z2 UF_z3]]]]]]]].
have Hyhne := DWDivDW_cond_yh_nonzero xh xl yh yl COND.
have UF_th := DWDivDW_cond_UF_th xh xl yh yl COND.
have FINAL_cond := DWDivDW_final_cond_from_cond_normal xh xl yh yl
  Hp14 COND UF_zprod.
have FIN := DWDivDW3_finite_from_final_cond xh xl yh yl ltac:(lia) FINAL_cond.
exact (relative_errorDWDivDW3_correct xh xl yh yl
         DWx DWy FIN Hp14 Hyhne UF_th UF_rh UF_rl
         UF_dprod UF_dlow UF_zprod UF_z0 UF_z1 UF_z2 UF_z3).
Qed.

End CondAccuracyDWDivDW.

(* ============================================================
   Public condition-level accuracy theorem

   The arm-specific proof above already covers both normal and underflowing
   executions.  This section exports its [16.5*u^2] relative bound as the
   canonical condition-level result.
   ============================================================ *)
Section CondAccuracyDWDivDW_public.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Variables (xh xl yh yl : ftype t).
Hypothesis Hp14 : (14 <= fprec t)%Z.
Hypothesis COND : DWDivDW_cond xh xl yh yl.

Notation u := (bpow radix2 (-fprec t)).
Let X := FT2R xh + FT2R xl.
Let Q := X / (FT2R yh + FT2R yl).
Let zr := FT2R (fst (DWDivDW3 xh xl yh yl)) +
          FT2R (snd (DWDivDW3 xh xl yh yl)).

(** Canonical exported regime-independent relative bound.  The proof keeps the
    ordered and unordered refinement-arm budgets separate through the closing
    multiplication and underflow-floor conversion. *)
Theorem relative_errorDWDivDW3_from_cond_combined :
  Rabs ((zr-Q)/Q) <= 165/10*u^2.
Proof.
exact (relative_errorDWDivDW3_from_cond_arms
  xh xl yh yl Hp14 COND).
Qed.

End CondAccuracyDWDivDW_public.
