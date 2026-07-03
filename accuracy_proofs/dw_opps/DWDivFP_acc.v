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
From Flocq Require Import Mult_error FLT Div_sqrt_error.

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

(* Node (B): the FLX two-product equals the runtime Fast2Mult (product bridge). *)
Lemma bridge_prod :
  DWTimesFP.Fast2Mult (fprec t) choice (FT2R (BDIV xh y)) (FT2R y)
    = F2Rp (Fast2Mult (BDIV xh y) y).
Proof.
exact (DWMulFP_acc.Fast2Mult_correct (BDIV xh y) y (FINpih xh xl y FIN)
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

(* Node (C): dh = xh - pih is exact. *)
Lemma bridge_dh :
  FT2R xh - FT2R (BMULT (BDIV xh y) y) = FT2R (BMINUS xh (BMULT (BDIV xh y) y)).
Proof.
have Hexact := @xhmpih_exact (fprec t) (fprec_gt_one t) choice eq_refl
                 (FT2R xh) (FT2R y) Fxh_flx Hyne.
rewrite bridge_th bridge_pih in Hexact.
have Hgflx : generic_format radix2 (FLX_exp (fprec t))
    (FT2R xh - FT2R (BMULT (BDIV xh y) y))
  by rewrite -Hexact; apply: generic_format_round.
have HgFLT : generic_format radix2 (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
    (FT2R xh - FT2R (BMULT (BDIV xh y) y))
  by apply: generic_format_FLT_FLX; [ exact UF_dh | exact Hgflx ].
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
have HgFLT : generic_format radix2 (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
    (FT2R (BMINUS xh (BMULT (BDIV xh y) y)) - FT2R (Fast2Mult_err (BDIV xh y) y))
  by apply: generic_format_FLT_FLX; [ exact UF_dt | exact Hgflx ].
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
rewrite (DWDivFP3_FLX_FLT xh xl y FIN Hyne UF_th UF_prod UF_dh UF_dt UF_tl) in Hpaper.
rewrite /F2Rp/= in Hpaper.
unfold relative_error_DWDivFP, zh, zl.
eapply Rle_trans; [ apply Req_le; reflexivity | ].
rewrite (_ : 3 * u ^ 2 = 3 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t)));
  [ exact Hpaper | rewrite /=; ring ].
Qed.

End FiniteAccuracyDWDivFP.

(* ============================================================
   Layer-2: finiteness + underflow-discipline facts derived from DWDivFP_cond.

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

Local Instance valid_fexp_inst_div : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.

(* Omega/4 = bpow(femax-2). *)
Lemma aux_quarter_Omega : bpow radix2 (femax t - 2) = /4 * Omega.
Proof.
have -> : Omega = (bpow radix2 (femax t - 2) * bpow radix2 2)%R
  by rewrite -bpow_plus; f_equal; lia.
have -> : bpow radix2 2 = 4%R by reflexivity. lra.
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
eapply Rle_lt_trans; [apply DWMulFP_acc.aux_round_ub|].
have Hu := DWMulFP_acc.aux_ulp_real _ Hlt.
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
Lemma DWDivFP3_fst_finite (xh xl y : ftype t) :
  DWDivFP_cond xh xl y ->
  is_finite (fst (DWDivFP3 xh xl y)) = true.
Proof.
Admitted.

(* Finiteness of snd (DWDivFP3): the closing Fast2Sum's snd needs the ulp
   ordering ulp(tl) <= ulp(th) (or th = 0), from the double-word relation of the
   result (|tl| <= ulp(th)), then is_finite_FastSum_ulp. *)
Lemma DWDivFP3_snd_finite (xh xl y : ftype t) :
  DWDivFP_cond xh xl y ->
  is_finite (snd (DWDivFP3 xh xl y)) = true.
Proof.
Admitted.

(* The intermediate normal-range (strong-underflow) facts consumed by the
   Layer-1 theorem, derived from the cond's quotient underflow bound.  These are
   the division analog of the "|w| normal" side conditions in the multiplication
   development; each says a specific rounded node stays in the normal range.
   OBLIGATION: propagate the quotient normal-range bound through th*y ~ xh
   (UF_prod, at the emin+3*fprec threshold forced by the Fast2Mult product
   bridge), the exact residuals (UF_dh, UF_dt), and the second quotient (UF_tl). *)
Lemma cond_UF_prod (xh xl y : ftype t) :
  DWDivFP_cond xh xl y ->
  bpow radix2 (emin + 3 * fprec t) <= Rabs (FT2R (BDIV xh y) * FT2R y).
Proof. Admitted.

Lemma cond_UF_dh (xh xl y : ftype t) :
  DWDivFP_cond xh xl y ->
  bpow radix2 (emin + fprec t - 1)
    <= Rabs (FT2R xh - FT2R (BMULT (BDIV xh y) y)).
Proof. Admitted.

Lemma cond_UF_dt (xh xl y : ftype t) :
  DWDivFP_cond xh xl y ->
  bpow radix2 (emin + fprec t - 1)
    <= Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y))
             - FT2R (Fast2Mult_err (BDIV xh y) y)).
Proof. Admitted.

Lemma cond_UF_tl (xh xl y : ftype t) :
  DWDivFP_cond xh xl y ->
  bpow radix2 (emin + fprec t - 1)
    <= Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                 (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y).
Proof. Admitted.

End DWDivFP_Finite.

(* Layer-2 corollary: the 3u^2 bound behind the single precondition
   DWDivFP_cond.  double_word, y <> 0, and the top-level quotient normal-range
   bound (UF_th) are derived here directly from the cond's component/underflow
   bounds; is_finite_p and the intermediate normal-range facts come from the
   DWDivFP_Finite lemmas.  Hp4 (4 <= fprec t) is threaded by the caller. *)
Section CondAccuracyDWDivFP.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (@common.emin t).
Notation u := (bpow radix2 (- fprec t)).

Variables (xh xl y : ftype t).

Hypothesis Hp4 : (4 <= fprec t)%Z.
Hypothesis COND : DWDivFP_cond xh xl y.

Theorem relative_errorDWDivFP3_from_cond :
  relative_error_DWDivFP xh xl y <= 3 * u ^ 2.
Proof.
have Hfp : is_finite_p (DWDivFP3 xh xl y).
{ split;
    [ exact (DWDivFP3_fst_finite xh xl y COND)
    | exact (DWDivFP3_snd_finite xh xl y COND) ]. }
move: (COND) => [Hfxh [Hfxl [Hfy [Hdwp [Hquot [Hxhb Hqub]]]]]].
have Hyne : FT2R y <> 0.
{ intro H0.
  have Hp := bpow_gt_0 radix2 (SpecFloat.emin (fprec t) (femax t) + 2 * fprec t - 1).
  move: Hquot; rewrite H0 /Rdiv Rinv_0 Rmult_0_r Rabs_R0 => Hc.
  lra. }
have Uth : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xh / FT2R y).
{ apply Rle_trans with
    (bpow radix2 (SpecFloat.emin (fprec t) (femax t) + 2 * fprec t - 1)).
  - apply bpow_le. unfold common.emin. pose proof (fprec_gt_0 t). lia.
  - exact Hquot. }
exact (relative_errorDWDivFP3_correct xh xl y Hdwp Hfp Hp4 Hyne
         Uth (cond_UF_prod xh xl y COND) (cond_UF_dh xh xl y COND)
         (cond_UF_dt xh xl y COND) (cond_UF_tl xh xl y COND)).
Qed.

End CondAccuracyDWDivFP.
