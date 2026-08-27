(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Accuracy and representation results for [DWTimesDW3] (Algorithm 12).

    Public results:
    - [DWTimesDW_relative_accuracy]: the pure [4u^2] relative bound under
      [DWTimesDW_relative_error_input_cond];
    - [DWTimesDW_mixed_accuracy_from_cond]: the whole-range
      [4u^2|P| + 2.5 eta] bound under [DWTimesDW_mixed_cond];
    - [DWTimesDW_double_word_from_cond]: output closure under the same
      condition;
    - [DWTimesDW_mixed_guarantee_from_cond]: the whole-range
      accuracy-and-closure bundle assembled from those two results;
    - [DWTimesDW_mixed_guarantee_from_safe_input_cond]: the same bundle after
      an input-only sufficient condition establishes result finiteness.

    [DWDivDW_acc] also consumes the FLX bridge and detailed absolute-error
    regime lemmas used to analyze its closing multiplication. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common FLT_helpers.
Require Import DWTimesFP DWTimesDW DDConds DWord_defs Fast2Mult_acc TwoSum_acc Fast2Sum_acc.
Require Import DWPlusFP_acc_helpers DW_acc_lemmas.
(* The primitive Fast2Sum and Fast2Mult files supply the generic exact-sum and
   underflow-floor lemmas reused by the Algorithm-12 gap block.  DWMulFP_acc
   supplies only the operation-specific bridge shared with division. *)
Require Import DWMulFP_acc.
From Flocq Require Import Pff2Flocq Core.

From Stdlib Require Import Reals.Reals.

Require Import mathcomp.ssreflect.ssreflect.

(* for choice functions : choice = fun x0 : Z => negb (Z.even x0) *)
From Stdlib Require Import Logic.FunctionalExtensionality.

Set Bullet Behavior "Strict Subproofs".

(* Keep the paper's two-product folded; proofs expose it via TwoProdE. *)
Opaque DWTimesFP.TwoProd.
Arguments DWTimesFP.TwoProd : simpl never.



(* ============================================================
   Section 1: extract per-operation finiteness from
   FIN : is_finite_p (DWTimesDW3 xh xl yh yl).
   ============================================================ *)
Section CorrectDWMulDW.
  Context {NANS: Nans} {t : type} {STD: is_standard t}.

  Variables (xh xl yh yl : ftype t).

  Hypothesis FIN : is_finite_p (DWTimesDW3 xh xl yh yl).

  (* fst (DWTimesDW3 xh xl yh yl) reduces to
       BPLUS (BMULT xh yh) (BPLUS (Fast2Mult_err xh yh)
                                  (BFMA xl yh (BFMA xh yl (BMULT xl yl)))).
     One pass of BPLUS/BFMA finite-elimination exposes every subterm's
     finiteness; the descriptive result facts below then close by
     [exact]/[split]. *)
  Ltac prove_finite :=
    let Hf := fresh "Hf" in
    have Hf := proj1 FIN;
    change (is_finite (BPLUS (BMULT xh yh)
              (BPLUS (Fast2Mult_err xh yh)
                     (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) = true) in Hf;
    destruct (BPLUS_finite_e t _ _ Hf) as [Hmul Hrest];
    destruct (BPLUS_finite_e t _ _ Hrest) as [Hcl1 Hcl2];
    destruct (BFMA_finite_e t _ _ _ Hcl2) as [Hxl [Hyh Htl1]];
    destruct (BFMA_finite_e t _ _ _ Htl1) as [Hxh [Hyl Htl0]];
    first [ exact Hxh | exact Hxl | exact Hyh | exact Hyl
          | exact Hmul | exact Htl0 | exact Htl1 | exact Hcl2 | exact Hrest
          | split; [ exact Hmul | exact Hcl1 ] ].

  Fact DWTimesDW3_xh_finite : is_finite xh = true.
  Proof. prove_finite. Qed.

  Fact DWTimesDW3_xl_finite : is_finite xl = true.
  Proof. prove_finite. Qed.

  Fact DWTimesDW3_yh_finite : is_finite yh = true.
  Proof. prove_finite. Qed.

  Fact DWTimesDW3_yl_finite : is_finite yl = true.
  Proof. prove_finite. Qed.

  (* ch = fst (Fast2Mult xh yh) = BMULT xh yh *)
  Fact DWTimesDW3_mul_finite : is_finite (BMULT xh yh) = true.
  Proof. prove_finite. Qed.

  Fact DWTimesDW3_fast2mult_finite : is_finite_p (Fast2Mult xh yh).
  Proof. prove_finite. Qed.

  Let cl1 := snd (Fast2Mult xh yh).
  Let tl0 := BMULT xl yl.
  Let tl1 := BFMA xh yl tl0.
  Let cl2 := BFMA xl yh tl1.
  Let cl3 := BPLUS cl1 cl2.

  Fact DWTimesDW3_low_low_finite : is_finite tl0 = true.
  Proof. prove_finite. Qed.

  Fact DWTimesDW3_first_correction_finite : is_finite tl1 = true.
  Proof. prove_finite. Qed.

  Fact DWTimesDW3_second_correction_finite : is_finite cl2 = true.
  Proof. prove_finite. Qed.

  Fact DWTimesDW3_correction_finite : is_finite cl3 = true.
  Proof. prove_finite. Qed.

End CorrectDWMulDW.


(* ============================================================
   Section 2: the load-bearing FLX -> FLT bridge for DWTimesDW3.
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

Hypothesis FIN : is_finite_p (DWTimesDW3 xh xl yh yl).
(* Normal-regime hypotheses: every rounding argument of DWTimesDW3 is normal
   (>= bpow(emin+fprec-1)), so each FLT rounding equals its FLX counterpart
   (round_FLT_FLX).  Nprod is the two-product threshold for
   DWMulFP_acc.Fast2Mult_correct_weak. *)
Hypothesis Nprod : bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh).
Hypothesis N0 : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xl * FT2R yl).
Hypothesis N1 : bpow radix2 (emin + fprec t - 1)
             <= Rabs (FT2R xh * FT2R yl + FT2R (BMULT xl yl)).
Hypothesis N2 : bpow radix2 (emin + fprec t - 1)
             <= Rabs (FT2R (BFMA xh yl (BMULT xl yl)) + FT2R xl * FT2R yh).
Hypothesis N3 : bpow radix2 (emin + fprec t - 1)
             <= Rabs (FT2R (Fast2Mult_err xh yh)
                      + FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))).

Local Lemma round_FLT_FLX_exact_or_normal (v : R) :
  generic_format radix2 fexp v \/
  bpow radix2 (emin+fprec t-1) <= Rabs v ->
  round radix2 (FLX_exp (fprec t)) (Znearest choice) v =
  round radix2 fexp (Znearest choice) v.
Proof.
move => [Fv|Nv].
- have Fvx : generic_format radix2 (FLX_exp (fprec t)) v
    by (apply (generic_format_FLX_FLT radix2 emin (fprec t)); exact Fv).
  rewrite !round_generic; [reflexivity|exact Fv|exact Fvx].
- symmetry; exact (round_FLT_FLX radix2 emin (fprec t)
    (Znearest choice) v Nv).
Qed.

(** Assembly lemma for weakened bridges.  It separates the purely algebraic
    Algorithm-12 composition from the per-node reason why FLT and FLX agree
    (normality, zero, or exact subnormal representability). *)
Local Lemma DWTimesDW3_FLX_FLT_from_node_equalities :
  round radix2 (FLX_exp (fprec t)) (Znearest choice)
      (FT2R xl*FT2R yl) = FT2R (BMULT xl yl) ->
  round radix2 (FLX_exp (fprec t)) (Znearest choice)
      (FT2R xh*FT2R yl+FT2R (BMULT xl yl)) =
    FT2R (BFMA xh yl (BMULT xl yl)) ->
  round radix2 (FLX_exp (fprec t)) (Znearest choice)
      (FT2R (BFMA xh yl (BMULT xl yl))+FT2R xl*FT2R yh) =
    FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))) ->
  round radix2 (FLX_exp (fprec t)) (Znearest choice)
      (FT2R (Fast2Mult_err xh yh)+
       FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) =
    FT2R (BPLUS (Fast2Mult_err xh yh)
      (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) ->
  DWTimesDW.DWTimesDW12 (fprec t) choice
    (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl) =
  F2Rp (DWTimesDW3 xh xl yh yl).
Proof.
move => H0 H1 H2 H3.
have Hfmul := DWTimesDW3_mul_finite xh xl yh yl FIN.
have Nprod' : FT2R xh*FT2R yh<>0 ->
    bpow radix2 (emin+2*fprec t-1) <= Rabs (FT2R xh*FT2R yh)
  by auto.
rewrite /DWTimesDW.DWTimesDW12 DWTimesFP.TwoProdE.
rewrite (DWMulFP_acc.Fast2Mult_correct_weak xh yh Hfmul Nprod').
rewrite /F2Rp /Fast2Mult_err /Fast2Mult_mul /Fast2Mult /fst /snd.
cbv zeta. rewrite H0 H1 H2 H3.
rewrite (FastTwoSumEq_FLT (Fast2Mult_mul xh yh)
  (BPLUS (Fast2Mult_err xh yh)
    (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) FIN).
reflexivity.
Qed.

Local Lemma DWTimesDW3_FLX_FLT_exact_or_normal :
  (generic_format radix2 fexp
      (FT2R (BFMA xh yl (BMULT xl yl))+FT2R xl*FT2R yh) \/
   bpow radix2 (emin+fprec t-1) <=
      Rabs (FT2R (BFMA xh yl (BMULT xl yl))+FT2R xl*FT2R yh)) ->
  (generic_format radix2 fexp
      (FT2R (Fast2Mult_err xh yh)+
       FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) \/
   bpow radix2 (emin+fprec t-1) <=
      Rabs (FT2R (Fast2Mult_err xh yh)+
       FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) ->
  DWTimesDW.DWTimesDW12 (fprec t) choice
    (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl) =
  F2Rp (DWTimesDW3 xh xl yh yl).
Proof.
move => E2 E3.
have Hftl0 := DWTimesDW3_low_low_finite xh xl yh yl FIN.
have Hftl1 := DWTimesDW3_first_correction_finite xh xl yh yl FIN.
have Hfcl2 := DWTimesDW3_second_correction_finite xh xl yh yl FIN.
have Hfcl3 := DWTimesDW3_correction_finite xh xl yh yl FIN.
have H0 : round radix2 (FLX_exp (fprec t)) (Znearest choice)
      (FT2R xl*FT2R yl) = FT2R (BMULT xl yl).
{ rewrite -(round_FLT_FLX radix2 emin (fprec t) (Znearest choice) _ N0).
  exact (BMULT_round_correct t xl yl Hftl0). }
have H1 : round radix2 (FLX_exp (fprec t)) (Znearest choice)
      (FT2R xh*FT2R yl+FT2R (BMULT xl yl)) =
    FT2R (BFMA xh yl (BMULT xl yl)).
{ rewrite -(round_FLT_FLX radix2 emin (fprec t) (Znearest choice) _ N1).
  exact (BFMA_round_correct t xh yl (BMULT xl yl) Hftl1). }
have H2 := round_FLT_FLX_exact_or_normal
  (FT2R (BFMA xh yl (BMULT xl yl))+FT2R xl*FT2R yh) E2.
replace (FT2R (BFMA xh yl (BMULT xl yl))+FT2R xl*FT2R yh)%R with
  (FT2R xl*FT2R yh+FT2R (BFMA xh yl (BMULT xl yl)))%R in H2 by ring.
rewrite (BFMA_round_correct t xl yh
  (BFMA xh yl (BMULT xl yl)) Hfcl2) in H2.
have H3 := round_FLT_FLX_exact_or_normal
  (FT2R (Fast2Mult_err xh yh)+
   FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) E3.
rewrite (BPLUS_round_correct t (Fast2Mult_err xh yh)
  (BFMA xl yh (BFMA xh yl (BMULT xl yl))) Hfcl3) in H3.
have H2' : round radix2 (FLX_exp (fprec t)) (Znearest choice)
    (FT2R (BFMA xh yl (BMULT xl yl))+FT2R xl*FT2R yh) =
  FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))).
{ replace (FT2R (BFMA xh yl (BMULT xl yl))+FT2R xl*FT2R yh)%R with
    (FT2R xl*FT2R yh+FT2R (BFMA xh yl (BMULT xl yl)))%R by ring.
  exact H2. }
exact (DWTimesDW3_FLX_FLT_from_node_equalities H0 H1 H2' H3).
Qed.

Theorem DWTimesDW3_FLX_FLT :
  DWTimesDW.DWTimesDW12 (fprec t) choice
    (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl)
    = F2Rp (DWTimesDW3 xh xl yh yl).
Proof.
have Hfmul := DWTimesDW3_mul_finite xh xl yh yl FIN.
have Hftl0 := DWTimesDW3_low_low_finite xh xl yh yl FIN.
have Hftl1 := DWTimesDW3_first_correction_finite xh xl yh yl FIN.
have Hfcl2 := DWTimesDW3_second_correction_finite xh xl yh yl FIN.
have Hfcl3 := DWTimesDW3_correction_finite xh xl yh yl FIN.
have Nprod' : FT2R xh * FT2R yh <> 0 ->
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh)
  by (move => _; exact Nprod).
(* the four layer equalities: FLX round = FT2R of the FLT op *)
have H0 : round radix2 (FLX_exp (fprec t)) (Znearest choice) (FT2R xl * FT2R yl)
        = FT2R (BMULT xl yl).
{ rewrite -(round_FLT_FLX radix2 emin (fprec t) (Znearest choice) (FT2R xl * FT2R yl) N0).
  exact (BMULT_round_correct t xl yl Hftl0). }
have H1 : round radix2 (FLX_exp (fprec t)) (Znearest choice)
              (FT2R xh * FT2R yl + FT2R (BMULT xl yl))
        = FT2R (BFMA xh yl (BMULT xl yl)).
{ rewrite -(round_FLT_FLX radix2 emin (fprec t) (Znearest choice) _ N1).
  exact (BFMA_round_correct t xh yl (BMULT xl yl) Hftl1). }
have H2 : round radix2 (FLX_exp (fprec t)) (Znearest choice)
              (FT2R (BFMA xh yl (BMULT xl yl)) + FT2R xl * FT2R yh)
        = FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))).
{ rewrite -(round_FLT_FLX radix2 emin (fprec t) (Znearest choice) _ N2).
  rewrite Rplus_comm.
  exact (BFMA_round_correct t xl yh (BFMA xh yl (BMULT xl yl)) Hfcl2). }
have H3 : round radix2 (FLX_exp (fprec t)) (Znearest choice)
              (FT2R (Fast2Mult_err xh yh)
               + FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))
        = FT2R (BPLUS (Fast2Mult_err xh yh)
                      (BFMA xl yh (BFMA xh yl (BMULT xl yl)))).
{ rewrite -(round_FLT_FLX radix2 emin (fprec t) (Znearest choice) _ N3).
  exact (BPLUS_round_correct t (Fast2Mult_err xh yh)
           (BFMA xl yh (BFMA xh yl (BMULT xl yl))) Hfcl3). }
(* assemble: bridge the product and closing Fast2Sum, then peel the four rounds *)
rewrite /DWTimesDW.DWTimesDW12 DWTimesFP.TwoProdE.
rewrite (DWMulFP_acc.Fast2Mult_correct_weak xh yh Hfmul Nprod').
rewrite /F2Rp /Fast2Mult_err /Fast2Mult_mul /Fast2Mult /fst /snd.
cbv zeta.
rewrite H0 H1 H2 H3.
rewrite (FastTwoSumEq_FLT (Fast2Mult_mul xh yh)
          (BPLUS (Fast2Mult_err xh yh)
                 (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) FIN).
reflexivity.
Qed.

End CorrectDWMulDW_bridge.


(* ============================================================
   Section 3: finiteness of DWTimesDW3 from
   DWTimesDW_mixed_safe_input_cond.
     fst (DWTimesDW3 xh xl yh yl) = BPLUS ch cl3, where
       ch  = Fast2Mult_mul xh yh   (= BMULT xh yh),
       cl3 = BPLUS (Fast2Mult_err xh yh) (BFMA xl yh (BFMA xh yl (BMULT xl yl))).
   The cond's product bound |xh*yh| <= Omega/2 keeps |ch| small; the two
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

(** Strictly below the first subnormal midpoint, round-to-nearest-even is
    zero.  Keeping this lemma explicit avoids charging a half ulp for nodes
    whose exact argument is too small to reach the physical lattice. *)
Local Lemma round_FLT_abs_lt_half_emin_0 (x : R) :
  Rabs x < /2*bpow radix2 emin ->
  round radix2 fexp (Znearest choice) x=0.
Proof.
move => Hx.
set a := Rabs x.
fold a in Hx.
have Ha0 : 0 <= a by (unfold a;apply Rabs_pos).
have Hulp0 : Ulp.ulp radix2 fexp 0=bpow radix2 emin.
{ unfold fexp, SpecFloat.fexp. apply ulp_FLT_small.
  - apply fprec_gt_0.
  - rewrite Rabs_R0. apply bpow_gt_0. }
destruct (Req_dec a 0) as [Ha|Ha].
- have Hx0 : x=0 by apply Rabs_eq_R0; exact Ha.
  rewrite Hx0 round_0. reflexivity.
- have Hd : round radix2 fexp Zfloor a=0.
  { replace a with (0+a)%R by ring.
    apply round_DN_plus_eps_pos.
    - exact valid_fexp_inst.
    - lra.
    - apply generic_format_0.
    - split; [exact Ha0|]. rewrite Hulp0. nra. }
  have Hna : ~ generic_format radix2 fexp a.
  { intro Fa. move: Hd. rewrite (round_generic _ _ _ a Fa). lra. }
  have Hrn : round radix2 fexp (Znearest choice) a=0.
  { rewrite -Hd.
    apply (@round_N_eq_DN radix2 fexp valid_fexp_inst choice a).
    cbv zeta.
    rewrite round_UP_DN_ulp // Hd.
    have Hulpa : Ulp.ulp radix2 fexp a=bpow radix2 emin.
    { apply ulp_FLT_small; [apply fprec_gt_0|].
      rewrite Rabs_pos_eq; [|exact Ha0].
      eapply Rlt_trans; [exact Hx|].
      have Hhalf : /2*bpow radix2 emin=bpow radix2 (emin-1).
      { rewrite (bpow_plus radix2 emin (-1)).
        change (bpow radix2 (-1)) with (/2:R). ring. }
      rewrite Hhalf. apply bpow_lt.
      pose proof (fprec_gt_0 t) as Hp; red in Hp; lia. }
    rewrite Hulpa. nra. }
  have Habs : Rabs (round radix2 fexp (Znearest choice) x)=0.
  { rewrite -round_NE_abs. fold a. rewrite Hrn. reflexivity. }
  exact (Rabs_eq_R0 _ Habs).
Qed.

(** Binade-local half-ulp bound above the subnormal floor. *)
Local Lemma half_ulp_FLT_below_binade (x : R) (k : Z) :
  (0 <= k)%Z ->
  Rabs x < bpow radix2 (emin+fprec t+k) ->
  /2*Ulp.ulp radix2 fexp x <= /2*bpow radix2 (emin+k).
Proof.
move => Hk Hx.
destruct (Req_dec x 0) as [->|Hx0].
- rewrite FLT.ulp_FLT_0.
  apply Rmult_le_compat_l; [lra|].
  change (bpow radix2 emin <= bpow radix2 (emin+k)).
  apply bpow_le; lia.
- rewrite (Ulp.ulp_neq_0 radix2 fexp x Hx0).
  apply Rmult_le_compat_l; [lra|apply bpow_le].
  unfold cexp, fexp, SpecFloat.fexp, FLT_exp.
  have Hmag := mag_le_bpow radix2 x (emin+fprec t+k) Hx0 Hx.
  unfold common.emin, SpecFloat.emin in *.
  apply Z.max_lub; lia.
Qed.

Local Lemma round_FLT_error_below_binade (x : R) (k : Z) :
  (0 <= k)%Z ->
  Rabs x < bpow radix2 (emin+fprec t+k) ->
  Rabs (round radix2 fexp (Znearest choice) x-x) <=
    /2*bpow radix2 (emin+k).
Proof.
move => Hk Hx.
eapply Rle_trans.
- exact (@Ulp.error_le_half_ulp radix2 fexp
    valid_fexp_inst choice x).
- exact (half_ulp_FLT_below_binade x k Hk Hx).
Qed.

Local Lemma generic_format_FIX_plus (e : Z) (x y : R) :
  generic_format radix2 (FIX_exp e) x ->
  generic_format radix2 (FIX_exp e) y ->
  generic_format radix2 (FIX_exp e) (x+y).
Proof.
move => Fx Fy.
apply generic_format_FIX.
destruct (FIX_format_generic radix2 e x Fx) as [[mx ex] Hx Hex].
destruct (FIX_format_generic radix2 e y Fy) as [[my ey] Hy Hey].
cbn in Hex, Hey. subst ex; subst ey.
eapply (FIX_spec radix2 e (x+y) (Float radix2 (mx+my) e));
  cbn; [|reflexivity].
rewrite Hx Hy /F2R /= plus_IZR. ring.
Qed.

Local Lemma generic_format_FIX_opp (e : Z) (x : R) :
  generic_format radix2 (FIX_exp e) x ->
  generic_format radix2 (FIX_exp e) (-x).
Proof. move => Fx; apply generic_format_opp; exact Fx. Qed.

Local Lemma generic_format_FIX_minus (e : Z) (x y : R) :
  generic_format radix2 (FIX_exp e) x ->
  generic_format radix2 (FIX_exp e) y ->
  generic_format radix2 (FIX_exp e) (x-y).
Proof.
move => Fx Fy. unfold Rminus.
apply generic_format_FIX_plus; [exact Fx|apply generic_format_FIX_opp; exact Fy].
Qed.

(** Products preserve fixed-point lattices, with the lattice exponents
    adding.  This elementary fact is the useful form of exponent provenance
    for the underflow bridge: products entering the low-word FMA are not
    arbitrary reals. *)
Local Lemma generic_format_FIX_mult (ex ey : Z) (x y : R) :
  generic_format radix2 (FIX_exp ex) x ->
  generic_format radix2 (FIX_exp ey) y ->
  generic_format radix2 (FIX_exp (ex+ey)) (x*y).
Proof.
move => Fx Fy.
apply generic_format_FIX.
destruct (FIX_format_generic radix2 ex x Fx) as [[mx ex'] Hx Hex].
destruct (FIX_format_generic radix2 ey y Fy) as [[my ey'] Hy Hey].
cbn in Hex, Hey. subst ex'; subst ey'.
eapply (FIX_spec radix2 (ex+ey) (x*y)
  (Float radix2 (mx*my) (ex+ey))); cbn; [|reflexivity].
rewrite Hx Hy /F2R /= mult_IZR bpow_plus. ring.
Qed.

(** A value on a finer binary lattice is also on every coarser lattice whose
    exponent is no larger. *)
Local Lemma generic_format_FIX_weaken (e1 e2 : Z) (x : R) :
  (e1 <= e2)%Z ->
  generic_format radix2 (FIX_exp e2) x ->
  generic_format radix2 (FIX_exp e1) x.
Proof.
move => He Fx.
apply generic_format_FIX.
destruct (FIX_format_generic radix2 e2 x Fx) as [[m e] Hx Heq].
cbn in Heq. subst e.
set k := (e2-e1)%Z.
have Hk : (0 <= k)%Z by (unfold k; lia).
eapply (FIX_spec radix2 e1 x (Float radix2 (m*radix2^k) e1)); cbn.
- rewrite Hx /F2R /= mult_IZR.
  change (IZR m*bpow radix2 e2 =
    IZR m*IZR (radix2^k)*bpow radix2 e1).
  rewrite IZR_Zpower; [|exact Hk].
  rewrite Rmult_assoc -bpow_plus.
  replace (k+e1)%Z with e2 by (unfold k; lia).
  reflexivity.
- reflexivity.
Qed.

(** In the cancellation branch, membership in the physical [2^emin] lattice
    is enough: below the first binade the FLT format is precisely that fixed
    lattice. *)
Local Lemma generic_format_FLT_of_FIX_small (x : R) :
  Rabs x <= bpow radix2 (emin+fprec t) ->
  generic_format radix2 (FIX_exp emin) x ->
  generic_format radix2 fexp x.
Proof.
move => Hx Fx.
exact (generic_format_FLT_FIX radix2 emin (fprec t)
  x Hx Fx).
Qed.

(** FLT and FLX rounding coincide on every value belonging to the physical
    subnormal lattice.  Below the first binade such a value is exactly FLT;
    above it the standard normal-range bridge applies. *)
Local Lemma round_FLT_FLX_FIX (x : R) :
  generic_format radix2 (FIX_exp emin) x ->
  round radix2 fexp (Znearest choice) x =
  round radix2 (FLX_exp (fprec t)) (Znearest choice) x.
Proof.
move => Fx.
destruct (Rle_or_lt (Rabs x) (bpow radix2 (emin+fprec t))) as [Hs|Hn].
- have Fflt := generic_format_FLT_of_FIX_small x Hs Fx.
  have Fflx : generic_format radix2 (FLX_exp (fprec t)) x
    by apply (generic_format_FLX_FLT radix2 emin (fprec t)); exact Fflt.
  rewrite !round_generic; [reflexivity|exact Fflx|exact Fflt].
- apply round_FLT_FLX.
  have Hb : bpow radix2 (emin+fprec t-1) <=
      bpow radix2 (emin+fprec t) by (apply bpow_le; lia).
  exact (Rle_trans _ _ _ Hb (Rlt_le _ _ Hn)).
Qed.


(** Every FLT rounding error splits into a normal relative component and one
    genuine underflow-floor component.  Exactly one component is nonzero in
    the proof.  This decomposition is the interface used to replay the paper
    Algorithm-12 algebra while carrying denormal effects separately. *)
Local Lemma round_FLT_error_relative_plus_floor (x : R) :
  exists er ef : R,
    (round radix2 fexp (Znearest choice) x-x = er+ef)%R /\
    Rabs er <= bpow radix2 (-fprec t)*Rabs x /\
    Rabs ef <= /2*bpow radix2 emin /\
    (er=0 \/ ef=0) /\
    round radix2 fexp (Znearest choice) x =
      round radix2 (FLX_exp (fprec t)) (Znearest choice) (x+ef) /\
    ((ef=0 /\ bpow radix2 (emin+fprec t-1) <= Rabs x) \/
     (er=0 /\ Rabs x < bpow radix2 (emin+fprec t-1))).
Proof.
have Vf : Generic_fmt.Valid_exp fexp
  by (apply FLT.FLT_exp_valid, fprec_gt_0).
have E := @Ulp.error_le_half_ulp radix2 fexp Vf choice x.
destruct (Rle_lt_dec (bpow radix2 (emin+fprec t-1)) (Rabs x)) as [Hn|Hs].
- exists (round radix2 fexp (Znearest choice) x-x), 0.
  split; [ring|]. split.
  + have Hu := ulp_FLT_le radix2 emin (fprec t) x Hn.
    have Hb : bpow radix2 (1-fprec t) =
        2*bpow radix2 (-fprec t).
    { replace (1-fprec t)%Z with (1+ -fprec t)%Z by lia.
      rewrite bpow_plus. change (bpow radix2 1) with (2:R). ring. }
    eapply Rle_trans; [exact E|].
    eapply Rle_trans.
    * apply Rmult_le_compat_l; [lra|exact Hu].
    * rewrite Hb. nra.
  + split.
    * rewrite Rabs_R0. have := bpow_ge_0 radix2 emin. nra.
    * split; [right; reflexivity|]. split.
      { rewrite Rplus_0_r. apply round_FLT_FLX; exact Hn. }
      { left; split; [reflexivity|exact Hn]. }
- exists 0, (round radix2 fexp (Znearest choice) x-x).
  split; [ring|]. split.
  + rewrite Rabs_R0. apply Rmult_le_pos; [apply bpow_ge_0|apply Rabs_pos].
  + split.
    * have Hsmall : Rabs x < bpow radix2 (emin+fprec t)
      by (eapply Rlt_le_trans; [exact Hs|apply bpow_le; lia]).
      have Hu : Ulp.ulp radix2 fexp x=bpow radix2 emin
      by apply ulp_FLT_small; [apply fprec_gt_0|exact Hsmall].
      rewrite Hu in E. exact E.
    * split; [left; reflexivity|]. split.
      {
      set rf := round radix2 fexp (Znearest choice) x.
      change (rf = round radix2 (FLX_exp (fprec t))
        (Znearest choice) (x+(rf-x))).
      replace (x+(rf-x))%R with rf by ring.
      rewrite round_generic; [reflexivity|].
      apply (generic_format_FLX_FLT radix2 emin (fprec t)).
      unfold rf. apply generic_format_round;
        [apply FLT.FLT_exp_valid, fprec_gt_0|apply valid_rnd_N]. }
      { right; split; [reflexivity|exact Hs]. }
Qed.

Local Lemma FIX_FLT_or_normal (x : R) :
  generic_format radix2 (FIX_exp emin) x ->
  generic_format radix2 fexp x \/
  bpow radix2 (emin+fprec t-1) <= Rabs x.
Proof.
move => Fx.
destruct (Rle_or_lt (Rabs x) (bpow radix2 (emin+fprec t))) as [Hs|Hn].
- left. exact (generic_format_FLT_of_FIX_small x Hs Fx).
- right.
  have Hb : bpow radix2 (emin+fprec t-1) <=
      bpow radix2 (emin+fprec t) by (apply bpow_le; lia).
  exact (Rle_trans _ _ _ Hb (Rlt_le _ _ Hn)).
Qed.

(** A product large enough to reach the two-product normal threshold is on
    the physical FLT lattice.  Although a product of arbitrary FLT values is
    initially only known to be on the [2^(ex+ey)] lattice, the mantissa bounds
    force [ex+ey >= emin] at this magnitude. *)
Local Lemma FLT_product_FIX_of_large (x y : R) :
  generic_format radix2 fexp x ->
  generic_format radix2 fexp y ->
  bpow radix2 (emin+2*fprec t-1) <= Rabs (x*y) ->
  generic_format radix2 (FIX_exp emin) (x*y).
Proof.
move => Fx Fy Hlarge.
have Fx' := FLT_format_generic radix2 emin (fprec t) x Fx.
have Fy' := FLT_format_generic radix2 emin (fprec t) y Fy.
case: Fx' => [[mx ex] Hx Hmx Hex].
case: Fy' => [[my ey] Hy Hmy Hey].
cbn in Hmx, Hex, Hmy, Hey.
have Hexy : (emin <= ex+ey)%Z.
{ apply Z.nlt_ge; intro Hbad.
  have Hexy' : (ex+ey <= emin-1)%Z by lia.
  have HmxR : Rabs (IZR mx) < bpow radix2 (fprec t).
  { rewrite -abs_IZR -IZR_Zpower; [apply IZR_lt; exact Hmx|].
    pose proof (fprec_lb t). lia. }
  have HmyR : Rabs (IZR my) < bpow radix2 (fprec t).
  { rewrite -abs_IZR -IZR_Zpower; [apply IZR_lt; exact Hmy|].
    pose proof (fprec_lb t). lia. }
  have Hb0 := bpow_gt_0 radix2 (ex+ey).
  have Hbp := bpow_gt_0 radix2 (fprec t).
  have Hmant : Rabs (IZR mx)*Rabs (IZR my) <
      bpow radix2 (fprec t)*bpow radix2 (fprec t).
  { apply Rmult_lt_compat; [apply Rabs_pos|apply Rabs_pos|exact HmxR|exact HmyR]. }
  have Hscale := Rmult_lt_compat_r (bpow radix2 (ex+ey)) _ _ Hb0 Hmant.
  rewrite -!bpow_plus in Hscale.
  have Hexp : bpow radix2 (fprec t+fprec t+(ex+ey)) <=
      bpow radix2 (emin+2*fprec t-1) by (apply bpow_le; lia).
  have Hxy : Rabs (x*y) =
      Rabs (IZR mx)*Rabs (IZR my)*bpow radix2 (ex+ey).
  { rewrite Hx Hy /F2R /= !Rabs_mult.
    rewrite (Rabs_pos_eq (bpow radix2 ex)); try apply bpow_ge_0.
    replace (Rabs (bpow radix2 ey)) with (bpow radix2 ey)
      by (symmetry; apply Rabs_pos_eq; apply bpow_ge_0).
    rewrite bpow_plus. ring. }
  rewrite Hxy in Hlarge.
  nra. }
have Fprod := generic_format_FIX_mult ex ey x y.
rewrite Hx Hy in Fprod.
have Fmx : generic_format radix2 (FIX_exp ex)
    (F2R (Float radix2 mx ex)).
{ apply (generic_format_F2R radix2 (FIX_exp ex) mx ex).
  move => _. unfold cexp, FIX_exp. lia. }
have Fmy : generic_format radix2 (FIX_exp ey)
    (F2R (Float radix2 my ey)).
{ apply (generic_format_F2R radix2 (FIX_exp ey) my ey).
  move => _. unfold cexp, FIX_exp. lia. }
specialize (Fprod Fmx Fmy).
apply (generic_format_FIX_weaken emin (ex+ey)); [exact Hexy|].
rewrite Hx Hy. exact Fprod.
Qed.

(** A value on the [2^e] lattice that is strictly smaller than two lattice
    steps has magnitude at most one step. *)
Local Lemma FIX_abs_lt_two_steps (e : Z) (x : R) :
  generic_format radix2 (FIX_exp e) x ->
  Rabs x < 2*bpow radix2 e ->
  Rabs x <= bpow radix2 e.
Proof.
move => Fx Hx.
destruct (FIX_format_generic radix2 e x Fx) as [[m ex] Hm Hex].
cbn in Hex. subst ex.
rewrite Hm /F2R /= Rabs_mult in Hx |- *.
have He0 : 0 < bpow radix2 e by apply bpow_gt_0.
have Hege : 0 <= bpow radix2 e by apply Rlt_le; exact He0.
rewrite (Rabs_right (bpow radix2 e) (Rle_ge _ _ Hege)) in Hx |- *.
have Hm2 : Rabs (IZR m) < 2.
{ apply (Rmult_lt_reg_r (bpow radix2 e)); [exact He0|]. nra. }
have Hm1 : Rabs (IZR m) <= 1.
{ destruct (Z.leb_spec0 0 m) as [Hmpos|Hmneg].
  - rewrite Rabs_right in Hm2 |- *.
    2: { apply Rle_ge. change (IZR 0 <= IZR m). apply IZR_le; exact Hmpos. }
    have Hz : (m<2)%Z by exact (lt_IZR _ _ Hm2).
    change (IZR m <= IZR 1). apply IZR_le; lia.
  - rewrite Rabs_left in Hm2 |- *.
    2: { change (IZR m < IZR 0). apply IZR_lt; lia. }
    rewrite -opp_IZR in Hm2 |- *.
    have Hz : (-m<2)%Z by exact (lt_IZR _ _ Hm2).
    change (IZR (-m) <= IZR 1). apply IZR_le; lia. }
nra.
Qed.


Lemma aux_dw_exact_product_lower (xh xl yh yl : ftype t) :
  double_word_prop xh xl -> double_word_prop yh yl ->
  (1-bpow radix2 (-fprec t))^2*Rabs (FT2R xh*FT2R yh) <=
  Rabs ((FT2R xh+FT2R xl)*(FT2R yh+FT2R yl)).
Proof.
move => DWx DWy.
set u := bpow radix2 (-fprec t).
have Hu0 : 0 <= u by (unfold u;apply bpow_ge_0).
have Hu1 : u <= 1.
{ unfold u. have -> : (1:R)=bpow radix2 0 by reflexivity.
  apply bpow_le. pose proof (fprec_gt_0 t) as Hp; red in Hp; lia. }
have Hxl := @dw_low_le_u_high t STD xh xl DWx.
have Hyl := @dw_low_le_u_high t STD yh yl DWy.
fold u in Hxl, Hyl.
have Hx := Rabs_triang_inv (FT2R xh) (-FT2R xl).
rewrite Rabs_Ropp in Hx.
replace (FT2R xh- -FT2R xl)%R with
  (FT2R xh+FT2R xl)%R in Hx by ring.
have Hy := Rabs_triang_inv (FT2R yh) (-FT2R yl).
rewrite Rabs_Ropp in Hy.
replace (FT2R yh- -FT2R yl)%R with
  (FT2R yh+FT2R yl)%R in Hy by ring.
have Hx' : (1-u)*Rabs (FT2R xh) <=
    Rabs (FT2R xh+FT2R xl) by nra.
have Hy' : (1-u)*Rabs (FT2R yh) <=
    Rabs (FT2R yh+FT2R yl) by nra.
rewrite !Rabs_mult.
eapply Rle_trans with (r2:=
  ((1-u)*Rabs (FT2R xh))*((1-u)*Rabs (FT2R yh))).
- apply Req_le. ring.
- apply Rmult_le_compat.
  + apply Rmult_le_pos; [nra|apply Rabs_pos].
  + apply Rmult_le_pos; [nra|apply Rabs_pos].
  + exact Hx'.
  + exact Hy'.
Qed.

(** Normality propagates through the first low-word FMA.  If [xl*yl] already
    reaches the FLT normal threshold, [xh*yl] is at least four times larger
    (the double-word relation gives [|xl| <= u|xh|]); rounding [xl*yl] cannot
    cancel enough of it to cross back below that threshold. *)
Local Lemma normal_low0_implies_low1 (xh xl yh yl : ftype t) :
  (2 <= fprec t)%Z ->
  double_word_prop xh xl ->
  is_finite (BMULT xl yl) = true ->
  bpow radix2 (emin+fprec t-1) <= Rabs (FT2R xl*FT2R yl) ->
  bpow radix2 (emin+fprec t-1) <=
    Rabs (FT2R xh*FT2R yl+FT2R (BMULT xl yl)).
Proof.
move => Hp2 DWx Ftl0 N0.
set u := bpow radix2 (-fprec t).
set eta := bpow radix2 emin.
set P := Rabs (FT2R xl*FT2R yl).
set A := Rabs (FT2R xh*FT2R yl).
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu4 : u <= /4.
{ unfold u. have -> : (/4:R)=bpow radix2 (-2) by (simpl;lra).
  apply bpow_le; lia. }
have HP0 : 0 < P.
{ eapply Rlt_le_trans; [apply bpow_gt_0|exact N0]. }
have Hxl := @dw_low_le_u_high t STD xh xl DWx.
fold u in Hxl.
have HPA : P <= u*A.
{ unfold P, A. rewrite !Rabs_mult.
  have Hyl0 := Rabs_pos (FT2R yl).
  have H := Rmult_le_compat_r (Rabs (FT2R yl)) _ _ Hyl0 Hxl.
  eapply Rle_trans; [exact H|]. right; ring. }
have Heta : /2*eta <= u*P.
{ have Hmul := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) N0.
  fold P in Hmul. eapply Rle_trans; [|exact Hmul].
  apply Req_le. unfold u, eta.
  rewrite -bpow_plus.
  replace (-fprec t+(emin+fprec t-1))%Z with (emin-1)%Z by ring.
  rewrite (bpow_plus radix2 emin (-1)).
  change (bpow radix2 (-1)) with (/2:R). ring. }
have Htl0r : FT2R (BMULT xl yl) =
    round radix2 fexp (Znearest choice) (FT2R xl*FT2R yl)
  by symmetry; exact (BMULT_round_correct t xl yl Ftl0).
have Htl0 : Rabs (FT2R (BMULT xl yl)) <= P*(1+u)+/2*eta.
{ rewrite Htl0r. apply round_abs_le_of_abs_bound. unfold P; apply Rle_refl. }
have HA0 : 0 <= A by unfold A; apply Rabs_pos.
have HPn : 0 <= P by lra.
have HuA : u*A <= /4*A
  by (apply Rmult_le_compat_r; [exact HA0|exact Hu4]).
have HuP : u*P <= /4*P
  by (apply Rmult_le_compat_r; [exact HPn|exact Hu4]).
have HAge : 4*P <= A by nra.
have Htl0small : Rabs (FT2R (BMULT xl yl)) <= 3/2*P by nra.
have Htri : A <=
    Rabs (FT2R xh*FT2R yl+FT2R (BMULT xl yl))+
    Rabs (FT2R (BMULT xl yl)).
{ unfold A.
  have H := Rabs_triang
    (FT2R xh*FT2R yl+FT2R (BMULT xl yl))
    (-FT2R (BMULT xl yl)).
  specialize (H NANS STD NANS STD).
  replace (FT2R xh*FT2R yl+FT2R (BMULT xl yl)+
    -FT2R (BMULT xl yl))%R with (FT2R xh*FT2R yl)%R in H by ring.
  try rewrite Rabs_Ropp in H. exact H. }
eapply Rle_trans; [exact N0|].
change (P <= Rabs (FT2R xh*FT2R yl+FT2R (BMULT xl yl))).
nra.
Qed.

(** The same low-product normality premise forces the opposite cross product
    [xl*yh] onto the physical lattice.  The double-word relation contributes
    the missing factor [2^p]: [|yl| <= u|yh|]. *)
Local Lemma normal_low0_implies_cross_product_FIX
    (xh xl yh yl : ftype t) :
  double_word_prop yh yl ->
  bpow radix2 (emin+fprec t-1) <= Rabs (FT2R xl*FT2R yl) ->
  generic_format radix2 (FIX_exp emin) (FT2R xl*FT2R yh).
Proof.
move => DWy N0.
set u := bpow radix2 (-fprec t).
have Hu0 : 0 < u by apply bpow_gt_0.
have Hyl := @dw_low_le_u_high t STD yh yl DWy.
fold u in Hyl.
have Hmul := Rmult_le_compat_l (Rabs (FT2R xl)) _ _
  (Rabs_pos _) Hyl.
have Hcross : bpow radix2 (emin+2*fprec t-1) <=
    Rabs (FT2R xl*FT2R yh).
{ rewrite !Rabs_mult in N0 |- *.
  have Hid : u*bpow radix2 (emin+2*fprec t-1) =
      bpow radix2 (emin+fprec t-1).
  { unfold u. rewrite -bpow_plus. f_equal; lia. }
  have Hscaled : u*bpow radix2 (emin+2*fprec t-1) <=
      u*(Rabs (FT2R xl)*Rabs (FT2R yh)).
  { rewrite Hid. eapply Rle_trans; [exact N0|].
    eapply Rle_trans; [exact Hmul|]. right; ring. }
  apply (Rmult_le_reg_l u); [exact Hu0|].
  exact Hscaled. }
apply FLT_product_FIX_of_large.
- apply generic_format_FLT_FT2R.
- apply generic_format_FLT_FT2R.
- exact Hcross.
Qed.

(** Consequently the third low-word rounding argument is always on the FLT
    floor lattice.  It may cancel into the subnormal range, but that case is
    exact rather than an additional underflow error. *)
Local Lemma normal_low0_implies_low2_FIX
    (xh xl yh yl : ftype t) :
  double_word_prop yh yl ->
  bpow radix2 (emin+fprec t-1) <= Rabs (FT2R xl*FT2R yl) ->
  generic_format radix2 (FIX_exp emin)
    (FT2R (BFMA xh yl (BMULT xl yl))+FT2R xl*FT2R yh).
Proof.
move => DWy N0.
apply generic_format_FIX_plus.
- apply (generic_format_FIX_FLT radix2 emin (fprec t)).
  apply generic_format_FLT_FT2R.
- exact (normal_low0_implies_cross_product_FIX xh xl yh yl DWy N0).
Qed.

(** Under the leading two-product threshold, its exact error word is also on
    the physical lattice.  This supplies the lattice provenance of [cl1] in
    the complementary low-low-underflow branch. *)
Local Lemma Fast2Mult_err_FIX_of_normal_product (xh yh : ftype t) :
  is_finite (BMULT xh yh) = true ->
  bpow radix2 (emin+2*fprec t-1) <= Rabs (FT2R xh*FT2R yh) ->
  generic_format radix2 (FIX_exp emin) (FT2R (Fast2Mult_err xh yh)).
Proof.
move => Fmul Nprod.
have Ferr := Fast2MultModel_correct xh yh Fmul ltac:(auto).
have Fprod := FLT_product_FIX_of_large
  (FT2R xh) (FT2R yh)
  (generic_format_FLT_FT2R xh) (generic_format_FLT_FT2R yh) Nprod.
specialize (Fprod STD STD).
have Fch : generic_format radix2 (FIX_exp emin)
    (FT2R (Fast2Mult_mul xh yh)).
{ apply (generic_format_FIX_FLT radix2 emin (fprec t)).
  apply generic_format_FLT_FT2R. }
rewrite Ferr. apply generic_format_FIX_minus; assumption.
Qed.

(** Therefore the final [cl1+cl2] argument is on the floor lattice for every
    FLT correction word [cl2].  In particular the last BPLUS never creates a
    separate FLT/FLX discrepancy once the preceding correction agrees. *)
Local Lemma closing_arg_FIX_of_normal_product
    (xh yh cl2 : ftype t) :
  is_finite (BMULT xh yh) = true ->
  bpow radix2 (emin+2*fprec t-1) <= Rabs (FT2R xh*FT2R yh) ->
  generic_format radix2 (FIX_exp emin)
    (FT2R (Fast2Mult_err xh yh)+FT2R cl2).
Proof.
move => Fmul Nprod.
apply generic_format_FIX_plus.
- exact (Fast2Mult_err_FIX_of_normal_product xh yh Fmul Nprod).
- apply (generic_format_FIX_FLT radix2 emin (fprec t)).
  apply generic_format_FLT_FT2R.
Qed.

(** Exact FLT/FLX bridge when each low-word node is either on the physical
    floor lattice or in the normal range. *)
Local Lemma DWTimesDW3_FLX_FLT_FIX_or_normal
    (xh xl yh yl : ftype t) :
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  bpow radix2 (emin+2*fprec t-1) <= Rabs (FT2R xh*FT2R yh) ->
  (generic_format radix2 (FIX_exp emin) (FT2R xl*FT2R yl) \/
   bpow radix2 (emin+fprec t-1) <= Rabs (FT2R xl*FT2R yl)) ->
  (generic_format radix2 (FIX_exp emin)
      (FT2R xh*FT2R yl+FT2R (BMULT xl yl)) \/
   bpow radix2 (emin+fprec t-1) <=
      Rabs (FT2R xh*FT2R yl+FT2R (BMULT xl yl))) ->
  (generic_format radix2 (FIX_exp emin)
      (FT2R (BFMA xh yl (BMULT xl yl))+FT2R xl*FT2R yh) \/
   bpow radix2 (emin+fprec t-1) <=
      Rabs (FT2R (BFMA xh yl (BMULT xl yl))+FT2R xl*FT2R yh)) ->
  (generic_format radix2 (FIX_exp emin)
      (FT2R (Fast2Mult_err xh yh)+
       FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) \/
   bpow radix2 (emin+fprec t-1) <=
      Rabs (FT2R (Fast2Mult_err xh yh)+
       FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) ->
  DWTimesDW.DWTimesDW12 (fprec t) choice
    (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl) =
  F2Rp (DWTimesDW3 xh xl yh yl).
Proof.
move => FIN Nprod E0 E1 E2 E3.
have F0 := DWTimesDW3_low_low_finite xh xl yh yl FIN.
have F1 := DWTimesDW3_first_correction_finite xh xl yh yl FIN.
have F2 := DWTimesDW3_second_correction_finite xh xl yh yl FIN.
have F3 := DWTimesDW3_correction_finite xh xl yh yl FIN.
have H0 : round radix2 (FLX_exp (fprec t)) (Znearest choice)
      (FT2R xl*FT2R yl) = FT2R (BMULT xl yl).
{ destruct E0 as [E0|E0].
  - rewrite -(round_FLT_FLX_FIX (FT2R xl*FT2R yl) E0).
    exact (BMULT_round_correct t xl yl F0).
  - rewrite -(round_FLT_FLX radix2 emin (fprec t)
      (Znearest choice) _ E0). exact (BMULT_round_correct t xl yl F0). }
have H1 : round radix2 (FLX_exp (fprec t)) (Znearest choice)
      (FT2R xh*FT2R yl+FT2R (BMULT xl yl)) =
    FT2R (BFMA xh yl (BMULT xl yl)).
{ destruct E1 as [E1|E1].
  - rewrite -(round_FLT_FLX_FIX
      (FT2R xh*FT2R yl+FT2R (BMULT xl yl)) E1).
    exact (BFMA_round_correct t xh yl (BMULT xl yl) F1).
  - rewrite -(round_FLT_FLX radix2 emin (fprec t)
      (Znearest choice) _ E1).
    exact (BFMA_round_correct t xh yl (BMULT xl yl) F1). }
have H2 : round radix2 (FLX_exp (fprec t)) (Znearest choice)
      (FT2R (BFMA xh yl (BMULT xl yl))+FT2R xl*FT2R yh) =
    FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))).
{ destruct E2 as [E2|E2].
  - rewrite -(round_FLT_FLX_FIX
      (FT2R (BFMA xh yl (BMULT xl yl))+FT2R xl*FT2R yh) E2).
    rewrite Rplus_comm. exact (BFMA_round_correct t xl yh
      (BFMA xh yl (BMULT xl yl)) F2).
  - rewrite -(round_FLT_FLX radix2 emin (fprec t)
      (Znearest choice) _ E2). rewrite Rplus_comm.
    exact (BFMA_round_correct t xl yh
      (BFMA xh yl (BMULT xl yl)) F2). }
have H3 : round radix2 (FLX_exp (fprec t)) (Znearest choice)
      (FT2R (Fast2Mult_err xh yh)+
       FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) =
    FT2R (BPLUS (Fast2Mult_err xh yh)
      (BFMA xl yh (BFMA xh yl (BMULT xl yl)))).
{ destruct E3 as [E3|E3].
  - rewrite -(round_FLT_FLX_FIX
      (FT2R (Fast2Mult_err xh yh)+
       FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) E3).
    exact (BPLUS_round_correct t (Fast2Mult_err xh yh)
      (BFMA xl yh (BFMA xh yl (BMULT xl yl))) F3).
  - rewrite -(round_FLT_FLX radix2 emin (fprec t)
      (Znearest choice) _ E3).
    exact (BPLUS_round_correct t (Fast2Mult_err xh yh)
      (BFMA xl yh (BFMA xh yl (BMULT xl yl))) F3). }
exact (DWTimesDW3_FLX_FLT_from_node_equalities
  xh xl yh yl FIN Nprod H0 H1 H2 H3).
Qed.

(* --- DW x DW-specific term bounds (new; the extra products / FMAs) --- *)

(* |xh*yl| and |xl*yh| are ~u-small relative to |xh*yh| (one low word each);
   |xl*yl| is ~u^2-small (both low words).  Each stays well under Omega. *)
Local Lemma aux_xhyl_bnd (xh xl yh yl : ftype t) :
  double_word_prop yh yl ->
  Rabs (FT2R xh * FT2R yh) <= /2 * Omega ->
  Rabs (FT2R xh * FT2R yl) <= /2 * bpow radix2 (femax t - fprec t).
Proof.
move => Hdwy Hxhy.
have Hrel := @dw_low_le_u_high t STD yh yl Hdwy.
have Hxhp : 0 <= Rabs (FT2R xh) by apply Rabs_pos.
have HB0 : 0 <= bpow radix2 (- fprec t) by apply bpow_ge_0.
have HuO : /2 * bpow radix2 (femax t - fprec t)
         = bpow radix2 (- fprec t) * (/2 * Omega).
{ rewrite (_ : bpow radix2 (femax t - fprec t)
             = bpow radix2 (- fprec t) * Omega);
    [ring | rewrite -bpow_plus; f_equal; lia]. }
rewrite Rabs_mult HuO.
rewrite Rabs_mult in Hxhy.
eapply Rle_trans; [apply Rmult_le_compat_l; [exact Hxhp | exact Hrel]|].
nra.
Qed.

Local Lemma aux_xlyh_bnd (xh xl yh yl : ftype t) :
  double_word_prop xh xl ->
  Rabs (FT2R xh * FT2R yh) <= /2 * Omega ->
  Rabs (FT2R xl * FT2R yh) <= /2 * bpow radix2 (femax t - fprec t).
Proof.
move => Hdwx Hxhy.
have Hrel := @dw_low_le_u_high t STD xh xl Hdwx.
have Hyhp : 0 <= Rabs (FT2R yh) by apply Rabs_pos.
have HB0 : 0 <= bpow radix2 (- fprec t) by apply bpow_ge_0.
have HuO : /2 * bpow radix2 (femax t - fprec t)
         = bpow radix2 (- fprec t) * (/2 * Omega).
{ rewrite (_ : bpow radix2 (femax t - fprec t)
             = bpow radix2 (- fprec t) * Omega);
    [ring | rewrite -bpow_plus; f_equal; lia]. }
rewrite Rabs_mult HuO.
rewrite Rabs_mult in Hxhy.
eapply Rle_trans; [apply Rmult_le_compat_r; [exact Hyhp | exact Hrel]|].
nra.
Qed.

Local Lemma aux_xlyl_bnd (xh xl yh yl : ftype t) :
  double_word_prop xh xl ->
  double_word_prop yh yl ->
  Rabs (FT2R xh * FT2R yh) <= /2 * Omega ->
  Rabs (FT2R xl * FT2R yl) <= /2 * bpow radix2 (femax t - fprec t).
Proof.
move => Hdwx Hdwy Hxhy.
have Hrelx := @dw_low_le_u_high t STD xh xl Hdwx.
have Hrely := @dw_low_le_u_high t STD yh yl Hdwy.
have Hxlp : 0 <= Rabs (FT2R xl) by apply Rabs_pos.
have Hylp : 0 <= Rabs (FT2R yl) by apply Rabs_pos.
have Hyhp : 0 <= Rabs (FT2R yh) by apply Rabs_pos.
have HB0 : 0 <= bpow radix2 (- fprec t) by apply bpow_ge_0.
have Hu1 : bpow radix2 (- fprec t) <= 1.
{ have -> : (1 = bpow radix2 0)%R by reflexivity. apply bpow_le; pose proof fprec_lb t; lia. }
have HuO : /2 * bpow radix2 (femax t - fprec t)
         = bpow radix2 (- fprec t) * (/2 * Omega).
{ rewrite (_ : bpow radix2 (femax t - fprec t)
             = bpow radix2 (- fprec t) * Omega);
    [ring | rewrite -bpow_plus; f_equal; lia]. }
rewrite Rabs_mult HuO.
rewrite Rabs_mult in Hxhy.
have Hxhp : 0 <= Rabs (FT2R xh) by apply Rabs_pos.
have Hstep : Rabs (FT2R xl) * Rabs (FT2R yl)
          <= (bpow radix2 (- fprec t) * Rabs (FT2R xh))
             * (bpow radix2 (- fprec t) * Rabs (FT2R yh)).
{ apply Rmult_le_compat; [exact Hxlp | exact Hylp | exact Hrelx | exact Hrely]. }
eapply Rle_trans; [exact Hstep|].
have Hre : (bpow radix2 (- fprec t) * Rabs (FT2R xh))
           * (bpow radix2 (- fprec t) * Rabs (FT2R yh))
         = bpow radix2 (- fprec t)
           * (bpow radix2 (- fprec t) * (Rabs (FT2R xh) * Rabs (FT2R yh))) by ring.
rewrite Hre.
apply Rmult_le_compat_l; [exact HB0|].
have HRxy : 0 <= Rabs (FT2R xh) * Rabs (FT2R yh) by apply Rmult_le_pos.
nra.
Qed.

(* Magnitude ordering |cl3| <= |ch| for the closing Fast2Sum, in the normal
   product regime |xh*yh| >= bpow(emin+2p-1).  Everything scales with the
   product P = |xh*yh|: the low words give |cl1|,|xh*yl|,|xl*yh| <= u*P and
   |xl*yl| <= u^2*P, so accumulating the four roundings keeps |cl3| <= 6u*P,
   which is <= (1-u)*P <= |ch| once 7u <= 1 (fprec >= 3). *)
Local Lemma aux_cl3_arg_le_ch (xh xl yh yl : ftype t) :
  (3 <= fprec t)%Z ->
  double_word_prop xh xl ->
  double_word_prop yh yl ->
  is_finite (BMULT xh yh) = true ->
  is_finite (BPLUS (Fast2Mult_err xh yh)
                   (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) = true ->
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh) ->
  Rabs (FT2R (Fast2Mult_err xh yh)
           + FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))
    <= Rabs (FT2R (Fast2Mult_mul xh yh)).
Proof.
move => Hp3 Hdwx Hdwy Hfmul Hfsum Hthresh.
(* basic quantities *)
have HP0 : 0 < Rabs (FT2R xh * FT2R yh)
  by (eapply Rlt_le_trans; [apply bpow_gt_0 | exact Hthresh]).
have Hu0 : 0 < bpow radix2 (- fprec t) by apply bpow_gt_0.
have Hule : bpow radix2 (- fprec t) <= /8.
{ have -> : (/8 = bpow radix2 (-3))%R by (simpl; lra). apply bpow_le; lia. }
have H1u : 1 + bpow radix2 (- fprec t) <= 9/8 by lra.
have HuP0 : 0 <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)
  by (apply Rmult_le_pos; [lra | apply Rabs_pos]).
have Hu2P0 : 0 <= bpow radix2 (- fprec t) * bpow radix2 (- fprec t)
                    * Rabs (FT2R xh * FT2R yh)
  by (repeat apply Rmult_le_pos; try lra; apply Rabs_pos).
(* u^2 P <= /8 (u P) *)
have Huu : bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)
        <= /8 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)).
{ have -> : bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)
          = bpow radix2 (- fprec t) * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh))
    by ring.
  apply Rmult_le_compat_r; [exact HuP0 | exact Hule]. }
(* the subnormal floor is tiny: E <= 2 u^2 P *)
have HEP : bpow radix2 emin
        <= 2 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t))
             * Rabs (FT2R xh * FT2R yh).
{ have Hle : bpow radix2 (emin - 1)
          <= bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
  { eapply Rle_trans;
      [| apply Rmult_le_compat_l; [apply Rmult_le_pos; apply bpow_ge_0 | exact Hthresh]].
    rewrite -!bpow_plus. apply bpow_le. lia. }
  have -> : bpow radix2 emin = 2 * bpow radix2 (emin - 1).
  { have H1 : bpow radix2 emin = bpow radix2 (emin - 1) * bpow radix2 1
      by (rewrite -bpow_plus; f_equal; lia).
    rewrite H1. have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
  lra. }
(* subterm finiteness *)
destruct (BPLUS_finite_e t _ _ Hfsum) as [Hfcl1 Hfcl2].
destruct (BFMA_finite_e t xl yh (BFMA xh yl (BMULT xl yl)) Hfcl2) as [_ [_ Hftl1]].
destruct (BFMA_finite_e t xh yl (BMULT xl yl) Hftl1) as [_ [_ Hftl0]].
have Huf' : FT2R xh * FT2R yh <> 0 ->
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh)
  by (move => _; exact Hthresh).
(* |cl1| <= u P and |ch| >= P - u P *)
have Hcl1u : Rabs (FT2R (Fast2Mult_err xh yh)) <= /2 * ulp (FT2R xh * FT2R yh)
  by (apply Fast2Mult_accuracy_norm; exact Hfmul).
have Hulpxhyh : ulp (FT2R xh * FT2R yh)
             <= Rabs (FT2R xh * FT2R yh) * bpow radix2 (1 - fprec t).
{ apply ulp_FLT_le. eapply Rle_trans; [| exact Hthresh]. apply bpow_le.
  unfold common.emin, SpecFloat.emin. pose proof fprec_lb t; lia. }
have HBp : bpow radix2 (1 - fprec t) = 2 * bpow radix2 (- fprec t).
{ have -> : (1 - fprec t = 1 + - fprec t)%Z by lia.
  rewrite bpow_plus. have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
have Hcl1 : Rabs (FT2R (Fast2Mult_err xh yh))
         <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
{ rewrite HBp in Hulpxhyh. nra. }
have Hcl1_eq : FT2R (Fast2Mult_err xh yh) = FT2R xh * FT2R yh - FT2R (Fast2Mult_mul xh yh)
  by (apply Fast2MultModel_correct; [exact Hfmul | exact Huf']).
have Hch_lb : Rabs (FT2R xh * FT2R yh) - bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)
           <= Rabs (FT2R (Fast2Mult_mul xh yh)).
{ have Hche : FT2R (Fast2Mult_mul xh yh) = FT2R xh * FT2R yh - FT2R (Fast2Mult_err xh yh)
    by (rewrite Hcl1_eq; ring).
  rewrite Hche.
  eapply Rle_trans; [| apply Rabs_triang_inv].
  have := Hcl1. lra. }
(* the three products (relative bounds) *)
have Hxhyl : Rabs (FT2R xh * FT2R yl)
          <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
{ have Hyl := @dw_low_le_u_high t STD yh yl Hdwy.
  rewrite !Rabs_mult. have Hxhp : 0 <= Rabs (FT2R xh) by apply Rabs_pos. nra. }
have Hxlyh : Rabs (FT2R xl * FT2R yh)
          <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
{ have Hxl := @dw_low_le_u_high t STD xh xl Hdwx.
  rewrite !Rabs_mult. have Hyhp : 0 <= Rabs (FT2R yh) by apply Rabs_pos. nra. }
have Hxlyl : Rabs (FT2R xl * FT2R yl)
          <= bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
{ have Hxl := @dw_low_le_u_high t STD xh xl Hdwx.
  have Hyl := @dw_low_le_u_high t STD yh yl Hdwy.
  rewrite !Rabs_mult.
  have Hxlp : 0 <= Rabs (FT2R xl) by apply Rabs_pos.
  have Hylp : 0 <= Rabs (FT2R yl) by apply Rabs_pos.
  have Hstep : Rabs (FT2R xl) * Rabs (FT2R yl)
            <= (bpow radix2 (- fprec t) * Rabs (FT2R xh))
               * (bpow radix2 (- fprec t) * Rabs (FT2R yh))
    by (apply Rmult_le_compat; [exact Hxlp | exact Hylp | exact Hxl | exact Hyl]).
  eapply Rle_trans; [exact Hstep|]. apply Req_le; ring. }
(* |tl0| <= u P *)
have Htl0 : Rabs (FT2R (BMULT xl yl))
         <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
{ rewrite -BMULT_round_correct; [| exact Hftl0].
  eapply Rle_trans; [ apply (round_abs_le_of_abs_bound _ _ Hxlyl) |].
  have Hm := Rmult_le_compat_l _ _ _ Hu2P0 H1u. lra. }
(* |tl1| <= 3 u P *)
have Harg1 : Rabs (FT2R xh * FT2R yl + FT2R (BMULT xl yl))
          <= 2 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh))
  by (eapply Rle_trans; [apply Rabs_triang|]; lra).
have Htl1 : Rabs (FT2R (BFMA xh yl (BMULT xl yl)))
         <= 3 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)).
{ rewrite -BFMA_round_correct; [| exact Hftl1].
  eapply Rle_trans; [ apply (round_abs_le_of_abs_bound _ _ Harg1) |].
  have Hc0 : 0 <= 2 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)) by lra.
  have Hm := Rmult_le_compat_l _ _ _ Hc0 H1u. lra. }
(* |cl2| <= 5 u P *)
have Harg2 : Rabs (FT2R xl * FT2R yh + FT2R (BFMA xh yl (BMULT xl yl)))
          <= 4 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh))
  by (eapply Rle_trans; [apply Rabs_triang|]; lra).
have Hcl2 : Rabs (FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))
         <= 5 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)).
{ rewrite -BFMA_round_correct; [| exact Hfcl2].
  eapply Rle_trans; [ apply (round_abs_le_of_abs_bound _ _ Harg2) |].
  have Hc0 : 0 <= 4 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)) by lra.
  have Hm := Rmult_le_compat_l _ _ _ Hc0 H1u. lra. }
(* |cl1 + cl2| <= 6 u P <= (1-u) P <= |ch| *)
have Hw : Rabs (FT2R (Fast2Mult_err xh yh)
                + FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))
       <= Rabs (FT2R (Fast2Mult_mul xh yh)).
{ eapply Rle_trans; [apply Rabs_triang|].
  eapply Rle_trans; [apply Rplus_le_compat; [exact Hcl1 | exact Hcl2]|].
  eapply Rle_trans; [| exact Hch_lb]. nra. }
exact Hw.
Qed.

(* Rounded form used by the runtime closing Fast2Sum.  The argument form above
   is also needed when the corresponding FLX node is compared with FLT. *)
Lemma aux_cl3_le_ch (xh xl yh yl : ftype t) :
  (3 <= fprec t)%Z ->
  double_word_prop xh xl ->
  double_word_prop yh yl ->
  is_finite (BMULT xh yh) = true ->
  is_finite (BPLUS (Fast2Mult_err xh yh)
                   (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) = true ->
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh) ->
  Rabs (FT2R (BPLUS (Fast2Mult_err xh yh)
                    (BFMA xl yh (BFMA xh yl (BMULT xl yl)))))
    <= Rabs (FT2R (Fast2Mult_mul xh yh)).
Proof.
move => Hp3 Hdwx Hdwy Hfmul Hfsum Hthresh.
have Hw := aux_cl3_arg_le_ch xh xl yh yl
  Hp3 Hdwx Hdwy Hfmul Hfsum Hthresh.
rewrite -BPLUS_round_correct; [| exact Hfsum].
apply abs_round_le_generic.
all: try exact Hw.
all: try apply valid_rnd_N.
all: try apply generic_format_abs.
all: try exact valid_fexp_inst.
all: try apply generic_format_FLT_FT2R.
Qed.

(* Sharper per-term error bound: the relative term and the subnormal floor are a
   MAX, not a sum.  In the normal range ulp v = 2u|v| so the error is <= u|v| <= uc
   with no floor; in the subnormal range the error is <= 1/2 bpow emin and the
   relative term is smaller.  This lets aux_eta_bnd ABSORB the four 1/2 bpow emin
   floors into the u^2 P scale rather than adding them, dropping |eta| from ~11 to
   ~7.5 u^2 P. *)
Lemma aux_err_step2 (v c : R) :
  Rabs v <= c ->
  Rabs (round radix2 fexp (Znearest choice) v - v)
    <= Rmax (c * bpow radix2 (- fprec t)) (/2 * bpow radix2 emin).
Proof.
move => Hv.
have He := @Ulp.error_le_half_ulp radix2 fexp valid_fexp_inst choice v.
have Hvp := Rabs_pos v.
have Hu0 : 0 <= bpow radix2 (- fprec t) by apply bpow_ge_0.
destruct (Rle_lt_dec (bpow radix2 (emin + fprec t - 1)) (Rabs v)) as [Hn | Hs].
- (* normal: 1/2 ulp v <= u|v| <= u c *)
  have Hle : ulp v <= Rabs v * bpow radix2 (1 - fprec t) by apply ulp_FLT_le.
  have HBe : bpow radix2 (1 - fprec t) = 2 * bpow radix2 (- fprec t).
  { have -> : (1 - fprec t = 1 + - fprec t)%Z by lia.
    rewrite bpow_plus. have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
  rewrite HBe in Hle.
  eapply Rle_trans; [exact He|]. eapply Rle_trans; [| apply Rmax_l]. nra.
- (* subnormal: ulp v = bpow emin *)
  have Heq : ulp v = bpow radix2 emin.
  { apply ulp_FLT_small;
      first [ apply fprec_gt_0 | eapply Rlt_trans; [exact Hs | apply bpow_lt; lia] ]. }
  eapply Rle_trans; [exact He|]. rewrite Heq. apply Rmax_r.
Qed.

(* Aggregate error bound for the underflow leg: |e0+e1+e2+e3| <= 15/2 u^2 P.  Uses
   the floor-ABSORBING chain (aux_err_step2 gives each error as a MAX of relative
   term and subnormal floor, not a sum): magnitudes |tl0|<=2u^2P, |tl1|<=uP+4u^2P,
   |cl2|<=2uP+7u^2P (leading coeffs 1,2,3 on uP), each error e_i <= u*|arg_i| for
   i>=1 (floor absorbed) and e0<=u^2P.  Sum = 7 u^2 P + 13 u^3 P <= 15/2 u^2 P via
   u <= 1/32 (from 5 <= fprec t).  The floors are no longer additive. *)
Local Lemma aux_eta_bnd (xh xl yh yl : ftype t) :
  (5 <= fprec t)%Z ->
  double_word_prop xh xl -> double_word_prop yh yl ->
  is_finite (BMULT xh yh) = true ->
  is_finite (BMULT xl yl) = true ->
  is_finite (BFMA xh yl (BMULT xl yl)) = true ->
  is_finite (BFMA xl yh (BFMA xh yl (BMULT xl yl))) = true ->
  is_finite (BPLUS (Fast2Mult_err xh yh)
                   (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) = true ->
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh) ->
  Rabs ((FT2R (BMULT xl yl) - FT2R xl * FT2R yl)
        + (FT2R (BFMA xh yl (BMULT xl yl))
           - (FT2R xh * FT2R yl + FT2R (BMULT xl yl)))
        + (FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))
           - (FT2R xl * FT2R yh + FT2R (BFMA xh yl (BMULT xl yl))))
        + (FT2R (BPLUS (Fast2Mult_err xh yh)
                       (BFMA xl yh (BFMA xh yl (BMULT xl yl))))
           - (FT2R (Fast2Mult_err xh yh)
              + FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))))
    <= 15/2 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t))
          * Rabs (FT2R xh * FT2R yh).
Proof.
move => Hp5 Hdwx Hdwy Hfmul Hftl0 Hftl1 Hfcl2 Hfsum Hthresh.
have HP0 : 0 < Rabs (FT2R xh * FT2R yh)
  by (eapply Rlt_le_trans; [apply bpow_gt_0 | exact Hthresh]).
have Hu0 : 0 < bpow radix2 (- fprec t) by apply bpow_gt_0.
have Hule : bpow radix2 (- fprec t) <= /32.
{ have -> : (/32 = bpow radix2 (-5))%R by (simpl; lra). apply bpow_le; lia. }
have H1u : 1 + bpow radix2 (- fprec t) <= 9/8 by lra.
have HuP0 : 0 <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)
  by (apply Rmult_le_pos; [lra | apply Rabs_pos]).
have Hu2P0 : 0 <= bpow radix2 (- fprec t) * bpow radix2 (- fprec t)
                    * Rabs (FT2R xh * FT2R yh)
  by (repeat apply Rmult_le_pos; try lra; apply Rabs_pos).
have Huu : bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)
        <= /8 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)).
{ have -> : bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)
          = bpow radix2 (- fprec t) * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh))
    by ring.
  apply Rmult_le_compat_r; [exact HuP0 |]. have := Hule; lra. }
have HEP : bpow radix2 emin
        <= 2 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t))
             * Rabs (FT2R xh * FT2R yh).
{ have Hle : bpow radix2 (emin - 1)
          <= bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
  { eapply Rle_trans;
      [| apply Rmult_le_compat_l; [apply Rmult_le_pos; apply bpow_ge_0 | exact Hthresh]].
    rewrite -!bpow_plus. apply bpow_le. lia. }
  have -> : bpow radix2 emin = 2 * bpow radix2 (emin - 1).
  { have H1 : bpow radix2 emin = bpow radix2 (emin - 1) * bpow radix2 1
      by (rewrite -bpow_plus; f_equal; lia).
    rewrite H1. have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
  lra. }
have Huf' : FT2R xh * FT2R yh <> 0 ->
  bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh)
  by (move => _; exact Hthresh).
(* argument-magnitude chain (copied from aux_cl3_le_ch) *)
have Hcl1u : Rabs (FT2R (Fast2Mult_err xh yh)) <= /2 * ulp (FT2R xh * FT2R yh)
  by (apply Fast2Mult_accuracy_norm; exact Hfmul).
have Hulpxhyh : ulp (FT2R xh * FT2R yh)
             <= Rabs (FT2R xh * FT2R yh) * bpow radix2 (1 - fprec t).
{ apply ulp_FLT_le. eapply Rle_trans; [| exact Hthresh]. apply bpow_le.
  unfold common.emin, SpecFloat.emin. pose proof fprec_lb t; lia. }
have HBp : bpow radix2 (1 - fprec t) = 2 * bpow radix2 (- fprec t).
{ have -> : (1 - fprec t = 1 + - fprec t)%Z by lia.
  rewrite bpow_plus. have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
have Hcl1 : Rabs (FT2R (Fast2Mult_err xh yh))
         <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
{ rewrite HBp in Hulpxhyh. nra. }
have Hxhyl : Rabs (FT2R xh * FT2R yl)
          <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
{ have Hyl := @dw_low_le_u_high t STD yh yl Hdwy.
  rewrite !Rabs_mult. have Hxhp : 0 <= Rabs (FT2R xh) by apply Rabs_pos. nra. }
have Hxlyh : Rabs (FT2R xl * FT2R yh)
          <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
{ have Hxl := @dw_low_le_u_high t STD xh xl Hdwx.
  rewrite !Rabs_mult. have Hyhp : 0 <= Rabs (FT2R yh) by apply Rabs_pos. nra. }
have Hxlyl : Rabs (FT2R xl * FT2R yl)
          <= bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
{ have Hxl := @dw_low_le_u_high t STD xh xl Hdwx.
  have Hyl := @dw_low_le_u_high t STD yh yl Hdwy.
  rewrite !Rabs_mult.
  have Hxlp : 0 <= Rabs (FT2R xl) by apply Rabs_pos.
  have Hylp : 0 <= Rabs (FT2R yl) by apply Rabs_pos.
  have Hstep : Rabs (FT2R xl) * Rabs (FT2R yl)
            <= (bpow radix2 (- fprec t) * Rabs (FT2R xh))
               * (bpow radix2 (- fprec t) * Rabs (FT2R yh))
    by (apply Rmult_le_compat; [exact Hxlp | exact Hylp | exact Hxl | exact Hyl]).
  eapply Rle_trans; [exact Hstep|]. apply Req_le; ring. }
(* Floor-absorbing chain.  Each rounding error is bounded by a MAX (aux_err_step2),
   and each intermediate magnitude by |arg| + error (triangle); so the four
   1/2 bpow emin floors are ABSORBED into the u^2 P scale instead of added.  Leading
   coefficients on uP stay 1,2,3; the u^2 P corrections shrink (2,4,7).  Order:
   compute each error e_i first, then the magnitude it feeds. *)
(* e0, then |tl0| <= 2 u^2 P *)
have He0 : Rabs (FT2R (BMULT xl yl) - FT2R xl * FT2R yl)
        <= bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh).
{ rewrite -BMULT_round_correct; [| exact Hftl0].
  eapply Rle_trans; [ apply (aux_err_step2 _ _ Hxlyl) |].
  apply Rmax_lub; [ have := Hu2P0; have := Hule; nra | have := HEP; lra ]. }
have Htl0 : Rabs (FT2R (BMULT xl yl))
         <= 2 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)).
{ have Hsplit : FT2R (BMULT xl yl)
             = FT2R xl * FT2R yl + (FT2R (BMULT xl yl) - FT2R xl * FT2R yl) by ring.
  rewrite {1}Hsplit. eapply Rle_trans; [apply Rabs_triang|].
  have := Hxlyl. have := He0. lra. }
(* |arg1| <= uP + 2 u^2 P, e1, then |tl1| <= uP + 4 u^2 P *)
have Harg1 : Rabs (FT2R xh * FT2R yl + FT2R (BMULT xl yl))
          <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)
           + 2 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)).
{ eapply Rle_trans; [apply Rabs_triang|]. have := Hxhyl. have := Htl0. lra. }
have He1 : Rabs (FT2R (BFMA xh yl (BMULT xl yl))
                 - (FT2R xh * FT2R yl + FT2R (BMULT xl yl)))
        <= (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)
            + 2 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)))
             * bpow radix2 (- fprec t).
{ rewrite -BFMA_round_correct; [| exact Hftl1].
  eapply Rle_trans; [ apply (aux_err_step2 _ _ Harg1) |].
  apply Rmax_lub; [ apply Rle_refl
                  | have := HuP0; have := Hu2P0; have := HEP; have := Hule; nra ]. }
have Htl1 : Rabs (FT2R (BFMA xh yl (BMULT xl yl)))
         <= bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)
          + 4 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)).
{ have Hsplit : FT2R (BFMA xh yl (BMULT xl yl))
             = (FT2R xh * FT2R yl + FT2R (BMULT xl yl))
               + (FT2R (BFMA xh yl (BMULT xl yl))
                  - (FT2R xh * FT2R yl + FT2R (BMULT xl yl))) by ring.
  rewrite {1}Hsplit. eapply Rle_trans; [apply Rabs_triang|].
  have := Harg1. have := He1. have := Hu2P0. have := Hule. nra. }
(* |arg2| <= 2uP + 4 u^2 P, e2, then |cl2| <= 2uP + 7 u^2 P *)
have Harg2 : Rabs (FT2R xl * FT2R yh + FT2R (BFMA xh yl (BMULT xl yl)))
          <= 2 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh))
           + 4 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)).
{ eapply Rle_trans; [apply Rabs_triang|]. have := Hxlyh. have := Htl1. lra. }
have He2 : Rabs (FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))
                 - (FT2R xl * FT2R yh + FT2R (BFMA xh yl (BMULT xl yl))))
        <= (2 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh))
            + 4 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)))
             * bpow radix2 (- fprec t).
{ rewrite -BFMA_round_correct; [| exact Hfcl2].
  eapply Rle_trans; [ apply (aux_err_step2 _ _ Harg2) |].
  apply Rmax_lub; [ apply Rle_refl
                  | have := HuP0; have := Hu2P0; have := HEP; have := Hule; nra ]. }
have Hcl2 : Rabs (FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))
         <= 2 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh))
          + 7 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)).
{ have Hsplit : FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))
             = (FT2R xl * FT2R yh + FT2R (BFMA xh yl (BMULT xl yl)))
               + (FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))
                  - (FT2R xl * FT2R yh + FT2R (BFMA xh yl (BMULT xl yl)))) by ring.
  rewrite {1}Hsplit. eapply Rle_trans; [apply Rabs_triang|].
  have := Harg2. have := He2. have := Hu2P0. have := Hule. nra. }
(* |arg3| <= 3uP + 7 u^2 P, e3 *)
have Harg3 : Rabs (FT2R (Fast2Mult_err xh yh)
                   + FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))
          <= 3 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh))
           + 7 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)).
{ eapply Rle_trans; [apply Rabs_triang|]. have := Hcl1. have := Hcl2. lra. }
have He3 : Rabs (FT2R (BPLUS (Fast2Mult_err xh yh)
                             (BFMA xl yh (BFMA xh yl (BMULT xl yl))))
                 - (FT2R (Fast2Mult_err xh yh)
                    + FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))))
        <= (3 * (bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh))
            + 7 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t) * Rabs (FT2R xh * FT2R yh)))
             * bpow radix2 (- fprec t).
{ rewrite -BPLUS_round_correct; [| exact Hfsum].
  eapply Rle_trans; [ apply (aux_err_step2 _ _ Harg3) |].
  apply Rmax_lub; [ apply Rle_refl
                  | have := HuP0; have := Hu2P0; have := HEP; have := Hule; nra ]. }
(* triangle over the four terms, then combine numerically:
   sum <= u^2 P + (uP+2u^2P)u + (2uP+4u^2P)u + (3uP+7u^2P)u = 7 u^2 P + 13 u^3 P;
   with u <= 1/32, 13 u^3 P <= 13/32 u^2 P < 1/2 u^2 P, so sum <= 15/2 u^2 P. *)
eapply Rle_trans.
- eapply Rle_trans; [apply Rabs_triang|]. apply Rplus_le_compat; [| exact He3].
  eapply Rle_trans; [apply Rabs_triang|]. apply Rplus_le_compat; [| exact He2].
  eapply Rle_trans; [apply Rabs_triang|]. apply Rplus_le_compat; [exact He0 | exact He1].
- have := HuP0. have := Hu2P0. have := HEP. have := Hule. nra.
Qed.

(* DWTimesDW_mixed_safe_input_cond bounds the real product by /2*Omega; since
   /2*Omega is representable (generic_format_half_Omega), the rounded product stays
   <= /2*Omega. *)
Local Lemma aux_round_half_bnd (a b : ftype t) :
  is_finite (BMULT a b) = true ->
  Rabs (FT2R a * FT2R b) <= /2 * Omega ->
  Rabs (FT2R (BMULT a b)) <= /2 * Omega.
Proof.
move => Hfin Hp.
rewrite -BMULT_round_correct; [| exact Hfin].
apply abs_round_le_generic.
all: try exact Hp.
all: try apply valid_rnd_N.
all: try exact valid_fexp_inst.
all: try apply generic_format_half_Omega.
Qed.

(* MAIN: BOTH components of DWTimesDW3 stay finite under DWTimesDW_mixed_safe_input_cond,
   the weaker condition that has NO underflow hypothesis on the leading
   product.  Two places in the argument used to need the underflow disjunct;
   neither does -- exactly as for Algorithm 9
   (the corresponding DWTimesFP3 finiteness proof):

     - finiteness of cl1 = Fast2Mult_err xh yh is unconditional: the FMA's
       rounded result is at most /2 ulp(xh*yh), so it cannot overflow whatever
       the regime.  Here it comes straight out of DWTimesDW3_fast2mult_finite, which reads it off the
       computed pair's finiteness;

     - finiteness of the closing Fast2Sum's error term used to be routed
       through is_finite_FastSum_ulp, whose ulp-ordering premise comes from
       aux_cl3_le_ch and so needs a NORMAL leading product.  In the underflow
       gap that ordering can genuinely fail.  We take the headroom route
       instead (is_finite_FastSum_small): |cl3| <= 4*2^(femax-p) <= Omega/4
       already bounds both Fast2Sum subtractions, with no ordering and hence no
       regime split.

   So overflow headroom -- all that DWTimesDW_mixed_safe_input_cond asserts beyond the two
   double-word relations -- is exactly what finiteness costs. *)
Local Lemma DWTimesDW3_finite_from_safe_input_cond (xh xl yh yl : ftype t) :
  (4 <= fprec t)%Z ->
  DWTimesDW_mixed_safe_input_cond xh xl yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl).
Proof.
intros Hp4 (Hfxl & Hfyl & Hdwx & Hdwy & Hf2m & Hxhy4).
have Hp3 : (3 <= fprec t)%Z by lia.
have Hfmul : is_finite (BMULT xh yh) = true by exact Hf2m.
have [Hfxh Hfyh] := BMULT_finite_e t xh yh Hfmul.
(* the cond now bounds the real product by /2*Omega; the rounded product then
   stays <= /2*Omega (representable bound, RN monotone) *)
have Hprod : Rabs (FT2R (BMULT xh yh)) <= /2 * Omega
  by (apply aux_round_half_bnd; [exact Hfmul | exact Hxhy4]).
have HΩ : 0 < Omega by apply bpow_gt_0.
have HE0 : 0 <= bpow radix2 (femax t - fprec t) by apply bpow_ge_0.
have HEq : bpow radix2 (femax t - fprec t) <= /4 * Omega.
{ have -> : (/4 * Omega = bpow radix2 (femax t - 2))%R.
  { have -> : Omega = (bpow radix2 (femax t - 2) * bpow radix2 2)%R
      by rewrite -bpow_plus; f_equal; lia.
    have -> : bpow radix2 2 = 4%R by reflexivity. lra. }
  apply bpow_le; pose proof fprec_lb t; lia. }
(* tighter: bpow(femax-fprec) = u*Omega <= Omega/16 (fprec >= 4) *)
have Hbu : bpow radix2 (femax t - fprec t) = bpow radix2 (- fprec t) * Omega
  by (rewrite -bpow_plus; f_equal; lia).
have Hu16 : bpow radix2 (- fprec t) <= /16.
{ have -> : (/16 = bpow radix2 (-4))%R by (simpl; lra).
  apply bpow_le; lia. }
have HE16 : bpow radix2 (femax t - fprec t) <= /16 * Omega.
{ rewrite Hbu. have := bpow_ge_0 radix2 (- fprec t). nra. }
(* ch = BMULT xh yh : finite, bounded by Omega/2 *)
have Hfch : is_finite (Fast2Mult_mul xh yh) = true.
{ unfold Fast2Mult_mul, Fast2Mult, fst. exact Hfmul. }
have Hch4 : Rabs (FT2R (Fast2Mult_mul xh yh)) <= /2 * Omega.
{ unfold Fast2Mult_mul, Fast2Mult, fst. exact Hprod. }
(* cl1 = Fast2Mult_err xh yh : finite, |cl1| <= 1/2 bpow(femax-fprec).
   Finiteness of the error FMA needs NO underflow hypothesis: its rounded
   result is at most /2 ulp(xh*yh), so it cannot overflow in any regime. *)
have Hfcl1 : is_finite (Fast2Mult_err xh yh) = true.
{ destruct (Fast2Mult_finite_unconditional xh yh Hfmul) as [_ H]. exact H. }
have Hcl1u : Rabs (FT2R (Fast2Mult_err xh yh)) <= /2 * ulp (FT2R xh * FT2R yh).
{ apply Fast2Mult_accuracy_norm; exact Hfmul. }
have Hxhy : Rabs (FT2R xh * FT2R yh) <= /2 * Omega
  by (eapply Rle_trans; [exact Hxhy4|]; lra).
have Hxhy_lt : Rabs (FT2R xh * FT2R yh) < Omega by lra.
have Hcl1b : Rabs (FT2R (Fast2Mult_err xh yh)) <= /2 * bpow radix2 (femax t - fprec t).
{ eapply Rle_trans; [exact Hcl1u|]. apply Rmult_le_compat_l; [lra|].
  apply ulp_below_overflow; exact Hxhy_lt. }
(* the three extra products, each <= 1/2 bpow(femax-fprec) *)
have Hxlyl : Rabs (FT2R xl * FT2R yl) <= /2 * bpow radix2 (femax t - fprec t)
  by (apply (aux_xlyl_bnd xh xl yh yl); [exact Hdwx | exact Hdwy | exact Hxhy]).
have Hxhyl : Rabs (FT2R xh * FT2R yl) <= /2 * bpow radix2 (femax t - fprec t)
  by (apply (aux_xhyl_bnd xh xl yh yl); [exact Hdwy | exact Hxhy]).
have Hxlyh : Rabs (FT2R xl * FT2R yh) <= /2 * bpow radix2 (femax t - fprec t)
  by (apply (aux_xlyh_bnd xh xl yh yl); [exact Hdwx | exact Hxhy]).
(* tl0 = BMULT xl yl : finite, |tl0| <= bpow(femax-fprec) *)
have Hxlyl_lt : Rabs (FT2R xl * FT2R yl) < Omega by lra.
have Hftl0 : is_finite (BMULT xl yl) = true.
{ apply no_overflow_mult_is_finite => //.
  eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
  have Hu := ulp_below_overflow _ Hxlyl_lt. lra. }
have Htl0b : Rabs (FT2R (BMULT xl yl)) <= bpow radix2 (femax t - fprec t).
{ rewrite -BMULT_round_correct; [| exact Hftl0].
  eapply Rle_trans; [apply round_abs_le_abs_plus_half_ulp|].
  have Hu := ulp_below_overflow _ Hxlyl_lt. lra. }
(* tl1 = BFMA xh yl tl0 : finite, |tl1| <= 2 bpow(femax-fprec) *)
have Harg1 : Rabs (FT2R xh * FT2R yl + FT2R (BMULT xl yl))
          <= 3/2 * bpow radix2 (femax t - fprec t)
  by (eapply Rle_trans; [apply Rabs_triang|]; lra).
have Harg1_lt : Rabs (FT2R xh * FT2R yl + FT2R (BMULT xl yl)) < Omega
  by (eapply Rle_lt_trans; [exact Harg1|]; lra).
have Hftl1 : is_finite (BFMA xh yl (BMULT xl yl)) = true.
{ apply no_overflow_fma_is_finite => //.
  eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
  have Hu := ulp_below_overflow _ Harg1_lt. lra. }
have Htl1b : Rabs (FT2R (BFMA xh yl (BMULT xl yl))) <= 2 * bpow radix2 (femax t - fprec t).
{ rewrite -BFMA_round_correct; [| exact Hftl1].
  eapply Rle_trans; [apply round_abs_le_abs_plus_half_ulp|].
  have Hu := ulp_below_overflow _ Harg1_lt. lra. }
(* cl2 = BFMA xl yh tl1 : finite, |cl2| <= 3 bpow(femax-fprec) *)
have Harg2 : Rabs (FT2R xl * FT2R yh + FT2R (BFMA xh yl (BMULT xl yl)))
          <= 5/2 * bpow radix2 (femax t - fprec t)
  by (eapply Rle_trans; [apply Rabs_triang|]; lra).
have Harg2_lt : Rabs (FT2R xl * FT2R yh + FT2R (BFMA xh yl (BMULT xl yl))) < Omega
  by (eapply Rle_lt_trans; [exact Harg2|]; lra).
have Hfcl2 : is_finite (BFMA xl yh (BFMA xh yl (BMULT xl yl))) = true.
{ apply no_overflow_fma_is_finite => //.
  eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
  have Hu := ulp_below_overflow _ Harg2_lt. lra. }
have Hcl2b : Rabs (FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))
          <= 3 * bpow radix2 (femax t - fprec t).
{ rewrite -BFMA_round_correct; [| exact Hfcl2].
  eapply Rle_trans; [apply round_abs_le_abs_plus_half_ulp|].
  have Hu := ulp_below_overflow _ Harg2_lt. lra. }
(* cl3 = BPLUS cl1 cl2 : finite, |cl3| <= 4 bpow(femax-fprec) *)
have Hcl3_arg : Rabs (FT2R (Fast2Mult_err xh yh)
                      + FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))
             <= 7/2 * bpow radix2 (femax t - fprec t)
  by (eapply Rle_trans; [apply Rabs_triang|]; lra).
have Hcl3_arg_lt :
  Rabs (FT2R (Fast2Mult_err xh yh) + FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) < Omega
  by (eapply Rle_lt_trans; [exact Hcl3_arg|]; lra).
have Hfcl3 : is_finite (BPLUS (Fast2Mult_err xh yh)
                              (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) = true.
{ apply (no_overflow_sum_is_finite t _ _ Hfcl1 Hfcl2).
  unfold Bplus_no_overflow.
  eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
  have Hu := ulp_below_overflow _ Hcl3_arg_lt. lra. }
have Hcl3b : Rabs (FT2R (BPLUS (Fast2Mult_err xh yh)
                               (BFMA xl yh (BFMA xh yl (BMULT xl yl)))))
          <= 4 * bpow radix2 (femax t - fprec t).
{ rewrite -BPLUS_round_correct; [| exact Hfcl3].
  eapply Rle_trans; [apply round_abs_le_abs_plus_half_ulp|].
  have Hu := ulp_below_overflow _ Hcl3_arg_lt. lra. }
(* leading component: fst (DWTimesDW3) = BPLUS ch cl3, no overflow.
   fprec >= 4 gives 4*bpow(femax-fprec) = 4*2^-fprec*Omega <= /4*Omega, so with
   ch <= /2*Omega the sum stays <= 3/4*Omega and the closing round is < Omega. *)
have H4 : 4 * bpow radix2 (femax t - fprec t) <= /4 * Omega by (rewrite Hbu; nra).
have Hfst : is_finite (BPLUS (Fast2Mult_mul xh yh)
                    (BPLUS (Fast2Mult_err xh yh)
                           (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) = true.
{ apply (no_overflow_sum_is_finite t _ _ Hfch Hfcl3).
  unfold Bplus_no_overflow.
  have Hsum : Rabs (FT2R (Fast2Mult_mul xh yh)
                    + FT2R (BPLUS (Fast2Mult_err xh yh)
                                  (BFMA xl yh (BFMA xh yl (BMULT xl yl)))))
           <= 3/4 * Omega.
  { eapply Rle_trans; [apply Rabs_triang|]. lra. }
  have Hsum_lt : Rabs (FT2R (Fast2Mult_mul xh yh)
                       + FT2R (BPLUS (Fast2Mult_err xh yh)
                                     (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) < Omega
    by (eapply Rle_lt_trans; [exact Hsum|]; lra).
  eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
  have Hu := ulp_below_overflow _ Hsum_lt. lra. }
split.
- (* fst *)
  change (is_finite (BPLUS (Fast2Mult_mul xh yh)
                      (BPLUS (Fast2Mult_err xh yh)
                             (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) = true).
  exact Hfst.
- (* snd: headroom route, no closing-Fast2Sum ordering required *)
  apply (is_finite_FastSum_small (Fast2Mult_mul xh yh)
           (BPLUS (Fast2Mult_err xh yh)
                  (BFMA xl yh (BFMA xh yl (BMULT xl yl)))));
    [ lra | exact Hfst ].
Qed.

(* Closing-Fast2Sum closure from its two primitive obligations. *)
Local Lemma DWTimesDW3_double_word_from_pre (xh xl yh yl : ftype t) :
  is_finite (BPLUS (Fast2Mult_mul xh yh)
                   (BPLUS (Fast2Mult_err xh yh)
                          (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) = true ->
  Rabs (FT2R (BPLUS (Fast2Mult_err xh yh)
                    (BFMA xl yh (BFMA xh yl (BMULT xl yl)))))
    <= Rabs (FT2R (Fast2Mult_mul xh yh)) ->
  double_word (fst (DWTimesDW3 xh xl yh yl)) (snd (DWTimesDW3 xh xl yh yl)).
Proof.
move => Hfp Hord.
exact (Fast2Sum_is_DW (Fast2Mult_mul xh yh)
         (BPLUS (Fast2Mult_err xh yh)
                (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) Hfp Hord).
Qed.

End DWTimesDW_Finite.


(** Error identities and rounding bounds shared by the normal-range relative
    proof and the whole-range mixed proof. *)
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

(** Above the [9/8] boundary band, half a physical ulp is less than
    [8/9*u^2] of the leading product.  This is the quantitative margin that
    keeps the floored normal rounds on the paper proof's midpoint side. *)
Local Lemma low0_half_floor_budget_above_nine_eighths (P : R) :
  9/8*bpow radix2 (eminA+2*fprec t-1) < P ->
  /2*bpow radix2 eminA < 8/9*u^2*P.
Proof.
move => Hfar.
have Hu0 : 0 < u^2 by (apply pow_lt; apply bpow_gt_0).
have HT :
  (/2*bpow radix2 eminA =
    u^2*bpow radix2 (eminA+2*fprec t-1))%R.
{ unfold u.
  change (bpow radix2 (-1)*bpow radix2 eminA =
    bpow radix2 (-fprec t)^2*
      bpow radix2 (eminA+2*fprec t-1)).
  replace (bpow radix2 (-fprec t)^2) with
    (bpow radix2 (-fprec t)*bpow radix2 (-fprec t)) by ring.
  rewrite -!bpow_plus. f_equal. ring. }
rewrite HT.
have Hscale := Rmult_lt_compat_l (8/9*u^2)
  (bpow radix2 (eminA+2*fprec t-1)) P.
have Hcoef : 0 < 8/9*u^2 by nra.
specialize (Hscale Hcoef).
nra.
Qed.

(** At magnitude [3u] the spacing is [4u^2].  Hence even after the sharp
    [tl1] error is added, the accumulated [16/9*u^2] perturbation remains
    strictly below the midpoint and still rounds to [3u]. *)
Local Lemma round_three_u_plus_tail_margin :
  (5 <= fprec t)%Z ->
  round radix2 (FLX_exp (fprec t)) (Znearest choice)
    (3*u+16/9*u^2) = 3*u.
Proof.
move => Hp5.
have Hp1 : (1 < fprec t)%Z by lia.
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu1 : u < 1 by (unfold u;apply Bayleyaux.bpow_lt_1;lia).
replace (3*u+16/9*u^2) with ((3+16/9*u)*u) by ring.
change (round radix2 (FLX_exp (fprec t)) (Znearest choice)
  ((3+16/9*bpow radix2 (-fprec t))*bpow radix2 (-fprec t)) =
  3*bpow radix2 (-fprec t)).
rewrite Bayleyaux.round_bpow. congr Rmult.
apply (DWPlus.rbpowpuW' Hp1 choice); try lra.
- apply (@DWPlus.FLX_format_Rabs_Fnum (fprec t) 3 (Float radix2 3 0)).
  + rewrite /F2R /=. ring.
  + rewrite /=. apply (Rlt_le_trans _ (bpow radix2 2)).
    * change (Rabs 3 < 4). rewrite Rabs_pos_eq; lra.
    * change (bpow radix2 2 <= bpow radix2 (fprec t)).
      apply bpow_le. lia.
- split; [nra|].
  rewrite Ulp.ulp_neq_0; last lra.
  rewrite /Generic_fmt.cexp /FLX_exp (Raux.mag_unique_pos _ _ 2).
  + rewrite bpow_plus. change (16/9*u < /2*(4*u)). nra.
  + change (2 <= 3 < 4). lra.
Qed.

Local Lemma round_two_u_plus_low0_margin :
  (5 <= fprec t)%Z ->
  round radix2 (FLX_exp (fprec t)) (Znearest choice)
    (2*u+7/9*u^2) = 2*u.
Proof.
move => Hp5.
have Hp1 : (1 < fprec t)%Z by lia.
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu1 : u < 1 by (unfold u;apply Bayleyaux.bpow_lt_1;lia).
replace (2*u+7/9*u^2) with ((2+7/9*u)*u) by ring.
change (round radix2 (FLX_exp (fprec t)) (Znearest choice)
  ((2+7/9*bpow radix2 (-fprec t))*bpow radix2 (-fprec t)) =
  2*bpow radix2 (-fprec t)).
rewrite Bayleyaux.round_bpow. congr Rmult.
apply (DWPlus.rbpowpuW' Hp1 choice); try lra.
- apply (@DWPlus.FLX_format_Rabs_Fnum (fprec t) 2 (Float radix2 2 0)).
  + rewrite /F2R /=. ring.
  + rewrite /=. apply (Rlt_le_trans _ (bpow radix2 2)).
    * change (Rabs 2 < 4). rewrite Rabs_pos_eq; lra.
    * change (bpow radix2 2 <= bpow radix2 (fprec t)).
      apply bpow_le. lia.
- split; [nra|].
  rewrite Ulp.ulp_neq_0; last lra.
  rewrite /Generic_fmt.cexp /FLX_exp (Raux.mag_unique_pos _ _ 2).
  + rewrite bpow_plus. change (7/9*u < /2*(4*u)). nra.
  + change (2 <= 2 < 4). lra.
Qed.

Local Lemma round_four_u_plus_easy_margin :
  (5 <= fprec t)%Z ->
  round radix2 (FLX_exp (fprec t)) (Znearest choice)
    (4*u+23/9*u^2) = 4*u.
Proof.
move => Hp5.
have Hp1 : (1 < fprec t)%Z by lia.
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu1 : u < 1 by (unfold u;apply Bayleyaux.bpow_lt_1;lia).
replace (4*u+23/9*u^2) with ((4+23/9*u)*u) by ring.
change (round radix2 (FLX_exp (fprec t)) (Znearest choice)
  ((4+23/9*bpow radix2 (-fprec t))*bpow radix2 (-fprec t)) =
  4*bpow radix2 (-fprec t)).
rewrite Bayleyaux.round_bpow. congr Rmult.
apply (DWPlus.rbpowpuW' Hp1 choice); try lra.
- apply (@DWPlus.FLX_format_Rabs_Fnum (fprec t) 4 (Float radix2 4 0)).
  + rewrite /F2R /=. ring.
  + rewrite /=. apply (Rlt_le_trans _ (bpow radix2 3)).
    * change (Rabs 4 < 8). rewrite Rabs_pos_eq; lra.
    * change (bpow radix2 3 <= bpow radix2 (fprec t)).
      apply bpow_le. lia.
- split; [nra|].
  rewrite Ulp.ulp_neq_0; last lra.
  rewrite /Generic_fmt.cexp /FLX_exp (Raux.mag_unique_pos _ _ 3).
  + rewrite bpow_plus. change (23/9*u < /2*(8*u)). nra.
  + change (4 <= 4 < 8). lra.
Qed.

Local Lemma round_abs_le_two_u_with_low0_margin (a : R) :
  (5 <= fprec t)%Z -> Rabs a <= 2*u+7/9*u^2 ->
  Rabs (round radix2 (FLX_exp (fprec t)) (Znearest choice) a) <= 2*u.
Proof.
move => Hp5 Ha.
rewrite -(@Bayleyaux.rnd_p_abs (fprec t) ltac:(lia) choice choiceP a).
rewrite -(round_two_u_plus_low0_margin Hp5).
apply round_le; [apply FLX_exp_valid, fprec_gt_0|apply valid_rnd_N|exact Ha].
Qed.

Local Lemma round_abs_le_three_u_with_tail_margin (a : R) :
  (5 <= fprec t)%Z -> Rabs a <= 3*u+16/9*u^2 ->
  Rabs (round radix2 (FLX_exp (fprec t)) (Znearest choice) a) <= 3*u.
Proof.
move => Hp5 Ha.
rewrite -(@Bayleyaux.rnd_p_abs (fprec t) ltac:(lia) choice choiceP a).
rewrite -(round_three_u_plus_tail_margin Hp5).
apply round_le; [apply FLX_exp_valid, fprec_gt_0|apply valid_rnd_N|exact Ha].
Qed.

Local Lemma round_error_le_2u2_with_tail_margin (a : R) :
  (5 <= fprec t)%Z -> Rabs a <= 3*u+16/9*u^2 ->
  Rabs (round radix2 (FLX_exp (fprec t)) (Znearest choice) a-a) <= 2*u^2.
Proof.
move => Hp5 Ha.
have Hp1 : (1 < fprec t)%Z by lia.
have Hu0 : 0 < u by apply bpow_gt_0.
set rp := round radix2 (FLX_exp (fprec t)) (Znearest choice).
have Hsym : forall z, rp (-z)=-rp z.
{ move => z. unfold rp. exact (@rnd_p_sym (fprec t) choice choiceP z). }
have Herrabs : Rabs (rp a-a)=Rabs (rp (Rabs a)-Rabs a).
{ destruct (Rle_dec 0 a) as [Ha0|Ha0].
  - have Habsa : Rabs a=a by apply Rabs_pos_eq.
    rewrite Habsa. reflexivity.
  - have Habsa : Rabs a=-a by (apply Rabs_left;lra).
    rewrite Habsa Hsym.
    replace (-rp a- -a)%R with (-(rp a-a))%R by ring.
    exact (eq_sym (Rabs_Ropp (rp a-a))). }
rewrite Herrabs.
have Hpow4 : 4*u=bpow radix2 (2-fprec t).
{ change (4*bpow radix2 (-fprec t)=bpow radix2 (2-fprec t)).
  rewrite bpow_plus /= IZR_Zpower_pos /=.
  have -> : IZR (Z.pow_pos 2 2)=4 by reflexivity. ring. }
destruct (Rle_dec (Rabs a) (3*u)) as [Hsmall|Hlarge].
- have H := @Bayleyaux.error_le_half_ulp' (fprec t) Hp1 choice
    (Rabs a) (2-fprec t)%Z.
  specialize (H ltac:(rewrite Rabs_pos_eq; [rewrite -Hpow4;nra|apply Rabs_pos])).
  fold rp in H.
  have Heq : (/2*u*bpow radix2 (2-fprec t)=2*u^2)%R.
  { rewrite -Hpow4. nra. }
  rewrite Heq in H. exact H.
- have Hroundle := round_abs_le_three_u_with_tail_margin a Hp5 Ha.
  rewrite -(@Bayleyaux.rnd_p_abs (fprec t) Hp1 choice choiceP a)
    in Hroundle. fold rp in Hroundle.
  have Hfmt3 : generic_format radix2 (FLX_exp (fprec t)) (3*u).
  { unfold u. apply (DWPlus.formatS Hp1).
    apply (@DWPlus.FLX_format_Rabs_Fnum (fprec t) 3
      (Float radix2 3 0)).
    - rewrite /F2R /=. ring.
    - rewrite /=. apply (Rlt_le_trans _ (bpow radix2 2)).
      + change (Rabs 3 < 4). rewrite Rabs_pos_eq; lra.
      + change (bpow radix2 2 <= bpow radix2 (fprec t)).
        apply bpow_le. lia. }
  have Hroundge : 3*u <= rp (Rabs a).
  { rewrite -(round_generic radix2 (FLX_exp (fprec t))
      (Znearest choice) (3*u) Hfmt3).
    apply round_le; [apply FLX_exp_valid, fprec_gt_0|apply valid_rnd_N|lra]. }
  have Hround : rp (Rabs a)=3*u by lra.
  rewrite Hround Rabs_left; nra.
Qed.

Local Lemma round_abs_le_four_u_with_easy_margin (a : R) :
  (5 <= fprec t)%Z -> Rabs a <= 4*u+23/9*u^2 ->
  Rabs (round radix2 (FLX_exp (fprec t)) (Znearest choice) a) <= 4*u.
Proof.
move => Hp5 Ha.
rewrite -(@Bayleyaux.rnd_p_abs (fprec t) ltac:(lia) choice choiceP a).
rewrite -(round_four_u_plus_easy_margin Hp5).
apply round_le; [apply FLX_exp_valid, fprec_gt_0|apply valid_rnd_N|exact Ha].
Qed.

Local Lemma round_error_le_2u2_below_four_u (a : R) :
  (5 <= fprec t)%Z -> Rabs a <= 4*u ->
  Rabs (round radix2 (FLX_exp (fprec t)) (Znearest choice) a-a) <= 2*u^2.
Proof.
move => Hp5 Ha.
have Hp1 : (1 < fprec t)%Z by lia.
have Hpow : 4*u=bpow radix2 (2-fprec t).
{ change (4*bpow radix2 (-fprec t)=bpow radix2 (2-fprec t)).
  replace 4 with (bpow radix2 2) by reflexivity.
  rewrite -bpow_plus. f_equal. }
have H := @Bayleyaux.error_le_half_ulp' (fprec t) Hp1 choice
  a (2-fprec t)%Z.
specialize (H ltac:(rewrite -Hpow;exact Ha)).
have Heq : (/2*u*bpow radix2 (2-fprec t)=2*u^2)%R.
{ rewrite -Hpow. nra. }
rewrite Heq in H. exact H.
Qed.

Local Lemma round_error_le_3u2_with_easy_margin (a : R) :
  (5 <= fprec t)%Z -> Rabs a <= 4*u+23/9*u^2 ->
  Rabs (round radix2 (FLX_exp (fprec t)) (Znearest choice) a-a) <= 3*u^2.
Proof.
move => Hp5 Ha.
have Hp1 : (1 < fprec t)%Z by lia.
have Hu0 : 0 < u by apply bpow_gt_0.
set rp := round radix2 (FLX_exp (fprec t)) (Znearest choice).
have Hsym : forall z, rp (-z)=-rp z.
{ move => z. unfold rp. exact (@rnd_p_sym (fprec t) choice choiceP z). }
have Herrabs : Rabs (rp a-a)=Rabs (rp (Rabs a)-Rabs a).
{ destruct (Rle_dec 0 a) as [Ha0|Ha0].
  - have Habsa : Rabs a=a by apply Rabs_pos_eq.
    rewrite Habsa. reflexivity.
  - have Habsa : Rabs a=-a by (apply Rabs_left;lra).
    rewrite Habsa Hsym.
    replace (-rp a- -a)%R with (-(rp a-a))%R by ring.
    exact (eq_sym (Rabs_Ropp (rp a-a))). }
rewrite Herrabs.
destruct (Rle_dec (Rabs a) (4*u)) as [Hsmall|Hlarge].
- have H := round_error_le_2u2_below_four_u (Rabs a) Hp5.
  specialize (H ltac:(rewrite Rabs_pos_eq; [exact Hsmall|apply Rabs_pos])).
  fold rp in H. eapply Rle_trans; [exact H|]. nra.
- have Hroundle := round_abs_le_four_u_with_easy_margin a Hp5 Ha.
  rewrite -(@Bayleyaux.rnd_p_abs (fprec t) Hp1 choice choiceP a)
    in Hroundle. fold rp in Hroundle.
  have Hpow : 4*u=bpow radix2 (2-fprec t).
  { change (4*bpow radix2 (-fprec t)=bpow radix2 (2-fprec t)).
    replace 4 with (bpow radix2 2) by reflexivity.
    rewrite -bpow_plus. f_equal. }
  have Hfmt4 : generic_format radix2 (FLX_exp (fprec t)) (4*u).
  { rewrite Hpow. apply generic_format_bpow. unfold FLX_exp. lia. }
  have Hroundge : 4*u <= rp (Rabs a).
  { rewrite -(round_generic radix2 (FLX_exp (fprec t))
      (Znearest choice) (4*u) Hfmt4).
    apply round_le; [apply FLX_exp_valid, fprec_gt_0|apply valid_rnd_N|lra]. }
  have Hround : rp (Rabs a)=4*u by lra.
  rewrite Hround Rabs_left; nra.
Qed.

Local Lemma round_error_le_u2_with_low0_margin (a : R) :
  (5 <= fprec t)%Z -> Rabs a <= 2*u+7/9*u^2 ->
  Rabs (round radix2 (FLX_exp (fprec t)) (Znearest choice) a-a) <= u^2.
Proof.
move => Hp5 Ha.
have Hp1 : (1 < fprec t)%Z by lia.
have Hu0 : 0 < u by apply bpow_gt_0.
set rp := round radix2 (FLX_exp (fprec t)) (Znearest choice).
have Hsym : forall z, rp (-z)=-rp z.
{ move => z. unfold rp. exact (@rnd_p_sym (fprec t) choice choiceP z). }
have Herrabs : Rabs (rp a-a)=Rabs (rp (Rabs a)-Rabs a).
{ destruct (Rle_dec 0 a) as [Ha0|Ha0].
  - have Habsa : Rabs a=a by apply Rabs_pos_eq.
    rewrite Habsa. reflexivity.
  - have Ha' : a<0 by lra.
    have Habsa : Rabs a=-a by (apply Rabs_left;lra).
    rewrite Habsa Hsym.
    replace (-rp a- -a)%R with (-(rp a-a))%R by ring.
    exact (eq_sym (Rabs_Ropp (rp a-a))). }
rewrite Herrabs.
have Hpow : 2*u=bpow radix2 (1-fprec t).
{ change (2*bpow radix2 (-fprec t)=bpow radix2 (1-fprec t)).
  rewrite bpow_plus /= IZR_Zpower_pos /=.
  have -> : IZR (Z.pow_pos 2 1)=2 by reflexivity. ring. }
destruct (Rle_dec (Rabs a) (2*u)) as [Hsmall|Hlarge].
- have H := @Bayleyaux.error_le_half_ulp' (fprec t) Hp1 choice
    (Rabs a) (1-fprec t)%Z.
  specialize (H ltac:(rewrite Rabs_pos_eq; [rewrite -Hpow;exact Hsmall|apply Rabs_pos])).
  fold rp in H.
  have Heq : (/2*u*bpow radix2 (1-fprec t)=u^2)%R.
  { rewrite -Hpow. nra. }
  rewrite Heq in H.
  exact H.
- have Hroundle := round_abs_le_two_u_with_low0_margin a Hp5 Ha.
  rewrite -(@Bayleyaux.rnd_p_abs (fprec t) Hp1 choice choiceP a)
    in Hroundle.
  fold rp in Hroundle.
  have Hfmt2 : generic_format radix2 (FLX_exp (fprec t)) (2*u).
  { rewrite Hpow. apply generic_format_bpow. unfold FLX_exp. lia. }
  have Hroundge : 2*u <= rp (Rabs a).
  { rewrite -(round_generic radix2 (FLX_exp (fprec t))
      (Znearest choice) (2*u) Hfmt2).
    apply round_le; [apply FLX_exp_valid, fprec_gt_0|apply valid_rnd_N|lra]. }
  have Hround : rp (Rabs a)=2*u by lra.
  rewrite Hround Rabs_left; nra.
Qed.

(** First floored node of the normalized Algorithm-12 replay.  Despite the
    low-word floor, [tl1] retains both of the paper proof's sharp facts:
    output magnitude at most [2u] and rounding error at most [u^2]. *)
Local Lemma low0_tl1_sharp
    (P f base : R) :
  (5 <= fprec t)%Z -> 0 <= P -> P <= 2 ->
  Rabs f <= 8/9*u^2*P ->
  Rabs base <= 2*u-u^2 ->
  let tl1 := round radix2 (FLX_exp (fprec t)) (Znearest choice) (base+f) in
  Rabs tl1 <= 2*u /\ Rabs (tl1-(base+f)) <= u^2.
Proof.
move => Hp5 HP0 HP2 Hf Hbase /=.
have Hu0 : 0 < u by apply bpow_gt_0.
have Harg : Rabs (base+f) <= 2*u+7/9*u^2.
{ eapply Rle_trans; [apply Rabs_triang|]. nra. }
split.
- exact (round_abs_le_two_u_with_low0_margin (base+f) Hp5 Harg).
- exact (round_error_le_u2_with_low0_margin (base+f) Hp5 Harg).
Qed.

(** Second floored node.  The paper bound on the unrounded cross term has
    a [-u^2] reserve; [tl1]'s [u^2] error consumes that reserve, leaving only
    the low-floor contribution.  Its [16/9*u^2] normalized maximum is below
    the [2*u^2] midpoint at [3u], so [cl2] remains bounded by [3u]. *)
Local Lemma low0_cl2_sharp
    (P f e1 cross : R) :
  (5 <= fprec t)%Z -> 0 <= P -> P <= 2 ->
  Rabs f <= 8/9*u^2*P ->
  Rabs e1 <= u^2 ->
  Rabs cross <= 3*u-u^2 ->
  let cl2 := round radix2 (FLX_exp (fprec t)) (Znearest choice)
    (cross+f+e1) in
  Rabs cl2 <= 3*u /\ Rabs (cl2-(cross+f+e1)) <= 2*u^2.
Proof.
move => Hp5 HP0 HP2 Hf He1 Hcross /=.
have Harg : Rabs (cross+f+e1) <= 3*u+16/9*u^2.
{ have Htri1 := Rabs_triang (cross+f) e1.
  have Htri0 := Rabs_triang cross f.
  eapply Rle_trans; [exact Htri1|].
  eapply Rle_trans; [apply Rplus_le_compat_r;exact Htri0|].
  nra. }
split.
- exact (round_abs_le_three_u_with_tail_margin
    (cross+f+e1) Hp5 Harg).
- exact (round_error_le_2u2_with_tail_margin
    (cross+f+e1) Hp5 Harg).
Qed.

(** With [cl2] back under [3u], the closing round is exactly in the paper's
    original binade: output magnitude at most [4u], error at most [2u^2]. *)
Local Lemma low0_cl3_sharp (cl1 cl2 : R) :
  (5 <= fprec t)%Z ->
  Rabs cl1 <= u -> Rabs cl2 <= 3*u ->
  let cl3 := round radix2 (FLX_exp (fprec t)) (Znearest choice) (cl1+cl2) in
  Rabs cl3 <= 4*u /\ Rabs (cl3-(cl1+cl2)) <= 2*u^2.
Proof.
move => Hp5 Hcl1 Hcl2 /=.
have Hp1 : (1 < fprec t)%Z by lia.
have Harg : Rabs (cl1+cl2) <= 4*u.
{ eapply Rle_trans; [apply Rabs_triang|]. nra. }
have Hpow : 4*u=bpow radix2 (2-fprec t).
{ change (4*bpow radix2 (-fprec t)=bpow radix2 (2-fprec t)).
  rewrite bpow_plus /= IZR_Zpower_pos /=.
  have -> : IZR (Z.pow_pos 2 2)=4 by reflexivity. ring. }
split.
- rewrite -(@Bayleyaux.rnd_p_abs (fprec t) Hp1 choice choiceP (cl1+cl2)).
  rewrite -(round_generic radix2 (FLX_exp (fprec t))
    (Znearest choice) (4*u)).
  2:{ rewrite Hpow. apply generic_format_bpow. unfold FLX_exp. lia. }
  apply round_le; [apply FLX_exp_valid, fprec_gt_0|apply valid_rnd_N|exact Harg].
- have H := @Bayleyaux.error_le_half_ulp' (fprec t) Hp1 choice
    (cl1+cl2) (2-fprec t)%Z.
  specialize (H ltac:(rewrite -Hpow;exact Harg)).
  have Heq : (/2*u*bpow radix2 (2-fprec t)=2*u^2)%R.
  { rewrite -Hpow. nra. }
  rewrite Heq in H. exact H.
Qed.

(* KEYSTONE (DW analog of FP relerr_error_eq): the whole double-word error is the
   sum of the four FLT rounding errors e0..e3.  Fast2Sum is exact (aux_cl3_le_ch),
   the product error cl1 is representable (Fast2MultModel_correct), and each
   intermediate is round(arg); the identity then telescopes by [ring].  Mirrors
   paper DWTimesDW.v:4960-4968. *)
Local Lemma relerr_error_eq :
  (3 <= fprec t)%Z ->
  double_word_prop xh xl ->
  double_word_prop yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  is_finite (BMULT xh yh) = true ->
  bpow radix2 (eminA + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh) ->
  (zh + zl - xr * yr)%R
  = ((FT2R (BMULT xl yl) - FT2R xl * FT2R yl)
     + (FT2R (BFMA xh yl (BMULT xl yl))
        - (FT2R xh * FT2R yl + FT2R (BMULT xl yl)))
     + (FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))
        - (FT2R xl * FT2R yh + FT2R (BFMA xh yl (BMULT xl yl))))
     + (FT2R (BPLUS (Fast2Mult_err xh yh)
                    (BFMA xl yh (BFMA xh yl (BMULT xl yl))))
        - (FT2R (Fast2Mult_err xh yh)
           + FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))))%R.
Proof.
move => Hp3 Hdwx Hdwy Hfp Hfmul Hbig.
set ch  := Fast2Mult_mul xh yh.
set cl2 := BFMA xl yh (BFMA xh yl (BMULT xl yl)).
set cl3 := BPLUS (Fast2Mult_err xh yh) cl2.
have Hfst : is_finite (BPLUS ch cl3) = true by exact (proj1 Hfp).
have Hfcl3 : is_finite cl3 = true
  by (destruct (BPLUS_finite_e t ch cl3 Hfst) as [_ Hf]; exact Hf).
have Hord : Rabs (FT2R cl3) <= Rabs (FT2R ch)
  by exact (aux_cl3_le_ch xh xl yh yl Hp3 Hdwx Hdwy Hfmul Hfcl3 Hbig).
have Hexact : FT2R (Fast2Sum_err ch cl3)
            = FT2R ch + FT2R cl3 - FT2R (Fast2Sum_sum ch cl3)
  by exact (FastTwoSum_correct ch cl3 Hfst Hord).
have Huf' : FT2R xh * FT2R yh <> 0 ->
  bpow radix2 (eminA + 2 * fprec t - 1) <= Rabs (FT2R xh * FT2R yh)
  by (move => _; exact Hbig).
have Hch_eq : FT2R ch = FT2R xh * FT2R yh - FT2R (Fast2Mult_err xh yh).
{ have H := Fast2MultModel_correct xh yh Hfmul Huf'. rewrite -/ch in H. lra. }
have Hsum : (zh + zl)%R = (FT2R ch + FT2R cl3)%R.
{ unfold zh, zl.
  have Hfst_eq : fst (DWTimesDW3 xh xl yh yl) = Fast2Sum_sum ch cl3 by reflexivity.
  have Hsnd_eq : snd (DWTimesDW3 xh xl yh yl) = Fast2Sum_err ch cl3 by reflexivity.
  rewrite Hfst_eq Hsnd_eq Hexact. ring. }
rewrite Hsum Hch_eq. unfold xr, yr, cl3, cl2. ring.
Qed.

(** Mixed-error form of [relerr_error_eq].  The four Algorithm-12 rounding
    errors are decomposed into the relative pieces consumed by the paper's
    normal proof and four explicit floor pieces.  No triangle inequality is
    taken here, so the correlations used by the paper analysis remain
    available. *)
Local Lemma relerr_error_relative_floor_decomposition :
  (3 <= fprec t)%Z ->
  double_word_prop xh xl ->
  double_word_prop yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  is_finite (BMULT xh yh) = true ->
  bpow radix2 (eminA+2*fprec t-1) <= Rabs (FT2R xh*FT2R yh) ->
  exists er0 er1 er2 er3 ef0 ef1 ef2 ef3 : R,
    (zh+zl-xr*yr = (er0+er1+er2+er3)+(ef0+ef1+ef2+ef3))%R /\
    Rabs er0 <= u*Rabs (FT2R xl*FT2R yl) /\
    Rabs er1 <= u*Rabs (FT2R xh*FT2R yl+FT2R (BMULT xl yl)) /\
    Rabs er2 <= u*Rabs (FT2R xl*FT2R yh+
      FT2R (BFMA xh yl (BMULT xl yl))) /\
    Rabs er3 <= u*Rabs (FT2R (Fast2Mult_err xh yh)+
      FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) /\
    Rabs ef0 <= /2*bpow radix2 eminA /\
    Rabs ef1 <= /2*bpow radix2 eminA /\
    Rabs ef2 <= /2*bpow radix2 eminA /\
    Rabs ef3 <= /2*bpow radix2 eminA /\
    Rabs (ef0+ef1+ef2+ef3) <= 2*bpow radix2 eminA /\
    Rabs er1 <= u*Rabs (FT2R xh*FT2R yl+FT2R xl*FT2R yl+er0)
                    +u*Rabs ef0 /\
    Rabs er2 <= u*Rabs (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
                         FT2R xl*FT2R yl+er0+er1)
                    +u*Rabs (ef0+ef1) /\
    Rabs er3 <= u*Rabs (FT2R (Fast2Mult_err xh yh)+
                         FT2R xl*FT2R yh+FT2R xh*FT2R yl+
                         FT2R xl*FT2R yl+er0+er1+er2)
                    +u*Rabs (ef0+ef1+ef2) /\
    Rabs er1 <= u*Rabs (FT2R xh*FT2R yl+FT2R xl*FT2R yl+er0)
                    +/2*u*bpow radix2 eminA /\
    Rabs er2 <= u*Rabs (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
                         FT2R xl*FT2R yl+er0+er1)
                    +u*bpow radix2 eminA /\
    Rabs er3 <= u*Rabs (FT2R (Fast2Mult_err xh yh)+
                         FT2R xl*FT2R yh+FT2R xh*FT2R yl+
                         FT2R xl*FT2R yl+er0+er1+er2)
                    +3/2*u*bpow radix2 eminA /\
    (er0=0 \/ ef0=0) /\
    (er1=0 \/ ef1=0) /\
    (er2=0 \/ ef2=0) /\
    (er3=0 \/ ef3=0) /\
    ((ef0=0 /\ bpow radix2 (eminA+fprec t-1) <=
        Rabs (FT2R xl*FT2R yl)) \/
     (er0=0 /\ Rabs (FT2R xl*FT2R yl) <
        bpow radix2 (eminA+fprec t-1))) /\
    ((ef1=0 /\ bpow radix2 (eminA+fprec t-1) <=
        Rabs (FT2R xh*FT2R yl+FT2R (BMULT xl yl))) \/
     (er1=0 /\ Rabs (FT2R xh*FT2R yl+FT2R (BMULT xl yl)) <
        bpow radix2 (eminA+fprec t-1))) /\
    ((ef2=0 /\ bpow radix2 (eminA+fprec t-1) <=
        Rabs (FT2R xl*FT2R yh+
          FT2R (BFMA xh yl (BMULT xl yl)))) \/
     (er2=0 /\ Rabs (FT2R xl*FT2R yh+
          FT2R (BFMA xh yl (BMULT xl yl))) <
        bpow radix2 (eminA+fprec t-1))) /\
    ((ef3=0 /\ bpow radix2 (eminA+fprec t-1) <=
        Rabs (FT2R (Fast2Mult_err xh yh)+
          FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) \/
     (er3=0 /\ Rabs (FT2R (Fast2Mult_err xh yh)+
          FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) <
        bpow radix2 (eminA+fprec t-1))) /\
    FT2R (BMULT xl yl) =
      FT2R xl*FT2R yl+er0+ef0 /\
    FT2R (BFMA xh yl (BMULT xl yl)) =
      FT2R xh*FT2R yl+FT2R xl*FT2R yl+er0+er1+(ef0+ef1) /\
    FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))) =
      FT2R xl*FT2R yh+FT2R xh*FT2R yl+FT2R xl*FT2R yl+
        er0+er1+er2+(ef0+ef1+ef2) /\
    FT2R (BMULT xl yl) =
      round radix2 (FLX_exp (fprec t)) (Znearest choice)
        (FT2R xl*FT2R yl+ef0) /\
    FT2R (BFMA xh yl (BMULT xl yl)) =
      round radix2 (FLX_exp (fprec t)) (Znearest choice)
        (FT2R xh*FT2R yl+FT2R (BMULT xl yl)+ef1) /\
    FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))) =
      round radix2 (FLX_exp (fprec t)) (Znearest choice)
        (FT2R xl*FT2R yh+FT2R (BFMA xh yl (BMULT xl yl))+ef2) /\
    FT2R (BPLUS (Fast2Mult_err xh yh)
      (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) =
      round radix2 (FLX_exp (fprec t)) (Znearest choice)
        (FT2R (Fast2Mult_err xh yh)+
         FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))+ef3).
Proof.
move => Hp3 DWx DWy FIN Fmul Nprod.
have F0 := DWTimesDW3_low_low_finite xh xl yh yl FIN.
have F1 := DWTimesDW3_first_correction_finite xh xl yh yl FIN.
have F2 := DWTimesDW3_second_correction_finite xh xl yh yl FIN.
have F3 := DWTimesDW3_correction_finite xh xl yh yl FIN.
have D0 := round_FLT_error_relative_plus_floor
  (t:=t) (FT2R xl*FT2R yl).
have D1 := round_FLT_error_relative_plus_floor
  (t:=t) (FT2R xh*FT2R yl+FT2R (BMULT xl yl)).
have D2 := round_FLT_error_relative_plus_floor
  (t:=t) (FT2R xl*FT2R yh+FT2R (BFMA xh yl (BMULT xl yl))).
have D3 := round_FLT_error_relative_plus_floor
  (t:=t) (FT2R (Fast2Mult_err xh yh)+
    FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))).
move: D0 => [er0 [ef0 [D0 [R0 [F0b [Z0 [S0 G0]]]]]]].
move: D1 => [er1 [ef1 [D1 [R1 [F1b [Z1 [S1 G1]]]]]]].
move: D2 => [er2 [ef2 [D2 [R2 [F2b [Z2 [S2 G2]]]]]]].
move: D3 => [er3 [ef3 [D3 [R3 [F3b [Z3 [S3 G3]]]]]]].
rewrite (BMULT_round_correct t xl yl F0) in D0.
rewrite (BFMA_round_correct t xh yl (BMULT xl yl) F1) in D1.
rewrite (BFMA_round_correct t xl yh
  (BFMA xh yl (BMULT xl yl)) F2) in D2.
rewrite (BPLUS_round_correct t (Fast2Mult_err xh yh)
  (BFMA xl yh (BFMA xh yl (BMULT xl yl))) F3) in D3.
rewrite (BMULT_round_correct t xl yl F0) in S0.
rewrite (BFMA_round_correct t xh yl (BMULT xl yl) F1) in S1.
rewrite (BFMA_round_correct t xl yh
  (BFMA xh yl (BMULT xl yl)) F2) in S2.
rewrite (BPLUS_round_correct t (Fast2Mult_err xh yh)
  (BFMA xl yh (BFMA xh yl (BMULT xl yl))) F3) in S3.
have Herr := relerr_error_eq Hp3 DWx DWy FIN Fmul Nprod.
have T0 : FT2R (BMULT xl yl) =
    FT2R xl*FT2R yl+er0+ef0 by lra.
have T1 : FT2R (BFMA xh yl (BMULT xl yl)) =
    FT2R xh*FT2R yl+FT2R xl*FT2R yl+er0+er1+(ef0+ef1).
{ rewrite T0 in D1. lra. }
have T2 : FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))) =
    FT2R xl*FT2R yh+FT2R xh*FT2R yl+FT2R xl*FT2R yl+
      er0+er1+er2+(ef0+ef1+ef2).
{ rewrite T1 in D2. lra. }
have ER1 : Rabs er1 <=
    u*Rabs (FT2R xh*FT2R yl+FT2R xl*FT2R yl+er0)+u*Rabs ef0.
{ eapply Rle_trans; [exact R1|]. rewrite T0.
  replace (FT2R xh*FT2R yl+(FT2R xl*FT2R yl+er0+ef0))%R with
    ((FT2R xh*FT2R yl+FT2R xl*FT2R yl+er0)+ef0)%R by ring.
  have H := Rabs_triang
    (FT2R xh*FT2R yl+FT2R xl*FT2R yl+er0) ef0.
  have Hu0 : 0 <= u by apply bpow_ge_0.
  have H' := Rmult_le_compat_l u _ _ Hu0 H.
  eapply Rle_trans; [exact H'|]. right; ring. }
have ER2 : Rabs er2 <=
    u*Rabs (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
      FT2R xl*FT2R yl+er0+er1)+u*Rabs (ef0+ef1).
{ eapply Rle_trans; [exact R2|]. rewrite T1.
  replace (FT2R xl*FT2R yh+
    (FT2R xh*FT2R yl+FT2R xl*FT2R yl+er0+er1+(ef0+ef1)))%R with
    ((FT2R xl*FT2R yh+FT2R xh*FT2R yl+
      FT2R xl*FT2R yl+er0+er1)+(ef0+ef1))%R by ring.
  have H := Rabs_triang
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
      FT2R xl*FT2R yl+er0+er1) (ef0+ef1).
  have Hu0 : 0 <= u by apply bpow_ge_0.
  have H' := Rmult_le_compat_l u _ _ Hu0 H.
  eapply Rle_trans; [exact H'|]. right; ring. }
have ER3 : Rabs er3 <=
    u*Rabs (FT2R (Fast2Mult_err xh yh)+FT2R xl*FT2R yh+
      FT2R xh*FT2R yl+FT2R xl*FT2R yl+er0+er1+er2)+
      u*Rabs (ef0+ef1+ef2).
{ eapply Rle_trans; [exact R3|]. rewrite T2.
  replace (FT2R (Fast2Mult_err xh yh)+
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+FT2R xl*FT2R yl+
      er0+er1+er2+(ef0+ef1+ef2)))%R with
    ((FT2R (Fast2Mult_err xh yh)+FT2R xl*FT2R yh+
      FT2R xh*FT2R yl+FT2R xl*FT2R yl+er0+er1+er2)+
      (ef0+ef1+ef2))%R by ring.
  have H := Rabs_triang
    (FT2R (Fast2Mult_err xh yh)+FT2R xl*FT2R yh+
      FT2R xh*FT2R yl+FT2R xl*FT2R yl+er0+er1+er2)
    (ef0+ef1+ef2).
  specialize (H NANS STD).
  have Hu0 : 0 <= u by apply bpow_ge_0.
  have H' := Rmult_le_compat_l u _ _ Hu0 H.
  eapply Rle_trans; [exact H'|]. right; ring. }
change (Rabs ef0 <= /2*bpow radix2 eminA) in F0b.
change (Rabs ef1 <= /2*bpow radix2 eminA) in F1b.
change (Rabs ef2 <= /2*bpow radix2 eminA) in F2b.
change (Rabs ef3 <= /2*bpow radix2 eminA) in F3b.
have EF01 : Rabs (ef0+ef1) <= bpow radix2 eminA.
{ eapply Rle_trans; [apply Rabs_triang|]. nra. }
have EF012 : Rabs (ef0+ef1+ef2) <= 3/2*bpow radix2 eminA.
{ have H := Rabs_triang (ef0+ef1) ef2.
  eapply Rle_trans; [exact H|]. nra. }
have ER1f : Rabs er1 <=
    u*Rabs (FT2R xh*FT2R yl+FT2R xl*FT2R yl+er0)+
      /2*u*bpow radix2 eminA.
{ eapply Rle_trans; [exact ER1|].
  apply Rplus_le_compat_l.
  have Hu0 : 0 <= u by apply bpow_ge_0.
  have H := Rmult_le_compat_l u _ _ Hu0 F0b.
  eapply Rle_trans; [exact H|]. right; ring. }
have ER2f : Rabs er2 <=
    u*Rabs (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
      FT2R xl*FT2R yl+er0+er1)+u*bpow radix2 eminA.
{ eapply Rle_trans; [exact ER2|].
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_l; [apply bpow_ge_0|exact EF01]. }
have ER3f : Rabs er3 <=
    u*Rabs (FT2R (Fast2Mult_err xh yh)+FT2R xl*FT2R yh+
      FT2R xh*FT2R yl+FT2R xl*FT2R yl+er0+er1+er2)+
      3/2*u*bpow radix2 eminA.
{ eapply Rle_trans; [exact ER3|].
  apply Rplus_le_compat_l.
  have Hu0 : 0 <= u by apply bpow_ge_0.
  have H := Rmult_le_compat_l u _ _ Hu0 EF012.
  eapply Rle_trans; [exact H|]. right; ring. }
exists er0, er1, er2, er3, ef0, ef1, ef2, ef3.
split.
- rewrite Herr. rewrite D0 D1 D2 D3. ring.
- repeat split; try assumption.
  have H01 := Rabs_triang ef0 ef1.
  have H23 := Rabs_triang ef2 ef3.
  have H := Rabs_triang (ef0+ef1) (ef2+ef3).
  replace (ef0+ef1+ef2+ef3)%R with ((ef0+ef1)+(ef2+ef3))%R by ring.
  eapply Rle_trans; [exact H|].
  eapply Rle_trans.
  { apply Rplus_le_compat; [exact H01|exact H23]. }
  have He := bpow_ge_0 radix2 eminA. nra.
Qed.









End DWTimesDW_Accuracy.

(* ===== migrated from former DWMulDW_div_helpers.v: DW*DW division-regime accuracy helpers ===== *)

(* ===== direct far low-low-underflow apparatus ===== *)
Section FarLow0Apparatus.
Context {NANS: Nans} {t : type} {STD: is_standard t}.
Notation u      := (bpow Zaux.radix2 (- fprec t)).
Notation eminA  := (SpecFloat.emin (fprec t) (femax t)).
(* The explicit FLX rounding chain of the low-order DW*DW nodes with a floor
   term f at the low-low node.  This is a NOTATION (pure syntax), not a
   synthetic algorithm Definition; it expands to the real nodes' FLX rounds. *)
Local Notation FLXlow0 axh axl ayh ayl f :=
  (F2Sum.Fast2Sum (fprec t) choice
    (round radix2 (FLX_exp (fprec t)) (Znearest choice) (axh*ayh))
    (round radix2 (FLX_exp (fprec t)) (Znearest choice)
      ((axh*ayh - round radix2 (FLX_exp (fprec t)) (Znearest choice) (axh*ayh))
       + round radix2 (FLX_exp (fprec t)) (Znearest choice)
           (axl*ayh
            + round radix2 (FLX_exp (fprec t)) (Znearest choice)
                ((axh*ayl + axl*ayl) + f))))).

(* Perturbed-free hard arm: the explicit FLX chain (real algorithm's low-node
   error analysis), no synthetic Definition.  Mirrors the proof of the former
   DWTimesDW12_low0_floored_normalized_hard, whose statement was the packaged
   Definition; here the conclusion is about the explicit Fast2Sum ch cl3. *)
Local Lemma flx_dwtimesdw_hard
    (axh axl ayh ayl f : R) :
  (5 <= fprec t)%Z ->
  DWPlus.double_word (fprec t) choice axh axl ->
  DWPlus.double_word (fprec t) choice ayh ayl ->
  1 <= axh <= 2-2*u -> 1 <= ayh <= 2-2*u ->
  axh*ayh <= 2 ->
  Rabs f <= 8/9*u^2*(axh*ayh) ->
  let '(rzh,rzl) := F2Sum.Fast2Sum (fprec t) choice
    (round radix2 (FLX_exp (fprec t)) (Znearest choice) (axh*ayh))
    (round radix2 (FLX_exp (fprec t)) (Znearest choice)
      ((axh*ayh - round radix2 (FLX_exp (fprec t)) (Znearest choice) (axh*ayh))
       + round radix2 (FLX_exp (fprec t)) (Znearest choice)
           (axl*ayh
            + round radix2 (FLX_exp (fprec t)) (Znearest choice)
                ((axh*ayl + axl*ayl) + f)))) in
  Rabs ((rzh+rzl)-(axh+axl)*(ayh+ayl)-f) <=
    4*u^2*Rabs ((axh+axl)*(ayh+ayl))+3*Rabs f.
Proof.
move => Hp5 DWx DWy Hxh Hyh HP Hf.
have Hp1 : (1 < fprec t)%Z by lia.
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu1 : u < 1 by (unfold u;apply Bayleyaux.bpow_lt_1;lia).
have Hu : u <= /32.
{ unfold u. have -> : (/32:R)=bpow radix2 (-5) by (simpl;lra).
  apply bpow_le;lia. }
have Hxlu : Rabs axl <= u.
{ exact (@DWTimesDW.double_lpart_u (fprec t) Hp1 choice axh axl
    DWx ltac:(lra)). }
have Hylu : Rabs ayl <= u.
{ exact (@DWTimesDW.double_lpart_u (fprec t) Hp1 choice ayh ayl
    DWy ltac:(lra)). }
set rp := round radix2 (FLX_exp (fprec t)) (Znearest choice).
set ch := rp (axh*ayh).
set cl1 := axh*ayh-ch.
set base1 := axh*ayl+axl*ayl.
set tl1 := rp (base1+f).
(* reconcile the goal's cl2 argument (def form axl*ayh+tl1) with the
   analysis form cross+f+(tl1-(base1+f)) *)
have Ecl2arg : axl*ayh + tl1 = (axh*ayl+ayh*axl+axl*ayl)+f+(tl1-(base1+f)).
{ unfold base1. ring. }
rewrite Ecl2arg.
set cross := axh*ayl+ayh*axl+axl*ayl.
set cl2 := rp (cross+f+(tl1-(base1+f))).
set cl3 := rp (cl1+cl2).
have Hxhyl : Rabs (axh*ayl) <= 2*u-2*u^2.
{ rewrite Rabs_mult Rabs_pos_eq; [|lra].
  replace (2*u-2*u^2)%R with ((2-2*u)*u)%R by ring.
  apply Rmult_le_compat; try apply Rabs_pos; lra. }
have Hlow : Rabs (axl*ayl) <= u^2.
{ rewrite Rabs_mult. replace (u^2)%R with (u*u)%R by ring.
  apply Rmult_le_compat; try apply Rabs_pos; assumption. }
have Hbase1 : Rabs base1 <= 2*u-u^2.
{ unfold base1. eapply Rle_trans; [apply Rabs_triang|]. nra. }
have Htl1 := low0_tl1_sharp
  (axh*ayh) f base1 Hp5 ltac:(nra) HP Hf Hbase1.
destruct Htl1 as [Htl1 He1].
change (Rabs tl1 <= 2*u) in Htl1.
change (Rabs (tl1-(base1+f)) <= u^2) in He1.
have Hsumxy : axh+ayh <= 3-2*u.
{ apply (@DWTimesDW.l5_2F (fprec t) Hp1 axh ayh).
  - exact (proj1 (proj1 DWx)).
  - exact (proj1 (proj1 DWy)).
  - split; lra.
  - split; lra.
  - exact HP. }
have Hcross0 : Rabs (axh*ayl+ayh*axl) <= 3*u-2*u^2.
{ eapply Rle_trans; [apply Rabs_triang|].
  rewrite !Rabs_mult.
  rewrite (Rabs_pos_eq axh); [|lra].
  rewrite (Rabs_pos_eq ayh); [|lra].
  have H1 := Rmult_le_compat_l axh _ _ ltac:(lra) Hylu.
  have H2 := Rmult_le_compat_l ayh _ _ ltac:(lra) Hxlu.
  nra. }
have Hcross : Rabs cross <= 3*u-u^2.
{ unfold cross. replace (axh*ayl+ayh*axl+axl*ayl)%R with
    ((axh*ayl+ayh*axl)+(axl*ayl))%R by ring.
  eapply Rle_trans; [apply Rabs_triang|]. nra. }
have Hcl2 := low0_cl2_sharp
  (axh*ayh) f (tl1-(base1+f)) cross Hp5 ltac:(nra) HP
  Hf He1 Hcross.
destruct Hcl2 as [Hcl2 He2].
change (Rabs cl2 <= 3*u) in Hcl2.
change (Rabs (cl2-(cross+f+(tl1-(base1+f)))) <= 2*u^2) in He2.
have Hcl1 : Rabs cl1 <= u.
{ unfold cl1,ch,rp.
  replace (axh*ayh-
    round radix2 (FLX_exp (fprec t)) (Znearest choice) (axh*ayh))%R with
    (-(round radix2 (FLX_exp (fprec t)) (Znearest choice) (axh*ayh)-
       axh*ayh))%R by ring.
  rewrite Rabs_Ropp.
  replace u with (/2*u*bpow radix2 1)%R.
  2:{ simpl. nra. }
  apply (@Bayleyaux.error_le_half_ulp' (fprec t) Hp1 choice
    (axh*ayh) 1%Z).
  rewrite Rabs_pos_eq; [change (axh*ayh<=2);exact HP|nra]. }
have Fcl1 : generic_format radix2 (FLX_exp (fprec t)) cl1.
{ have Hneg : generic_format radix2 (FLX_exp (fprec t)) (-cl1).
  {
  replace (-cl1)%R with
    (rp (axh*ayh)-axh*ayh)%R by (unfold cl1,ch;ring).
  unfold rp. apply Mult_error.mult_error_FLX;
    [exact (fprec_gt_0 t)|apply valid_rnd_N|
     exact (proj1 (proj1 DWx))|exact (proj1 (proj1 DWy))]. }
  have Hopp := generic_format_opp radix2 (FLX_exp (fprec t)) (-cl1) Hneg.
  rewrite Ropp_involutive in Hopp. exact Hopp. }
have Hcl3 := low0_cl3_sharp cl1 cl2 Hp5 Hcl1 Hcl2.
destruct Hcl3 as [Hcl3 He3].
change (Rabs cl3 <= 4*u) in Hcl3.
change (Rabs (cl3-(cl1+cl2)) <= 2*u^2) in He3.
have Hchge : 1 <= Rabs ch.
{ unfold ch,rp.
  rewrite -(round_generic radix2 (FLX_exp (fprec t))
    (Znearest choice) 1).
  2:{ change (generic_format radix2 (FLX_exp (fprec t))
        (bpow radix2 0)); apply generic_format_bpow;unfold FLX_exp;lia. }
  rewrite -(@Bayleyaux.rnd_p_abs (fprec t) Hp1 choice choiceP (axh*ayh)).
  apply round_le; [apply FLX_exp_valid, fprec_gt_0|apply valid_rnd_N|].
  rewrite Rabs_pos_eq; nra. }
have H4u : 4*u <= 1.
{ have H := bpow_le radix2 (-fprec t) (-2) ltac:(lia).
  change (u <= /4) in H. nra. }
have Hord : Rabs cl3 <= Rabs ch.
{ lra. }
have Fch : generic_format radix2 (FLX_exp (fprec t)) ch.
{ unfold ch,rp. apply generic_format_round;
    [apply FLX_exp_valid, fprec_gt_0|apply valid_rnd_N]. }
have Fcl3 : generic_format radix2 (FLX_exp (fprec t)) cl3.
{ unfold cl3,rp. apply generic_format_round;
    [apply FLX_exp_valid, fprec_gt_0|apply valid_rnd_N]. }
have Hrsym : forall z,
  round radix2 (FLX_exp (fprec t)) (Znearest choice) (-z) =
  -round radix2 (FLX_exp (fprec t)) (Znearest choice) z.
{ exact (@rnd_p_sym (fprec t) choice choiceP). }
have Hrad : (radix_val radix2 <= 3)%Z by (change (2<=3)%Z;lia).
have Hfast := @F2Sum.F2Sum_correct_abs (fprec t) Hp1 choice
  Hrsym Hrad ch cl3 Fch Fcl3 Hord.
unfold F2Sum.Fast2Sum_correct in Hfast.
case Efast: (F2Sum.Fast2Sum (fprec t) choice ch cl3) => [rzh rzl].
rewrite Efast /= in Hfast.
have Hsum : rzh+rzl=ch+cl3 by lra.
have Herrid :
  rzh+rzl-(axh+axl)*(ayh+ayl)-f =
    (tl1-(base1+f))+(cl2-(cross+f+(tl1-(base1+f))))+
      (cl3-(cl1+cl2)).
{ rewrite Hsum. unfold cl1,base1,cross. ring. }
have Fcl2 : generic_format radix2 (FLX_exp (fprec t)) cl2.
{ unfold cl2,rp. apply generic_format_round;
    [apply FLX_exp_valid,fprec_gt_0|apply valid_rnd_N]. }
have Hxlb := Hxlu. move/Rabs_le_inv: Hxlb => [Hxl Hxlu'].
have Hylb := Hylu. move/Rabs_le_inv: Hylb => [Hyl Hylu'].
have Hxp : 0 < axh+axl by nra.
have Hyp : 0 < ayh+ayl by nra.
have Hxyabs : Rabs ((axh+axl)*(ayh+ayl))=
    (axh+axl)*(ayh+ayl).
{ rewrite Rabs_mult !Rabs_pos_eq; lra. }
have Hxylo : (1-u)^2 <= Rabs ((axh+axl)*(ayh+ayl)).
{ rewrite Hxyabs.
  have H1 : 1-u <= axh+axl by lra.
  have H2 : 1-u <= ayh+ayl by lra.
  replace ((1-u)^2)%R with ((1-u)*(1-u))%R by ring.
  apply Rmult_le_compat; nra. }
have He3zero_eq : axh=1 \/ ayh=1 -> cl3-(cl1+cl2)=0.
{ move => [Hxeq|Hyeq].
  - have Hcl10 : cl1=0.
    { unfold cl1,ch,rp. rewrite Hxeq Rmult_1_l.
      rewrite round_generic; [ring|exact (proj1 (proj1 DWy))]. }
    unfold cl3,rp. rewrite Hcl10 Rplus_0_l.
    rewrite round_generic; [ring|exact Fcl2].
  - have Hcl10 : cl1=0.
    { unfold cl1,ch,rp. rewrite Hyeq Rmult_1_r.
      rewrite round_generic; [ring|exact (proj1 (proj1 DWx))]. }
    unfold cl3,rp. rewrite Hcl10 Rplus_0_l.
    rewrite round_generic; [ring|exact Fcl2]. }
have Hnext (a : R) :
    generic_format radix2 (FLX_exp (fprec t)) a ->
    1 <= a -> a<>1 -> 1+2*u <= a.
{ move => Fa Ha Hane.
  have Hlt : 1<a by lra.
  have Hsucc : succ radix2 (FLX_exp (fprec t)) 1 <= a.
  { apply succ_le_lt; try assumption.
    - apply FLX_exp_valid. exact (fprec_gt_0 t).
    - change (generic_format radix2 (FLX_exp (fprec t))
        (bpow radix2 0)).
      apply generic_format_bpow. unfold FLX_exp. lia. }
  rewrite succ_eq_pos in Hsucc; [|lra].
  have Hulp : Ulp.ulp radix2 (FLX_exp (fprec t)) 1=2*u.
  { rewrite ulp_neq_0; [|lra].
    unfold cexp, FLX_exp. rewrite mag_1.
    change (bpow radix2 (1-fprec t)=2*bpow radix2 (-fprec t)).
    rewrite bpow_plus. reflexivity. }
  rewrite Hulp in Hsucc. exact Hsucc. }
rewrite Herrid.
have Hfinish3 : Rabs ((tl1-(base1+f))+
    (cl2-(cross+f+(tl1-(base1+f))))+(cl3-(cl1+cl2))) <= 3*u^2 ->
    Rabs ((tl1-(base1+f))+
      (cl2-(cross+f+(tl1-(base1+f))))+(cl3-(cl1+cl2))) <=
      4*u^2*Rabs ((axh+axl)*(ayh+ayl))+3*Rabs f.
{ move => Herr3.
  have Hc : 3 <= 4*((1-u)^2) by nra.
  have Hcoef0 := Rmult_le_compat_r (u^2) _ _ (pow2_ge_0 u) Hc.
  have Hcoef : 3*u^2 <= 4*u^2*((1-u)^2).
  { eapply Rle_trans;[exact Hcoef0|]. apply Req_le. ring. }
  have Hscale := Rmult_le_compat_l (4*u^2) _ _ ltac:(nra) Hxylo.
  eapply Rle_trans;[exact Herr3|].
  eapply Rle_trans;[exact Hcoef|].
  eapply Rle_trans;[exact Hscale|].
  have Hf0 := Rabs_pos f. nra. }
have Hfinish4 : axh<>1 -> ayh<>1 ->
    Rabs ((tl1-(base1+f))+
      (cl2-(cross+f+(tl1-(base1+f))))+(cl3-(cl1+cl2))) <= 4*u^2 ->
    Rabs ((tl1-(base1+f))+
      (cl2-(cross+f+(tl1-(base1+f))))+(cl3-(cl1+cl2))) <=
      4*u^2*Rabs ((axh+axl)*(ayh+ayl))+3*Rabs f.
{ move => Hxne Hyne Herr4.
  have Hxn := Hnext axh (proj1 (proj1 DWx)) (proj1 Hxh) Hxne.
  have Hyn := Hnext ayh (proj1 (proj1 DWy)) (proj1 Hyh) Hyne.
  have Hxy1 : 1 <= Rabs ((axh+axl)*(ayh+ayl)).
  { rewrite Hxyabs.
    have Hsx : 1+u <= axh+axl by lra.
    have Hsy : 1+u <= ayh+ayl by lra.
    have Hmul : (1+u)*(1+u) <= (axh+axl)*(ayh+ayl).
    { apply Rmult_le_compat; [nra|nra|exact Hsx|exact Hsy]. }
    eapply Rle_trans;[|exact Hmul]. nra. }
  have Hscale := Rmult_le_compat_l (4*u^2) _ _ ltac:(nra) Hxy1.
  replace (4*u^2*1)%R with (4*u^2)%R in Hscale by ring.
  eapply Rle_trans;[exact Herr4|].
  eapply Rle_trans;[exact Hscale|].
  have Hf0 := Rabs_pos f. nra. }
have Hpow2 : 2*u=bpow radix2 (1-fprec t).
{ change (2*bpow radix2 (-fprec t)=bpow radix2 (1-fprec t)).
  rewrite bpow_plus /= IZR_Zpower_pos /=.
  have -> : IZR (Z.pow_pos 2 1)=2 by reflexivity. ring. }
destruct (Rlt_dec (Rabs cl2) (2*u)) as [Hcl2small|Hcl2large].
- have Harg2 : Rabs (cross+f+(tl1-(base1+f))) < 2*u.
  { destruct (Rle_dec (2*u)
      (Rabs (cross+f+(tl1-(base1+f))))) as [Hge|Hlt]; [|lra].
    have Hmono :
      round radix2 (FLX_exp (fprec t)) (Znearest choice) (2*u) <=
      round radix2 (FLX_exp (fprec t)) (Znearest choice)
        (Rabs (cross+f+(tl1-(base1+f)))).
    { apply round_le;
        [apply FLX_exp_valid,fprec_gt_0|apply valid_rnd_N|exact Hge]. }
    have F2u : generic_format radix2 (FLX_exp (fprec t)) (2*u).
    { rewrite Hpow2. apply generic_format_bpow. unfold FLX_exp. lia. }
    rewrite (round_generic radix2 (FLX_exp (fprec t))
      (Znearest choice) (2*u) F2u) in Hmono.
    rewrite (@Bayleyaux.rnd_p_abs (fprec t) Hp1 choice choiceP
      (cross+f+(tl1-(base1+f)))) in Hmono.
    fold rp cl2 in Hmono. lra. }
  have He2small := @Bayleyaux.error_le_half_ulp' (fprec t) Hp1 choice
    (cross+f+(tl1-(base1+f))) (1-fprec t)%Z.
  specialize (He2small ltac:(rewrite -Hpow2;apply Rlt_le;exact Harg2)).
  have He2small' :
    Rabs (cl2-(cross+f+(tl1-(base1+f)))) <= u^2.
  { change (Rabs (cl2-(cross+f+(tl1-(base1+f)))) <=
      /2*u*bpow radix2 (1-fprec t)) in He2small.
    eapply Rle_trans; [exact He2small|].
    rewrite -Hpow2. nra. }
  have Htri1 := Rabs_triang
    ((tl1-(base1+f))+(cl2-(cross+f+(tl1-(base1+f)))))
    (cl3-(cl1+cl2)).
  have Htri0 := Rabs_triang (tl1-(base1+f))
    (cl2-(cross+f+(tl1-(base1+f)))).
  destruct (Req_dec axh 1) as [Hxeq|Hxne].
  + apply Hfinish3.
    have He3z := He3zero_eq (or_introl Hxeq). rewrite He3z Rplus_0_r.
    eapply Rle_trans;[exact Htri0|]. nra.
  + destruct (Req_dec ayh 1) as [Hyeq|Hyne].
    * apply Hfinish3.
      have He3z := He3zero_eq (or_intror Hyeq). rewrite He3z Rplus_0_r.
      eapply Rle_trans;[exact Htri0|]. nra.
    * apply (Hfinish4 Hxne Hyne).
      eapply Rle_trans; [exact Htri1|].
      eapply Rle_trans; [apply Rplus_le_compat_r;exact Htri0|].
      eapply Rle_trans.
      { apply Rplus_le_compat.
        - apply Rplus_le_compat; [exact He1|exact He2small'].
        - exact He3. }
      nra.
- have Hcl2ge : 2*u <= Rabs cl2 by lra.
  have Hcl2pow : bpow radix2 (1-fprec t) <= Rabs cl2.
  { rewrite -Hpow2. exact Hcl2ge. }
  destruct (@DWTimesFP.ex_mul (fprec t) cl2 (1-fprec t)%Z
    Hcl2pow Fcl2) as [mcl2 Hmcl2].
  have Fx : generic_format radix2 (FLX_exp (fprec t)) axh
    by exact (proj1 (proj1 DWx)).
  have Fy : generic_format radix2 (FLX_exp (fprec t)) ayh
    by exact (proj1 (proj1 DWy)).
  have Hx1 : bpow radix2 0 <= Rabs axh.
  { change (1<=Rabs axh). rewrite Rabs_pos_eq; lra. }
  have Hy1 : bpow radix2 0 <= Rabs ayh.
  { change (1<=Rabs ayh). rewrite Rabs_pos_eq; lra. }
  destruct (@DWTimesFP.ex_mul (fprec t) axh 0%Z Hx1 Fx)
    as [mx Hmx].
  destruct (@DWTimesFP.ex_mul (fprec t) ayh 0%Z Hy1 Fy)
    as [my Hmy].
  have Hprodgrid : axh*ayh=IZR (mx*my)*(4*u^2).
  { change (bpow radix2 0) with 1 in Hmx.
    change (bpow radix2 0) with 1 in Hmy.
    rewrite Hmx Hmy !Rmult_1_r mult_IZR. ring. }
  have Hch1 : bpow radix2 0 <= Rabs ch by exact Hchge.
  destruct (@DWTimesFP.ex_mul (fprec t) ch 0%Z Hch1 Fch)
    as [mch Hmch].
  have Hchgrid : ch=IZR (mch*2^(fprec t-1))*(4*u^2).
  { rewrite Hmch.
    have HE : 2*u=4*u^2*bpow radix2 (fprec t-1).
    { change (2*bpow radix2 (-fprec t) =
        4*bpow radix2 (-fprec t)^2*bpow radix2 (fprec t-1)).
      replace 2 with (bpow radix2 1) by reflexivity.
      replace 4 with (bpow radix2 2) by reflexivity.
      replace (bpow radix2 (-fprec t)^2) with
        (bpow radix2 (-fprec t)*bpow radix2 (-fprec t)) by ring.
      rewrite -!bpow_plus. f_equal. ring. }
    rewrite HE mult_IZR.
    rewrite (IZR_Zpower radix2); [|lia].
    change (bpow radix2 0) with 1. ring. }
  set mcl1 := (mx*my-mch*2^(fprec t-1))%Z.
  have Hgrid2 : cl2=IZR mcl2*(4*u^2).
  { rewrite Hmcl2 -Hpow2. ring. }
  have Hgrid1 : cl1=IZR mcl1*(4*u^2).
  { unfold cl1,mcl1. rewrite Hprodgrid Hchgrid -Rmult_minus_distr_r.
    rewrite minus_IZR. reflexivity. }
  set mg := (mcl1+mcl2)%Z.
  have Hgrid : cl1+cl2=IZR mg*(4*u^2).
  { rewrite Hgrid1 Hgrid2 /mg plus_IZR. ring. }
  have Harg3 : Rabs (cl1+cl2) <= 4*u.
  { eapply Rle_trans; [apply Rabs_triang|]. nra. }
  have Hmg : Rabs (IZR mg) <= bpow radix2 (fprec t).
  { have Hg := Harg3.
    rewrite Hgrid Rabs_mult in Hg.
    have Hpos : Rabs (4*u^2)=4*u^2.
    { rewrite Rabs_pos_eq; [reflexivity|]. clear -Hu0; nra. }
    rewrite Hpos in Hg.
    have H4u2pos : 0<4*u^2 by (clear -Hu0;nra).
    apply (Rmult_le_reg_r (4*u^2)); [exact H4u2pos|].
    eapply Rle_trans; [exact Hg|].
    apply Req_le.
    change (4*bpow radix2 (-fprec t) =
      bpow radix2 (fprec t)*(4*bpow radix2 (-fprec t)^2)).
    replace 4 with (bpow radix2 2) by reflexivity.
    replace (bpow radix2 (-fprec t)^2) with
      (bpow radix2 (-fprec t)*bpow radix2 (-fprec t)) by ring.
    rewrite -!bpow_plus. f_equal. ring. }
  have Hunit : 4*u^2=bpow radix2 (2-2*fprec t).
  { change (4*bpow radix2 (-fprec t)^2 =
      bpow radix2 (2-2*fprec t)).
    replace 4 with (bpow radix2 2) by reflexivity.
    replace (bpow radix2 (-fprec t)^2) with
      (bpow radix2 (-fprec t)*bpow radix2 (-fprec t)) by ring.
    rewrite -!bpow_plus. f_equal. ring. }
  have Fsum : generic_format radix2 (FLX_exp (fprec t)) (cl1+cl2).
  { rewrite Hgrid.
    destruct Hmg as [Hmg|Hmg].
    - replace (IZR mg*(4*u^2))%R with
        (F2R (Float radix2 mg (2-2*fprec t))) by
        (rewrite Hunit /F2R /=;ring).
      apply (@DWPlus.FLX_format_Rabs_Fnum (fprec t)
        (F2R (Float radix2 mg (2-2*fprec t)))
        (Float radix2 mg (2-2*fprec t)));
        [reflexivity|exact Hmg].
    - have Hpoweq : Rabs (IZR mg)=bpow radix2 (fprec t) by lra.
      have Hbp : Rabs (bpow radix2 (fprec t))=
          bpow radix2 (fprec t) by
          (rewrite Rabs_pos_eq; [reflexivity|apply bpow_ge_0]).
      rewrite -Hbp in Hpoweq.
      destruct (Rabs_eq_Rabs _ _ Hpoweq) as [Hm|Hm]; rewrite Hm.
      + replace (bpow radix2 (fprec t)*(4*u^2))%R with
          (bpow radix2 (2-fprec t)) by
          (rewrite Hunit -bpow_plus;f_equal;ring).
        apply generic_format_bpow. unfold FLX_exp. lia.
      + rewrite Ropp_mult_distr_l_reverse.
        apply generic_format_opp.
        replace (bpow radix2 (fprec t)*(4*u^2))%R with
          (bpow radix2 (2-fprec t)) by
          (rewrite Hunit -bpow_plus;f_equal;ring).
        apply generic_format_bpow. unfold FLX_exp. lia. }
  have He3zero : cl3-(cl1+cl2)=0.
  { unfold cl3,rp. rewrite round_generic; [ring|exact Fsum]. }
  apply Hfinish3. rewrite He3zero Rplus_0_r.
  eapply Rle_trans; [apply Rabs_triang|].
  eapply Rle_trans; [apply Rplus_le_compat; [exact He1|exact He2]|].
  nra.
Qed.

Local Lemma flx_dwtimesdw_easy
    (axh axl ayh ayl f : R) :
  (5 <= fprec t)%Z ->
  DWPlus.double_word (fprec t) choice axh axl ->
  DWPlus.double_word (fprec t) choice ayh ayl ->
  1 <= axh <= 2-2*u -> 1 <= ayh <= 2-2*u ->
  2 < axh*ayh ->
  Rabs f <= 8/9*u^2*(axh*ayh) ->
  let '(rzh,rzl) := F2Sum.Fast2Sum (fprec t) choice
    (round radix2 (FLX_exp (fprec t)) (Znearest choice) (axh*ayh))
    (round radix2 (FLX_exp (fprec t)) (Znearest choice)
      ((axh*ayh - round radix2 (FLX_exp (fprec t)) (Znearest choice) (axh*ayh))
       + round radix2 (FLX_exp (fprec t)) (Znearest choice)
           (axl*ayh
            + round radix2 (FLX_exp (fprec t)) (Znearest choice)
                ((axh*ayl + axl*ayl) + f)))) in
  Rabs ((rzh+rzl)-(axh+axl)*(ayh+ayl)-f) <=
    4*u^2*Rabs ((axh+axl)*(ayh+ayl))+3*Rabs f.
Proof.
move => Hp5 DWx DWy Hxh Hyh HP Hf.
have Hp1 : (1 < fprec t)%Z by lia.
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /32.
{ unfold u. have -> : (/32:R)=bpow radix2 (-5) by (simpl;lra).
  apply bpow_le;lia. }
have Hxlu : Rabs axl <= u.
{ exact (@DWTimesDW.double_lpart_u (fprec t) Hp1 choice axh axl
    DWx ltac:(lra)). }
have Hylu : Rabs ayl <= u.
{ exact (@DWTimesDW.double_lpart_u (fprec t) Hp1 choice ayh ayl
    DWy ltac:(lra)). }
set rp := round radix2 (FLX_exp (fprec t)) (Znearest choice).
set ch := rp (axh*ayh).
set cl1 := axh*ayh-ch.
set base1 := axh*ayl+axl*ayl.
set tl1 := rp (base1+f).
set cross := axh*ayl+ayh*axl+axl*ayl.
set e1 := tl1-(base1+f).
have Ecl2arg : axl*ayh + tl1 = cross+f+e1.
{ unfold cross,e1,base1. ring. }
rewrite Ecl2arg.
set cl2 := rp (cross+f+e1).
set e2 := cl2-(cross+f+e1).
set cl3 := rp (cl1+cl2).
set e3 := cl3-(cl1+cl2).
have HP4 : axh*ayh < 4 by nra.
have Hlow : Rabs (axl*ayl) <= u^2.
{ rewrite Rabs_mult. replace (u^2)%R with (u*u)%R by ring.
  apply Rmult_le_compat; try apply Rabs_pos; assumption. }
have Hxhyl : Rabs (axh*ayl) <= 2*u-2*u^2.
{ rewrite Rabs_mult Rabs_pos_eq; [|lra].
  replace (2*u-2*u^2)%R with ((2-2*u)*u)%R by ring.
  apply Rmult_le_compat; try apply Rabs_pos; lra. }
have Hbase : Rabs base1 <= 2*u-u^2.
{ unfold base1. eapply Rle_trans; [apply Rabs_triang|]. nra. }
have Hf4 : Rabs f <= 32/9*u^2 by nra.
have Harg1 : Rabs (base1+f) <= 2*u+23/9*u^2.
{ eapply Rle_trans; [apply Rabs_triang|]. nra. }
have He1b : Rabs e1 <= 2*u^2.
{ unfold e1,tl1,rp. exact (round_error_le_2u2_below_four_u
    (base1+f) Hp5 ltac:(eapply Rle_trans;[exact Harg1|];nra)). }
have Hcross : Rabs cross <= 4*u-3*u^2.
{ unfold cross.
  have Htwo : Rabs (axh*ayl+ayh*axl) <= (axh+ayh)*u.
  { eapply Rle_trans; [apply Rabs_triang|].
    rewrite !Rabs_mult.
    have Hax : Rabs axh=axh by (apply Rabs_pos_eq;lra).
    have Hay : Rabs ayh=ayh by (apply Rabs_pos_eq;lra).
    rewrite Hax Hay.
    have H1 := Rmult_le_compat_l axh _ _ ltac:(lra) Hylu.
    have H2 := Rmult_le_compat_l ayh _ _ ltac:(lra) Hxlu. nra. }
  replace (axh*ayl+ayh*axl+axl*ayl)%R with
    ((axh*ayl+ayh*axl)+axl*ayl)%R by ring.
  eapply Rle_trans; [apply Rabs_triang|]. nra. }
have Harg2 : Rabs (cross+f+e1) <= 4*u+23/9*u^2.
{ have H0 := Rabs_triang (cross+f) e1.
  have H1 := Rabs_triang cross f.
  eapply Rle_trans; [exact H0|].
  eapply Rle_trans; [apply Rplus_le_compat_r;exact H1|]. nra. }
have Hcl2 : Rabs cl2 <= 4*u.
{ unfold cl2,rp. exact (round_abs_le_four_u_with_easy_margin
    (cross+f+e1) Hp5 Harg2). }
have He2b : Rabs e2 <= 3*u^2.
{ unfold e2,cl2,rp. exact (round_error_le_3u2_with_easy_margin
    (cross+f+e1) Hp5 Harg2). }
have Hcl1 : Rabs cl1 <= 2*u.
{ unfold cl1,ch,rp.
  replace (axh*ayh-round radix2 (FLX_exp (fprec t))
    (Znearest choice) (axh*ayh))%R with
    (-(round radix2 (FLX_exp (fprec t)) (Znearest choice)
      (axh*ayh)-axh*ayh))%R by ring.
  rewrite Rabs_Ropp.
  have H := @Bayleyaux.error_le_half_ulp' (fprec t) Hp1 choice
    (axh*ayh) 2%Z.
  specialize (H ltac:(rewrite Rabs_pos_eq;[apply Rlt_le;exact HP4|nra])).
  change (Rabs (round radix2 (FLX_exp (fprec t)) (Znearest choice)
    (axh*ayh)-axh*ayh) <= /2*u*bpow radix2 2) in H.
  replace (bpow radix2 2) with 4 in H by reflexivity. nra. }
have Harg3 : Rabs (cl1+cl2) <= 6*u.
{ eapply Rle_trans; [apply Rabs_triang|]. nra. }
have He3b : Rabs e3 <= 4*u^2.
{ unfold e3,cl3,rp.
  have H := @Bayleyaux.error_le_half_ulp' (fprec t) Hp1 choice
    (cl1+cl2) (3-fprec t)%Z.
  have Hb : Rabs (cl1+cl2) <= bpow radix2 (3-fprec t).
  { eapply Rle_trans; [exact Harg3|].
    change (6*bpow radix2 (-fprec t) <= bpow radix2 (3-fprec t)).
    rewrite bpow_plus. replace (bpow radix2 3) with 8 by reflexivity. nra. }
  specialize (H Hb).
  have HE : (/2*u*bpow radix2 (3-fprec t)=4*u^2)%R.
  { have H8 : bpow radix2 (3-fprec t)=8*u.
    { change (bpow radix2 (3-fprec t)=
        8*bpow radix2 (-fprec t)).
      replace (8*bpow radix2 (-fprec t))%R with
        (bpow radix2 3*bpow radix2 (-fprec t))%R by reflexivity.
      rewrite -bpow_plus. f_equal. }
    rewrite H8. replace (u^2)%R with (u*u)%R by ring. field. }
  rewrite HE in H. exact H. }
have Fcl1 : generic_format radix2 (FLX_exp (fprec t)) cl1.
{ have Hneg : generic_format radix2 (FLX_exp (fprec t)) (-cl1).
  { replace (-cl1)%R with (rp (axh*ayh)-axh*ayh)%R by
      (unfold cl1,ch;ring).
    unfold rp. apply Mult_error.mult_error_FLX;
      [exact (fprec_gt_0 t)|apply valid_rnd_N|
       exact (proj1 (proj1 DWx))|exact (proj1 (proj1 DWy))]. }
  have Hopp := generic_format_opp radix2 (FLX_exp (fprec t)) (-cl1) Hneg.
  rewrite Ropp_involutive in Hopp. exact Hopp. }
have Fch : generic_format radix2 (FLX_exp (fprec t)) ch.
{ unfold ch,rp. apply generic_format_round;
    [apply FLX_exp_valid,fprec_gt_0|apply valid_rnd_N]. }
have Fcl3 : generic_format radix2 (FLX_exp (fprec t)) cl3.
{ unfold cl3,rp. apply generic_format_round;
    [apply FLX_exp_valid,fprec_gt_0|apply valid_rnd_N]. }
have Hchge : 2 <= Rabs ch.
{ unfold ch,rp.
  rewrite -(round_generic radix2 (FLX_exp (fprec t))
    (Znearest choice) 2).
  2:{ change (generic_format radix2 (FLX_exp (fprec t))
      (bpow radix2 1));apply generic_format_bpow;unfold FLX_exp;lia. }
  rewrite -(@Bayleyaux.rnd_p_abs (fprec t) Hp1 choice choiceP
    (axh*ayh)).
  apply round_le;[apply FLX_exp_valid,fprec_gt_0|apply valid_rnd_N|].
  rewrite Rabs_pos_eq;nra. }
have H8u : bpow radix2 (3-fprec t)=8*u.
{ change (bpow radix2 (3-fprec t)=8*bpow radix2 (-fprec t)).
  replace (8*bpow radix2 (-fprec t))%R with
    (bpow radix2 3*bpow radix2 (-fprec t))%R by reflexivity.
  rewrite -bpow_plus. f_equal. }
have Hcl3 : Rabs cl3 <= 8*u.
{ unfold cl3,rp.
  rewrite -(@Bayleyaux.rnd_p_abs (fprec t) Hp1 choice choiceP (cl1+cl2)).
  rewrite -(round_generic radix2 (FLX_exp (fprec t))
    (Znearest choice) (8*u)).
  2:{ rewrite -H8u. apply generic_format_bpow. unfold FLX_exp. lia. }
  apply round_le;[apply FLX_exp_valid,fprec_gt_0|apply valid_rnd_N|].
  eapply Rle_trans;[exact Harg3|]. nra. }
have Hord : Rabs cl3 <= Rabs ch by nra.
have Hrsym : forall z, rp (-z) = -rp z.
{ move=>z;unfold rp;exact (@rnd_p_sym (fprec t) choice choiceP z). }
have Hfast := @F2Sum.F2Sum_correct_abs (fprec t) Hp1 choice
  Hrsym ltac:(change (2<=3)%Z;lia) ch cl3 Fch Fcl3 Hord.
unfold F2Sum.Fast2Sum_correct in Hfast.
case Efast: (F2Sum.Fast2Sum (fprec t) choice ch cl3) => [rzh rzl].
rewrite Efast /= in Hfast.
have Hsum : rzh+rzl=ch+cl3 by lra.
have Herrid : rzh+rzl-(axh+axl)*(ayh+ayl)-f=e1+e2+e3.
{ rewrite Hsum. unfold e2,e3,cl1,cross. ring. }
rewrite Herrid.
have Hxy : 2*(1-u)^2 < Rabs ((axh+axl)*(ayh+ayl)).
{ have Hxlb := Hxlu. move/Rabs_le_inv: Hxlb => [Hxl Hxlu'].
  have Hylb := Hylu. move/Rabs_le_inv: Hylb => [Hyl Hylu'].
  have Hxp : 0 <= axh+axl by nra.
  have Hyp : 0 <= ayh+ayl by nra.
  rewrite Rabs_mult (Rabs_pos_eq _ Hxp) (Rabs_pos_eq _ Hyp).
  have H1 : axh*(1-u) <= axh+axl by nra.
  have H2 : ayh*(1-u) <= ayh+ayl by nra.
  have Hm : (axh*(1-u))*(ayh*(1-u)) <=
      (axh+axl)*(ayh+ayl).
  { apply Rmult_le_compat; [nra|nra|exact H1|exact H2]. }
  have Hs : 0 < (1-u)^2 by nra.
  have Hstrict := Rmult_lt_compat_r ((1-u)^2) _ _ Hs HP.
  eapply Rlt_le_trans;[|exact Hm].
  replace ((axh*(1-u))*(ayh*(1-u)))%R with
    ((axh*ayh)*(1-u)^2)%R by ring. nra. }
have Hscaled := Rmult_lt_compat_l (4*u^2) _ _ ltac:(nra) Hxy.
have Hscaled' : 4*u^2*(2*(1-u)^2) <=
    4*u^2*Rabs ((axh+axl)*(ayh+ayl)) by (apply Rlt_le;exact Hscaled).
have Hfabs0 := Rabs_pos f.
have Hcoef7 : 7*u^2 <= 4*u^2*(2*(1-u)^2) by nra.
have Hcoef9 : 9*u^2 <= 4*u^2*(2*(1-u)^2)+3*u^2 by nra.
destruct (Rle_dec (Rabs f) (u^2)) as [Hfs|Hfl].
- have He1s : Rabs e1 <= u^2.
  { unfold e1,tl1,rp. apply round_error_le_u2_with_low0_margin;
      [exact Hp5|].
    eapply Rle_trans;[apply Rabs_triang|]. lra. }
  have He2s : Rabs e2 <= 2*u^2.
  { unfold e2,cl2,rp. apply round_error_le_2u2_below_four_u;
      [exact Hp5|].
    have Ht := Rabs_triang (cross+f) e1.
    have Ht' := Rabs_triang cross f.
    eapply Rle_trans;[exact Ht|].
    eapply Rle_trans;[apply Rplus_le_compat_r;exact Ht'|]. lra. }
  have Ht0 := Rabs_triang e1 e2.
  have Ht1 := Rabs_triang (e1+e2) e3.
  eapply Rle_trans;[exact Ht1|].
  eapply Rle_trans;[apply Rplus_le_compat_r;exact Ht0|].
  have Herr7 : Rabs e1+Rabs e2+Rabs e3 <= 7*u^2 by lra.
  eapply Rle_trans;[exact Herr7|].
  eapply Rle_trans;[exact Hcoef7|].
  eapply Rle_trans;[exact Hscaled'|].
  have Hf0 := Rabs_pos f. lra.
- have Ht0 := Rabs_triang e1 e2.
  have Ht1 := Rabs_triang (e1+e2) e3.
  eapply Rle_trans;[exact Ht1|].
  eapply Rle_trans;[apply Rplus_le_compat_r;exact Ht0|].
  have Herr9 : Rabs e1+Rabs e2+Rabs e3 <= 9*u^2 by lra.
  have Hfloor3 : 3*u^2 < 3*Rabs f by lra.
  eapply Rle_trans;[exact Herr9|].
  eapply Rle_trans;[exact Hcoef9|].
  apply Rplus_le_compat;[exact Hscaled'|apply Rlt_le;exact Hfloor3].
Qed.

(* Homogeneity/symmetry of the FLX chain (direct analogues of the
   former DWTimesDW12_low0_floored_{Asym_r,Asym_l,Sx,Sy}). *)
Local Lemma flx_Asym_r (xh xl yh yl f : R) :
  FLXlow0 xh xl (-yh) (-yl) (-f) = F2Sum.pair_opp (FLXlow0 xh xl yh yl f).
Proof.
rewrite !(=^~Ropp_mult_distr_r, rnd_p_sym (fprec t) choice choiceP,
  F2Sum.Fast2Sum_asym (rnd_p_sym (fprec t) choice choiceP)) //.
have -> : (- (xh*yh) - - round radix2 (FLX_exp (fprec t)) (Znearest choice) (xh*yh)) =
    -((xh*yh)-round radix2 (FLX_exp (fprec t)) (Znearest choice) (xh*yh)) by ring.
by rewrite !(=^~Ropp_plus_distr, rnd_p_sym (fprec t) choice choiceP,
  F2Sum.Fast2Sum_asym (rnd_p_sym (fprec t) choice choiceP)) ?Ropp_involutive //;
  apply (rnd_p_sym (fprec t) choice choiceP).
Qed.

Local Lemma flx_Asym_l (xh xl yh yl f : R) :
  FLXlow0 (-xh) (-xl) yh yl (-f) = F2Sum.pair_opp (FLXlow0 xh xl yh yl f).
Proof.
rewrite !(=^~Ropp_mult_distr_l, rnd_p_sym (fprec t) choice choiceP,
  F2Sum.Fast2Sum_asym (rnd_p_sym (fprec t) choice choiceP)) //.
have -> : (- (xh*yh) - - round radix2 (FLX_exp (fprec t)) (Znearest choice) (xh*yh)) =
    -((xh*yh)-round radix2 (FLX_exp (fprec t)) (Znearest choice) (xh*yh)) by ring.
by rewrite !(=^~Ropp_plus_distr, rnd_p_sym (fprec t) choice choiceP,
  F2Sum.Fast2Sum_asym (rnd_p_sym (fprec t) choice choiceP)) ?Ropp_involutive //;
  apply (rnd_p_sym (fprec t) choice choiceP).
Qed.

Local Lemma flx_Sx (xh xl yh yl f : R) (e : Z) :
  FLXlow0 (xh*bpow radix2 e) (xl*bpow radix2 e) yh yl (f*bpow radix2 e) =
  DWTimesFP.map_pair (fun z => z*bpow radix2 e) (FLXlow0 xh xl yh yl f).
Proof.
rewrite !(Rmult_comm _ yh) !(Rmult_comm _ yl)
  !(=^~Rmult_assoc, Bayleyaux.round_bpow, =^~Rmult_plus_distr_r,
    F2Sum.Fast2SumS, =^~Rmult_minus_distr_r)
  !(Rmult_comm yh) //.
all: apply Generic_fmt.generic_format_round.
all: try apply valid_rnd_N.
all: apply FLX_exp_valid; exact (fprec_gt_0 t).
Qed.

Local Lemma flx_Sy (xh xl yh yl f : R) (e : Z) :
  FLXlow0 xh xl (yh*bpow radix2 e) (yl*bpow radix2 e) (f*bpow radix2 e) =
  DWTimesFP.map_pair (fun z => z*bpow radix2 e) (FLXlow0 xh xl yh yl f).
Proof.
rewrite !(=^~Rmult_assoc, Bayleyaux.round_bpow,
  =^~Rmult_plus_distr_r, F2Sum.Fast2SumS,
  =^~Rmult_minus_distr_r) //.
all: apply Generic_fmt.generic_format_round.
all: try apply valid_rnd_N.
all: apply FLX_exp_valid; exact (fprec_gt_0 t).
Qed.

(* Scaling reduction to normalized leading words (direct positive). *)
Local Lemma flx_positive (xh0 xl0 yh0 yl0 f0 : R) :
  (5 <= fprec t)%Z ->
  DWPlus.double_word (fprec t) choice xh0 xl0 ->
  DWPlus.double_word (fprec t) choice yh0 yl0 ->
  0 < xh0 -> 0 < yh0 ->
  Rabs f0 <= 8/9*u^2*Rabs (xh0*yh0) ->
  let '(rzh,rzl) := FLXlow0 xh0 xl0 yh0 yl0 f0 in
  Rabs ((rzh+rzl)-(xh0+xl0)*(yh0+yl0)-f0) <=
    4*u^2*Rabs ((xh0+xl0)*(yh0+yl0))+3*Rabs f0.
Proof.
move => Hp5 DWx DWy Hxp Hyp Hf.
have Hp1 : (1 < fprec t)%Z by lia.
destruct DWx as [[Fxh Fxl] Ex].
destruct DWy as [[Fyh Fyl] Ey].
destruct (DWPlus.scale_generic_12 (p:=fprec t) Fxh Hxp)
  as [ex Hx].
destruct (DWPlus.scale_generic_12 (p:=fprec t) Fyh Hyp)
  as [ey Hy].
set bx := bpow radix2 ex.
set sy := bpow radix2 ey.
set axh := xh0*bx. set axl := xl0*bx.
set ayh := yh0*sy. set ayl := yl0*sy.
set af := f0*bx*sy.
have Hbx : 0<bx by (unfold bx;apply bpow_gt_0).
have Hsy : 0<sy by (unfold sy;apply bpow_gt_0).
have DWax : DWPlus.double_word (fprec t) choice axh axl.
{ split; [split|].
  - unfold axh,bx. exact (DWPlus.formatS Hp1 Fxh ex).
  - unfold axl,bx. exact (DWPlus.formatS Hp1 Fxl ex).
  - unfold axh,axl,bx.
    rewrite -Rmult_plus_distr_r Bayleyaux.round_bpow -Ex. reflexivity. }
have DWay : DWPlus.double_word (fprec t) choice ayh ayl.
{ split; [split|].
  - unfold ayh,sy. exact (DWPlus.formatS Hp1 Fyh ey).
  - unfold ayl,sy. exact (DWPlus.formatS Hp1 Fyl ey).
  - unfold ayh,ayl,sy.
    rewrite -Rmult_plus_distr_r Bayleyaux.round_bpow -Ey. reflexivity. }
have Hax : 1<=axh<=2-2*u by (unfold axh,bx;exact Hx).
have Hay : 1<=ayh<=2-2*u by (unfold ayh,sy;exact Hy).
have Haf : Rabs af <= 8/9*u^2*(axh*ayh).
{ unfold af,axh,ayh.
  rewrite !Rabs_mult.
  have Abx : Rabs bx=bx by (apply Rabs_pos_eq;lra).
  have Asy : Rabs sy=sy by (apply Rabs_pos_eq;lra).
  rewrite Abx Asy.
  rewrite Rabs_mult in Hf.
  have Ax : Rabs xh0=xh0 by (apply Rabs_pos_eq;lra).
  have Ay : Rabs yh0=yh0 by (apply Rabs_pos_eq;lra).
  rewrite Ax Ay in Hf.
  have Hs := Rmult_le_compat_r (bx*sy) _ _ ltac:(nra) Hf.
  nra. }
case E0: (FLXlow0 xh0 xl0 yh0 yl0 f0) => [rzh0 rzl0].
have Escaled : FLXlow0 axh axl ayh ayl af = (rzh0*bx*sy,rzl0*bx*sy).
{ unfold axh,axl,ayh,ayl,af,bx,sy.
  rewrite (flx_Sy (xh0*bpow radix2 ex) (xl0*bpow radix2 ex)
    yh0 yl0 (f0*bpow radix2 ex) ey).
  rewrite (flx_Sx xh0 xl0 yh0 yl0 f0 ex) E0.
  reflexivity. }
have Hnorm :
  let '(rzh,rzl) := FLXlow0 axh axl ayh ayl af in
  Rabs ((rzh+rzl)-(axh+axl)*(ayh+ayl)-af) <=
    4*u^2*Rabs ((axh+axl)*(ayh+ayl))+3*Rabs af.
{ destruct (Rle_dec (axh*ayh) 2) as [Hhard|Heasy].
  - exact (flx_dwtimesdw_hard
      axh axl ayh ayl af Hp5 DWax DWay Hax Hay Hhard Haf).
  - apply flx_dwtimesdw_easy;
      try assumption; lra. }
rewrite Escaled /= in Hnorm.
have Hb : 0<bx*sy by nra.
have HL : Rabs (((rzh0+rzl0)-(xh0+xl0)*(yh0+yl0)-f0)*(bx*sy)) =
    (bx*sy)*Rabs ((rzh0+rzl0)-(xh0+xl0)*(yh0+yl0)-f0).
{ rewrite Rabs_mult (Rabs_pos_eq (bx*sy)); [ring|lra]. }
have HP : Rabs (((xh0+xl0)*(yh0+yl0))*(bx*sy)) =
    (bx*sy)*Rabs ((xh0+xl0)*(yh0+yl0)).
{ rewrite Rabs_mult (Rabs_pos_eq (bx*sy)); [ring|lra]. }
have HF : Rabs (f0*(bx*sy))=(bx*sy)*Rabs f0.
{ rewrite Rabs_mult (Rabs_pos_eq (bx*sy)); [ring|lra]. }
replace ((rzh0*bx*sy+rzl0*bx*sy)-
  (axh+axl)*(ayh+ayl)-af)%R with
  (((rzh0+rzl0)-(xh0+xl0)*(yh0+yl0)-f0)*(bx*sy))%R in Hnorm
  by (unfold axh,axl,ayh,ayl,af;ring).
replace ((axh+axl)*(ayh+ayl))%R with
  (((xh0+xl0)*(yh0+yl0))*(bx*sy))%R in Hnorm
  by (unfold axh,axl,ayh,ayl;ring).
replace af with (f0*(bx*sy)) in Hnorm by (unfold af;ring).
rewrite HL HP HF in Hnorm.
apply (Rmult_le_reg_l (bx*sy)); [exact Hb|].
have HEq : ((bx*sy)*(4*u^2*Rabs ((xh0+xl0)*(yh0+yl0))+
    3*Rabs f0))%R =
    (4*u^2*((bx*sy)*Rabs ((xh0+xl0)*(yh0+yl0)))+
      3*((bx*sy)*Rabs f0))%R by ring.
rewrite HEq. exact Hnorm.
Qed.

(* Sign reduction (direct mixed). *)
Local Lemma flx_mixed (xh0 xl0 yh0 yl0 f0 : R) :
  (5 <= fprec t)%Z ->
  DWPlus.double_word (fprec t) choice xh0 xl0 ->
  DWPlus.double_word (fprec t) choice yh0 yl0 ->
  xh0<>0 -> yh0<>0 ->
  Rabs f0 <= 8/9*u^2*Rabs (xh0*yh0) ->
  let '(rzh,rzl) := FLXlow0 xh0 xl0 yh0 yl0 f0 in
  Rabs ((rzh+rzl)-(xh0+xl0)*(yh0+yl0)-f0) <=
    4*u^2*Rabs ((xh0+xl0)*(yh0+yl0))+3*Rabs f0.
Proof.
move => Hp5 DWx DWy Hx0 Hy0 Hf.
have DWopp (ah al : R) :
    DWPlus.double_word (fprec t) choice ah al ->
    DWPlus.double_word (fprec t) choice (-ah) (-al).
{ move => [[Fh Fl] E]. split;[split|].
  - exact (generic_format_opp _ _ _ Fh).
  - exact (generic_format_opp _ _ _ Fl).
  - replace (-ah+-al)%R with (-(ah+al))%R by ring.
    rewrite (@rnd_p_sym (fprec t) choice choiceP). f_equal. exact E. }
case E0: (FLXlow0 xh0 xl0 yh0 yl0 f0) => [rzh0 rzl0].
destruct (Rlt_dec 0 xh0) as [Hxp|Hxn].
- destruct (Rlt_dec 0 yh0) as [Hyp|Hyn].
  + have H := flx_positive
      xh0 xl0 yh0 yl0 f0 Hp5 DWx DWy Hxp Hyp Hf.
    change (Rabs (fst (FLXlow0 xh0 xl0 yh0 yl0 f0)+
      snd (FLXlow0 xh0 xl0 yh0 yl0 f0)-(xh0+xl0)*(yh0+yl0)-f0) <=
      4*u^2*Rabs ((xh0+xl0)*(yh0+yl0))+3*Rabs f0) in H.
    rewrite E0 /= in H. exact H.
  + have Hyn' : 0 < -yh0 by lra.
    have DWyn := DWopp yh0 yl0 DWy.
    have Hfn : Rabs (-f0) <= 8/9*u^2*Rabs (xh0*(-yh0)).
    { rewrite Rabs_Ropp.
      replace (xh0*(-yh0))%R with (-(xh0*yh0))%R by ring.
      rewrite Rabs_Ropp. exact Hf. }
    have H := flx_positive
      xh0 xl0 (-yh0) (-yl0) (-f0) Hp5 DWx DWyn Hxp Hyn' Hfn.
    change (Rabs (fst (FLXlow0 xh0 xl0 (-yh0) (-yl0) (-f0))+
      snd (FLXlow0 xh0 xl0 (-yh0) (-yl0) (-f0))-
      (xh0+xl0)*(-yh0+-yl0)- -f0) <=
      4*u^2*Rabs ((xh0+xl0)*(-yh0+-yl0))+3*Rabs (-f0)) in H.
    have En : FLXlow0 xh0 xl0 (-yh0) (-yl0) (-f0)=(-rzh0,-rzl0).
    { rewrite (flx_Asym_r xh0 xl0 yh0 yl0 f0) E0. reflexivity. }
    rewrite En /= in H.
    replace ((-rzh0+-rzl0)-
      (xh0+xl0)*(-yh0+-yl0)- -f0)%R with
      (-((rzh0+rzl0)-(xh0+xl0)*(yh0+yl0)-f0))%R in H by ring.
    rewrite Rabs_Ropp in H.
    replace ((xh0+xl0)*(-yh0+-yl0))%R with
      (-((xh0+xl0)*(yh0+yl0)))%R in H by ring.
    rewrite Rabs_Ropp Rabs_Ropp in H. exact H.
- have Hxn' : 0 < -xh0 by lra.
  have DWxn := DWopp xh0 xl0 DWx.
  destruct (Rlt_dec 0 yh0) as [Hyp|Hyn].
  + have Hfn : Rabs (-f0) <= 8/9*u^2*Rabs ((-xh0)*yh0).
    { rewrite Rabs_Ropp.
      replace ((-xh0)*yh0)%R with (-(xh0*yh0))%R by ring.
      rewrite Rabs_Ropp. exact Hf. }
    have H := flx_positive
      (-xh0) (-xl0) yh0 yl0 (-f0) Hp5 DWxn DWy Hxn' Hyp Hfn.
    change (Rabs (fst (FLXlow0 (-xh0) (-xl0) yh0 yl0 (-f0))+
      snd (FLXlow0 (-xh0) (-xl0) yh0 yl0 (-f0))-
      (-xh0+-xl0)*(yh0+yl0)- -f0) <=
      4*u^2*Rabs ((-xh0+-xl0)*(yh0+yl0))+3*Rabs (-f0)) in H.
    have En : FLXlow0 (-xh0) (-xl0) yh0 yl0 (-f0)=(-rzh0,-rzl0).
    { rewrite (flx_Asym_l xh0 xl0 yh0 yl0 f0) E0. reflexivity. }
    rewrite En /= in H.
    replace ((-rzh0+-rzl0)-
      (-xh0+-xl0)*(yh0+yl0)- -f0)%R with
      (-((rzh0+rzl0)-(xh0+xl0)*(yh0+yl0)-f0))%R in H by ring.
    rewrite Rabs_Ropp in H.
    replace ((-xh0+-xl0)*(yh0+yl0))%R with
      (-((xh0+xl0)*(yh0+yl0)))%R in H by ring.
    rewrite Rabs_Ropp Rabs_Ropp in H. exact H.
  + have Hyn' : 0 < -yh0 by lra.
    have DWyn := DWopp yh0 yl0 DWy.
    have Hfp : Rabs f0 <= 8/9*u^2*Rabs ((-xh0)*(-yh0)).
    { replace ((-xh0)*(-yh0))%R with (xh0*yh0)%R by ring. exact Hf. }
    have H := flx_positive
      (-xh0) (-xl0) (-yh0) (-yl0) f0
      Hp5 DWxn DWyn Hxn' Hyn' Hfp.
    change (Rabs (fst (FLXlow0 (-xh0) (-xl0) (-yh0) (-yl0) f0)+
      snd (FLXlow0 (-xh0) (-xl0) (-yh0) (-yl0) f0)-
      (-xh0+-xl0)*(-yh0+-yl0)-f0) <=
      4*u^2*Rabs ((-xh0+-xl0)*(-yh0+-yl0))+3*Rabs f0) in H.
    have En1 : FLXlow0 (-xh0) (-xl0) yh0 yl0 (-f0)=(-rzh0,-rzl0).
    { rewrite (flx_Asym_l xh0 xl0 yh0 yl0 f0) E0. reflexivity. }
    have En : FLXlow0 (-xh0) (-xl0) (-yh0) (-yl0) f0=(rzh0,rzl0).
    { replace f0 with (-(-f0)) by ring.
      rewrite (flx_Asym_r (-xh0) (-xl0) yh0 yl0 (-f0)) En1.
      unfold F2Sum.pair_opp. simpl. f_equal; ring. }
    rewrite En /= in H.
    replace ((-xh0+-xl0)*(-yh0+-yl0))%R with
      ((xh0+xl0)*(yh0+yl0))%R in H by ring.
    exact H.
Qed.

(* The far low-low-underflow bound, DIRECTLY for the real DWTimesDW3, via the
   FLT floor decomposition (no synthetic floored algorithm). *)
Lemma DWTimesDW_abs_low0_far (xh xl yh yl : ftype t) :
  double_word xh xl -> double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  9/8*bpow radix2 (eminA+2*fprec t-1) < Rabs (FT2R xh*FT2R yh) ->
  Rabs (FT2R xl*FT2R yl) < bpow radix2 (eminA+fprec t-1) ->
  bpow radix2 (eminA+fprec t-1) <=
    Rabs (FT2R xh*FT2R yl+FT2R (BMULT xl yl)) ->
  bpow radix2 (eminA+fprec t-1) <=
    Rabs (FT2R xl*FT2R yh+FT2R (BFMA xh yl (BMULT xl yl))) ->
  bpow radix2 (eminA+fprec t-1) <=
    Rabs (FT2R (Fast2Mult_err xh yh)+
      FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) ->
  Rabs (FT2R (fst (DWTimesDW3 xh xl yh yl)) +
        FT2R (snd (DWTimesDW3 xh xl yh yl)) -
        (FT2R xh+FT2R xl)*(FT2R yh+FT2R yl)) <=
    4*u^2*Rabs ((FT2R xh+FT2R xl)*(FT2R yh+FT2R yl))+2*bpow radix2 eminA.
Proof.
move => DWx DWy FIN Hp5 Hfar U0 N1 N2 N3.
have Hp3 : (3 <= fprec t)%Z by lia.
have Fmul := DWTimesDW3_mul_finite xh xl yh yl FIN.
have T0 : bpow radix2 (eminA+2*fprec t-1) <= Rabs (FT2R xh*FT2R yh).
{ have HT0 := bpow_gt_0 radix2 (eminA+2*fprec t-1). nra. }
have Hdec := relerr_error_relative_floor_decomposition xh xl yh yl
  Hp3 DWx DWy FIN Fmul T0.
destruct Hdec as
  (er0 & er1 & er2 & er3 & ef0 & ef1 & ef2 & ef3 &
   Heq & R0 & R1 & R2 & R3 & F0b & F1b & F2b & F3b & Hef &
   ER1 & ER2 & ER3 & ER1f & ER2f & ER3f &
   Z0 & Z1 & Z2 & Z3 & G0 & G1 & G2 & G3 &
   Teq0 & Teq1 & Teq2 & Seq0 & Seq1 & Seq2 & Seq3).
destruct G0 as [[Ef0 N0]|[Er0 N0small]].
{ exfalso;exact (Rlt_not_le _ _ U0 N0). }
destruct G1 as [[Ef1 N1']|[Er1eq N1small]].
2:{ exfalso;exact (Rlt_not_le _ _ N1small N1). }
destruct G2 as [[Ef2 N2']|[Er2eq N2small]].
2:{ exfalso;exact (Rlt_not_le _ _ N2small N2). }
destruct G3 as [[Ef3 N3']|[Er3eq N3small]].
2:{ exfalso;exact (Rlt_not_le _ _ N3small N3). }
subst er0; subst ef1; subst ef2; subst ef3.
rewrite Rplus_0_r in Seq1. rewrite Rplus_0_r in Seq2.
rewrite Rplus_0_r in Seq3.
have T0e : FT2R (BMULT xl yl) = FT2R xl*FT2R yl + ef0
  by (rewrite Teq0; ring).
(* node reconciliations to the real nodes *)
have Etl1 : round radix2 (FLX_exp (fprec t)) (Znearest choice)
    ((FT2R xh*FT2R yl + FT2R xl*FT2R yl) + ef0) =
    FT2R (BFMA xh yl (BMULT xl yl)).
{ rewrite Seq1. f_equal. rewrite T0e. ring. }
have Ecl2 : round radix2 (FLX_exp (fprec t)) (Znearest choice)
    (FT2R xl*FT2R yh + FT2R (BFMA xh yl (BMULT xl yl))) =
    FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))).
{ rewrite Seq2. reflexivity. }
have HDWx : DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl)
  by (apply (dw_word_DWdouble xh xl xh);exact DWx).
have HDWy : DWPlus.double_word (fprec t) choice (FT2R yh) (FT2R yl)
  by (apply (dw_word_DWdouble yh yl yh);exact DWy).
have Fxh := proj1 (proj1 HDWx).
have Fyh := proj1 (proj1 HDWy).
have Htp := DWMulFP_acc.Fast2Mult_correct_weak xh yh Fmul ltac:(auto).
rewrite /DWTimesFP.Fast2Mult /F2Rp /= in Htp.
have Ech := f_equal fst Htp. have Ecl1raw := f_equal snd Htp.
simpl in Ech, Ecl1raw.
have Fcl1 : generic_format radix2 (FLX_exp (fprec t))
    (FT2R xh*FT2R yh -
     round radix2 (FLX_exp (fprec t)) (Znearest choice) (FT2R xh*FT2R yh)).
{ rewrite -Ropp_minus_distr. apply generic_format_opp.
  apply Mult_error.mult_error_FLX;
    [exact (fprec_gt_0 t)|apply valid_rnd_N|exact Fxh|exact Fyh]. }
have Ecl1 : FT2R xh*FT2R yh -
    round radix2 (FLX_exp (fprec t)) (Znearest choice) (FT2R xh*FT2R yh) =
    FT2R (Fast2Mult_err xh yh).
{ rewrite -Ecl1raw. symmetry. apply round_generic;
    [apply valid_rnd_N|exact Fcl1]. }
have Hbridge : FLXlow0 (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl) ef0 =
    F2Rp (DWTimesDW3 xh xl yh yl).
{ rewrite Etl1 Ecl2 Ecl1 Ech -Seq3.
  rewrite (FastTwoSumEq_FLT (Fast2Mult_mul xh yh)
    (BPLUS (Fast2Mult_err xh yh)
      (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) FIN).
  reflexivity. }
(* floor budget from the far threshold *)
have HP0 : 0 < Rabs (FT2R xh*FT2R yh).
{ eapply Rlt_le_trans;[apply bpow_gt_0|exact T0]. }
have Hxh0 : FT2R xh<>0.
{ intro H. rewrite H Rmult_0_l Rabs_R0 in HP0. lra. }
have Hyh0 : FT2R yh<>0.
{ intro H. rewrite H Rmult_0_r Rabs_R0 in HP0. lra. }
have Hbudget : Rabs ef0 <= 8/9*u^2*Rabs (FT2R xh*FT2R yh).
{ have H := low0_half_floor_budget_above_nine_eighths
    (Rabs (FT2R xh*FT2R yh)) Hfar. lra. }
have Hmix := flx_mixed (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl) ef0
  Hp5 HDWx HDWy Hxh0 Hyh0 Hbudget.
change (Rabs (fst (FLXlow0 (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl) ef0)+
    snd (FLXlow0 (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl) ef0)-
    (FT2R xh+FT2R xl)*(FT2R yh+FT2R yl)-ef0) <=
  4*u^2*Rabs ((FT2R xh+FT2R xl)*(FT2R yh+FT2R yl))+3*Rabs ef0) in Hmix.
rewrite Hbridge /F2Rp in Hmix. cbn [fst snd] in Hmix.
have Hz : (FT2R (fst (DWTimesDW3 xh xl yh yl))+
   FT2R (snd (DWTimesDW3 xh xl yh yl))-
   (FT2R xh+FT2R xl)*(FT2R yh+FT2R yl))%R =
  ((FT2R (fst (DWTimesDW3 xh xl yh yl))+
   FT2R (snd (DWTimesDW3 xh xl yh yl))-
   (FT2R xh+FT2R xl)*(FT2R yh+FT2R yl)-ef0)+ef0)%R by ring.
rewrite Hz.
eapply Rle_trans;[apply Rabs_triang|].
eapply Rle_trans;[apply Rplus_le_compat_r;exact Hmix|].
have H4f : 4*Rabs ef0 <= 2*bpow radix2 eminA by (have := F0b; nra).
replace (4*u^2*Rabs ((FT2R xh+FT2R xl)*(FT2R yh+FT2R yl))+3*Rabs ef0+Rabs ef0)%R
  with (4*u^2*Rabs ((FT2R xh+FT2R xl)*(FT2R yh+FT2R yl))+4*Rabs ef0)%R by ring.
apply Rplus_le_compat_l. exact H4f.
Qed.

End FarLow0Apparatus.

Section DWMulDW_Division_Helpers.
Context {NANS: Nans} {t : type} {STD: is_standard t}.
Notation u := (bpow Zaux.radix2 (- fprec t)).
Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Notation eminA := (SpecFloat.emin (fprec t) (femax t)).
Notation ulp := (Ulp.ulp Zaux.radix2 fexp).
Notation OmegaA := (bpow Zaux.radix2 (femax t)).
Local Instance valid_fexp_inst_dh : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.
Variables (xh xl yh yl : ftype t).
Let zh := FT2R (fst (DWTimesDW3 xh xl yh yl)).
Let zl := FT2R (snd (DWTimesDW3 xh xl yh yl)).
Let xr := (FT2R xh + FT2R xl).
Let yr := (FT2R yh + FT2R yl).


(** Sharp normal-range core.  Normality of the leading and low-low products
    propagates enough exact-or-normal structure through the remaining nodes
    to recover the paper's [4u^2] relative bound. *)
Local Lemma DWTimesDW_relative_accuracy_core :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  bpow radix2 (eminA + 2 * fprec t - 1) <=
    Rabs (FT2R xh * FT2R yh) ->
  bpow radix2 (eminA + fprec t - 1) <=
    Rabs (FT2R xl * FT2R yl) ->
  relative_error_DWTimesDW xh xl yh yl <= 4 * u ^ 2.
Proof.
move => Hdw Hdwy Hfin Hp5 Nprod N0.
have Hfmul : is_finite (BMULT xh yh)=true
  by exact (DWTimesDW3_mul_finite xh xl yh yl Hfin).
have Hftl0 : is_finite (BMULT xl yl)=true
  by exact (DWTimesDW3_low_low_finite xh xl yh yl Hfin).
have N1 := normal_low0_implies_low1
  xh xl yh yl ltac:(lia) Hdw Hftl0 N0.
have F2fix := normal_low0_implies_low2_FIX xh xl yh yl Hdwy N0.
specialize (F2fix NANS STD).
have E2 := FIX_FLT_or_normal
  (FT2R (BFMA xh yl (BMULT xl yl))+FT2R xl*FT2R yh) F2fix.
have F3fix := closing_arg_FIX_of_normal_product xh yh
  (BFMA xl yh (BFMA xh yl (BMULT xl yl))) Hfmul Nprod.
specialize (F3fix NANS STD NANS STD).
specialize (F3fix NANS STD).
have E3 := FIX_FLT_or_normal
  (FT2R (Fast2Mult_err xh yh)+
   FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) F3fix.
have Hbridge := DWTimesDW3_FLX_FLT_exact_or_normal
  xh xl yh yl Hfin Nprod N0 N1 E2 E3.
have HDWx : DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl)
  by (apply (dw_word_DWdouble xh xl xh); exact Hdw).
have HDWy : DWPlus.double_word (fprec t) choice (FT2R yh) (FT2R yl)
  by (apply (dw_word_DWdouble yh yl yh); exact Hdwy).
have Hpaper :
  (let (zh, zl) := DWTimesDW.DWTimesDW12 (fprec t) choice
                     (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl) in
   let xy := (FT2R xh + FT2R xl) * (FT2R yh + FT2R yl) in
   Rabs ((zh + zl - xy) / xy) <
     4 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t)))
  := @DWTimesDW.DWTimesDW12_correct (fprec t) (fprec_gt_one t)
       choice choiceP Hp5 (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl)
       HDWx HDWy.
rewrite Hbridge /F2Rp /= in Hpaper.
unfold relative_error_DWTimesDW, zh, zl, xr, yr.
replace (4*u^2)%R with
  (4*(bpow radix2 (-fprec t)*bpow radix2 (-fprec t)))%R by ring.
apply Rlt_le. exact Hpaper.
Qed.

(** Public pure-relative result for the normal range. *)
Theorem DWTimesDW_relative_accuracy :
  (5 <= fprec t)%Z ->
  DWTimesDW_relative_error_input_cond xh xl yh yl ->
  relative_error_DWTimesDW xh xl yh yl <= 4 * u ^ 2.
Proof.
move => Hp5 [Hsafe [Nprod N0]].
have Hfin := DWTimesDW3_finite_from_safe_input_cond xh xl yh yl ltac:(lia) Hsafe.
move: Hsafe => [_ [_ [DWx [DWy _]]]].
exact (DWTimesDW_relative_accuracy_core
  DWx DWy Hfin Hp5 Nprod N0).
Qed.

Corollary DWTimesDW_abs_low0_normal :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  bpow radix2 (eminA + 2 * fprec t - 1) <=
    Rabs (FT2R xh * FT2R yh) ->
  bpow radix2 (eminA + fprec t - 1) <=
    Rabs (FT2R xl * FT2R yl) ->
  Rabs (zh+zl-xr*yr) <= 4*u^2*Rabs (xr*yr).
Proof.
move => Hdw Hdwy Hfin Hp5 Nprod N0.
have Hrel := DWTimesDW_relative_accuracy_core
  Hdw Hdwy Hfin Hp5 Nprod N0.
have Hprod0 : 0 < Rabs (FT2R xh*FT2R yh).
{ eapply Rlt_le_trans; [apply bpow_gt_0|exact Nprod]. }
have Hxhne : FT2R xh<>0.
{ intro H0. rewrite H0 Rmult_0_l Rabs_R0 in Hprod0. lra. }
have Hyhne : FT2R yh<>0.
{ intro H0. rewrite H0 Rmult_0_r Rabs_R0 in Hprod0. lra. }
have Hxrne : xr<>0.
{ intro H0. apply Hxhne.
  unfold double_word in Hdw. fold xr in Hdw.
  rewrite H0 /rounded round_0 in Hdw. exact Hdw. }
have Hyrne : yr<>0.
{ intro H0. apply Hyhne.
  unfold double_word in Hdwy. fold yr in Hdwy.
  rewrite H0 /rounded round_0 in Hdwy. exact Hdwy. }
have Hxyne : xr*yr<>0
  by apply Rmult_integral_contrapositive_currified; assumption.
unfold relative_error_DWTimesDW in Hrel.
have Heq : Rabs (zh+zl-xr*yr) =
    Rabs ((zh+zl-xr*yr)/(xr*yr))*Rabs (xr*yr).
{ rewrite -Rabs_mult. f_equal. field; split; assumption. }
rewrite Heq. apply Rmult_le_compat_r; [apply Rabs_pos|exact Hrel].
Qed.

(** Absolute paper bound for the broader exact-node regime.  Each node may
    be normal or merely representable on the physical FIX lattice. *)


(** If both the low-low node and the final correction node are subnormal,
    their relative components vanish.  The two remaining relative errors fit
    strictly inside the paper [4*u^2] budget; all additive pieces retain the
    common two-ulps allowance. *)
Theorem DWTimesDW_abs_low0_final_underflow :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  bpow radix2 (eminA+2*fprec t-1) <=
    Rabs (FT2R xh*FT2R yh) ->
  Rabs (FT2R xl*FT2R yl) < bpow radix2 (eminA+fprec t-1) ->
  Rabs (FT2R (Fast2Mult_err xh yh)+
    FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) <
      bpow radix2 (eminA+fprec t-1) ->
  Rabs (zh+zl-xr*yr) <=
    4*u^2*Rabs (xr*yr)+2*bpow radix2 eminA.
Proof.
move => DWx DWy FIN Hp5 Nprod N0 N3.
have Hp3 : (3 <= fprec t)%Z by lia.
have Fmul := DWTimesDW3_mul_finite xh xl yh yl FIN.
have H := relerr_error_relative_floor_decomposition xh xl yh yl
  Hp3 DWx DWy FIN Fmul Nprod.
destruct H as
  (er0 & er1 & er2 & er3 & ef0 & ef1 & ef2 & ef3 &
   Heq & R0 & R1 & R2 & R3 & F0b & F1b & F2b & F3b & Hef &
   ER1 & ER2 & ER3 & ER1f & ER2f & ER3f &
   Z0 & Z1 & Z2 & Z3 & G0 & G1 & G2 & G3 &
   T0 & T1 & T2 & S0 & S1 & S2 & S3).
destruct G0 as [[Ef0 N0normal]|[Er0 N0small]].
{ exfalso;exact (Rlt_not_le _ _ N0 N0normal). }
destruct G3 as [[Ef3 N3normal]|[Er3 N3small]].
{ exfalso;exact (Rlt_not_le _ _ N3 N3normal). }
subst er0; subst er3.
set P := Rabs (FT2R xh*FT2R yh).
set eta := bpow radix2 eminA.
have Hu0 : 0 < u by (unfold u;apply bpow_gt_0).
have Hu : u <= /32.
{ unfold u. have -> : (/32:R)=bpow radix2 (-5) by (simpl;lra).
  apply bpow_le;lia. }
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have Heta0 : 0 < eta by (unfold eta;apply bpow_gt_0).
have Hxl := @dw_low_le_u_high t STD xh xl DWx.
have Hyl := @dw_low_le_u_high t STD yh yl DWy.
fold u in Hxl,Hyl.
have HA : Rabs (FT2R xh*FT2R yl) <= u*P.
{ unfold P. rewrite !Rabs_mult.
  have H := Rmult_le_compat_l (Rabs (FT2R xh)) _ _
    (Rabs_pos _) Hyl. nra. }
have HB : Rabs (FT2R xl*FT2R yh) <= u*P.
{ unfold P. rewrite !Rabs_mult.
  have H := Rmult_le_compat_r (Rabs (FT2R yh)) _ _
    (Rabs_pos _) Hxl. nra. }
have HC : Rabs (FT2R xl*FT2R yl) <= u^2*P.
{ unfold P. rewrite !Rabs_mult.
  have H := Rmult_le_compat _ _ _ _
    (Rabs_pos _) (Rabs_pos _) Hxl Hyl.
  eapply Rle_trans; [exact H|]. right; ring. }
set T := bpow radix2 (eminA+2*fprec t-1).
fold P T in Nprod.
have Hscale : u^2*T=/2*eta.
{ replace (u^2) with (u*u) by ring. unfold u,T,eta.
  rewrite -(bpow_plus radix2 (-fprec t) (-fprec t)).
  rewrite -(bpow_plus radix2 (-fprec t+-fprec t)
    (eminA+2*fprec t-1)).
  replace (-fprec t+-fprec t+(eminA+2*fprec t-1))%Z with
    (eminA-1)%Z by ring.
  rewrite (bpow_plus radix2 eminA (-1)).
  change (bpow radix2 (-1)) with (/2:R). ring. }
have HetaP : eta <= 2*u^2*P.
{ have Hs := Rmult_le_compat_l (u^2) _ _ (pow2_ge_0 u) Nprod.
  nra. }
fold u eta in ER1f,ER2f.
ring_simplify in ER1f. ring_simplify in ER2f.
replace (FT2R xh*FT2R yl+FT2R xl*FT2R yl+0) with
  (FT2R xh*FT2R yl+FT2R xl*FT2R yl) in ER1f by ring.
replace (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
  FT2R xl*FT2R yl+0+er1) with
  (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
   FT2R xl*FT2R yl+er1) in ER2f by ring.
have Harg1 : Rabs (FT2R xh*FT2R yl+FT2R xl*FT2R yl) <=
    u*P+u^2*P.
{ eapply Rle_trans; [apply Rabs_triang|]. nra. }
have HE1 : Rabs er1 <= u^2*P+2*u^3*P.
{ eapply Rle_trans; [exact ER1f|].
  have Hm := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Harg1.
  have He := Rmult_le_compat_l (/2*u) _ _ ltac:(nra) HetaP.
  eapply Rle_trans.
  - apply Rplus_le_compat; [exact Hm|].
    replace (u*/2*eta) with (/2*u*eta) by ring. exact He.
  - nra. }
have Harg2 : Rabs (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
    FT2R xl*FT2R yl+er1) <= 2*u*P+u^2*P+Rabs er1.
{ have H1 := Rabs_triang
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+FT2R xl*FT2R yl) er1.
  have H2 := Rabs_triang
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl) (FT2R xl*FT2R yl).
  have H3 := Rabs_triang (FT2R xl*FT2R yh) (FT2R xh*FT2R yl).
  nra. }
have HE2 : Rabs er2 <= 2*u^2*P+4*u^3*P+2*u^4*P.
{ eapply Rle_trans; [exact ER2f|].
  have Hm := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Harg2.
  have He := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) HetaP.
  eapply Rle_trans.
  - apply Rplus_le_compat; [exact Hm|exact He].
  - have Harg2' : 2*u*P+u^2*P+Rabs er1 <=
        2*u*P+u^2*P+(u^2*P+2*u^3*P) by nra.
    have Hm' := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Harg2'.
    eapply Rle_trans.
    + apply Rplus_le_compat_r. exact Hm'.
    + nra. }
have Hcore : Rabs (er1+er2) <= 4*u^2*((1-u)^2*P).
{ eapply Rle_trans; [apply Rabs_triang|].
  have Hsmall : 15*u-2*u^2 <= 1 by nra.
  nra. }
have Hprod := aux_dw_exact_product_lower xh xl yh yl DWx DWy.
specialize (Hprod STD). fold u xr yr P in Hprod.
have Hcore' : Rabs (er1+er2) <= 4*u^2*Rabs (xr*yr).
{ eapply Rle_trans; [exact Hcore|].
  apply Rmult_le_compat_l; [nra|exact Hprod]. }
rewrite Heq.
replace (0+er1+er2+0+(ef0+ef1+ef2+ef3)) with
  (er1+er2+(ef0+ef1+ef2+ef3)) by ring.
have Htri := Rabs_triang (er1+er2) (ef0+ef1+ef2+ef3).
fold eta in Hef.
eapply Rle_trans; [exact Htri|].
eapply Rle_trans.
- apply Rplus_le_compat; [exact Hcore'|exact Hef].
- right; ring.
Qed.

(** If the first cross-term FMA underflows but the following two nodes are
    normal, the small-node hypothesis replaces one full [u*P] contribution.
    The two active physical floors consume one ulp; their propagation consumes
    at most the second ulp, leaving the paper [4*u^2] term unchanged. *)
Theorem DWTimesDW_abs_low0_low1_tail_normal :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  bpow radix2 (eminA+2*fprec t-1) <=
    Rabs (FT2R xh*FT2R yh) ->
  Rabs (FT2R xl*FT2R yl) < bpow radix2 (eminA+fprec t-1) ->
  Rabs (FT2R xh*FT2R yl+FT2R (BMULT xl yl)) <
    bpow radix2 (eminA+fprec t-1) ->
  bpow radix2 (eminA+fprec t-1) <=
    Rabs (FT2R xl*FT2R yh+
      FT2R (BFMA xh yl (BMULT xl yl))) ->
  bpow radix2 (eminA+fprec t-1) <=
    Rabs (FT2R (Fast2Mult_err xh yh)+
      FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) ->
  Rabs (zh+zl-xr*yr) <=
    4*u^2*Rabs (xr*yr)+2*bpow radix2 eminA.
Proof.
move => DWx DWy FIN Hp5 Nprod N0 N1 N2 N3.
have Hp3 : (3 <= fprec t)%Z by lia.
have Fmul := DWTimesDW3_mul_finite xh xl yh yl FIN.
have H := relerr_error_relative_floor_decomposition xh xl yh yl
  Hp3 DWx DWy FIN Fmul Nprod.
destruct H as
  (er0 & er1 & er2 & er3 & ef0 & ef1 & ef2 & ef3 &
   Heq & R0 & R1 & R2 & R3 & F0b & F1b & F2b & F3b & Hef &
   ER1 & ER2 & ER3 & ER1f & ER2f & ER3f &
   Z0 & Z1 & Z2 & Z3 & G0 & G1 & G2 & G3 &
   T0 & T1 & T2 & S0 & S1 & S2 & S3).
destruct G0 as [[Ef0 N0normal]|[Er0 N0small]].
{ exfalso; exact (Rlt_not_le _ _ N0 N0normal). }
destruct G1 as [[Ef1 N1normal]|[Er1 N1small]].
{ exfalso; exact (Rlt_not_le _ _ N1 N1normal). }
destruct G2 as [[Ef2 N2normal]|[Er2 N2small]].
2:{ exfalso; exact (Rlt_not_le _ _ N2small N2). }
destruct G3 as [[Ef3 N3normal]|[Er3 N3small]].
2:{ exfalso; exact (Rlt_not_le _ _ N3small N3). }
subst er0; subst er1; subst ef2; subst ef3.
set P := Rabs (FT2R xh*FT2R yh).
set eta := bpow radix2 eminA.
set U := bpow radix2 (eminA+fprec t-1).
have Hu0 : 0 < u by (unfold u;apply bpow_gt_0).
have Hu : u <= /32.
{ unfold u. have -> : (/32:R)=bpow radix2 (-5) by (simpl;lra).
  apply bpow_le;lia. }
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have Heta0 : 0 < eta by (unfold eta;apply bpow_gt_0).
have Hxl := @dw_low_le_u_high t STD xh xl DWx.
have Hyl := @dw_low_le_u_high t STD yh yl DWy.
fold u in Hxl,Hyl.
have HA : Rabs (FT2R xh*FT2R yl) <= u*P.
{ unfold P. rewrite !Rabs_mult.
  have Hm := Rmult_le_compat_l (Rabs (FT2R xh)) _ _
    (Rabs_pos _) Hyl. nra. }
have HB : Rabs (FT2R xl*FT2R yh) <= u*P.
{ unfold P. rewrite !Rabs_mult.
  have Hm := Rmult_le_compat_r (Rabs (FT2R yh)) _ _
    (Rabs_pos _) Hxl. nra. }
have HC : Rabs (FT2R xl*FT2R yl) <= u^2*P.
{ unfold P. rewrite !Rabs_mult.
  have Hm := Rmult_le_compat _ _ _ _
    (Rabs_pos _) (Rabs_pos _) Hxl Hyl.
  eapply Rle_trans; [exact Hm|]. right; ring. }
have Hcl1u : Rabs (FT2R (Fast2Mult_err xh yh)) <=
    /2*ulp (FT2R xh*FT2R yh)
  by (apply Fast2Mult_accuracy_norm;exact Fmul).
have Hulp : ulp (FT2R xh*FT2R yh) <=
    P*bpow radix2 (1-fprec t).
{ unfold P. apply ulp_FLT_le.
  eapply Rle_trans; [|exact Nprod]. apply bpow_le.
  unfold eminA, common.emin, SpecFloat.emin.
  pose proof fprec_lb t. lia. }
have HBp : bpow radix2 (1-fprec t)=2*u.
{ unfold u.
  change (bpow radix2 (1-fprec t)=
    bpow radix2 1*bpow radix2 (-fprec t)).
  rewrite -(bpow_plus radix2 1 (-fprec t)). f_equal;lia. }
have Hcl1 : Rabs (FT2R (Fast2Mult_err xh yh)) <= u*P.
{ rewrite HBp in Hulp. nra. }
have HUscale : u*U=/2*eta.
{ unfold u,U,eta. rewrite -(bpow_plus radix2 (-fprec t)
    (eminA+fprec t-1)).
  replace (-fprec t+(eminA+fprec t-1))%Z with (eminA-1)%Z by ring.
  rewrite (bpow_plus radix2 eminA (-1)).
  change (bpow radix2 (-1)) with (/2:R). ring. }
have Hscale : u^2*bpow radix2 (eminA+2*fprec t-1)=/2*eta.
{ replace (u^2) with (u*u) by ring. unfold u,eta.
  rewrite -(bpow_plus radix2 (-fprec t) (-fprec t)).
  rewrite -(bpow_plus radix2 (-fprec t+-fprec t)
    (eminA+2*fprec t-1)).
  replace (-fprec t+-fprec t+(eminA+2*fprec t-1))%Z with
    (eminA-1)%Z by ring.
  rewrite (bpow_plus radix2 eminA (-1)).
  change (bpow radix2 (-1)) with (/2:R). ring. }
have HetaP : eta <= 2*u^2*P.
{ have Hs := Rmult_le_compat_l (u^2) _ _ (pow2_ge_0 u) Nprod.
  rewrite Hscale in Hs.
  fold P in Hs.
  apply (Rmult_le_reg_l (/2)); [lra|].
  eapply Rle_trans; [exact Hs|]. nra. }
fold P eta U in N1small,F0b,F1b,ER2,ER3.
replace (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
  FT2R xl*FT2R yl+0+0)%R with
  (FT2R xl*FT2R yh+FT2R xh*FT2R yl+FT2R xl*FT2R yl)%R
  in ER2 by ring.
replace (FT2R (Fast2Mult_err xh yh)+FT2R xl*FT2R yh+
  FT2R xh*FT2R yl+FT2R xl*FT2R yl+0+0+er2)%R with
  (FT2R (Fast2Mult_err xh yh)+FT2R xl*FT2R yh+
   FT2R xh*FT2R yl+FT2R xl*FT2R yl+er2)%R in ER3 by ring.
replace (ef0+ef1+0)%R with (ef0+ef1)%R in ER3 by ring.
have HEF01 : Rabs (ef0+ef1) <= eta.
{ eapply Rle_trans; [apply Rabs_triang|]. nra. }
have Hcentral2 : Rabs (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
    FT2R xl*FT2R yl) <= u*P+U+/2*eta.
{ have Hinput :
    Rabs ((FT2R xh*FT2R yl+FT2R (BMULT xl yl))+(-ef0)) <=
    Rabs (FT2R xh*FT2R yl+FT2R (BMULT xl yl))+Rabs (-ef0)
    := Rabs_triang _ _.
  specialize (Hinput NANS STD).
  have HT0 : FT2R (BMULT xl yl)=FT2R xl*FT2R yl+ef0 by nra.
  replace ((FT2R xh*FT2R yl+FT2R (BMULT xl yl))+(-ef0))%R with
    (FT2R xh*FT2R yl+FT2R xl*FT2R yl) in Hinput.
  2:{ replace (FT2R (BMULT xl yl)) with
        (FT2R xl*FT2R yl+ef0) by (symmetry;exact HT0). ring. }
  have Hsum := Rabs_triang (FT2R xl*FT2R yh)
    (FT2R xh*FT2R yl+FT2R xl*FT2R yl).
  replace (FT2R xl*FT2R yh+
    (FT2R xh*FT2R yl+FT2R xl*FT2R yl))%R with
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+FT2R xl*FT2R yl)%R
    in Hsum by ring.
  rewrite Rabs_Ropp in Hinput.
  eapply Rle_trans; [exact Hsum|].
  eapply Rle_trans with (r2:=u*P+(U+/2*eta)); [|right;ring].
  apply Rplus_le_compat; [exact HB|].
  eapply Rle_trans; [exact Hinput|]. nra. }
have HE2 : Rabs er2 <= u^2*P+/2*eta+3/2*u*eta.
{ eapply Rle_trans; [exact ER2|].
  have Hm := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Hcentral2.
  have Hf := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) HEF01.
  nra. }
have Hcentral3 : Rabs (FT2R (Fast2Mult_err xh yh)+
    FT2R xl*FT2R yh+FT2R xh*FT2R yl+FT2R xl*FT2R yl+er2) <=
    2*u*P+U+/2*eta+Rabs er2.
{ have H0 := Rabs_triang (FT2R (Fast2Mult_err xh yh))
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
      FT2R xl*FT2R yl+er2).
  specialize (H0 NANS STD).
  have H1 := Rabs_triang
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+FT2R xl*FT2R yl) er2.
  replace (FT2R (Fast2Mult_err xh yh)+
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
      FT2R xl*FT2R yl+er2))%R with
    (FT2R (Fast2Mult_err xh yh)+FT2R xl*FT2R yh+
      FT2R xh*FT2R yl+FT2R xl*FT2R yl+er2)%R in H0 by ring.
  replace (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
    FT2R xl*FT2R yl+er2)%R with
    ((FT2R xl*FT2R yh+FT2R xh*FT2R yl+
      FT2R xl*FT2R yl)+er2)%R in H1 by ring.
  eapply Rle_trans; [exact H0|].
  eapply Rle_trans.
  - apply Rplus_le_compat; [exact Hcl1|exact H1].
  - nra. }
have HE3 : Rabs er3 <= 2*u^2*P+/2*eta+3/2*u*eta+u*Rabs er2.
{ eapply Rle_trans; [exact ER3|].
  have Hm := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Hcentral3.
  have Hf := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) HEF01.
  nra. }
have Hprod := aux_dw_exact_product_lower xh xl yh yl DWx DWy.
specialize (Hprod STD). fold u xr yr P in Hprod.
have Hrel : Rabs (er2+er3) <=
    4*u^2*Rabs (xr*yr)+eta.
{ eapply Rle_trans; [apply Rabs_triang|].
  have HB0 : 0 <= u^2*P by
    (apply Rmult_le_pos;[apply pow_le;left;exact Hu0|exact HP0]).
  have HE2u := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) HE2.
  have HE3b : Rabs er3 <=
      2*(u^2*P)+u*(u^2*P)+/2*eta+2*u*eta+3/2*u^2*eta.
  { eapply Rle_trans; [exact HE3|].
    eapply Rle_trans.
    - apply Rplus_le_compat_l. exact HE2u.
    - apply Req_le. field. }
  have Hsum : Rabs er2+Rabs er3 <=
      3*(u^2*P)+u*(u^2*P)+eta+7/2*u*eta+3/2*u^2*eta.
  { eapply Rle_trans.
    - apply Rplus_le_compat; [exact HE2|exact HE3b].
    - apply Req_le. field. }
  have Hueta := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) HetaP.
  have Hu2eta := Rmult_le_compat_l (u^2) _ _ (pow2_ge_0 u) HetaP.
  have Hprop : 7/2*u*eta+3/2*u^2*eta <=
      7*u*(u^2*P)+3*u^2*(u^2*P).
  { have H7 := Rmult_le_compat_l (7/2) _ _ ltac:(lra) Hueta.
    have H3 := Rmult_le_compat_l (3/2) _ _ ltac:(lra) Hu2eta.
    replace (7/2*u*eta+3/2*u^2*eta)%R with
      (7/2*(u*eta)+3/2*(u^2*eta))%R by field.
    replace (7*u*(u^2*P)+3*u^2*(u^2*P))%R with
      (7/2*(u*(2*u^2*P))+3/2*(u^2*(2*u^2*P)))%R by field.
    apply Rplus_le_compat; [exact H7|exact H3]. }
  have H16 : 16*u <= 1 by lra.
  have Hu2pos : 0 <= u^2 by apply pow2_ge_0.
  have Hcoef0 : 3+8*u+3*u^2 <= 4*(1-u)^2.
  { eapply Rle_trans with
      (r2:=(3+8*u+3*u^2)+(1-16*u+u^2)).
    - lra.
    - apply Req_le. field. }
  have Hcoef : (3+8*u+3*u^2)*(u^2*P) <=
      4*(1-u)^2*(u^2*P)
    by (apply Rmult_le_compat_r;[exact HB0|exact Hcoef0]).
  have Hpaper : 4*u^2*((1-u)^2*P) <=
      4*u^2*Rabs (xr*yr).
  { apply Rmult_le_compat_l; [apply Rmult_le_pos;[lra|exact Hu2pos]|exact Hprod]. }
  have Hsum' : Rabs er2+Rabs er3 <=
      (3*(u^2*P)+u*(u^2*P)+eta)+
      (7/2*u*eta+3/2*u^2*eta).
  { eapply Rle_trans; [exact Hsum|]. apply Req_le. field. }
  eapply Rle_trans; [exact Hsum'|].
  eapply Rle_trans with
      (r2:=(3+8*u+3*u^2)*(u^2*P)+eta).
  - eapply Rle_trans.
    + apply Rplus_le_compat_l. exact Hprop.
    + apply Req_le. field.
  - eapply Rle_trans.
    + apply Rplus_le_compat_r. exact Hcoef.
    + eapply Rle_trans; [|apply Rplus_le_compat_r;exact Hpaper].
      apply Req_le. field. }
rewrite Heq.
replace (0+0+er2+er3+(ef0+ef1+0+0)) with
  ((er2+er3)+(ef0+ef1)) by ring.
have Htri := Rabs_triang (er2+er3) (ef0+ef1).
eapply Rle_trans; [exact Htri|]. nra.
Qed.

(** Symmetric tail case: the low-low node and the second FMA underflow,
    while the first FMA and final addition are normal.  Here the subnormal
    second-FMA input bounds the whole correction entering the last round, so
    the relative pieces fit in [4*u^2] and the two floor pieces total one ulp. *)
Theorem DWTimesDW_abs_low0_low2_other_normal :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  bpow radix2 (eminA+2*fprec t-1) <=
    Rabs (FT2R xh*FT2R yh) ->
  Rabs (FT2R xl*FT2R yl) < bpow radix2 (eminA+fprec t-1) ->
  bpow radix2 (eminA+fprec t-1) <=
    Rabs (FT2R xh*FT2R yl+FT2R (BMULT xl yl)) ->
  Rabs (FT2R xl*FT2R yh+
    FT2R (BFMA xh yl (BMULT xl yl))) <
    bpow radix2 (eminA+fprec t-1) ->
  bpow radix2 (eminA+fprec t-1) <=
    Rabs (FT2R (Fast2Mult_err xh yh)+
      FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) ->
  Rabs (zh+zl-xr*yr) <=
    4*u^2*Rabs (xr*yr)+2*bpow radix2 eminA.
Proof.
move => DWx DWy FIN Hp5 Nprod N0 N1 N2 N3.
have Hp3 : (3 <= fprec t)%Z by lia.
have Fmul := DWTimesDW3_mul_finite xh xl yh yl FIN.
have H := relerr_error_relative_floor_decomposition xh xl yh yl
  Hp3 DWx DWy FIN Fmul Nprod.
destruct H as
  (er0 & er1 & er2 & er3 & ef0 & ef1 & ef2 & ef3 &
   Heq & R0 & R1 & R2 & R3 & F0b & F1b & F2b & F3b & Hef &
   ER1 & ER2 & ER3 & ER1f & ER2f & ER3f &
   Z0 & Z1 & Z2 & Z3 & G0 & G1 & G2 & G3 &
   T0 & T1 & T2 & S0 & S1 & S2 & S3).
destruct G0 as [[Ef0 N0normal]|[Er0 N0small]].
{ exfalso; exact (Rlt_not_le _ _ N0 N0normal). }
destruct G1 as [[Ef1 N1normal]|[Er1 N1small]].
2:{ exfalso; exact (Rlt_not_le _ _ N1small N1). }
destruct G2 as [[Ef2 N2normal]|[Er2 N2small]].
{ exfalso; exact (Rlt_not_le _ _ N2 N2normal). }
destruct G3 as [[Ef3 N3normal]|[Er3 N3small]].
2:{ exfalso; exact (Rlt_not_le _ _ N3small N3). }
subst er0; subst ef1; subst er2; subst ef3.
set P := Rabs (FT2R xh*FT2R yh).
set eta := bpow radix2 eminA.
set U := bpow radix2 (eminA+fprec t-1).
have Hu0 : 0 < u by (unfold u;apply bpow_gt_0).
have Hu : u <= /32.
{ unfold u. have -> : (/32:R)=bpow radix2 (-5) by (simpl;lra).
  apply bpow_le;lia. }
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have Heta0 : 0 < eta by (unfold eta;apply bpow_gt_0).
have Hxl := @dw_low_le_u_high t STD xh xl DWx.
have Hyl := @dw_low_le_u_high t STD yh yl DWy.
fold u in Hxl,Hyl.
have HA : Rabs (FT2R xh*FT2R yl) <= u*P.
{ unfold P. rewrite !Rabs_mult.
  have Hm := Rmult_le_compat_l (Rabs (FT2R xh)) _ _
    (Rabs_pos _) Hyl. nra. }
have HC : Rabs (FT2R xl*FT2R yl) <= u^2*P.
{ unfold P. rewrite !Rabs_mult.
  have Hm := Rmult_le_compat _ _ _ _
    (Rabs_pos _) (Rabs_pos _) Hxl Hyl.
  eapply Rle_trans; [exact Hm|]. apply Req_le. ring. }
have Hcl1u : Rabs (FT2R (Fast2Mult_err xh yh)) <=
    /2*ulp (FT2R xh*FT2R yh)
  by (apply Fast2Mult_accuracy_norm;exact Fmul).
have Hulp : ulp (FT2R xh*FT2R yh) <=
    P*bpow radix2 (1-fprec t).
{ unfold P. apply ulp_FLT_le.
  eapply Rle_trans; [|exact Nprod]. apply bpow_le.
  unfold eminA, common.emin, SpecFloat.emin.
  pose proof fprec_lb t. lia. }
have HBp : bpow radix2 (1-fprec t)=2*u.
{ unfold u.
  change (bpow radix2 (1-fprec t)=
    bpow radix2 1*bpow radix2 (-fprec t)).
  rewrite -(bpow_plus radix2 1 (-fprec t)). f_equal;lia. }
have Hcl1 : Rabs (FT2R (Fast2Mult_err xh yh)) <= u*P.
{ rewrite HBp in Hulp. nra. }
have HUscale : u*U=/2*eta.
{ unfold u,U,eta. rewrite -(bpow_plus radix2 (-fprec t)
    (eminA+fprec t-1)).
  replace (-fprec t+(eminA+fprec t-1))%Z with (eminA-1)%Z by ring.
  rewrite (bpow_plus radix2 eminA (-1)).
  change (bpow radix2 (-1)) with (/2:R). ring. }
have Hscale : u^2*bpow radix2 (eminA+2*fprec t-1)=/2*eta.
{ replace (u^2) with (u*u) by ring. unfold u,eta.
  rewrite -(bpow_plus radix2 (-fprec t) (-fprec t)).
  rewrite -(bpow_plus radix2 (-fprec t+-fprec t)
    (eminA+2*fprec t-1)).
  replace (-fprec t+-fprec t+(eminA+2*fprec t-1))%Z with
    (eminA-1)%Z by ring.
  rewrite (bpow_plus radix2 eminA (-1)).
  change (bpow radix2 (-1)) with (/2:R). ring. }
have HetaP : eta <= 2*u^2*P.
{ have Hs := Rmult_le_compat_l (u^2) _ _ (pow2_ge_0 u) Nprod.
  rewrite Hscale in Hs. fold P in Hs.
  apply (Rmult_le_reg_l (/2)); [lra|].
  eapply Rle_trans; [exact Hs|]. nra. }
fold P eta U in N2small,F0b,F2b,ER1,ER3.
replace (FT2R xh*FT2R yl+FT2R xl*FT2R yl+0)%R with
  (FT2R xh*FT2R yl+FT2R xl*FT2R yl)%R in ER1 by ring.
replace (FT2R (Fast2Mult_err xh yh)+FT2R xl*FT2R yh+
  FT2R xh*FT2R yl+FT2R xl*FT2R yl+0+er1+0)%R with
  (FT2R (Fast2Mult_err xh yh)+FT2R xl*FT2R yh+
   FT2R xh*FT2R yl+FT2R xl*FT2R yl+er1)%R in ER3 by ring.
replace (ef0+0+ef2)%R with (ef0+ef2)%R in ER3 by ring.
have HEF02 : Rabs (ef0+ef2) <= eta.
{ eapply Rle_trans; [apply Rabs_triang|]. nra. }
have Hcentral1 : Rabs (FT2R xh*FT2R yl+FT2R xl*FT2R yl) <=
    u*P+u^2*P.
{ eapply Rle_trans; [apply Rabs_triang|]. nra. }
have HE1 : Rabs er1 <= u^2*P+u^3*P+/2*u*eta.
{ eapply Rle_trans; [exact ER1|].
  have Hm := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Hcentral1.
  have Hf := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) F0b.
  eapply Rle_trans.
  - apply Rplus_le_compat; [exact Hm|exact Hf].
  - apply Req_le. field. }
have Hcentral3 : Rabs (FT2R (Fast2Mult_err xh yh)+
    FT2R xl*FT2R yh+FT2R xh*FT2R yl+FT2R xl*FT2R yl+er1) <=
    u*P+U+/2*eta.
{ have HT1 : FT2R (BFMA xh yl (BMULT xl yl))=
      FT2R xh*FT2R yl+FT2R xl*FT2R yl+er1+ef0 by nra.
  have Hinput :
      Rabs ((FT2R xl*FT2R yh+
        FT2R (BFMA xh yl (BMULT xl yl)))+(-ef0)) <=
      Rabs (FT2R xl*FT2R yh+
        FT2R (BFMA xh yl (BMULT xl yl)))+Rabs (-ef0)
      := Rabs_triang _ _.
  pose proof (@Hinput NANS STD NANS STD) as Hinput0.
  replace ((FT2R xl*FT2R yh+
    FT2R (BFMA xh yl (BMULT xl yl)))+(-ef0))%R with
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
      FT2R xl*FT2R yl+er1)%R in Hinput0.
  2:{ replace (FT2R (BFMA xh yl (BMULT xl yl))) with
        (FT2R xh*FT2R yl+FT2R xl*FT2R yl+er1+ef0)
        by (symmetry;exact HT1). ring. }
  rewrite Rabs_Ropp in Hinput0.
  have Hsum := Rabs_triang (FT2R (Fast2Mult_err xh yh))
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
      FT2R xl*FT2R yl+er1).
  specialize (Hsum NANS STD).
  replace (FT2R (Fast2Mult_err xh yh)+
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
      FT2R xl*FT2R yl+er1))%R with
    (FT2R (Fast2Mult_err xh yh)+FT2R xl*FT2R yh+
      FT2R xh*FT2R yl+FT2R xl*FT2R yl+er1)%R in Hsum by ring.
  eapply Rle_trans; [exact Hsum|].
  eapply Rle_trans.
  - apply Rplus_le_compat; [exact Hcl1|exact Hinput0].
  - lra. }
have HE3 : Rabs er3 <= u^2*P+/2*eta+3/2*u*eta.
{ eapply Rle_trans; [exact ER3|].
  have Hm := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Hcentral3.
  have Hf := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) HEF02.
  eapply Rle_trans.
  - apply Rplus_le_compat; [exact Hm|exact Hf].
  - nra. }
have Hprod := aux_dw_exact_product_lower xh xl yh yl DWx DWy.
specialize (Hprod STD). fold u xr yr P in Hprod.
have Hrel : Rabs (er1+er3) <= 4*u^2*Rabs (xr*yr).
{ eapply Rle_trans; [apply Rabs_triang|].
  have Hhalf : /2*eta <= u^2*P by lra.
  have Hueta := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) HetaP.
  have Hraw : Rabs er1+Rabs er3 <=
      3*(u^2*P)+5*u*(u^2*P).
  { eapply Rle_trans.
    - apply Rplus_le_compat; [exact HE1|exact HE3].
    - nra. }
  have Hcoef0 : 3+5*u <= 4*(1-u)^2.
  { have H13 : 13*u <= 1 by lra.
    have Hu2pos : 0 <= u^2 by apply pow2_ge_0.
    eapply Rle_trans with (r2:=(3+5*u)+(1-13*u+4*u^2)).
    - lra.
    - apply Req_le. field. }
  have HB0 : 0 <= u^2*P by
    (apply Rmult_le_pos;[apply pow2_ge_0|exact HP0]).
  have Hcoef := Rmult_le_compat_r (u^2*P) _ _ HB0 Hcoef0.
  have Hpaper : 4*u^2*((1-u)^2*P) <= 4*u^2*Rabs (xr*yr).
  { apply Rmult_le_compat_l; [apply Rmult_le_pos;[lra|apply pow2_ge_0]|exact Hprod]. }
  eapply Rle_trans; [exact Hraw|].
  eapply Rle_trans with (r2:=(3+5*u)*(u^2*P)).
  - apply Req_le. field.
  - eapply Rle_trans; [exact Hcoef|].
    eapply Rle_trans with (r2:=4*u^2*((1-u)^2*P)).
    + apply Req_le. field.
    + exact Hpaper. }
rewrite Heq.
replace (0+er1+0+er3+(ef0+0+ef2+0)) with
  ((er1+er3)+(ef0+ef2)) by ring.
have Htri := Rabs_triang (er1+er3) (ef0+ef2).
eapply Rle_trans; [exact Htri|].
eapply Rle_trans.
- apply Rplus_le_compat; [exact Hrel|exact HEF02].
- have := Heta0. nra.
Qed.
Local Lemma leading_product_gap_low_low_zero
    (xh0 xl0 yh0 yl0 : ftype t) :
  double_word_prop xh0 xl0 -> double_word_prop yh0 yl0 ->
  is_finite (BMULT xl0 yl0)=true ->
  Rabs (FT2R xh0*FT2R yh0) <
    bpow radix2 (common.emin (t:=t)+2*fprec t-1) ->
  FT2R (BMULT xl0 yl0)=0.
Proof.
move => DWx DWy F0 Hgap.
set u := bpow radix2 (-fprec t).
set eta := bpow radix2 (common.emin (t:=t)).
have Hu0 : 0 < u by apply bpow_gt_0.
have Hxl := @dw_low_le_u_high t STD xh0 xl0 DWx.
have Hyl := @dw_low_le_u_high t STD yh0 yl0 DWy.
fold u in Hxl, Hyl.
have Hlow : Rabs (FT2R xl0*FT2R yl0) <=
    u^2*Rabs (FT2R xh0*FT2R yh0).
{ rewrite !Rabs_mult.
  have H := Rmult_le_compat _ _ _ _
    (Rabs_pos _) (Rabs_pos _) Hxl Hyl.
  eapply Rle_trans; [exact H|]. right; ring. }
have Hu2 : 0 < u^2 by nra.
have Hscaled := Rmult_lt_compat_l (u^2) _ _ Hu2 Hgap.
have Hscale : u^2*bpow radix2
  (common.emin (t:=t)+2*fprec t-1)=/2*eta.
{ replace (u^2)%R with (u*u)%R by ring.
  unfold u, eta. rewrite -!bpow_plus.
  replace (-fprec t+-fprec t+
    (common.emin (t:=t)+2*fprec t-1))%Z
    with (common.emin (t:=t)-1)%Z by ring.
  rewrite (bpow_plus radix2 (common.emin (t:=t)) (-1)).
  change (bpow radix2 (-1)) with (/2:R). ring. }
have Htiny : Rabs (FT2R xl0*FT2R yl0) < /2*eta by nra.
have Hr := round_FLT_abs_lt_half_emin_0
  (FT2R xl0*FT2R yl0) Htiny.
rewrite (BMULT_round_correct t xl0 yl0 F0) in Hr.
exact Hr.
Qed.

(* ==================================================================
   ALGORITHM-12 UNDERFLOW-GAP BLOCK  (whole-range / mixed API)

   Below the TwoProd exactness threshold T = 2^(emin+2p-1) the leading
   product's residual is not representable, so the relative analysis of
   the regime lemmas above does not apply and the error is governed by an
   absolute floor instead.  The lemmas here bound that floor with NO
   hypothesis on the leading product beyond finiteness, and show that the
   output is still a valid double word, so the gap supplies both the mixed
   error guarantee and the required property of the result.

   Mirrors DWMulFP_acc's Algorithm-9 block (DWTimesFP_core_error_floor_gap
   / DWTimesFP3_error_floor_gap) node for node; Algorithm 12 just has five
   rounding nodes below the leading product instead of two.
   ================================================================== *)

(* The compensated core of Algorithm 12 in the gap, at NODE level: the
   exact sum ch + cl3 approximates xr*yr to within 5/2 ulp of the
   underflow floor, plus one u^2*P term for the discarded xl*yl product.
   No ordering hypothesis, no lower bound on the leading product -- the
   closing Fast2Sum is not involved yet, which is what lets both this file
   and DWDivDW_acc (whose closing step supplies its own ordering) share it.

   The 5/2 is spent as: eta/2 on the Fast2Mult residual (Hdelta), eta/2
   each on the tl1 and cl2 FMA roundings (He1, He2), and a full eta on the
   cl3 addition (He3) -- |cl1+cl2| can reach 4N, one binade above the
   others, so its ulp there is 2*eta. *)
Lemma DWTimesDW_core_error_floor_gap (xh0 xl0 yh0 yl0 : ftype t) :
  (3 <= fprec t)%Z ->
  double_word_prop xh0 xl0 -> double_word_prop yh0 yl0 ->
  is_finite_p (DWTimesDW3 xh0 xl0 yh0 yl0) ->
  Rabs (FT2R xh0*FT2R yh0) <
    bpow radix2 (common.emin (t:=t)+2*fprec t-1) ->
  Rabs ((FT2R (Fast2Mult_mul xh0 yh0)+
         FT2R (BPLUS (Fast2Mult_err xh0 yh0)
                     (BFMA xl0 yh0 (BFMA xh0 yl0 (BMULT xl0 yl0)))))-
        (FT2R xh0+FT2R xl0)*(FT2R yh0+FT2R yl0))
    <= 5/2*bpow radix2 (common.emin (t:=t))+
       u^2*Rabs (FT2R xh0*FT2R yh0).
Proof.
move => Hp3 DWx0 DWy0 FIN Hgap.
set u := bpow radix2 (-fprec t).
set eta := bpow radix2 (common.emin (t:=t)).
set T := bpow radix2 (common.emin (t:=t)+2*fprec t-1).
set N := bpow radix2 (common.emin (t:=t)+fprec t-1).
set P0 := (FT2R xh0*FT2R yh0)%R.
set P := Rabs P0.
set X := (FT2R xh0+FT2R xl0)%R.
set M := (FT2R yh0+FT2R yl0)%R.
have Hu0 : 0 < u by (unfold u;apply bpow_gt_0).
have Hu : u <= /8.
{ unfold u. have -> : (/8:R)=bpow radix2 (-3) by (simpl;lra).
  apply bpow_le; lia. }
have Heta0 : 0 < eta by (unfold eta;apply bpow_gt_0).
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have HN0 : 0 < N by (unfold N;apply bpow_gt_0).
have Hxl := @dw_low_le_u_high t STD xh0 xl0 DWx0.
have Hml := @dw_low_le_u_high t STD yh0 yl0 DWy0.
fold u in Hxl,Hml.
have Hxhml : Rabs (FT2R xh0*FT2R yl0) <= u*P.
{ unfold P,P0. rewrite !Rabs_mult.
  have H := Rmult_le_compat_l (Rabs (FT2R xh0)) _ _
    (Rabs_pos _) Hml. eapply Rle_trans; [exact H|]. right;ring. }
have Hxlmh : Rabs (FT2R xl0*FT2R yh0) <= u*P.
{ unfold P,P0. rewrite !Rabs_mult.
  have H := Rmult_le_compat_r (Rabs (FT2R yh0)) _ _
    (Rabs_pos _) Hxl. eapply Rle_trans; [exact H|]. right;ring. }
have Hxlml : Rabs (FT2R xl0*FT2R yl0) <= u^2*P.
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
set ch := Fast2Mult_mul xh0 yh0.
set cl1 := Fast2Mult_err xh0 yh0.
set tl0 := BMULT xl0 yl0.
set tl1 := BFMA xh0 yl0 tl0.
set cl2 := BFMA xl0 yh0 tl1.
set cl3 := BPLUS cl1 cl2.
have Fch : is_finite ch=true by
  (unfold ch,Fast2Mult_mul,Fast2Mult,fst;exact (DWTimesDW3_mul_finite xh0 xl0 yh0 yl0 FIN)).
have F0 : is_finite tl0=true by
  (unfold tl0;exact (DWTimesDW3_low_low_finite xh0 xl0 yh0 yl0 FIN)).
have F1 : is_finite tl1=true by
  (unfold tl1,tl0;exact (DWTimesDW3_first_correction_finite xh0 xl0 yh0 yl0 FIN)).
have F2 : is_finite cl2=true by
  (unfold cl2,tl1,tl0;exact (DWTimesDW3_second_correction_finite xh0 xl0 yh0 yl0 FIN)).
have F3 : is_finite cl3=true by
  (unfold cl3,cl1,cl2,tl1,tl0;
   exact (DWTimesDW3_correction_finite xh0 xl0 yh0 yl0 FIN)).
have Ffast := DWTimesDW3_fast2mult_finite xh0 xl0 yh0 yl0 FIN.
have Fcl1 : is_finite cl1=true by exact (proj2 Ffast).
have Htl00 := leading_product_gap_low_low_zero
  xh0 xl0 yh0 yl0 DWx0 DWy0 F0 Hgap.
fold tl0 in Htl00.
have Hdelta := Fast2Mult_sum_error_floor xh0 yh0 ltac:(lia) Ffast.
fold P0 ch cl1 eta in Hdelta.
have H1r : FT2R tl1=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
    (FT2R xh0*FT2R yl0).
{ unfold tl1. rewrite -(BFMA_round_correct t xh0 yl0 tl0 F1) Htl00.
  f_equal;ring. }
have He1 : Rabs (FT2R tl1-FT2R xh0*FT2R yl0) <= /2*eta.
{ rewrite H1r. eapply Rle_trans.
  - apply round_FLT_error_below_binade with(k:=0%Z);
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
  apply round_le; [exact valid_fexp_inst_dh|apply valid_rnd_N|].
  eapply Rle_trans; [exact Hxhml|]. lra. }
set a2 := FT2R xl0*FT2R yh0+FT2R tl1.
have Ha2 : Rabs a2 < 2*N.
{ unfold a2. eapply Rle_lt_trans; [apply Rabs_triang|]. nra. }
have H2r : FT2R cl2=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) a2.
{ unfold cl2,a2. symmetry;exact (BFMA_round_correct t xl0 yh0 tl1 F2). }
have He2 : Rabs (FT2R cl2-a2) <= /2*eta.
{ rewrite H2r. eapply Rle_trans.
  - apply round_FLT_error_below_binade with(k:=0%Z);
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
  apply round_le; [exact valid_fexp_inst_dh|apply valid_rnd_N|]. lra. }
have Hcl1N : Rabs (FT2R cl1) <= /2*N.
{ have Hc := Fast2Mult_accuracy_norm xh0 yh0 Fch.
  fold cl1 P0 in Hc.
  have HgapP : Rabs P0 <
      bpow radix2 (@common.emin t+fprec t+(fprec t-1)).
  { change (P < T) in Hgap. unfold T in Hgap.
    replace (@common.emin t+fprec t+(fprec t-1))%Z with
      (@common.emin t+2*fprec t-1)%Z by ring.
    exact Hgap. }
  have Hb := half_ulp_FLT_below_binade
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
  have H := round_FLT_error_below_binade
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
  apply round_le; [exact valid_fexp_inst_dh|apply valid_rnd_N|]. lra. }
have Herr : Rabs ((FT2R ch+FT2R cl3)-X*M) <=
    5/2*eta+u^2*P.
{ fold ch in Hdelta.
  set A := FT2R ch+FT2R cl1-P0.
  set B := -FT2R xl0*FT2R yl0.
  set C := FT2R tl1-FT2R xh0*FT2R yl0.
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
    by unfold B; replace (-FT2R xl0*FT2R yl0) with (-(FT2R xl0*FT2R yl0)) by ring;
       rewrite Rabs_Ropp;exact Hxlml.
  fold A in Hdelta. fold C in He1. fold D in He2. fold E in He3.
  eapply Rle_trans; [exact Htri|].
  eapply Rle_trans.
  - apply Rplus_le_compat; [|exact He3].
    apply Rplus_le_compat; [|exact He2].
    apply Rplus_le_compat; [|exact He1].
    apply Rplus_le_compat; [exact Hdelta|exact Hlow].
  - ring_simplify. lra. }
exact Herr.
Qed.

(* Bridge: the output pair of Algorithm 12 IS the closing Fast2Sum of
   (ch, cl3), so a sum-preservation fact about that Fast2Sum transfers to
   the algorithm's output.  Pure definitional unfolding. *)
Local Lemma DWTimesDW3_double_word_of_sum (xh0 xl0 yh0 yl0 : ftype t) :
  is_finite_p (DWTimesDW3 xh0 xl0 yh0 yl0) ->
  let ch := Fast2Mult_mul xh0 yh0 in
  let cl3 := BPLUS (Fast2Mult_err xh0 yh0)
                   (BFMA xl0 yh0 (BFMA xh0 yl0 (BMULT xl0 yl0))) in
  FT2R (fst (DWTimesDW3 xh0 xl0 yh0 yl0))+
  FT2R (snd (DWTimesDW3 xh0 xl0 yh0 yl0)) =
    FT2R ch+FT2R cl3 ->
  double_word_prop (fst (DWTimesDW3 xh0 xl0 yh0 yl0))
                   (snd (DWTimesDW3 xh0 xl0 yh0 yl0)).
Proof.
move => FIN ch cl3 Hsum.
set d := DWTimesDW3 xh0 xl0 yh0 yl0.
fold d in Hsum, FIN.
unfold double_word_prop, rounded. fold d. rewrite Hsum.
have Hfst : fst d=BPLUS ch cl3 by reflexivity.
rewrite Hfst. symmetry. apply BPLUS_round_correct.
rewrite -Hfst. exact (proj1 FIN).
Qed.

(* Two magnitude bounds on the closing Fast2Sum's arguments, in RELATIVE form
   (multiples of u*P and eta rather than of N).  They are coarser than the
   core chain's N-shaped bounds, but being expressed in u*P they make the
   ordering test of DWTimesDW3_error_floor_gap a single crossing computation
   instead of the two-step bootstrap that N-shaped bounds would force:
   |cl3| <= 6uP+4eta against |ch| >= (1-u)P-eta/2 cross only below P ~ 6*eta.

   Separate lemmas rather than inline [have]s so each nonlinear step runs
   against a small context; nra does not cope with the twenty-odd hypotheses
   in scope inside the gap theorem. *)
Lemma gap_ch_lower_bound (xh0 yh0 : ftype t) :
  is_finite (BMULT xh0 yh0)=true ->
  (1-u)*Rabs (FT2R xh0*FT2R yh0)-/2*bpow radix2 (common.emin (t:=t))
    <= Rabs (FT2R (Fast2Mult_mul xh0 yh0)).
Proof.
move => Fch.
set u' := bpow radix2 (-fprec t).
set eta := bpow radix2 (common.emin (t:=t)).
set P0 := (FT2R xh0*FT2R yh0)%R.
set P := Rabs P0.
set ch := Fast2Mult_mul xh0 yh0.
have Hchr : FT2R ch=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) P0.
{ unfold ch,Fast2Mult_mul,Fast2Mult,fst. symmetry.
  exact (BMULT_round_correct t xh0 yh0 Fch). }
have Hcherr := round_FLT_error_rel_emin (t:=t) P0.
fold u' eta in Hcherr. rewrite -Hchr in Hcherr. fold P in Hcherr.
have Hrev := Rabs_triang_inv P0 (P0-FT2R ch).
replace (P0-(P0-FT2R ch))%R with (FT2R ch) in Hrev by ring.
fold P in Hrev.
replace (P0-FT2R ch)%R with (-(FT2R ch-P0))%R in Hrev by ring.
rewrite Rabs_Ropp in Hrev. lra.
Qed.

Local Lemma gap_cl1_upper_bound (xh0 yh0 : ftype t) :
  (3 <= fprec t)%Z ->
  is_finite_p (Fast2Mult xh0 yh0) ->
  Rabs (FT2R (Fast2Mult_err xh0 yh0))
    <= u*Rabs (FT2R xh0*FT2R yh0)+bpow radix2 (common.emin (t:=t)).
Proof.
move => Hp3 Ffast.
have Fch : is_finite (BMULT xh0 yh0)=true by exact (proj1 Ffast).
set u' := bpow radix2 (-fprec t).
set eta := bpow radix2 (common.emin (t:=t)).
set P0 := (FT2R xh0*FT2R yh0)%R.
set P := Rabs P0.
set ch := Fast2Mult_mul xh0 yh0.
set cl1 := Fast2Mult_err xh0 yh0.
have Hdelta := Fast2Mult_sum_error_floor xh0 yh0 Hp3 Ffast.
fold P0 ch cl1 eta in Hdelta.
have Hchr : FT2R ch=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) P0.
{ unfold ch,Fast2Mult_mul,Fast2Mult,fst. symmetry.
  exact (BMULT_round_correct t xh0 yh0 Fch). }
have Hcherr := round_FLT_error_rel_emin (t:=t) P0.
fold u' eta in Hcherr. rewrite -Hchr in Hcherr. fold P in Hcherr.
have Htri := Rabs_triang (FT2R ch+FT2R cl1-P0) (P0-FT2R ch).
replace (FT2R ch+FT2R cl1-P0+(P0-FT2R ch))%R with (FT2R cl1)%R
  in Htri by ring.
replace (P0-FT2R ch)%R with (-(FT2R ch-P0))%R in Htri by ring.
rewrite Rabs_Ropp in Htri. lra.
Qed.

(* |cl3| <= 6uP + 4eta.  Each node's rounding costs a relative u factor plus
   eta/2; in the gap tl0 = 0, so only three products enter.  u <= /32 turns
   every u*(u*P) term into (u*P)/32, which keeps the whole computation linear
   in the two atoms u*P and eta. *)
Lemma gap_cl3_upper_bound (xh0 xl0 yh0 yl0 : ftype t) :
  (5 <= fprec t)%Z ->
  double_word_prop xh0 xl0 -> double_word_prop yh0 yl0 ->
  is_finite_p (DWTimesDW3 xh0 xl0 yh0 yl0) ->
  Rabs (FT2R xh0*FT2R yh0) <
    bpow radix2 (common.emin (t:=t)+2*fprec t-1) ->
  Rabs (FT2R (BPLUS (Fast2Mult_err xh0 yh0)
                    (BFMA xl0 yh0 (BFMA xh0 yl0 (BMULT xl0 yl0)))))
    <= 6*u*Rabs (FT2R xh0*FT2R yh0)+
       4*bpow radix2 (common.emin (t:=t)).
Proof.
move => Hp5 DWx0 DWy0 FIN Hgap.
have Hp3 : (3 <= fprec t)%Z by lia.
set u' := bpow radix2 (-fprec t).
set eta := bpow radix2 (common.emin (t:=t)).
set P0 := (FT2R xh0*FT2R yh0)%R.
set P := Rabs P0.
set cl1 := Fast2Mult_err xh0 yh0.
set tl0 := BMULT xl0 yl0.
set tl1 := BFMA xh0 yl0 tl0.
set cl2 := BFMA xl0 yh0 tl1.
set cl3 := BPLUS cl1 cl2.
have Hu0 : 0 < u' by (unfold u';apply bpow_gt_0).
have Hu : u' <= /32.
{ unfold u'. have -> : (/32:R)=bpow radix2 (-5) by (simpl;lra).
  apply bpow_le; lia. }
have Heta0 : 0 < eta by (unfold eta;apply bpow_gt_0).
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have HuP0 : 0 <= u'*P by nra.
have F0 : is_finite tl0=true by
  (unfold tl0;exact (DWTimesDW3_low_low_finite xh0 xl0 yh0 yl0 FIN)).
have F1 : is_finite tl1=true by
  (unfold tl1,tl0;exact (DWTimesDW3_first_correction_finite xh0 xl0 yh0 yl0 FIN)).
have F2 : is_finite cl2=true by
  (unfold cl2,tl1,tl0;exact (DWTimesDW3_second_correction_finite xh0 xl0 yh0 yl0 FIN)).
have F3 : is_finite cl3=true by
  (unfold cl3,cl1,cl2,tl1,tl0;exact (DWTimesDW3_correction_finite xh0 xl0 yh0 yl0 FIN)).
have Ffast := DWTimesDW3_fast2mult_finite xh0 xl0 yh0 yl0 FIN.
(* the two cross products, each at most u*P *)
have Hxl := @dw_low_le_u_high t STD xh0 xl0 DWx0.
have Hml := @dw_low_le_u_high t STD yh0 yl0 DWy0.
fold u' in Hxl,Hml.
have Hxhyl : Rabs (FT2R xh0*FT2R yl0) <= u'*P.
{ unfold P,P0. rewrite !Rabs_mult.
  have H := Rmult_le_compat_l (Rabs (FT2R xh0)) _ _
    (Rabs_pos _) Hml. eapply Rle_trans; [exact H|]. right;ring. }
have Hxlyh : Rabs (FT2R xl0*FT2R yh0) <= u'*P.
{ unfold P,P0. rewrite !Rabs_mult.
  have H := Rmult_le_compat_r (Rabs (FT2R yh0)) _ _
    (Rabs_pos _) Hxl. eapply Rle_trans; [exact H|]. right;ring. }
(* |cl1| <= uP + eta *)
have Hcl1 := gap_cl1_upper_bound xh0 yh0 Hp3 Ffast.
fold u' eta P0 P cl1 in Hcl1.
(* tl0 = 0 in the gap *)
have Htl00 := leading_product_gap_low_low_zero
  xh0 xl0 yh0 yl0 DWx0 DWy0 F0 Hgap.
fold tl0 in Htl00.
(* |tl1| <= 2uP + eta *)
have H1r : FT2R tl1=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
    (FT2R xh0*FT2R yl0).
{ unfold tl1. rewrite -(BFMA_round_correct t xh0 yl0 tl0 F1) Htl00.
  f_equal;ring. }
have Htl1 : Rabs (FT2R tl1) <= 2*(u'*P)+eta.
{ have He := round_FLT_error_rel_emin (t:=t) (FT2R xh0*FT2R yl0).
  fold u' eta in He. rewrite -H1r in He.
  have Htri := Rabs_triang (FT2R tl1-FT2R xh0*FT2R yl0)
    (FT2R xh0*FT2R yl0).
  replace (FT2R tl1-FT2R xh0*FT2R yl0+FT2R xh0*FT2R yl0)%R
    with (FT2R tl1)%R in Htri by ring.
  have HuA : u'*Rabs (FT2R xh0*FT2R yl0) <= /32*(u'*P).
  { eapply Rle_trans.
    - apply Rmult_le_compat_r; [apply Rabs_pos|exact Hu].
    - apply Rmult_le_compat_l; [lra|exact Hxhyl]. }
  lra. }
(* |cl2| <= 4uP + 2eta *)
have H2r : FT2R cl2=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
    (FT2R xl0*FT2R yh0+FT2R tl1).
{ unfold cl2. symmetry;exact (BFMA_round_correct t xl0 yh0 tl1 F2). }
have Hcl2 : Rabs (FT2R cl2) <= 4*(u'*P)+2*eta.
{ set a2 := (FT2R xl0*FT2R yh0+FT2R tl1)%R.
  have Ha2 : Rabs a2 <= 3*(u'*P)+eta.
  { unfold a2. eapply Rle_trans; [apply Rabs_triang|]. lra. }
  have Ha20 : 0 <= Rabs a2 by apply Rabs_pos.
  have He := round_FLT_error_rel_emin (t:=t) a2.
  fold u' eta in He. rewrite -H2r in He.
  have Htri := Rabs_triang (FT2R cl2-a2) a2.
  replace (FT2R cl2-a2+a2)%R with (FT2R cl2)%R in Htri by ring.
  have HuA : u'*Rabs a2 <= /32*(3*(u'*P)+eta).
  { eapply Rle_trans.
    - apply Rmult_le_compat_r; [exact Ha20|exact Hu].
    - apply Rmult_le_compat_l; [lra|exact Ha2]. }
  lra. }
(* |cl3| <= 6uP + 4eta *)
have H3r : FT2R cl3=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
    (FT2R cl1+FT2R cl2).
{ unfold cl3. symmetry;exact (BPLUS_round_correct t cl1 cl2 F3). }
set a3 := (FT2R cl1+FT2R cl2)%R.
have Ha3 : Rabs a3 <= 5*(u'*P)+3*eta.
{ unfold a3. eapply Rle_trans; [apply Rabs_triang|]. lra. }
have Ha30 : 0 <= Rabs a3 by apply Rabs_pos.
have He := round_FLT_error_rel_emin (t:=t) a3.
fold u' eta in He. rewrite -H3r in He.
have Htri := Rabs_triang (FT2R cl3-a3) a3.
replace (FT2R cl3-a3+a3)%R with (FT2R cl3)%R in Htri by ring.
have HuA : u'*Rabs a3 <= /32*(5*(u'*P)+3*eta).
{ eapply Rle_trans.
  - apply Rmult_le_compat_r; [exact Ha30|exact Hu].
  - apply Rmult_le_compat_l; [lra|exact Ha3]. }
have Hgoal : 6*u'*P = 6*(u'*P) by ring.
rewrite Hgoal. lra.
Qed.

(* Full Algorithm 12 in the Fast2Mult gap: the compensated core's 5/2 floor
   ulps are the whole cost, and the output is still a double word.

   Both arms of the closing Fast2Sum deliver SUM PRESERVATION, which is what
   closure needs -- ordering is not required:
     - ordered   -> FastTwoSum_correct (the returned pair reconstructs the sum
                    exactly in FLT, including for subnormal values);
     - unordered -> |cl3| > |ch| forces the leading product into the tiny
       regime (P < 6*eta), where the exact sum ch+cl3 still lies on the shared
       FLT/FIX lattice at exponent emin and Fast2Sum is exact anyway
       (Fast2Sum_sum_exact_of_sum_small).
   Thus the gap theorem establishes both the mixed error bound and that the
   output is a valid double word. *)
Lemma DWTimesDW3_error_floor_gap (xh0 xl0 yh0 yl0 : ftype t) :
  (5 <= fprec t)%Z ->
  double_word_prop xh0 xl0 -> double_word_prop yh0 yl0 ->
  is_finite_p (DWTimesDW3 xh0 xl0 yh0 yl0) ->
  Rabs (FT2R xh0*FT2R yh0) <
    bpow radix2 (common.emin (t:=t)+2*fprec t-1) ->
  Rabs ((FT2R (fst (DWTimesDW3 xh0 xl0 yh0 yl0))+
         FT2R (snd (DWTimesDW3 xh0 xl0 yh0 yl0)))-
        (FT2R xh0+FT2R xl0)*(FT2R yh0+FT2R yl0))
    <= 5/2*bpow radix2 (common.emin (t:=t))+
       u^2*Rabs (FT2R xh0*FT2R yh0) /\
  double_word_prop (fst (DWTimesDW3 xh0 xl0 yh0 yl0))
                   (snd (DWTimesDW3 xh0 xl0 yh0 yl0)).
Proof.
move => Hp5 DWx0 DWy0 FIN Hgap.
have Hp3 : (3 <= fprec t)%Z by lia.
have Hcore := DWTimesDW_core_error_floor_gap xh0 xl0 yh0 yl0
  Hp3 DWx0 DWy0 FIN Hgap.
have Hchlo0 := gap_ch_lower_bound xh0 yh0 (DWTimesDW3_mul_finite xh0 xl0 yh0 yl0 FIN).
have Hcl30 := gap_cl3_upper_bound xh0 xl0 yh0 yl0 Hp5 DWx0 DWy0 FIN Hgap.
set d := DWTimesDW3 xh0 xl0 yh0 yl0.
set u' := bpow radix2 (-fprec t).
set eta := bpow radix2 (common.emin (t:=t)).
set P0 := (FT2R xh0*FT2R yh0)%R.
set P := Rabs P0.
set X := (FT2R xh0+FT2R xl0)%R.
set M := (FT2R yh0+FT2R yl0)%R.
set ch := Fast2Mult_mul xh0 yh0.
set cl1 := Fast2Mult_err xh0 yh0.
set tl0 := BMULT xl0 yl0.
set tl1 := BFMA xh0 yl0 tl0.
set cl2 := BFMA xl0 yh0 tl1.
set cl3 := BPLUS cl1 cl2.
fold u' eta P0 P X M ch cl1 tl0 tl1 cl2 cl3 in Hcore.
fold u' eta P0 P ch in Hchlo0.
fold u' eta P0 P cl1 tl0 tl1 cl2 cl3 in Hcl30.
have Hu0 : 0 < u' by (unfold u';apply bpow_gt_0).
have Hu : u' <= /32.
{ unfold u'. have -> : (/32:R)=bpow radix2 (-5) by (simpl;lra).
  apply bpow_le; lia. }
have Heta0 : 0 < eta by (unfold eta;apply bpow_gt_0).
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have Fe : is_finite_p (Fast2Sum ch cl3).
{ unfold d, DWTimesDW3 in FIN. fold ch cl1 tl0 tl1 cl2 cl3 in FIN.
  exact FIN. }
destruct (Rle_dec (Rabs (FT2R cl3)) (Rabs (FT2R ch))) as [Hord|Hnord].
- (* ordered: the closing Fast2Sum pair reconstructs the sum exactly in FLT,
     including for subnormal values *)
  have Hsum := FastTwoSum_correct ch cl3 (proj1 Fe) Hord.
  change (FT2R (snd d)=FT2R ch+FT2R cl3-FT2R (fst d)) in Hsum.
  have HsumE : FT2R (fst d)+FT2R (snd d)=FT2R ch+FT2R cl3
    by (rewrite Hsum;ring).
  split.
  + rewrite HsumE. exact Hcore.
  + exact (Fast2Sum_is_DW ch cl3 (proj1 Fe) Hord).
- (* Unordered closing Fast2Sum.  |cl3| > |ch| can only happen when the
     leading product is tiny: |cl3| <= 6uP+4eta while |ch| >= (1-u)P-eta/2,
     and at u <= /32 those cross only below 6*eta, so P < 6*eta.  The EXACT
     sum ch+cl3 is then bounded THROUGH the compensated core error -- not by
     the triangle inequality on |ch| and |cl3| separately, which would
     overshoot -- and the shared FLT/FIX lattice at exponent emin makes
     Fast2Sum exact there, with no ordering and no precision hypothesis. *)
  have HuP' : u'*P <= /32*P.
  { have H := Rmult_le_compat_r P _ _ HP0 Hu. nra. }
  have HsmallP : P < 6*eta.
  { apply Rnot_le_lt. move => HPbig.
    have Hcontra : Rabs (FT2R cl3) <= Rabs (FT2R ch).
    { eapply Rle_trans; [exact Hcl30|]. eapply Rle_trans; [|exact Hchlo0].
      have H6 : 6*u'*P = 6*(u'*P) by ring.
      rewrite H6. nra. }
    exact (Hnord Hcontra). }
  have HXM : Rabs (X*M) <= (1+u')^2*P.
  { have Hxl := @dw_low_le_u_high t STD xh0 xl0 DWx0.
    have Hml := @dw_low_le_u_high t STD yh0 yl0 DWy0.
    fold u' in Hxl,Hml.
    have Hx : Rabs X <= (1+u')*Rabs (FT2R xh0).
    { unfold X. eapply Rle_trans; [apply Rabs_triang|]. nra. }
    have Hy : Rabs M <= (1+u')*Rabs (FT2R yh0).
    { unfold M. eapply Rle_trans; [apply Rabs_triang|]. nra. }
    have H := Rmult_le_compat _ _ _ _ (Rabs_pos _) (Rabs_pos _) Hx Hy.
    rewrite Rabs_mult. eapply Rle_trans; [exact H|].
    unfold P,P0. rewrite Rabs_mult. right;ring. }
  have Hu2P : u'^2*P <= /1024*P.
  { have H : (u'^2 <= /1024)%R by nra.
    have H2 := Rmult_le_compat_r P _ _ HP0 H. nra. }
  have Hbig16 : 16*eta <= bpow radix2 (common.emin (t:=t)+fprec t).
  { unfold eta. have -> : (16:R)=bpow radix2 4 by (simpl;lra).
    rewrite -bpow_plus. apply bpow_le; lia. }
  have Hsumsmall : Rabs (FT2R ch+FT2R cl3) <=
      bpow radix2 (common.emin (t:=t)+fprec t).
  { have Htri2 := Rabs_triang ((FT2R ch+FT2R cl3)-X*M) (X*M).
    replace ((FT2R ch+FT2R cl3)-X*M+X*M)%R with (FT2R ch+FT2R cl3)%R
      in Htri2 by ring.
    have Hstep : Rabs (FT2R ch+FT2R cl3) <= 5/2*eta+u'^2*P+(1+u')^2*P.
    { eapply Rle_trans; [exact Htri2|].
      apply Rplus_le_compat; [exact Hcore|exact HXM]. }
    (* 2.5*eta + P/1024 + (1+u)^2*P < 2.5*eta + 6.4*eta < 16*eta *)
    have Hexp : (1+u')^2*P = P+(2*u'*P+u'^2*P) by ring.
    have Hstep2 : 5/2*eta+u'^2*P+(1+u')^2*P <= 16*eta.
    { rewrite Hexp. nra. }
    eapply Rle_trans; [exact Hstep|].
    eapply Rle_trans; [exact Hstep2|exact Hbig16]. }
  have Hsum := Fast2Sum_sum_exact_of_sum_small ch cl3 Fe Hsumsmall.
  change (FT2R (fst d)+FT2R (snd d)=FT2R ch+FT2R cl3) in Hsum.
  split.
  + rewrite Hsum. exact Hcore.
  + exact (DWTimesDW3_double_word_of_sum xh0 xl0 yh0 yl0 FIN Hsum).
Qed.

(* Near-threshold regime: the leading product is normal but within 9/8 of the
   TwoProd exactness threshold T = 2^(emin+2p-1), so eta is not small relative
   to the product and the floor budget must be spent explicitly.

   WHY p >= 8 HERE (and only here).  The aggregate low-order error is
   7.5*u^2*P (aux_eta_bnd), the target is 4*u^2|xr*yr| + 2*eta, and
   |xr*yr| >= (1-u)^2*P with u^2*T = eta/2.  So it suffices that

       (15/2 - 4*(1-u)^2) * P <= 4*T,   and here P <= (9/8)*T,

   i.e. (15/2 - 4*(1-u)^2)*(9/8) <= 4.  As u -> 0 the left side tends to
   3.5*(9/8) = 3.9375, so the inequality holds with only 1.6% of headroom,
   and the u-linear term (coefficient 9) eats it at
   u > 0.0069687: it holds at p >= 8 and fails at p = 7
   (4.0075 > 4).  The bound is therefore a genuine limit of this route --
   7.5 from aux_eta_bnd against the 9/8 window -- not slack in an nra call.
   Every other regime of Algorithm 12 holds at p >= 5; this theorem is the
   sole reason DWTimesDW3_error_mixed_floor below carries p >= 8. *)
Theorem DWTimesDW_abs_normal_near_threshold :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  (8 <= fprec t)%Z ->
  bpow radix2 (eminA+2*fprec t-1) <=
    Rabs (FT2R xh*FT2R yh) ->
  Rabs (FT2R xh*FT2R yh) <=
    9/8*bpow radix2 (eminA+2*fprec t-1) ->
  Rabs (zh+zl-xr*yr) <=
    4*u^2*Rabs (xr*yr)+2*bpow radix2 eminA.
Proof.
move => DWx DWy FIN Hp8 Nprod Pnear.
have Hp5 : (5 <= fprec t)%Z by lia.
have Hp3 : (3 <= fprec t)%Z by lia.
have Fmul := DWTimesDW3_mul_finite xh xl yh yl FIN.
have F0 := DWTimesDW3_low_low_finite xh xl yh yl FIN.
have F1 := DWTimesDW3_first_correction_finite xh xl yh yl FIN.
have F2 := DWTimesDW3_second_correction_finite xh xl yh yl FIN.
have F3 := DWTimesDW3_correction_finite xh xl yh yl FIN.
have HerrEq := relerr_error_eq xh xl yh yl Hp3 DWx DWy FIN Fmul Nprod.
have HerrRaw := aux_eta_bnd xh xl yh yl Hp5 DWx DWy
  Fmul F0 F1 F2 F3 Nprod.
rewrite HerrEq.
set P := Rabs (FT2R xh*FT2R yh) in Nprod, Pnear, HerrRaw *.
set T := bpow radix2 (eminA+2*fprec t-1) in Nprod, Pnear *.
set eta := bpow radix2 eminA.
have Hu0 : 0 < u by (unfold u;apply bpow_gt_0).
have Hu : u <= /256.
{ unfold u. have -> : (/256:R)=bpow radix2 (-8) by (simpl;lra).
  apply bpow_le; lia. }
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have HT0 : 0 < T by (unfold T;apply bpow_gt_0).
have Heta0 : 0 < eta by (unfold eta;apply bpow_gt_0).
have Hscale : u^2*T=/2*eta.
{ replace (u^2) with (u*u) by ring. unfold u,T,eta.
  rewrite -(bpow_plus radix2 (-fprec t) (-fprec t)).
  rewrite -(bpow_plus radix2 (-fprec t+-fprec t)
    (eminA+2*fprec t-1)).
  replace (-fprec t+-fprec t+(eminA+2*fprec t-1))%Z with
    (eminA-1)%Z by ring.
  rewrite (bpow_plus radix2 eminA (-1)).
  change (bpow radix2 (-1)) with (/2:R). ring. }
have Hprod := aux_dw_exact_product_lower xh xl yh yl DWx DWy.
specialize (Hprod STD). fold u xr yr P in Hprod.
have Hpaperpart : 4*u^2*((1-u)^2*P) <=
    4*u^2*Rabs (xr*yr).
{ apply Rmult_le_compat_l; [nra|exact Hprod]. }
eapply Rle_trans; [exact HerrRaw|].
eapply Rle_trans; [|apply Rplus_le_compat_r;exact Hpaperpart].
have HnearScaled := Rmult_le_compat_l (u^2) _ _
  (pow2_ge_0 u) Pnear.
have Hbudget : 15/2*u^2*P <=
    4*u^2*((1-u)^2*P)+2*eta.
{ have Hcoef :
      (15/2-4*(1-u)^2)*(9/8) <= 4 by nra.
  have Hnonneg : 0 <= 15/2-4*(1-u)^2 by nra.
  have Hstep := Rmult_le_compat_l
    (15/2-4*(1-u)^2) _ _ Hnonneg HnearScaled.
  nra. }
replace (u*u) with (u^2) by ring. exact Hbudget.
Qed.

(* Same regime at the 5/2*eta floor, and therefore at p >= 5 rather than p >= 8.
   The budget above needed (15/2-4*(1-u)^2)*(9/8) <= 4, which tends to 3.9375
   and leaves only 1.6% of headroom; against a 5/2*eta target the requirement
   is <= 5 instead, i.e. u <= 0.126, so p >= 5 clears it by a wide margin.
   This is the variant the whole-range assembly below uses -- its gap regime
   costs 5/2*eta anyway (DWTimesDW3_error_floor_gap), so spending the same
   floor here is free and removes the file's only p >= 8 hypothesis.  The
   sharper 2*eta theorem above is unchanged and still available. *)
Local Theorem DWTimesDW_abs_normal_near_threshold_floor52 :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  bpow radix2 (eminA+2*fprec t-1) <=
    Rabs (FT2R xh*FT2R yh) ->
  Rabs (FT2R xh*FT2R yh) <=
    9/8*bpow radix2 (eminA+2*fprec t-1) ->
  Rabs (zh+zl-xr*yr) <=
    4*u^2*Rabs (xr*yr)+5/2*bpow radix2 eminA.
Proof.
move => DWx DWy FIN Hp5 Nprod Pnear.

have Hp3 : (3 <= fprec t)%Z by lia.
have Fmul := DWTimesDW3_mul_finite xh xl yh yl FIN.
have F0 := DWTimesDW3_low_low_finite xh xl yh yl FIN.
have F1 := DWTimesDW3_first_correction_finite xh xl yh yl FIN.
have F2 := DWTimesDW3_second_correction_finite xh xl yh yl FIN.
have F3 := DWTimesDW3_correction_finite xh xl yh yl FIN.
have HerrEq := relerr_error_eq xh xl yh yl Hp3 DWx DWy FIN Fmul Nprod.
have HerrRaw := aux_eta_bnd xh xl yh yl Hp5 DWx DWy
  Fmul F0 F1 F2 F3 Nprod.
rewrite HerrEq.
set P := Rabs (FT2R xh*FT2R yh) in Nprod, Pnear, HerrRaw *.
set T := bpow radix2 (eminA+2*fprec t-1) in Nprod, Pnear *.
set eta := bpow radix2 eminA.
have Hu0 : 0 < u by (unfold u;apply bpow_gt_0).
have Hu : u <= /32.
{ unfold u. have -> : (/32:R)=bpow radix2 (-5) by (simpl;lra).
  apply bpow_le; lia. }
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have HT0 : 0 < T by (unfold T;apply bpow_gt_0).
have Heta0 : 0 < eta by (unfold eta;apply bpow_gt_0).
have Hscale : u^2*T=/2*eta.
{ replace (u^2) with (u*u) by ring. unfold u,T,eta.
  rewrite -(bpow_plus radix2 (-fprec t) (-fprec t)).
  rewrite -(bpow_plus radix2 (-fprec t+-fprec t)
    (eminA+2*fprec t-1)).
  replace (-fprec t+-fprec t+(eminA+2*fprec t-1))%Z with
    (eminA-1)%Z by ring.
  rewrite (bpow_plus radix2 eminA (-1)).
  change (bpow radix2 (-1)) with (/2:R). ring. }
have Hprod := aux_dw_exact_product_lower xh xl yh yl DWx DWy.
specialize (Hprod STD). fold u xr yr P in Hprod.
have Hpaperpart : 4*u^2*((1-u)^2*P) <=
    4*u^2*Rabs (xr*yr).
{ apply Rmult_le_compat_l; [nra|exact Hprod]. }
eapply Rle_trans; [exact HerrRaw|].
eapply Rle_trans; [|apply Rplus_le_compat_r;exact Hpaperpart].
have HnearScaled := Rmult_le_compat_l (u^2) _ _
  (pow2_ge_0 u) Pnear.
have Hbudget : 15/2*u^2*P <=
    4*u^2*((1-u)^2*P)+5/2*eta.
{ have Hcoef :
      (15/2-4*(1-u)^2)*(9/8) <= 5 by nra.
  have Hnonneg : 0 <= 15/2-4*(1-u)^2 by nra.
  have Hstep := Rmult_le_compat_l
    (15/2-4*(1-u)^2) _ _ Hnonneg HnearScaled.
  nra. }
replace (u*u) with (u^2) by ring. exact Hbudget.
Qed.

(** Absolute form of the existing regime-independent multiplication estimate
    on the normal-leading branch.  This is used only for the pure-relative
    fallback outside the sharp floored-paper regimes. *)
Theorem DWTimesDW_abs_low0_low1_low2_final_normal :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  bpow radix2 (eminA+2*fprec t-1) <=
    Rabs (FT2R xh*FT2R yh) ->
  Rabs (FT2R xl*FT2R yl) < bpow radix2 (eminA+fprec t-1) ->
  Rabs (FT2R xh*FT2R yl+FT2R (BMULT xl yl)) <
    bpow radix2 (eminA+fprec t-1) ->
  Rabs (FT2R xl*FT2R yh+
    FT2R (BFMA xh yl (BMULT xl yl))) <
    bpow radix2 (eminA+fprec t-1) ->
  bpow radix2 (eminA+fprec t-1) <=
    Rabs (FT2R (Fast2Mult_err xh yh)+
      FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) ->
  Rabs (zh+zl-xr*yr) <=
    4*u^2*Rabs (xr*yr)+2*bpow radix2 eminA.
Proof.
move => DWx DWy FIN Hp5 Nprod N0 N1 N2 N3.
have Hp3 : (3 <= fprec t)%Z by lia.
have Fmul := DWTimesDW3_mul_finite xh xl yh yl FIN.
have H := relerr_error_relative_floor_decomposition xh xl yh yl
  Hp3 DWx DWy FIN Fmul Nprod.
destruct H as
  (er0 & er1 & er2 & er3 & ef0 & ef1 & ef2 & ef3 &
   Heq & R0 & R1 & R2 & R3 & F0b & F1b & F2b & F3b & Hef &
   ER1 & ER2 & ER3 & ER1f & ER2f & ER3f &
   Z0 & Z1 & Z2 & Z3 & G0 & G1 & G2 & G3 &
   T0 & T1 & T2 & S0 & S1 & S2 & S3).
destruct G0 as [[Ef0 N0normal]|[Er0 N0small]].
{ exfalso; exact (Rlt_not_le _ _ N0 N0normal). }
destruct G1 as [[Ef1 N1normal]|[Er1 N1small]].
{ exfalso; exact (Rlt_not_le _ _ N1 N1normal). }
destruct G2 as [[Ef2 N2normal]|[Er2 N2small]].
{ exfalso; exact (Rlt_not_le _ _ N2 N2normal). }
destruct G3 as [[Ef3 N3normal]|[Er3 N3small]].
2:{ exfalso; exact (Rlt_not_le _ _ N3small N3). }
subst er0; subst er1; subst er2; subst ef3.
set P := Rabs (FT2R xh*FT2R yh).
set eta := bpow radix2 eminA.
set U := bpow radix2 (eminA+fprec t-1).
have Hu0 : 0 < u by (unfold u;apply bpow_gt_0).
have Hu : u <= /32.
{ unfold u. have -> : (/32:R)=bpow radix2 (-5) by (simpl;lra).
  apply bpow_le;lia. }
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have Heta0 : 0 < eta by (unfold eta;apply bpow_gt_0).
have Hcl1u : Rabs (FT2R (Fast2Mult_err xh yh)) <=
    /2*ulp (FT2R xh*FT2R yh)
  by (apply Fast2Mult_accuracy_norm;exact Fmul).
have Hulp : ulp (FT2R xh*FT2R yh) <=
    P*bpow radix2 (1-fprec t).
{ unfold P. apply ulp_FLT_le.
  eapply Rle_trans; [|exact Nprod]. apply bpow_le.
  unfold eminA, common.emin, SpecFloat.emin.
  pose proof fprec_lb t. lia. }
have HBp : bpow radix2 (1-fprec t)=2*u.
{ unfold u.
  change (bpow radix2 (1-fprec t)=
    bpow radix2 1*bpow radix2 (-fprec t)).
  rewrite -(bpow_plus radix2 1 (-fprec t)). f_equal;lia. }
have Hcl1 : Rabs (FT2R (Fast2Mult_err xh yh)) <= u*P.
{ rewrite HBp in Hulp. nra. }
have HUscale : u*U=/2*eta.
{ unfold u,U,eta. rewrite -(bpow_plus radix2 (-fprec t)
    (eminA+fprec t-1)).
  replace (-fprec t+(eminA+fprec t-1))%Z with (eminA-1)%Z by ring.
  rewrite (bpow_plus radix2 eminA (-1)).
  change (bpow radix2 (-1)) with (/2:R). ring. }
have Hscale : u^2*bpow radix2 (eminA+2*fprec t-1)=/2*eta.
{ replace (u^2) with (u*u) by ring. unfold u,eta.
  rewrite -(bpow_plus radix2 (-fprec t) (-fprec t)).
  rewrite -(bpow_plus radix2 (-fprec t+-fprec t)
    (eminA+2*fprec t-1)).
  replace (-fprec t+-fprec t+(eminA+2*fprec t-1))%Z with
    (eminA-1)%Z by ring.
  rewrite (bpow_plus radix2 eminA (-1)).
  change (bpow radix2 (-1)) with (/2:R). ring. }
have HetaP : eta <= 2*u^2*P.
{ have Hs := Rmult_le_compat_l (u^2) _ _ (pow2_ge_0 u) Nprod.
  rewrite Hscale in Hs. fold P in Hs.
  apply (Rmult_le_reg_l (/2)); [lra|].
  eapply Rle_trans; [exact Hs|]. nra. }
fold P eta U in N2small,F0b,F1b,F2b,ER3.
replace (FT2R (Fast2Mult_err xh yh)+FT2R xl*FT2R yh+
  FT2R xh*FT2R yl+FT2R xl*FT2R yl+0+0+0)%R with
  (FT2R (Fast2Mult_err xh yh)+FT2R xl*FT2R yh+
   FT2R xh*FT2R yl+FT2R xl*FT2R yl)%R in ER3 by ring.
have HEF01 : Rabs (ef0+ef1) <= eta.
{ eapply Rle_trans; [apply Rabs_triang|]. nra. }
have HEF012 : Rabs (ef0+ef1+ef2) <= 3/2*eta.
{ have Ht := Rabs_triang (ef0+ef1) ef2.
  eapply Rle_trans; [exact Ht|]. nra. }
have HT1 : FT2R (BFMA xh yl (BMULT xl yl))=
    FT2R xh*FT2R yl+FT2R xl*FT2R yl+(ef0+ef1) by nra.
have Hcorr : Rabs (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
    FT2R xl*FT2R yl) <= U+eta.
{ have Hinput :
      Rabs ((FT2R xl*FT2R yh+
        FT2R (BFMA xh yl (BMULT xl yl)))+(-(ef0+ef1))) <=
      Rabs (FT2R xl*FT2R yh+
        FT2R (BFMA xh yl (BMULT xl yl)))+Rabs (-(ef0+ef1))
      := Rabs_triang _ _.
  pose proof (@Hinput NANS STD NANS STD) as Hinput0.
  replace ((FT2R xl*FT2R yh+
    FT2R (BFMA xh yl (BMULT xl yl)))+(-(ef0+ef1)))%R with
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
      FT2R xl*FT2R yl)%R in Hinput0.
  2:{ replace (FT2R (BFMA xh yl (BMULT xl yl))) with
        (FT2R xh*FT2R yl+FT2R xl*FT2R yl+(ef0+ef1))
        by (symmetry;exact HT1). ring. }
  rewrite Rabs_Ropp in Hinput0.
  eapply Rle_trans; [exact Hinput0|]. lra. }
have Hcentral3 : Rabs (FT2R (Fast2Mult_err xh yh)+
    FT2R xl*FT2R yh+FT2R xh*FT2R yl+FT2R xl*FT2R yl) <=
    u*P+U+eta.
{ have Ht := Rabs_triang (FT2R (Fast2Mult_err xh yh))
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+FT2R xl*FT2R yl).
  specialize (Ht NANS STD).
  replace (FT2R (Fast2Mult_err xh yh)+
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+FT2R xl*FT2R yl))%R with
    (FT2R (Fast2Mult_err xh yh)+FT2R xl*FT2R yh+
      FT2R xh*FT2R yl+FT2R xl*FT2R yl)%R in Ht by ring.
  eapply Rle_trans; [exact Ht|]. lra. }
have HE3 : Rabs er3 <= u^2*P+/2*eta+5/2*u*eta.
{ eapply Rle_trans; [exact ER3|].
  have Hm := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Hcentral3.
  have Hf := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) HEF012.
  eapply Rle_trans.
  - apply Rplus_le_compat; [exact Hm|exact Hf].
  - nra. }
have Hprod := aux_dw_exact_product_lower xh xl yh yl DWx DWy.
specialize (Hprod STD). fold u xr yr P in Hprod.
have Hrel : Rabs er3 <= 4*u^2*Rabs (xr*yr)+/2*eta.
{ have Hueta := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) HetaP.
  have Hcoef0 : 1+5*u <= 4*(1-u)^2.
  { have H13 : 13*u <= 1 by lra.
    have Hu2pos : 0 <= u^2 by apply pow2_ge_0.
    eapply Rle_trans with (r2:=(1+5*u)+(3-13*u+4*u^2)).
    - lra.
    - apply Req_le. field. }
  have HB0 : 0 <= u^2*P by
    (apply Rmult_le_pos;[apply pow2_ge_0|exact HP0]).
  have Hcoef := Rmult_le_compat_r (u^2*P) _ _ HB0 Hcoef0.
  have Hraw : Rabs er3 <= (1+5*u)*(u^2*P)+/2*eta.
  { eapply Rle_trans; [exact HE3|].
    eapply Rle_trans with
      (r2:=u^2*P+/2*eta+5*u*(u^2*P)).
    - apply Rplus_le_compat_l.
      have H5 := Rmult_le_compat_l (5/2) _ _ ltac:(lra) Hueta.
      replace (5/2*u*eta)%R with (5/2*(u*eta))%R by field.
      replace (5*u*(u^2*P))%R with
        (5/2*(u*(2*u^2*P)))%R by field.
      exact H5.
    - apply Req_le. field. }
  have Hpaper : 4*u^2*((1-u)^2*P) <= 4*u^2*Rabs (xr*yr).
  { apply Rmult_le_compat_l; [apply Rmult_le_pos;[lra|apply pow2_ge_0]|exact Hprod]. }
  eapply Rle_trans; [exact Hraw|].
  eapply Rle_trans with (r2:=4*(1-u)^2*(u^2*P)+/2*eta).
  - apply Rplus_le_compat_r. exact Hcoef.
  - eapply Rle_trans with (r2:=4*u^2*((1-u)^2*P)+/2*eta).
    + apply Req_le. field.
    + apply Rplus_le_compat_r. exact Hpaper. }
rewrite Heq.
replace (0+0+0+er3+(ef0+ef1+ef2+0)) with
  (er3+(ef0+ef1+ef2)) by ring.
have Htri := Rabs_triang er3 (ef0+ef1+ef2).
eapply Rle_trans; [exact Htri|].
eapply Rle_trans.
- apply Rplus_le_compat; [exact Hrel|exact HEF012].
- apply Req_le. field.
Qed.

(** Whole-range mixed analysis.  The normal arm retains the paper's [4u^2]
    coefficient.  Physical underflow in the low-order nodes is represented
    explicitly by the [2.5 eta] term.  A separate gap lemma covers leading
    products below the Fast2Mult exactness threshold, so no normality condition
    is required by the mixed API. *)

(* All four partial products vanish together: xh*yh = 0 forces one factor
   of each pair to be zero, and the double-word relation then forces the
   matching low component to be zero as well. *)

(* Hence the computed pair is exactly (0,0): every rounded node of
   Algorithm 12 is a rounding of an exact zero, and the closing Fast2Sum
   is trivially ordered so its sum is preserved. *)

(* ---------- public assembly: the whole-range mixed API ---------- *)

(* Normal arm at the 5/2*eta floor.  The near-threshold leg uses the _floor52
   variant, so the whole tree holds at p >= 5. *)
Local Theorem DWTimesDW3_error_floor_normal :
  (5 <= fprec t)%Z ->
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  bpow radix2 (eminA+2*fprec t-1) <= Rabs (FT2R xh*FT2R yh) ->
  Rabs (zh+zl-xr*yr) <=
    4*u^2*Rabs (xr*yr)+5/2*bpow radix2 eminA.
Proof.
move => Hp5 DWx DWy FIN Nprod.
have Heta0 : 0 < bpow radix2 eminA by apply bpow_gt_0.
set T := bpow radix2 (eminA + 2 * fprec t - 1).
set N := bpow radix2 (eminA + fprec t - 1).
set P := Rabs (FT2R xh * FT2R yh).
fold T P in Nprod.
destruct (Rle_or_lt P (9 / 8 * T)) as [Hnear | Hfar].
- exact (DWTimesDW_abs_normal_near_threshold_floor52
    DWx DWy FIN Hp5 Nprod Hnear).
- have H2 : Rabs (zh+zl-xr*yr) <=
      4*u^2*Rabs (xr*yr)+2*bpow radix2 eminA.
  { destruct (Rle_or_lt N (Rabs (FT2R xl * FT2R yl))) as [N0 | U0].
    - have H := DWTimesDW_abs_low0_normal
        DWx DWy FIN ltac:(lia) Nprod N0.
      eapply Rle_trans; [exact H|]. nra.
    - destruct (Rle_or_lt N
        (Rabs (FT2R (Fast2Mult_err xh yh) +
               FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))))
        as [N3 | U3].
      + destruct (Rle_or_lt N
          (Rabs (FT2R xh * FT2R yl + FT2R (BMULT xl yl)))) as [N1 | U1].
        * destruct (Rle_or_lt N
            (Rabs (FT2R xl * FT2R yh +
                   FT2R (BFMA xh yl (BMULT xl yl))))) as [N2 | U2].
          -- exact (DWTimesDW_abs_low0_far xh xl yh yl
               DWx DWy FIN ltac:(lia) Hfar U0 N1 N2 N3).
          -- exact (DWTimesDW_abs_low0_low2_other_normal
               DWx DWy FIN ltac:(lia) Nprod U0 N1 U2 N3).
        * destruct (Rle_or_lt N
            (Rabs (FT2R xl * FT2R yh +
                   FT2R (BFMA xh yl (BMULT xl yl))))) as [N2 | U2].
          -- exact (DWTimesDW_abs_low0_low1_tail_normal
               DWx DWy FIN ltac:(lia) Nprod U0 U1 N2 N3).
          -- exact (DWTimesDW_abs_low0_low1_low2_final_normal
               DWx DWy FIN ltac:(lia) Nprod U0 U1 U2 N3).
      + exact (DWTimesDW_abs_low0_final_underflow
          DWx DWy FIN ltac:(lia) Nprod U0 U3). }
  lra.
Qed.

(* WHOLE-RANGE error bound.  The leading-product hypothesis is gone: the three
   regimes are P = 0 and 0 < P < T (both handled by the gap lemma, which needs
   no lower bound at all) and T <= P (the regime tree).  The price of covering
   the gap is the floor rising from 2*eta to 5/2*eta; in exchange the bound
   now holds for every finite input, and p >= 5 replaces
   DWTimesDW3_error_mixed_floor's p >= 8. *)
Theorem DWTimesDW_mixed_accuracy_from_cond :
  (5 <= fprec t)%Z ->
  DWTimesDW_mixed_cond xh xl yh yl ->
  Rabs (zh+zl-xr*yr) <=
    4*u^2*Rabs (xr*yr)+5/2*bpow radix2 eminA.
Proof.
move => Hp5 [[DWx DWy] FIN].
destruct (Rle_or_lt (bpow radix2 (eminA+2*fprec t-1))
    (Rabs (FT2R xh*FT2R yh))) as [Nprod | Hgap].
- exact (DWTimesDW3_error_floor_normal Hp5 DWx DWy FIN Nprod).
- (* gap (P = 0 included): the u^2*P residual is absorbed into 4u^2|xr*yr|
     because |xr*yr| >= (1-u)^2*P and 4*(1-u)^2 >= 1 for u <= /2. *)
  have Hgap' : Rabs (FT2R xh*FT2R yh) <
      bpow radix2 (common.emin (t:=t)+2*fprec t-1) by exact Hgap.
  have H := proj1 (DWTimesDW3_error_floor_gap xh xl yh yl
    Hp5 DWx DWy FIN Hgap').
  fold zh zl xr yr in H.
  have HXM := aux_dw_exact_product_lower xh xl yh yl DWx DWy.
  specialize (HXM STD). fold u xr yr in HXM.
  set P := Rabs (FT2R xh*FT2R yh).
  set Q := Rabs (xr*yr).
  fold P in H. fold P Q in HXM. fold Q.
  have Heta : bpow radix2 (common.emin (t:=t)) = bpow radix2 eminA
    by reflexivity.
  rewrite Heta in H.
  have Hu0 : 0 < u by apply bpow_gt_0.
  have Hu : u <= /32.
  { have -> : (/32:R)=bpow radix2 (-5) by (simpl;lra).
    apply bpow_le; lia. }
  have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
  (* absorb the gap lemma's u^2*P residual into the target's 4u^2*|xr*yr|,
     using |xr*yr| >= (1-u)^2*P and 4*(1-u)^2 >= 1 at u <= /32 *)
  have Hc : 1 <= 4*(1-u)^2 by nra.
  have Hup : 0 <= u^2*P by nra.
  have H1 : u^2*P*1 <= u^2*P*(4*(1-u)^2)
    by (apply Rmult_le_compat_l; [exact Hup|exact Hc]).
  have H2 : 4*u^2*((1-u)^2*P) <= 4*u^2*Q
    by (apply Rmult_le_compat_l; [nra|exact HXM]).
  lra.
Qed.

(* WHOLE-RANGE closure.  Both regimes preserve the closing Fast2Sum's sum, so
   both give the double-word property: above the threshold through the
   ordering |cl3| <= |ch| (aux_cl3_le_ch), in the gap through the tiny-sum
   lattice argument inside DWTimesDW3_error_floor_gap. *)
Theorem DWTimesDW_double_word_from_cond :
  (5 <= fprec t)%Z ->
  DWTimesDW_mixed_cond xh xl yh yl ->
  double_word_prop (fst (DWTimesDW3 xh xl yh yl))
                   (snd (DWTimesDW3 xh xl yh yl)).
Proof.
move => Hp5 [[DWx DWy] FIN].
have Hp3 : (3 <= fprec t)%Z by lia.
destruct (Rle_or_lt (bpow radix2 (eminA+2*fprec t-1))
    (Rabs (FT2R xh*FT2R yh))) as [Nprod | Hgap].
- have Hfp : is_finite (BPLUS (Fast2Mult_mul xh yh)
                 (BPLUS (Fast2Mult_err xh yh)
                        (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) = true
    by exact (proj1 FIN).
  destruct (BPLUS_finite_e t _ _ Hfp) as [_ Hfcl3].
  have Hfmul : is_finite (BMULT xh yh)=true
    by exact (DWTimesDW3_mul_finite xh xl yh yl FIN).
  have Nprod' : bpow radix2 (common.emin (t:=t)+2*fprec t-1) <=
      Rabs (FT2R xh*FT2R yh) by exact Nprod.
  have Hord := aux_cl3_le_ch xh xl yh yl Hp3 DWx DWy Hfmul Hfcl3 Nprod'.
  exact (DWTimesDW3_double_word_from_pre xh xl yh yl Hfp Hord).
- have Hgap' : Rabs (FT2R xh*FT2R yh) <
      bpow radix2 (common.emin (t:=t)+2*fprec t-1) by exact Hgap.
  exact (proj2 (DWTimesDW3_error_floor_gap xh xl yh yl
    Hp5 DWx DWy FIN Hgap')).
Qed.

End DWMulDW_Division_Helpers.

Section MixedCondBridgeDWTimesDW.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Definition DWTimesDW_mixed_guarantee
    (xh xl yh yl : ftype t) : Prop :=
  let '(zh, zl) := DWTimesDW3 xh xl yh yl in
  Rabs
    (FT2R zh + FT2R zl -
       (FT2R xh + FT2R xl) * (FT2R yh + FT2R yl))
    <= 4 * bpow Zaux.radix2 (- fprec t) ^ 2 *
         Rabs ((FT2R xh + FT2R xl) * (FT2R yh + FT2R yl)) +
       5 / 2 * bpow Zaux.radix2 (@common.emin t) /\
  double_word_prop zh zl.

Theorem DWTimesDW_mixed_guarantee_from_cond
    (xh xl yh yl : ftype t) :
  (5 <= fprec t)%Z ->
  DWTimesDW_mixed_cond xh xl yh yl ->
  DWTimesDW_mixed_guarantee xh xl yh yl.
Proof.
intros Hp5 Hcond.
have Hacc :=
  DWTimesDW_mixed_accuracy_from_cond xh xl yh yl Hp5 Hcond.
have Hdw :=
  DWTimesDW_double_word_from_cond xh xl yh yl Hp5 Hcond.
unfold DWTimesDW_mixed_guarantee.
revert Hacc Hdw.
destruct (DWTimesDW3 xh xl yh yl) as [zh zl].
cbn [fst snd]. intros Hacc Hdw. exact (conj Hacc Hdw).
Qed.

Lemma DWTimesDW_mixed_cond_of_safe_input_cond
    (xh xl yh yl : ftype t) :
  (4 <= fprec t)%Z ->
  DWTimesDW_mixed_safe_input_cond xh xl yh yl ->
  DWTimesDW_mixed_cond xh xl yh yl.
Proof.
move => Hp4 Hsafe.
have Hfin := DWTimesDW3_finite_from_safe_input_cond xh xl yh yl Hp4 Hsafe.
move: Hsafe => [_ [_ [Hdx [Hdy _]]]].
unfold DWTimesDW_mixed_cond, DWTimesDW_mixed_input_cond,
       DWTimesDW_result_finite.
exact (conj (conj Hdx Hdy) Hfin).
Qed.

Theorem DWTimesDW_mixed_guarantee_from_safe_input_cond
    (xh xl yh yl : ftype t) :
  (5 <= fprec t)%Z ->
  DWTimesDW_mixed_safe_input_cond xh xl yh yl ->
  DWTimesDW_mixed_guarantee xh xl yh yl.
Proof.
intros Hp5 Hsafe.
apply DWTimesDW_mixed_guarantee_from_cond; [exact Hp5 |].
exact (DWTimesDW_mixed_cond_of_safe_input_cond
  xh xl yh yl ltac:(lia) Hsafe).
Qed.

Lemma DWTimesDW_inputs_finite_of_result_finite
    (xh xl yh yl : ftype t) :
  DWTimesDW_result_finite xh xl yh yl ->
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite yh = true /\
  is_finite yl = true.
Proof.
unfold DWTimesDW_result_finite.
move => Hfin.
exact (conj (DWTimesDW3_xh_finite xh xl yh yl Hfin)
       (conj (DWTimesDW3_xl_finite xh xl yh yl Hfin)
       (conj (DWTimesDW3_yh_finite xh xl yh yl Hfin)
             (DWTimesDW3_yl_finite xh xl yh yl Hfin)))).
Qed.

End MixedCondBridgeDWTimesDW.
