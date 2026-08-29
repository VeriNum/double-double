(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Relative accuracy and shared representation results for [DWTimesDW] (Algorithm 12).

    Its public result is [DWTimesDW_relative_accuracy], the pure [4u^2]
    relative bound under [DWTimesDW_relative_precond].  Shared
    runtime model and finiteness lemmas are consumed by [DWMulDW_mixed_acc],
    while [DWDivDW_relative_acc] consumes the FLX bridge for its closing
    multiplication. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common FLT_helpers.
Require Import DWTimesFP DWTimesDW DDConds DWord_defs Fast2Mult_acc TwoSum_acc Fast2Sum_acc.
Require Import DWPlusFP_relative_acc_helpers DW_acc_lemmas.
(* The primitive Fast2Sum and Fast2Mult files supply the generic exact sum and
   underflow floor lemmas reused by the Algorithm 12 gap block.  DWMulFP_relative_acc
   supplies only the bridge specific to this operation and shared with division. *)
Require Import DWMulFP_relative_acc.
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
   Section 1: derive finiteness of each node from
   FIN : is_finite_p (DWTimesDW xh xl yh yl).
   ============================================================ *)
Section CorrectDWMulDW.
  Context {NANS: Nans} {t : type} {STD: is_standard t}.

  Variables (xh xl yh yl : ftype t).

  Hypothesis FIN : is_finite_p (DWTimesDW xh xl yh yl).

  (* fst (DWTimesDW xh xl yh yl) reduces to
       BPLUS (BMULT xh yh) (BPLUS (Fast2Mult_err xh yh)
                                  (BFMA xl yh (BFMA xh yl (BMULT xl yl)))).
     One pass of BPLUS/BFMA elimination of finiteness exposes every subterm's
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

  Fact DWTimesDW_xh_finite : is_finite xh = true.
  Proof. prove_finite. Qed.

  Fact DWTimesDW_xl_finite : is_finite xl = true.
  Proof. prove_finite. Qed.

  Fact DWTimesDW_yh_finite : is_finite yh = true.
  Proof. prove_finite. Qed.

  Fact DWTimesDW_yl_finite : is_finite yl = true.
  Proof. prove_finite. Qed.

  (* ch = fst (Fast2Mult xh yh) = BMULT xh yh *)
  Fact DWTimesDW_mul_finite : is_finite (BMULT xh yh) = true.
  Proof. prove_finite. Qed.

  Fact DWTimesDW_fast2mult_finite : is_finite_p (Fast2Mult xh yh).
  Proof. prove_finite. Qed.

  Let cl1 := snd (Fast2Mult xh yh).
  Let tl0 := BMULT xl yl.
  Let tl1 := BFMA xh yl tl0.
  Let cl2 := BFMA xl yh tl1.
  Let cl3 := BPLUS cl1 cl2.

  Fact DWTimesDW_low_low_finite : is_finite tl0 = true.
  Proof. prove_finite. Qed.

  Fact DWTimesDW_first_correction_finite : is_finite tl1 = true.
  Proof. prove_finite. Qed.

  Fact DWTimesDW_second_correction_finite : is_finite cl2 = true.
  Proof. prove_finite. Qed.

  Fact DWTimesDW_correction_finite : is_finite cl3 = true.
  Proof. prove_finite. Qed.

End CorrectDWMulDW.


(* ============================================================
   Section 2: the essential FLX -> FLT bridge for DWTimesDW.
     DWTimesDW.DWTimesDW12 (fprec t) choice (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl)
       = F2Rp (DWTimesDW xh xl yh yl).
   Analog of DWMulFP_relative_acc.v's DWTimesFP_FLX_FLT_weak: each of the five rounded ops
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

Hypothesis FIN : is_finite_p (DWTimesDW xh xl yh yl).
(* Normal regime hypotheses: every rounding argument of DWTimesDW is normal
   (>= bpow(emin+fprec-1)), so each FLT rounding equals its FLX counterpart
   (round_FLT_FLX).  Nprod is the two-product threshold for
   DWMulFP_relative_acc.Fast2Mult_correct_weak. *)
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
    Algorithm 12 composition from the conditions under which each FLT and FLX node agrees
    (normality, zero, or exact subnormal representability). *)
Local Lemma DWTimesDW_FLX_FLT_from_node_equalities :
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
  F2Rp (DWTimesDW xh xl yh yl).
Proof.
move => H0 H1 H2 H3.
have Hfmul := DWTimesDW_mul_finite xh xl yh yl FIN.
have Nprod' : FT2R xh*FT2R yh<>0 ->
    bpow radix2 (emin+2*fprec t-1) <= Rabs (FT2R xh*FT2R yh)
  by auto.
rewrite /DWTimesDW.DWTimesDW12 DWTimesFP.TwoProdE.
rewrite (DWMulFP_relative_acc.Fast2Mult_correct_weak xh yh Hfmul Nprod').
rewrite /F2Rp /Fast2Mult_err /Fast2Mult_mul /Fast2Mult /fst /snd.
cbv zeta. rewrite H0 H1 H2 H3.
rewrite (FastTwoSumEq_FLT (Fast2Mult_mul xh yh)
  (BPLUS (Fast2Mult_err xh yh)
    (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) FIN).
reflexivity.
Qed.

Local Lemma DWTimesDW_FLX_FLT_exact_or_normal :
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
  F2Rp (DWTimesDW xh xl yh yl).
Proof.
move => E2 E3.
have Hftl0 := DWTimesDW_low_low_finite xh xl yh yl FIN.
have Hftl1 := DWTimesDW_first_correction_finite xh xl yh yl FIN.
have Hfcl2 := DWTimesDW_second_correction_finite xh xl yh yl FIN.
have Hfcl3 := DWTimesDW_correction_finite xh xl yh yl FIN.
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
exact (DWTimesDW_FLX_FLT_from_node_equalities H0 H1 H2' H3).
Qed.

Theorem DWTimesDW_FLX_FLT :
  DWTimesDW.DWTimesDW12 (fprec t) choice
    (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl)
    = F2Rp (DWTimesDW xh xl yh yl).
Proof.
have Hfmul := DWTimesDW_mul_finite xh xl yh yl FIN.
have Hftl0 := DWTimesDW_low_low_finite xh xl yh yl FIN.
have Hftl1 := DWTimesDW_first_correction_finite xh xl yh yl FIN.
have Hfcl2 := DWTimesDW_second_correction_finite xh xl yh yl FIN.
have Hfcl3 := DWTimesDW_correction_finite xh xl yh yl FIN.
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
rewrite (DWMulFP_relative_acc.Fast2Mult_correct_weak xh yh Hfmul Nprod').
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
   Section 3: finiteness of DWTimesDW from
   DWTimesDW_strong_precond.
     fst (DWTimesDW xh xl yh yl) = BPLUS ch cl3, where
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
Lemma round_FLT_abs_lt_half_emin_0 (x : R) :
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

(** Local to the binade half-ulp bound above the subnormal floor. *)
Lemma half_ulp_FLT_below_binade (x : R) (k : Z) :
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

Lemma round_FLT_error_below_binade (x : R) (k : Z) :
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
    for the underflow bridge: products entering the low word FMA are not
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



(** Every FLT rounding error splits into a normal relative component and one
    genuine underflow floor component.  Exactly one component is nonzero in
    the proof.  This decomposition is the interface used to replay the paper
    Algorithm 12 algebra while carrying denormal effects separately. *)
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

(** Normality propagates through the first low word FMA.  If [xl*yl] already
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

(** The same low product normality premise forces the opposite cross product
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

(** Consequently the third low word rounding argument is always on the FLT
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
    the complementary underflow in the low by low product branch. *)
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


(* --- Bounds specific to DW x DW for the extra products and FMAs --- *)

(* |xh*yl| and |xl*yh| are of order u relative to |xh*yh| (one low word each);
   |xl*yl| is of order u^2 (both low words).  Each stays well under Omega. *)
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
(* Basic quantities. *)
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
(* Finiteness of subterms. *)
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

(* Sharper error bound for each term: the relative term and the subnormal floor are a
   maximum, not a sum.  In the normal range ulp v = 2u|v| so the error is <= u|v| <= uc
   with no floor; in the subnormal range the error is <= 1/2 bpow emin and the
   relative term is smaller.  This lets aux_eta_bnd absorb the four 1/2 bpow emin
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
   the chain that absorbs the floor (aux_err_step2 gives each error as a maximum of relative
   term and subnormal floor, not a sum): magnitudes |tl0|<=2u^2P, |tl1|<=uP+4u^2P,
   |cl2|<=2uP+7u^2P (leading coeffs 1,2,3 on uP), each error e_i <= u*|arg_i| for
   i>=1 (floor absorbed) and e0<=u^2P.  Sum = 7 u^2 P + 13 u^3 P <= 15/2 u^2 P via
   u <= 1/32 (from 5 <= fprec t).  The floors are absorbed rather than added. *)
Lemma aux_eta_bnd (xh xl yh yl : ftype t) :
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
(* The same chain of argument magnitudes as in aux_cl3_le_ch. *)
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
(* Chain that absorbs the floor.  Each rounding error is bounded by a maximum (aux_err_step2),
   and each intermediate magnitude by |arg| + error (triangle); so the four
   1/2 bpow emin floors are absorbed into the u^2 P scale instead of added.  Leading
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

(* DWTimesDW_strong_precond bounds the real product by /2*Omega; since
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

(** A power-of-two endpoint is fixed by FLT rounding. *)
Local Lemma mul_round_abs_le_bpow (k : Z) (v : R) :
  (emin <= k)%Z ->
  Rabs v <= bpow radix2 k ->
  Rabs (round radix2 fexp (Znearest choice) v) <= bpow radix2 k.
Proof.
move => Hk Hv.
apply abs_round_le_generic.
- exact valid_fexp_inst.
- apply valid_rnd_N.
- apply Generic_fmt.generic_format_bpow.
  unfold fexp, SpecFloat.fexp. apply Z.max_lub.
  + pose proof (fprec_lb t). lia.
  + exact Hk.
- exact Hv.
Qed.

(** At the minimum legal precision, [5/8 E] is exactly the midpoint between
    [E/2] and [3E/4].  Ties-to-even selects [E/2]. *)
Local Lemma mul_round_p2_five_eighths_E :
  fprec t = 2%Z ->
  round radix2 fexp (Znearest choice)
    (5/8 * bpow radix2 (femax t - fprec t)) =
  /2 * bpow radix2 (femax t - fprec t).
Proof.
move => Hp.
have Hfm : (3 <= femax t)%Z by
  pose proof (fprec_lt_femax t); lia.
unfold round, scaled_mantissa, cexp, F2R; simpl.
have Hmag :
  (mag radix2 (5/8 * bpow radix2 (femax t - fprec t)) : Z) =
    (femax t - 2)%Z.
{ apply (mag_unique_pos radix2 _ (femax t - 2)). split.
  - rewrite Hp.
    replace (femax t - 2 - 1)%Z with (femax t - 3)%Z by lia.
    have Hsplit : bpow radix2 (femax t - 2) =
        bpow radix2 (femax t - 3) * bpow radix2 1.
    { rewrite -bpow_plus. f_equal; lia. }
    rewrite Hsplit. change (bpow radix2 1) with 2%R.
    have Hb := bpow_gt_0 radix2 (femax t - 3).
    change (bpow radix2 (femax t - 3) <=
      (5/8:R) * (bpow radix2 (femax t - 3) * 2)). nra.
  - rewrite Hp.
    have Hsplit : bpow radix2 (femax t - 2) =
        bpow radix2 (femax t - 3) * bpow radix2 1.
    { rewrite -bpow_plus. f_equal; lia. }
    rewrite Hsplit. change (bpow radix2 1) with 2%R.
    have Hb := bpow_gt_0 radix2 (femax t - 3).
    change ((5/8:R) * (bpow radix2 (femax t - 3) * 2) <
      bpow radix2 (femax t - 3) * 2). nra. }
rewrite Hmag /fexp /SpecFloat.fexp.
have Hmax :
  Z.max (femax t - 2 - fprec t)
        (SpecFloat.emin (fprec t) (femax t)) = (femax t - 4)%Z.
{ rewrite Hp /SpecFloat.emin.
  replace (femax t - 2 - 2)%Z with (femax t - 4)%Z by lia.
  apply Z.max_l. lia. }
rewrite Hmax Hp.
have Hscale :
  5 / 8 * bpow radix2 (femax t - 2) *
    bpow radix2 (-(femax t - 4)) = 5/2.
{ rewrite Rmult_assoc -bpow_plus.
  replace (femax t - 2 + - (femax t - 4))%Z with 2%Z by lia.
  change (bpow radix2 2) with 4%R. lra. }
rewrite Hscale.
have Hzn : Znearest choice (5/2) = 2%Z.
{ set (x := (5/2:R)).
  change (Znearest choice x = 2%Z).
  have Hf : Raux.Zfloor x = 2%Z.
  { apply Raux.Zfloor_imp. rewrite /x. simpl. lra. }
  unfold Znearest. fold x. rewrite Hf.
  have Hmid : x - IZR 2 = /2 by (rewrite /x; simpl; lra).
  rewrite Hmid Rcompare_Eq /choice /=.
  all: try reflexivity.
  all: simpl; lra. }
rewrite Hzn /=.
have Hrhs : /2 * bpow radix2 (femax t - 2) =
    IZR 2 * bpow radix2 (femax t - 4).
{ change (IZR 2) with 2%R.
  rewrite (_ : bpow radix2 (femax t - 2) =
      bpow radix2 (femax t - 4) * bpow radix2 2).
  - change (bpow radix2 2) with 4%R. lra.
  - rewrite -bpow_plus. f_equal; lia. }
symmetry; exact Hrhs.
Qed.

(** [3E/2] is an FLT number when [p=2]. *)
Local Lemma mul_three_halves_E_generic_p2 :
  fprec t = 2%Z ->
  generic_format radix2 fexp
    (3/2 * bpow radix2 (femax t - fprec t)).
Proof.
move => Hp.
apply generic_format_FLT.
eapply FLT_spec with
  (f := Float radix2 3 (femax t - fprec t - 1)).
- unfold F2R; simpl.
  rewrite (_ : bpow radix2 (femax t - fprec t) =
      bpow radix2 (femax t - fprec t - 1) * bpow radix2 1).
  + change (bpow radix2 1) with 2%R. lra.
  + rewrite -bpow_plus. f_equal; lia.
- change (3 < 2 ^ fprec t)%Z. rewrite Hp. reflexivity.
- change (SpecFloat.emin (fprec t) (femax t) <=
      femax t - fprec t - 1)%Z.
  unfold SpecFloat.emin. pose proof (fprec_lt_femax t). lia.
Qed.

(** The safe guard itself supplies enough overflow headroom at every legal
    precision.  For [p>=3] a direct absolute budget suffices.  At [p=2], the
    first correction uses the ties-to-even midpoint above; the remaining
    near-overflow branch uses the exact two-product reconstruction. *)
Lemma DWTimesDW_finite_post_cond_from_strong_precond (xh xl yh yl : ftype t) :
  DWTimesDW_strong_precond xh xl yh yl ->
  is_finite_p (DWTimesDW xh xl yh yl).
Proof.
intros (Hfxl & Hfyl & Hdwx & Hdwy & Hfmul & Hxhy).
have [Hfxh Hfyh] := BMULT_finite_e t xh yh Hfmul.
have Hp2lb := fprec_lb t.
have Hfm3 : (3 <= femax t)%Z by
  pose proof (fprec_lt_femax t); lia.
have HΩ : 0 < Omega by apply bpow_gt_0.
have HE0 : 0 < bpow radix2 (femax t - fprec t) by apply bpow_gt_0.
have HEq : bpow radix2 (femax t - fprec t) <= /4 * Omega
  by apply bpow_femax_fprec_le_quarter_Omega.
have Hbu : bpow radix2 (femax t - fprec t) =
    bpow radix2 (- fprec t) * Omega.
{ rewrite -bpow_plus. f_equal; lia. }
have Hu4 : bpow radix2 (- fprec t) <= /4.
{ have -> : (/4 = bpow radix2 (-2))%R by (simpl; lra).
  apply bpow_le; lia. }
have Hprod : Rabs (FT2R (BMULT xh yh)) <= /2 * Omega
  by (apply aux_round_half_bnd; [exact Hfmul | exact Hxhy]).
have Hfch : is_finite (Fast2Mult_mul xh yh) = true
  by (unfold Fast2Mult_mul, Fast2Mult, fst; exact Hfmul).
have Hch : Rabs (FT2R (Fast2Mult_mul xh yh)) <= /2 * Omega
  by (unfold Fast2Mult_mul, Fast2Mult, fst; exact Hprod).
have Hfcl1 : is_finite (Fast2Mult_err xh yh) = true.
{ destruct (Fast2Mult_finite_unconditional xh yh Hfmul) as [_ H]. exact H. }
have Hcl1u : Rabs (FT2R (Fast2Mult_err xh yh)) <=
    /2 * ulp (FT2R xh * FT2R yh)
  by (apply Fast2Mult_accuracy_norm; exact Hfmul).
have Hxhy_lt : Rabs (FT2R xh * FT2R yh) < Omega by lra.
have Hcl1 : Rabs (FT2R (Fast2Mult_err xh yh)) <=
    /2 * bpow radix2 (femax t - fprec t).
{ eapply Rle_trans; [exact Hcl1u|].
  apply Rmult_le_compat_l; [lra|].
  apply ulp_below_overflow; exact Hxhy_lt. }
(* The low-low product retains its second factor [u], unlike the older
   [E/2] estimate. *)
have Hxlylrel : Rabs (FT2R xl * FT2R yl) <=
    bpow radix2 (- fprec t) * bpow radix2 (- fprec t) *
      Rabs (FT2R xh * FT2R yh).
{ have Hxl := @dw_low_le_u_high t STD xh xl Hdwx.
  have Hyl := @dw_low_le_u_high t STD yh yl Hdwy.
  rewrite !Rabs_mult in Hxl, Hyl |- *.
  have Hxlp := Rabs_pos (FT2R xl).
  have Hylp := Rabs_pos (FT2R yl).
  have Hstep : Rabs (FT2R xl) * Rabs (FT2R yl) <=
      (bpow radix2 (- fprec t) * Rabs (FT2R xh)) *
      (bpow radix2 (- fprec t) * Rabs (FT2R yh))
    by (apply Rmult_le_compat; assumption).
  eapply Rle_trans; [exact Hstep|]. right; ring. }
have Hxlyl : Rabs (FT2R xl * FT2R yl) <=
    /8 * bpow radix2 (femax t - fprec t).
{ eapply Rle_trans; [exact Hxlylrel|].
  rewrite Hbu in Hxlylrel |- *.
  have Hu0 := bpow_ge_0 radix2 (- fprec t).
  have Hxy0 := Rabs_pos (FT2R xh * FT2R yh).
  nra. }
have HE8 : /8 * bpow radix2 (femax t - fprec t) =
    bpow radix2 (femax t - fprec t - 3).
{ have H : bpow radix2 (femax t - fprec t) =
      bpow radix2 (femax t - fprec t - 3) * bpow radix2 3.
  { rewrite -bpow_plus. f_equal; lia. }
  rewrite H. change (bpow radix2 3) with 8%R. lra. }
have Hk8 : (emin <= femax t - fprec t - 3)%Z.
{ unfold emin, common.emin, SpecFloat.emin. lia. }
have Hxlyl_lt : Rabs (FT2R xl * FT2R yl) < Omega by nra.
have Hftl0 : is_finite (BMULT xl yl) = true.
{ apply no_overflow_mult_is_finite => //.
  eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
  have Hu := ulp_below_overflow _ Hxlyl_lt. nra. }
have Htl0 : Rabs (FT2R (BMULT xl yl)) <=
    /8 * bpow radix2 (femax t - fprec t).
{ rewrite -BMULT_round_correct; [| exact Hftl0]. rewrite HE8.
  apply mul_round_abs_le_bpow; [exact Hk8|]. rewrite -HE8. exact Hxlyl. }
have Hxhyl : Rabs (FT2R xh * FT2R yl) <=
    /2 * bpow radix2 (femax t - fprec t)
  by (apply (aux_xhyl_bnd xh xl yh yl); assumption).
have Hxlyh : Rabs (FT2R xl * FT2R yh) <=
    /2 * bpow radix2 (femax t - fprec t)
  by (apply (aux_xlyh_bnd xh xl yh yl); assumption).
have Harg1 : Rabs (FT2R xh * FT2R yl + FT2R (BMULT xl yl)) <=
    5/8 * bpow radix2 (femax t - fprec t)
  by (eapply Rle_trans; [apply Rabs_triang|]; lra).
have Harg1_lt :
  Rabs (FT2R xh * FT2R yl + FT2R (BMULT xl yl)) < Omega by nra.
have Hftl1 : is_finite (BFMA xh yl (BMULT xl yl)) = true.
{ apply no_overflow_fma_is_finite => //.
  eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
  have Hu := ulp_below_overflow _ Harg1_lt. nra. }
destruct (Z.eq_dec (fprec t) 2) as [Hp2 | Hnp2].
- (* Minimum precision: exploit the even midpoint in the first FMA. *)
  have HEΩ : bpow radix2 (femax t - fprec t) = /4 * Omega.
  { rewrite Hbu Hp2. change (bpow radix2 (-2)) with (/4:R). reflexivity. }
  have Htl1 : Rabs (FT2R (BFMA xh yl (BMULT xl yl))) <=
      /2 * bpow radix2 (femax t - fprec t).
  { rewrite -BFMA_round_correct; [| exact Hftl1]. rewrite -round_NE_abs.
    eapply Rle_trans.
    - apply round_le; [exact valid_fexp_inst | apply valid_rnd_N | exact Harg1].
    - rewrite mul_round_p2_five_eighths_E; [lra | exact Hp2]. }
  have Harg2 :
    Rabs (FT2R xl * FT2R yh + FT2R (BFMA xh yl (BMULT xl yl))) <=
      bpow radix2 (femax t - fprec t)
    by (eapply Rle_trans; [apply Rabs_triang|]; lra).
  have Harg2_lt :
    Rabs (FT2R xl * FT2R yh + FT2R (BFMA xh yl (BMULT xl yl))) < Omega
    by nra.
  have Hfcl2 : is_finite (BFMA xl yh (BFMA xh yl (BMULT xl yl))) = true.
  { apply no_overflow_fma_is_finite => //.
    eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
    have Hu := ulp_below_overflow _ Harg2_lt. nra. }
  have Hcl2 :
    Rabs (FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) <=
      bpow radix2 (femax t - fprec t).
  { rewrite -BFMA_round_correct; [| exact Hfcl2].
    apply mul_round_abs_le_bpow.
    - unfold emin, common.emin, SpecFloat.emin. lia.
    - exact Harg2. }
  have Harg3 :
    Rabs (FT2R (Fast2Mult_err xh yh) +
      FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) <=
      3/2 * bpow radix2 (femax t - fprec t)
    by (eapply Rle_trans; [apply Rabs_triang|]; lra).
  have Harg3_lt :
    Rabs (FT2R (Fast2Mult_err xh yh) +
      FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) < Omega by nra.
  have Hfcl3 :
    is_finite (BPLUS (Fast2Mult_err xh yh)
      (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) = true.
  { apply (no_overflow_sum_is_finite t _ _ Hfcl1 Hfcl2).
    unfold Bplus_no_overflow.
    eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
    have Hu := ulp_below_overflow _ Harg3_lt. nra. }
  have Hcl3 :
    Rabs (FT2R (BPLUS (Fast2Mult_err xh yh)
      (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) <=
      3/2 * bpow radix2 (femax t - fprec t).
  { rewrite -BPLUS_round_correct; [| exact Hfcl3].
    apply abs_round_le_generic.
    - exact valid_fexp_inst.
    - apply valid_rnd_N.
    - apply mul_three_halves_E_generic_p2; exact Hp2.
    - exact Harg3. }
  set (a3 := FT2R (Fast2Mult_err xh yh) +
    FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))).
  have Hhalf3 : /2 * ulp a3 <=
      /4 * bpow radix2 (femax t - fprec t).
  { have Hk : (0 <= 2 * femax t - 4)%Z by lia.
    have Hb := half_ulp_FLT_below_binade a3 (2 * femax t - 4) Hk.
    have Hpow1 : bpow radix2 (emin + fprec t + (2 * femax t - 4)) =
        2 * bpow radix2 (femax t - fprec t).
    { unfold common.emin, SpecFloat.emin. rewrite Hp2.
      replace (3 - femax t - 2 + 2 + (2 * femax t - 4))%Z
        with (femax t - 1)%Z by lia.
      rewrite (_ : bpow radix2 (femax t - 1) =
        bpow radix2 (femax t - 2) * bpow radix2 1).
      - change (bpow radix2 1) with 2%R. lra.
      - rewrite -bpow_plus. f_equal; lia. }
    have Ha3 : Rabs a3 <
        bpow radix2 (emin + fprec t + (2 * femax t - 4)).
    { rewrite Hpow1. unfold a3 in *. nra. }
    specialize (Hb Ha3).
    have Hpow2 : /2 * bpow radix2 (emin + (2 * femax t - 4)) =
        /4 * bpow radix2 (femax t - fprec t).
    { unfold common.emin, SpecFloat.emin. rewrite Hp2.
      replace (3 - femax t - 2 + (2 * femax t - 4))%Z
        with (femax t - 3)%Z by lia.
      rewrite (_ : bpow radix2 (femax t - 3) =
        bpow radix2 (femax t - 2) * bpow radix2 (-1)).
      - change (bpow radix2 (-1)) with (/2:R). lra.
      - rewrite -bpow_plus. f_equal; lia. }
    rewrite Hpow2 in Hb. exact Hb. }
  have Hcl3err :
    Rabs (FT2R (BPLUS (Fast2Mult_err xh yh)
      (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) - a3) <=
      /4 * bpow radix2 (femax t - fprec t).
  { rewrite -BPLUS_round_correct; [| exact Hfcl3].
    fold a3.
    have Herr := @Ulp.error_le_half_ulp radix2 fexp
      valid_fexp_inst choice a3.
    eapply Rle_trans; [exact Herr|exact Hhalf3]. }
  have Hfst : is_finite (BPLUS (Fast2Mult_mul xh yh)
      (BPLUS (Fast2Mult_err xh yh)
        (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) = true.
  { apply (no_overflow_sum_is_finite t _ _ Hfch Hfcl3).
    unfold Bplus_no_overflow.
    destruct (Rle_dec
      (bpow radix2 (emin + 2 * fprec t - 1))
      (Rabs (FT2R xh * FT2R yh))) as [Hnormal | Hsmall].
    + have Huf : FT2R xh * FT2R yh <> 0 ->
          bpow radix2 (emin + 2 * fprec t - 1) <=
            Rabs (FT2R xh * FT2R yh) by (move => _; exact Hnormal).
      have Hex := Fast2MultModel_correct xh yh Hfmul Huf.
      have Hsum :
        Rabs (FT2R (Fast2Mult_mul xh yh) +
          FT2R (BPLUS (Fast2Mult_err xh yh)
            (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) <=
          Rabs (FT2R xh * FT2R yh) +
          bpow radix2 (femax t - fprec t) +
          /4 * bpow radix2 (femax t - fprec t).
      { have Hdecomp :
          FT2R (Fast2Mult_mul xh yh) +
            FT2R (BPLUS (Fast2Mult_err xh yh)
              (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) =
          (FT2R (Fast2Mult_mul xh yh) + FT2R (Fast2Mult_err xh yh)) +
            FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))) +
            (FT2R (BPLUS (Fast2Mult_err xh yh)
              (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) - a3)
          by (unfold a3; ring).
        rewrite Hdecomp Hex.
        replace (FT2R (Fast2Mult_mul xh yh) +
          (FT2R xh * FT2R yh - FT2R (Fast2Mult_mul xh yh)))
          with (FT2R xh * FT2R yh) by ring.
        have HA :
          Rabs (FT2R xh * FT2R yh +
            FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) <=
          Rabs (FT2R xh * FT2R yh) +
            bpow radix2 (femax t - fprec t).
        { eapply Rle_trans with (r2 :=
            Rabs (FT2R xh * FT2R yh) +
            Rabs (FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))).
          - apply Rabs_triang.
          - apply Rplus_le_compat; [apply Rle_refl | exact Hcl2]. }
        eapply Rle_trans; [apply Rabs_triang|].
        apply Rplus_le_compat; [exact HA | exact Hcl3err].
      }
      eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
      have Hsum_lt :
        Rabs (FT2R (Fast2Mult_mul xh yh) +
          FT2R (BPLUS (Fast2Mult_err xh yh)
            (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) < Omega
        by (rewrite HEΩ in Hsum; nra).
      have Hu := ulp_below_overflow _ Hsum_lt.
      rewrite HEΩ in Hu |- *. nra.
    + apply Rnot_le_lt in Hsmall.
      have HTfmt : generic_format radix2 fexp
          (bpow radix2 (emin + 2 * fprec t - 1)).
      { apply Generic_fmt.generic_format_bpow.
        unfold fexp, SpecFloat.fexp. apply Z.max_lub.
        - lia.
        - unfold common.emin, SpecFloat.emin. lia. }
      have Hchsmall : Rabs (FT2R (Fast2Mult_mul xh yh)) <=
          bpow radix2 (emin + 2 * fprec t - 1).
      { unfold Fast2Mult_mul, Fast2Mult, fst.
        rewrite -BMULT_round_correct; [| exact Hfmul].
        apply abs_round_le_generic; try assumption; try apply valid_rnd_N;
          try exact valid_fexp_inst.
        apply Rlt_le; exact Hsmall. }
      have HTq : bpow radix2 (emin + 2 * fprec t - 1) <= /4 * Omega.
      { rewrite Hp2 /emin /common.emin /SpecFloat.emin.
        have -> : (/4 * Omega = bpow radix2 (femax t - 2))%R.
        { rewrite (_ : Omega = bpow radix2 (femax t - 2) * bpow radix2 2).
          - change (bpow radix2 2) with 4%R. lra.
          - rewrite -bpow_plus. f_equal; lia. }
        apply bpow_le. lia. }
      eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
      have Hsum :
        Rabs (FT2R (Fast2Mult_mul xh yh) +
          FT2R (BPLUS (Fast2Mult_err xh yh)
            (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) <= 5/8 * Omega.
      { eapply Rle_trans; [apply Rabs_triang|]. rewrite HEΩ in Hcl3. nra. }
      have Hsum_lt :
        Rabs (FT2R (Fast2Mult_mul xh yh) +
          FT2R (BPLUS (Fast2Mult_err xh yh)
            (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) < Omega by lra.
      have Hu := ulp_below_overflow _ Hsum_lt.
      rewrite HEΩ in Hu |- *. nra. }
  split.
  + change (is_finite (BPLUS (Fast2Mult_mul xh yh)
      (BPLUS (Fast2Mult_err xh yh)
        (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) = true). exact Hfst.
  + set (aa := Fast2Mult_mul xh yh).
    set (bb := BPLUS (Fast2Mult_err xh yh)
      (BFMA xl yh (BFMA xh yl (BMULT xl yl)))).
    set (ss := BPLUS aa bb).
    set (zz := BMINUS ss aa).
    have HargS : Rabs (FT2R aa + FT2R bb) < Omega.
    { eapply Rle_lt_trans; [apply Rabs_triang|].
      have Hc := Hcl3. rewrite HEΩ in Hc.
      unfold aa, bb. nra. }
    have HerrS : Rabs (FT2R ss - (FT2R aa + FT2R bb)) <=
        /2 * bpow radix2 (femax t - fprec t).
    { unfold ss. rewrite -BPLUS_round_correct; [|unfold aa, bb; exact Hfst].
      eapply Rle_trans; [apply (@Ulp.error_le_half_ulp radix2 fexp
        valid_fexp_inst choice)|].
      apply Rmult_le_compat_l; [lra|]. apply ulp_below_overflow; exact HargS. }
    have HargZ : Rabs (FT2R ss - FT2R aa) <= /2 * Omega.
    { have Hid : FT2R ss - FT2R aa =
          FT2R bb + (FT2R ss - (FT2R aa + FT2R bb)) by ring.
      rewrite Hid. eapply Rle_trans; [apply Rabs_triang|].
      eapply Rle_trans with (r2 :=
        3/2 * bpow radix2 (femax t - fprec t) +
        /2 * bpow radix2 (femax t - fprec t)).
      - apply Rplus_le_compat.
        + unfold bb. exact Hcl3.
        + exact HerrS.
      - rewrite HEΩ. lra. }
    have HargZlt : Rabs (FT2R ss - FT2R aa) < Omega by lra.
    have Hfzz : is_finite zz = true.
    { unfold zz. apply no_overflow_minus_is_finite.
      - exact Hfst.
      - unfold aa. exact Hfch.
      - unfold Bminus_no_overflow.
        eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
        have Hu := ulp_below_overflow _ HargZlt. rewrite HEΩ in Hu. nra. }
    have HerrZ : Rabs (FT2R zz - (FT2R ss - FT2R aa)) <=
        /2 * bpow radix2 (femax t - fprec t).
    { unfold zz. rewrite -BMINUS_round_correct; [|exact Hfzz].
      eapply Rle_trans; [apply (@Ulp.error_le_half_ulp radix2 fexp
        valid_fexp_inst choice)|].
      apply Rmult_le_compat_l; [lra|]. apply ulp_below_overflow; exact HargZlt. }
    have Hlowarg : Rabs (FT2R bb - FT2R zz) <=
        bpow radix2 (femax t - fprec t).
    { have Hid : FT2R bb - FT2R zz =
          - ((FT2R ss - (FT2R aa + FT2R bb)) +
             (FT2R zz - (FT2R ss - FT2R aa))) by ring.
      rewrite Hid Rabs_Ropp. eapply Rle_trans; [apply Rabs_triang|]. lra. }
    change (is_finite (BMINUS bb zz) = true).
    apply no_overflow_minus_is_finite.
    * unfold bb. exact Hfcl3.
    * exact Hfzz.
    * unfold Bminus_no_overflow.
      have Hlowlt : Rabs (FT2R bb - FT2R zz) < Omega
        by (rewrite HEΩ in Hlowarg; lra).
      eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
      have Hu := ulp_below_overflow _ Hlowlt. rewrite HEΩ in Hu. nra.
- (* Every larger precision has enough direct absolute headroom. *)
  have Hp3 : (3 <= fprec t)%Z by lia.
  have HE8Ω : bpow radix2 (femax t - fprec t) <= /8 * Omega.
  { rewrite Hbu.
    have Hu8 : bpow radix2 (- fprec t) <= /8.
    { have -> : (/8 = bpow radix2 (-3))%R by (simpl; lra).
      apply bpow_le; lia. }
    have Hu0 := bpow_ge_0 radix2 (- fprec t). nra. }
  have Htl1 : Rabs (FT2R (BFMA xh yl (BMULT xl yl))) <=
      9/8 * bpow radix2 (femax t - fprec t).
  { rewrite -BFMA_round_correct; [| exact Hftl1].
    eapply Rle_trans; [apply round_abs_le_abs_plus_half_ulp|].
    have Hu := ulp_below_overflow _ Harg1_lt. lra. }
  have Harg2 :
    Rabs (FT2R xl * FT2R yh + FT2R (BFMA xh yl (BMULT xl yl))) <=
      13/8 * bpow radix2 (femax t - fprec t)
    by (eapply Rle_trans; [apply Rabs_triang|]; lra).
  have Harg2_lt :
    Rabs (FT2R xl * FT2R yh + FT2R (BFMA xh yl (BMULT xl yl))) < Omega
    by nra.
  have Hfcl2 : is_finite (BFMA xl yh (BFMA xh yl (BMULT xl yl))) = true.
  { apply no_overflow_fma_is_finite => //.
    eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
    have Hu := ulp_below_overflow _ Harg2_lt. nra. }
  have Hcl2 :
    Rabs (FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) <=
      17/8 * bpow radix2 (femax t - fprec t).
  { rewrite -BFMA_round_correct; [| exact Hfcl2].
    eapply Rle_trans; [apply round_abs_le_abs_plus_half_ulp|].
    have Hu := ulp_below_overflow _ Harg2_lt. lra. }
  have Harg3 :
    Rabs (FT2R (Fast2Mult_err xh yh) +
      FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) <=
      21/8 * bpow radix2 (femax t - fprec t)
    by (eapply Rle_trans; [apply Rabs_triang|]; lra).
  have Harg3_lt :
    Rabs (FT2R (Fast2Mult_err xh yh) +
      FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) < Omega by nra.
  have Hfcl3 : is_finite (BPLUS (Fast2Mult_err xh yh)
      (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) = true.
  { apply (no_overflow_sum_is_finite t _ _ Hfcl1 Hfcl2).
    unfold Bplus_no_overflow.
    eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
    have Hu := ulp_below_overflow _ Harg3_lt. nra. }
  have Hcl3 : Rabs (FT2R (BPLUS (Fast2Mult_err xh yh)
      (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) <=
      25/8 * bpow radix2 (femax t - fprec t).
  { rewrite -BPLUS_round_correct; [| exact Hfcl3].
    eapply Rle_trans; [apply round_abs_le_abs_plus_half_ulp|].
    have Hu := ulp_below_overflow _ Harg3_lt. lra. }
  have Hfst : is_finite (BPLUS (Fast2Mult_mul xh yh)
      (BPLUS (Fast2Mult_err xh yh)
        (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) = true.
  { apply (no_overflow_sum_is_finite t _ _ Hfch Hfcl3).
    unfold Bplus_no_overflow.
    eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
    have Hsum :
      Rabs (FT2R (Fast2Mult_mul xh yh) +
        FT2R (BPLUS (Fast2Mult_err xh yh)
          (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) <=
        /2 * Omega + 25/8 * bpow radix2 (femax t - fprec t)
      by (eapply Rle_trans; [apply Rabs_triang|]; lra).
    have Hsum_lt :
      Rabs (FT2R (Fast2Mult_mul xh yh) +
        FT2R (BPLUS (Fast2Mult_err xh yh)
          (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) < Omega by nra.
    have Hu := ulp_below_overflow _ Hsum_lt. nra. }
  split.
  + change (is_finite (BPLUS (Fast2Mult_mul xh yh)
      (BPLUS (Fast2Mult_err xh yh)
        (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) = true). exact Hfst.
  + set (aa := Fast2Mult_mul xh yh).
    set (bb := BPLUS (Fast2Mult_err xh yh)
      (BFMA xl yh (BFMA xh yl (BMULT xl yl)))).
    set (ss := BPLUS aa bb).
    set (zz := BMINUS ss aa).
    have HargS : Rabs (FT2R aa + FT2R bb) < Omega.
    { eapply Rle_lt_trans; [apply Rabs_triang|].
      unfold aa, bb. nra. }
    have HerrS : Rabs (FT2R ss - (FT2R aa + FT2R bb)) <=
        /2 * bpow radix2 (femax t - fprec t).
    { unfold ss. rewrite -BPLUS_round_correct; [|unfold aa, bb; exact Hfst].
      eapply Rle_trans; [apply (@Ulp.error_le_half_ulp radix2 fexp
        valid_fexp_inst choice)|].
      apply Rmult_le_compat_l; [lra|]. apply ulp_below_overflow; exact HargS. }
    have HargZ : Rabs (FT2R ss - FT2R aa) <=
        29/8 * bpow radix2 (femax t - fprec t).
    { have Hid : FT2R ss - FT2R aa =
          FT2R bb + (FT2R ss - (FT2R aa + FT2R bb)) by ring.
      rewrite Hid. eapply Rle_trans; [apply Rabs_triang|].
      eapply Rle_trans with (r2 :=
        25/8 * bpow radix2 (femax t - fprec t) +
        /2 * bpow radix2 (femax t - fprec t)).
      - apply Rplus_le_compat.
        + unfold bb. exact Hcl3.
        + exact HerrS.
      - lra. }
    have HargZlt : Rabs (FT2R ss - FT2R aa) < Omega by nra.
    have Hfzz : is_finite zz = true.
    { unfold zz. apply no_overflow_minus_is_finite.
      - exact Hfst.
      - unfold aa. exact Hfch.
      - unfold Bminus_no_overflow.
        eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
        have Hu := ulp_below_overflow _ HargZlt. nra. }
    have HerrZ : Rabs (FT2R zz - (FT2R ss - FT2R aa)) <=
        /2 * bpow radix2 (femax t - fprec t).
    { unfold zz. rewrite -BMINUS_round_correct; [|exact Hfzz].
      eapply Rle_trans; [apply (@Ulp.error_le_half_ulp radix2 fexp
        valid_fexp_inst choice)|].
      apply Rmult_le_compat_l; [lra|]. apply ulp_below_overflow; exact HargZlt. }
    have Hlowarg : Rabs (FT2R bb - FT2R zz) <=
        bpow radix2 (femax t - fprec t).
    { have Hid : FT2R bb - FT2R zz =
          - ((FT2R ss - (FT2R aa + FT2R bb)) +
             (FT2R zz - (FT2R ss - FT2R aa))) by ring.
      rewrite Hid Rabs_Ropp. eapply Rle_trans; [apply Rabs_triang|]. lra. }
    change (is_finite (BMINUS bb zz) = true).
    apply no_overflow_minus_is_finite.
    * unfold bb. exact Hfcl3.
    * exact Hfzz.
    * unfold Bminus_no_overflow.
      have Hlowlt : Rabs (FT2R bb - FT2R zz) < Omega by nra.
      eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
      have Hu := ulp_below_overflow _ Hlowlt. nra.
Qed.

(* Closing Fast2Sum validity from its two primitive obligations. *)
Lemma DWTimesDW_double_word_from_pre (xh xl yh yl : ftype t) :
  is_finite (BPLUS (Fast2Mult_mul xh yh)
                   (BPLUS (Fast2Mult_err xh yh)
                          (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) = true ->
  Rabs (FT2R (BPLUS (Fast2Mult_err xh yh)
                    (BFMA xl yh (BFMA xh yl (BMULT xl yl)))))
    <= Rabs (FT2R (Fast2Mult_mul xh yh)) ->
  double_word (fst (DWTimesDW xh xl yh yl)) (snd (DWTimesDW xh xl yh yl)).
Proof.
move => Hfp Hord.
exact (Fast2Sum_is_DW (Fast2Mult_mul xh yh)
         (BPLUS (Fast2Mult_err xh yh)
                (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) Hfp Hord).
Qed.

End DWTimesDW_Finite.


(** Error identities and rounding bounds shared by the normal range relative
    proof and the whole range mixed proof. *)
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

Let zh := FT2R (fst (DWTimesDW xh xl yh yl)).
Let zl := FT2R (snd (DWTimesDW xh xl yh yl)).
Let xr := (FT2R xh + FT2R xl).
Let yr := (FT2R yh + FT2R yl).

Definition relative_error_DWTimesDW : R :=
  Rabs (((zh + zl) - xr * yr) / (xr * yr)).

(** Above the [9/8] boundary band, half a physical ulp is less than
    [8/9*u^2] of the leading product.  This is the quantitative margin that
    keeps the floored normal rounds on the paper proof's midpoint side. *)
Lemma low0_half_floor_budget_above_nine_eighths (P : R) :
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

Lemma round_abs_le_four_u_with_easy_margin (a : R) :
  (5 <= fprec t)%Z -> Rabs a <= 4*u+23/9*u^2 ->
  Rabs (round radix2 (FLX_exp (fprec t)) (Znearest choice) a) <= 4*u.
Proof.
move => Hp5 Ha.
rewrite -(@Bayleyaux.rnd_p_abs (fprec t) ltac:(lia) choice choiceP a).
rewrite -(round_four_u_plus_easy_margin Hp5).
apply round_le; [apply FLX_exp_valid, fprec_gt_0|apply valid_rnd_N|exact Ha].
Qed.

Lemma round_error_le_2u2_below_four_u (a : R) :
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

Lemma round_error_le_3u2_with_easy_margin (a : R) :
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

Lemma round_error_le_u2_with_low0_margin (a : R) :
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

(** First floored node of the normalized Algorithm 12 replay.  Despite the
    low word floor, [tl1] retains both of the paper proof's sharp facts:
    output magnitude at most [2u] and rounding error at most [u^2]. *)
Lemma low0_tl1_sharp
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
    the low floor contribution.  Its [16/9*u^2] normalized maximum is below
    the [2*u^2] midpoint at [3u], so [cl2] remains bounded by [3u]. *)
Lemma low0_cl2_sharp
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
Lemma low0_cl3_sharp (cl1 cl2 : R) :
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

(* Key identity, analogous to FP relerr_error_eq: the whole double-word error is the
   sum of the four FLT rounding errors e0..e3.  Fast2Sum is exact (aux_cl3_le_ch),
   the product error cl1 is representable (Fast2MultModel_correct), and each
   intermediate is round(arg); the identity then telescopes by [ring].  This is
   the FLT form of the identity used in [DWTimesDW12_correct]. *)
Lemma relerr_error_eq :
  (3 <= fprec t)%Z ->
  double_word_prop xh xl ->
  double_word_prop yh yl ->
  is_finite_p (DWTimesDW xh xl yh yl) ->
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
  have Hfst_eq : fst (DWTimesDW xh xl yh yl) = Fast2Sum_sum ch cl3 by reflexivity.
  have Hsnd_eq : snd (DWTimesDW xh xl yh yl) = Fast2Sum_err ch cl3 by reflexivity.
  rewrite Hfst_eq Hsnd_eq Hexact. ring. }
rewrite Hsum Hch_eq. unfold xr, yr, cl3, cl2. ring.
Qed.

(** Mixed error form of [relerr_error_eq].  The four Algorithm 12 rounding
    errors are decomposed into the relative pieces consumed by the paper's
    normal proof and four explicit floor pieces.  No triangle inequality is
    taken here, so the correlations used by the paper analysis remain
    available. *)
Lemma relerr_error_relative_floor_decomposition :
  (3 <= fprec t)%Z ->
  double_word_prop xh xl ->
  double_word_prop yh yl ->
  is_finite_p (DWTimesDW xh xl yh yl) ->
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
have F0 := DWTimesDW_low_low_finite xh xl yh yl FIN.
have F1 := DWTimesDW_first_correction_finite xh xl yh yl FIN.
have F2 := DWTimesDW_second_correction_finite xh xl yh yl FIN.
have F3 := DWTimesDW_correction_finite xh xl yh yl FIN.
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

(* ===== Far underflow in the low by low product analysis ===== *)

Section RelativeAccuracyDWTimesDW.
Context {NANS: Nans} {t : type} {STD: is_standard t}.
Notation u := (bpow Zaux.radix2 (- fprec t)).
Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Notation eminA := (SpecFloat.emin (fprec t) (femax t)).
Notation ulp := (Ulp.ulp Zaux.radix2 fexp).
Notation OmegaA := (bpow Zaux.radix2 (femax t)).
Local Instance valid_fexp_inst_dh : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.
Variables (xh xl yh yl : ftype t).
Let zh := FT2R (fst (DWTimesDW xh xl yh yl)).
Let zl := FT2R (snd (DWTimesDW xh xl yh yl)).
Let xr := (FT2R xh + FT2R xl).
Let yr := (FT2R yh + FT2R yl).


(** Sharp normal range core.  Normality of the leading and low by low products
    propagates enough exact or normal structure through the remaining nodes
    to recover the paper's [4u^2] relative bound. *)
Lemma DWTimesDW_relative_accuracy_core :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  bpow radix2 (eminA + 2 * fprec t - 1) <=
    Rabs (FT2R xh * FT2R yh) ->
  bpow radix2 (eminA + fprec t - 1) <=
    Rabs (FT2R xl * FT2R yl) ->
  relative_error_DWTimesDW xh xl yh yl <= 4 * u ^ 2.
Proof.
move => Hdw Hdwy Hfin Hp5 Nprod N0.
have Hfmul : is_finite (BMULT xh yh)=true
  by exact (DWTimesDW_mul_finite xh xl yh yl Hfin).
have Hftl0 : is_finite (BMULT xl yl)=true
  by exact (DWTimesDW_low_low_finite xh xl yh yl Hfin).
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
have Hbridge := DWTimesDW_FLX_FLT_exact_or_normal
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

(** Public pure relative result for the normal range. *)
Theorem DWTimesDW_relative_accuracy :
  (5 <= fprec t)%Z ->
  DWTimesDW_relative_precond xh xl yh yl ->
  relative_error_DWTimesDW xh xl yh yl <= 4 * u ^ 2.
Proof.
move => Hp5 [Hsafe [Nprod N0]].
have Hfin := DWTimesDW_finite_post_cond_from_strong_precond xh xl yh yl Hsafe.
move: Hsafe => [_ [_ [DWx [DWy _]]]].
exact (DWTimesDW_relative_accuracy_core
  DWx DWy Hfin Hp5 Nprod N0).
Qed.

End RelativeAccuracyDWTimesDW.
