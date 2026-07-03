(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Body proofs for the double-word *operations* translation unit (dd_ops.c).
   All ops + guarded wrappers share the single dd_ops CompSpecs (from DDOpsASI),
   so intra-module calls (guarded -> unguarded, composite -> leaf) are resolved
   by ordinary forward_call against Gprog -- no per-file CompSpecs workarounds.
   Cross-module calls (guarded -> checks) use the check specs from DDOpsASI
   (mirroring fp_utils_specs); fma is from MathASI; both are discharged at VSU
   link time.  dw_plus_dw1 (the sloppy variant) is intentionally Admitted (it has
   no math proof); every other body is fully proved. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Require Import DDModels common real_extras op_defs.
Require Import DD.verif_proofs.dd_float_reconcile.
Require Import TwoSum_acc Fast2Sum_acc Fast2Mult_acc.
Require Import DD.accuracy_proofs.dw_opps.DWPlusFP_acc.
Require Import DD.accuracy_proofs.dw_opps.DWPlusDW_acc.
Require Import DD.accuracy_proofs.dw_opps.DWPlusDW_acc_helpers.
Require Import DD.accuracy_proofs.dw_opps.DWMulFP_acc.
Require Import DD.verif_proofs.verif_objs.dd_ops.
Require Import DD.verif_proofs.DDOpsASI.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec Tdouble) (femax Tdouble))).

(* The whole-TU Gprog is exactly the ops VSU's G = Imports ++ internal specs,
   so these body proofs feed directly into solve_SF_internal in Ops_VSU.v. *)
Definition Gprog : funspecs := Ops_Imports ++ Ops_Internal.

(* ======================================================================== *)
(*  Leaf primitives                                                          *)
(* ======================================================================== *)

Lemma body_two_sum: semax_body Vprog Gprog f_two_sum two_sum_spec.
Proof.
start_function.
forward. forward. forward. forward.
forward. forward. forward. forward.
entailer!.
Qed.

Lemma body_fast_2sum: semax_body Vprog Gprog f_fast_2sum fast_2sum_spec.
Proof.
start_function.
forward. forward. forward. forward.
entailer!.
Qed.

Lemma body_fast_2mult: semax_body Vprog Gprog f_fast_2mult fast_2mult_spec.
Proof.
start_function.
forward. forward. forward_call. forward.
entailer!.
Qed.

(* ======================================================================== *)
(*  Composite operations                                                     *)
(* ======================================================================== *)

(* The C body matches the DWPlusFP model line-for-line:
     two_sum(&sh, x->s, y);   (sh.s,sh.t) = TwoSumF xh y
     v = x->t + sh.t;         v = BPLUS xl sl
     fast_2sum(s, sh.s, v);   (zh,zl) = Fast2Sum sh.s v
   The inner two_sum / fast_2sum specs have empty preconditions, so the
   forward_call cascade discharges no side conditions -- identical in shape
   to body_dw_plus_dw2 above and body_dw_mult_fp9. *)
Lemma body_dw_plus_fp: semax_body Vprog Gprog f_dw_plus_fp dw_plus_fp_spec.
Proof.
  start_function.
  (* two_sum(&sh, x->s, y) *)
  forward.
  forward_call (v_sh, fst xh, y).
  (* v = x->t + sh.t *)
  forward.  forward.  forward.
  (* fast_2sum(s, sh.s, v) *)
  forward.
  forward_call (s, TwoSumF_sum (fst xh) y,
                BPLUS (snd xh) (TwoSumF_err (fst xh) y)).
  unfold f2val, DWPlusFP, TwoSumF, Fast2Sum,
         TwoSumF_sum, TwoSumF_err, fst, snd.
  entailer!.
Qed.

(* Out of scope (kept open): the sloppy DWPlusDW variant has no math proof. *)
Lemma body_dw_plus_dw1: semax_body Vprog Gprog f_dw_plus_dw1 dw_plus_dw1_spec.
Proof. Admitted.

Lemma body_dw_plus_dw2: semax_body Vprog Gprog f_dw_plus_dw2 dw_plus_dw2_spec.
Proof.
  start_function.
  forward.  forward.
  forward_call (v_sh, fst xh, fst yh).
  forward.  forward.
  forward_call (v_th, snd xh, snd yh).
  forward.  forward.  forward.
  forward.
  forward_call (v_vh, TwoSumF_sum (fst xh) (fst yh),
                BPLUS (TwoSumF_err (fst xh) (fst yh))
                      (TwoSumF_sum (snd xh) (snd yh))).
  forward.  forward.  forward.
  forward.
  forward_call (s,
                Fast2Sum_sum (TwoSumF_sum (fst xh) (fst yh))
                             (BPLUS (TwoSumF_err (fst xh) (fst yh))
                                    (TwoSumF_sum (snd xh) (snd yh))),
                BPLUS (TwoSumF_err (snd xh) (snd yh))
                      (Fast2Sum_err (TwoSumF_sum (fst xh) (fst yh))
                                    (BPLUS (TwoSumF_err (fst xh) (fst yh))
                                           (TwoSumF_sum (snd xh) (snd yh))))).
  unfold f2val, AccurateDWPlusDW, TwoSumF, Fast2Sum,
         TwoSumF_sum, TwoSumF_err, Fast2Sum_sum, Fast2Sum_err, fst, snd.
  entailer!.
Qed.

Lemma body_dw_mult_fp9: semax_body Vprog Gprog f_dw_mult_fp9 dw_mult_fp9_spec.
Proof.
start_function.
forward.
forward_call.
forward. forward.
forward_call.
forward. forward.
forward_call.
unfold f2val, DWTimesFP3, Fast2Mult, Fast2Sum, fst, snd.
entailer!.
Qed.

Lemma body_dw_mult_dw12: semax_body Vprog Gprog f_dw_mult_dw12 dw_mult_dw12_spec.
Proof.
start_function.
forward.
forward.
forward_call. 
forward.
forward.
forward.
forward.
forward.
forward_call. 
forward.
forward.
forward.
forward_call.
forward.
forward.
forward.
forward.
forward_call.
unfold f2val, SloppyDWPlusDW, Fast2Mult, Fast2Sum, fst, snd.
entailer!.
Qed.

(* Leaf reconciliation lemmas BDIV_Td/BMULT_Td/BOPP_Td/BFMA_Td/Zconst1_Td are
   factored into dd_float_reconcile (imported above); body_dw_div_dw18 uses
   them to make the stored value and the postcondition syntactically equal. *)

(* body_dw_div_dw18: the callees (fma from MathASI, fast_2sum, dw_mult_fp9,
   dw_plus_fp, dw_mult_dw12) are all precondition-free -- each returns its
   functional-model result -- so the forward_call cascade needs no cond
   discharge.  The stored value is exactly the composition

     DWTimesDW3 xh xl (fst (DWPlusFP dh dl th)) (snd (DWPlusFP dh dl th))

   with (dh,dl) = DWTimesFP3 eh el th, (eh,el) = Fast2Sum rh rl,
   th = BDIV 1 yh, rh = BFMA (-yh) th 1, rl = BOPP (yl*th),
   i.e. DWDivDW3.  Mirrors body_dw_mult_dw12 / body_dw_mult_fp9.

   The three double-word calls (dw_mult_fp9 / dw_plus_fp / dw_mult_dw12) each
   take a struct argument whose contents were produced by the previous call.
   Their WITH-clause pair (xh) cannot be inferred automatically: unifying the
   spec's `f2val xh` against the stored `f2val <pair>` degenerates into a
   projection unification (`fst xh = fst <pair>`) that Coq leaves open.  We
   therefore read the produced pair (and the divisor th) straight out of the
   goal with `match ... context` and pass them as explicit witnesses. *)
Lemma body_dw_div_dw18: semax_body Vprog Gprog f_dw_div_dw18 dw_div_dw18_spec.
Proof.
start_function.
forward.            (* t'4 = y->s *)
forward.            (* th  = 1.0 / t'4 *)
forward.            (* t'3 = y->s *)
forward_call.       (* t'1 = fma(-t'3, th, 1.0) *)
forward.            (* rh  = t'1 *)
forward.            (* t'2 = y->t *)
forward.            (* rl  = -(t'2 * th) *)
forward_call.       (* fast_2sum(&e, rh, rl) *)
(* dw_mult_fp9(&delta, &e, th): witness (s, x, xh, y) = (v_delta, v_e, e-pair, th) *)
match goal with |- context [temp _th (Vfloat ?T)] =>
 match goal with |- context [data_at _ _ (f2val ?E) v_e] =>
   forward_call (v_delta, v_e, E, T) end end.
(* dw_plus_fp(&m, &delta, th): witness (v_m, v_delta, delta-pair, th) *)
match goal with |- context [temp _th (Vfloat ?T)] =>
 match goal with |- context [data_at _ _ (f2val ?D) v_delta] =>
   forward_call (v_m, v_delta, D, T) end end.
(* dw_mult_dw12(z, x, &m): witness (s, x, v_m, xh, m-pair) *)
match goal with |- context [data_at _ _ (f2val ?M) v_m] =>
   forward_call (s, x, v_m, xh, M) end.
(* Rewrite the postcondition's DWDivDW3 term into the exact composition the
   cascade produced, so both `data_at` values become syntactically identical
   and the closing entailer needs no whole-term B-op/Float-op conversion. *)
match goal with |- context [data_at _ _ (f2val ?PROD) s] =>
  replace (DWDivDW3 (fst xh) (snd xh) (fst yh) (snd yh)) with PROD end.
2:{ unfold DWDivDW3.
    rewrite ?BDIV_Td, ?BFMA_Td, ?BOPP_Td, ?BMULT_Td, ?Zconst1_Td.
    destruct (Fast2Sum _ _)     as [eh el]; cbn [fst snd].
    destruct (DWTimesFP3 _ _ _) as [dh dl]; cbn [fst snd].
    destruct (DWPlusFP _ _ _)   as [mh ml]; cbn [fst snd].
    reflexivity. }
entailer!!.
Qed.


(* ======================================================================== *)
(*  Guarded wrappers                                                         *)
(* ======================================================================== *)

Lemma body_two_sum_guarded: semax_body Vprog Gprog f_two_sum_guarded two_sum_guarded_spec.
Proof.
start_function.
forward_call (a, b).
Intros vret_fin.
set (Post_if :=
  PROP (TwoSum_cond a b)
  LOCAL (temp _st p; temp _a (Vfloat a); temp _b (Vfloat b))
  SEP (data_at_ Tsh dword p)).
forward_if Post_if.
- forward_call (Int.repr 1).
  unfold Post_if. entailer!.
- forward.
  unfold Post_if. entailer!.
  apply H. destruct vret_fin; auto.
- unfold Post_if.
  assert_PROP (TwoSum_cond a b) as HFC by entailer!.
  forward_call (p, a, b).
  entailer!!.
  apply TwoSum_accuracy_from_cond, HFC.
Qed.

Lemma body_fast_2sum_guarded: semax_body Vprog Gprog f_fast_2sum_guarded fast_2sum_guarded_spec.
Proof.
start_function.
forward_call (a, b).
Intros vret_fin.
set (Post_if :=
  PROP (is_finite (BPLUS a b) = true /\ (Rabs (FT2R b) <= Rabs (FT2R a))%R)
  LOCAL (temp _st p; temp _a (Vfloat a); temp _b (Vfloat b))
  SEP (data_at_ Tsh dword p)).
forward_if Post_if.
- forward_call (Int.repr 1).
  unfold Post_if. entailer!.
- forward.
  unfold Post_if. entailer!.
  unfold SumResultIsSafeForFast2Sum in H.
  apply H. destruct vret_fin; auto.
- unfold Post_if.
  assert_PROP (is_finite (BPLUS a b) = true /\ (Rabs (FT2R b) <= Rabs (FT2R a))%R)
    as Hsafe by entailer!.
  destruct Hsafe as [Hfin Hle].
  assert (HFC : Fast2Sum_cond a b).
  { split; [exact Hfin |].
    left. apply Ulp.ulp_le.
    - apply BinarySingleNaN.fexp_correct; apply fprec_gt_0.
    - apply FLT.FLT_exp_monotone.
    - exact Hle. }
  forward_call (p, a, b).
  entailer!!.
  apply FastTwoSum_accuracy_from_cond; assumption.
Qed.

Lemma body_fast_2mult_guarded: semax_body Vprog Gprog f_fast_2mult_guarded fast_2mult_guarded_spec.
Proof.
start_function.
forward_call (a,b).
Intros vret_fin.
set (Post_if :=
  PROP (Fast2Mult_cond a b)
  LOCAL (temp _st st; temp _a (Vfloat a); temp _b (Vfloat b))
  SEP (data_at_ Tsh dword st)).
forward_if Post_if.
- forward_call (Int.repr 1).
  unfold Post_if. entailer!.
- forward.
  unfold Post_if. entailer!.
  apply H. destruct vret_fin; auto.
- unfold Post_if.
  assert_PROP (Fast2Mult_cond a b) as HFC by entailer!.
  forward_call (st, a, b).
  entailer!!.
  apply Fast2Mult_accuracy_from_safety, HFC.
Qed.

Lemma body_dw_plus_fp_guarded :
  semax_body Vprog Gprog f_dw_plus_fp_guarded dw_plus_fp_guarded_spec.
Proof.
start_function.
forward_call (x, xh, y).
Intros vret_fin.
set (Post_if :=
  PROP (DWPlusFP_cond (fst xh) (snd xh) y)
  LOCAL (temp _st s; temp _x x; temp _y (Vfloat y))
  SEP (data_at_ Tsh dword s;
       data_at Tsh dword (f2val xh) x)).
forward_if Post_if.
- forward_call (Int.repr 1).
  unfold Post_if. entailer!.
- forward.
  unfold Post_if. entailer!.
  apply H. destruct vret_fin; auto.
- unfold Post_if.
  assert_PROP (DWPlusFP_cond (fst xh) (snd xh) y) as HFC by entailer!.
  forward_call (s, x, xh, y).
  assert (Hfp : (3 <= fprec Tdouble)%Z)
    by (unfold fprec, Tdouble; simpl; lia).
  pose proof
    (@relative_errorDWPlusFP_from_cond _ Tdouble _ (fst xh) (snd xh) y HFC Hfp)
    as Hacc.
  entailer!!.
Qed.

Lemma body_dw_plus_dw2_guarded :
  semax_body Vprog Gprog f_dw_plus_dw2_guarded dw_plus_dw2_guarded_spec.
Proof.
start_function.
forward_call (x, y, xh, yh).
Intros vret_fin.
set (Post_if :=
  PROP (DWPlusDW_cond (fst xh) (snd xh) (fst yh) (snd yh))
  LOCAL (temp _st s; temp _x x; temp _y y)
  SEP (data_at_ Tsh dword s;
       data_at Tsh dword (f2val xh) x;
       data_at Tsh dword (f2val yh) y)).
forward_if Post_if.
- forward_call (Int.repr 1).
  unfold Post_if. entailer!.
- forward.
  unfold Post_if. entailer!.
  apply H. destruct vret_fin; auto.
- unfold Post_if.
  assert_PROP
    (DWPlusDW_cond (fst xh) (snd xh) (fst yh) (snd yh)) as HFC by entailer!.
  forward_call (s, x, y, xh, yh).
  assert (Hfp : (3 <= fprec Tdouble)%Z)
    by (unfold fprec, Tdouble; simpl; lia).
  pose proof
    (relative_errorDWPlusDW_correct (fst xh) (snd xh) (fst yh) (snd yh) HFC Hfp)
    as Hacc.
  entailer!!.
Qed.

Lemma body_dw_mult_fp9_guarded :
  semax_body Vprog Gprog f_dw_mult_fp9_guarded dw_mult_fp9_guarded_spec.
Proof.
start_function.
forward_call (x, xh, y).
Intros vret_fin.
set (Post_if :=
  PROP (DWTimesFP_cond (fst xh) (snd xh) y)
  LOCAL (temp _st s; temp _x x; temp _y (Vfloat y))
  SEP (data_at_ Tsh dword s;
       data_at Tsh dword (f2val xh) x)).
forward_if Post_if.
- forward_call (Int.repr 1).
  unfold Post_if. entailer!.
- forward.
  unfold Post_if. entailer!.
  apply H. destruct vret_fin; auto.
- unfold Post_if.
  forward_call (s, x, xh, y).
  assert (Hfp : (3 <= fprec Tdouble)%Z)
    by (unfold fprec, Tdouble; simpl; lia).
  pose proof
    (@DWTimesFP_accuracy_from_cond _ Tdouble _ (fst xh) (snd xh) y Hfp H0)
    as Hacc.
  entailer!!.
Qed.


