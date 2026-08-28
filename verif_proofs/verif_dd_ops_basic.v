(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Body proofs for the basic blocks and their guarded wrappers in dd_ops.c. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Require Import DDConds common real_extras op_defs.
Require Import TwoSum_acc Fast2Sum_acc Fast2Mult_acc.
Require Import DD.verif_proofs.verif_objs.dd_ops.
Require Import DD.verif_proofs.DDOpsASI.
Require Import DD.verif_proofs.verif_dd_ops_common.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

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

Lemma body_two_sum_guarded: semax_body Vprog Gprog f_two_sum_guarded two_sum_guarded_spec.
Proof.
start_function.
forward_call (a, b).
Intros vret_fin.
set (Post_if :=
  PROP (TwoSum_exact_cond a b)
  LOCAL (temp _st p; temp _a (Vfloat a); temp _b (Vfloat b))
  SEP (data_at_ Tsh dword p)).
forward_if Post_if.
- forward_call (Int.repr 1).
  unfold Post_if. entailer!.
- forward.
  unfold Post_if. entailer!.
  apply H. destruct vret_fin; auto.
- unfold Post_if.
  assert_PROP (TwoSum_exact_cond a b) as HFC by entailer!.
  forward_call (p, a, b).
  entailer!!.
  apply TwoSum_exact_guarantee_from_cond, HFC.
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
  unfold fp_utils_specs.SumResultIsSafeForFast2Sum in H.
  apply H. destruct vret_fin; auto.
- unfold Post_if.
  assert_PROP (is_finite (BPLUS a b) = true /\ (Rabs (FT2R b) <= Rabs (FT2R a))%R)
    as Hsafe by entailer!.
  destruct Hsafe as [Hfin Hle].
  assert (HFC : Fast2Sum_exact_cond a b).
  { split; [exact Hfin |].
    left. apply Ulp.ulp_le.
    - apply BinarySingleNaN.fexp_correct; apply fprec_gt_0.
    - apply FLT.FLT_exp_monotone.
    - exact Hle. }
  forward_call (p, a, b).
  entailer!!.
  apply Fast2Sum_exact_guarantee_from_magnitude_order; assumption.
Qed.

Lemma body_fast_2mult_guarded: semax_body Vprog Gprog f_fast_2mult_guarded fast_2mult_guarded_spec.
Proof.
start_function.
forward_call (a,b).
Intros vret_fin.
set (Post_if :=
  PROP (Fast2Mult_exact_cond a b)
  LOCAL (temp _st st; temp _a (Vfloat a); temp _b (Vfloat b))
  SEP (data_at_ Tsh dword st)).
forward_if Post_if.
- forward_call (Int.repr 1).
  unfold Post_if. entailer!.
- forward.
  unfold Post_if. entailer!.
  apply H. destruct vret_fin; auto.
- unfold Post_if.
  assert_PROP (Fast2Mult_exact_cond a b) as HFC by entailer!.
  forward_call (st, a, b).
  entailer!!.
  pose proof (Fast2Mult_correct_from_exact_cond a b HFC) as [Heq Hdw].
  split; [ apply Fast2Mult_accuracy_from_exact_cond, HFC | split; assumption ].
Qed.

Lemma body_fast_2mult_acc_guarded: semax_body Vprog Gprog f_fast_2mult_acc_guarded fast_2mult_acc_guarded_spec.
Proof.
start_function.
forward_call (a,b).
Intros vret_fin.
set (Post_if :=
  PROP (is_finite (BMULT a b) = true)
  LOCAL (temp _st st; temp _a (Vfloat a); temp _b (Vfloat b))
  SEP (data_at_ Tsh dword st)).
forward_if Post_if.
- forward_call (Int.repr 1).
  unfold Post_if. entailer!.
- forward.
  unfold Post_if. entailer!.
  apply H. destruct vret_fin; auto.
- unfold Post_if.
  assert_PROP (is_finite (BMULT a b) = true) as HFC by entailer!.
  forward_call (st, a, b).
  entailer!!.
  apply Fast2Mult_accuracy_norm, HFC.
Qed.
