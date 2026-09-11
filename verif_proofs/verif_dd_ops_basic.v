(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

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

Lemma body_two_sum_kernel:
  semax_body Vprog Gprog f_two_sum_kernel two_sum_kernel_spec.
Proof.
start_function.
forward. forward. forward. forward.
forward. forward. forward. forward.
entailer!.
Qed.

Lemma body_two_sum: semax_body Vprog Gprog f_two_sum two_sum_spec.
Proof.
start_function.
forward_call (a).
Intros vret_a.
forward_if.
- forward. Exists Int.one.
  assert (Hone : Int.one <> Int.zero) by computable.
  unfold default_wrapper_status; simpl; entailer!.
- forward_call (b).
  Intros vret_b.
  forward_if.
  + forward. Exists Int.one.
    assert (Hone : Int.one <> Int.zero) by computable.
    unfold default_wrapper_status; simpl; entailer!.
  + forward_call (s, a, b).
    forward_call (s, TwoSumF a b).
    Intros vret_out.
    forward_if.
    * forward. Exists (Int.repr 2).
      assert (Htwo : Int.repr 2 <> Int.zero) by computable.
      unfold default_wrapper_status; simpl; entailer!.
    * assert_PROP (is_finite_p (TwoSumF a b)) as Hfin.
      { entailer!.
        match goal with
        | Hout : vret_out = true -> is_finite_p _ |- _ =>
            apply Hout; destruct vret_out; auto
        end. }
      pose proof (TwoSumF_correct a b Hfin) as Hcorrect.
      pose proof (TwoSum_is_DW a b Hfin) as Hdw.
      assert (Hguarantee : TwoSum_guarantee a b).
      { unfold TwoSum_guarantee.
        split; [lra | exact Hdw]. }
      forward. Exists Int.zero.
      unfold default_wrapper_status; simpl; entailer!.
Qed.

Lemma body_fast_2sum_kernel:
  semax_body Vprog Gprog f_fast_2sum_kernel fast_2sum_kernel_spec.
Proof.
start_function.
forward. forward. forward. forward.
entailer!.
Qed.

Lemma body_fast_2mult_kernel:
  semax_body Vprog Gprog f_fast_2mult_kernel fast_2mult_kernel_spec.
Proof.
start_function.
forward. forward. forward_call. forward.
entailer!.
Qed.

Lemma body_fast_2sum: semax_body Vprog Gprog f_fast_2sum fast_2sum_spec.
Proof.
start_function.
forward_call (a, b).
Intros vret_fin.
forward_if.
- forward.
  assert (Hone : Int.one <> Int.zero) by computable.
  Exists Int.one.
  unfold weak_wrapper_status; simpl; entailer!.
- assert_PROP
    (is_finite (BPLUS a b) = true /\
     (Rabs (FT2R b) <= Rabs (FT2R a))%R) as Hsafe.
  { entailer!.
    unfold fp_utils_specs.Fast2Sum_magnitude_order_cond in H.
    apply H. destruct vret_fin; auto. }
  destruct Hsafe as [Hfin Hle].
  assert (HFC : Fast2Sum_exact_cond a b).
  { split; [exact Hfin |].
    left. apply Ulp.ulp_le.
    - apply BinarySingleNaN.fexp_correct; apply fprec_gt_0.
    - apply FLT.FLT_exp_monotone.
    - exact Hle. }
  forward_call (p, a, b).
  forward.
  assert (HG : Fast2Sum_exact_guarantee a b).
  { apply Fast2Sum_exact_guarantee_from_magnitude_order; assumption. }
  Exists Int.zero.
  unfold weak_wrapper_status; simpl; entailer!.
Qed.

Lemma body_fast_2mult: semax_body Vprog Gprog f_fast_2mult fast_2mult_spec.
Proof.
start_function.
forward_call (a,b).
Intros vret_fin.
forward_if.
- forward.
  assert (Hone : Int.one <> Int.zero) by computable.
  Exists Int.one.
  unfold weak_wrapper_status; simpl; entailer!.
- assert_PROP (Fast2Mult_exact_cond a b) as HFC.
  { entailer!. apply H. destruct vret_fin; auto. }
  forward_call (st, a, b).
  forward.
  pose proof (Fast2Mult_correct_from_exact_cond a b HFC) as [Heq Hdw].
  assert (HG :
    (Rabs (FT2R (Fast2Mult_err a b)) <=
       / 2 * ulp (FT2R a * FT2R b))%R /\
    (FT2R (Fast2Mult_mul a b) + FT2R (Fast2Mult_err a b) =
       FT2R a * FT2R b)%R /\
    double_word_prop (Fast2Mult_mul a b) (Fast2Mult_err a b)).
  { split; [ apply Fast2Mult_accuracy_from_exact_cond, HFC
           | split; assumption ]. }
  Exists Int.zero.
  unfold weak_wrapper_status; simpl; entailer!.
Qed.
