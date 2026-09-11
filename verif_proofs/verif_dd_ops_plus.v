(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Body proofs for double-word addition kernels and public wrappers. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Require Import DDConds common real_extras op_defs.
Require Import DD.accuracy_proofs.dw_opps.DWPlusFP_relative_acc.
Require Import DD.accuracy_proofs.dw_opps.DWPlusDW_relative_acc.
Require Import DD.verif_proofs.verif_objs.dd_ops.
Require Import DD.verif_proofs.DDOpsASI.
Require Import DD.verif_proofs.verif_dd_ops_common.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

(* The C body matches the DWPlusFP model directly:
     two_sum(&sh, x->s, y);   (sh.s,sh.t) = TwoSumF xh y
     v = x->t + sh.t;         v = BPLUS xl sl
     fast_2sum_kernel(s, sh.s, v);   (zh,zl) = Fast2Sum sh.s v
   The inner two_sum / fast_2sum_kernel specs have empty preconditions, so the
   forward_call cascade discharges no side conditions -- identical in shape
   to body_dw_plus_dw_kernel and body_dw_times_fp_kernel. *)
Lemma body_dw_plus_fp_kernel:
  semax_body Vprog Gprog f_dw_plus_fp_kernel dw_plus_fp_kernel_spec.
Proof.
  start_function.
  (* two_sum(&sh, x->s, y) *)
  forward.
  forward_call (v_sh, fst xh, y).
  (* v = x->t + sh.t *)
  forward.  forward.  forward.
  (* fast_2sum_kernel(s, sh.s, v) *)
  forward.
  forward_call (s, TwoSumF_sum (fst xh) y,
                BPLUS (snd xh) (TwoSumF_err (fst xh) y)).
  unfold f2val, DWPlusFP, TwoSumF, Fast2Sum,
         TwoSumF_sum, TwoSumF_err, fst, snd.
  entailer!.
Qed.

Lemma body_dw_plus_dw_kernel:
  semax_body Vprog Gprog f_dw_plus_dw_kernel dw_plus_dw_kernel_spec.
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
  unfold f2val, DWPlusDW, TwoSumF, Fast2Sum,
         TwoSumF_sum, TwoSumF_err, Fast2Sum_sum, Fast2Sum_err, fst, snd.
  entailer!.
Qed.

Lemma body_dw_plus_fp :
  semax_body Vprog Gprog f_dw_plus_fp dw_plus_fp_spec.
Proof.
start_function.
forward_call (x, xh, y).
Intros vret_fin.
forward_if.
- forward. Exists Int.one.
  assert (Hone : Int.one <> Int.zero) by computable.
  unfold default_wrapper_status; simpl; entailer!.
- assert_PROP (DWPlusFP_weak_precond (fst xh) (snd xh) y) as Hin.
  { entailer!. apply H. destruct vret_fin; auto. }
  forward_call (s, x, xh, y).
  forward_call (s, DWPlusFP (fst xh) (snd xh) y).
  Intros vret_out.
  forward_if.
  + forward. Exists (Int.repr 2).
    assert (Htwo : Int.repr 2 <> Int.zero) by computable.
    unfold default_wrapper_status; simpl; entailer!.
  + assert_PROP
      (DWPlusFP_weak_pre_and_finite_post_cond (fst xh) (snd xh) y)
      as Hcond.
    { unfold DWPlusFP_weak_pre_and_finite_post_cond,
             DWPlusFP_finite_post_cond.
      entailer!.
    match goal with
    | Hfin : vret_out = true -> is_finite_p _ |- _ =>
        apply Hfin; destruct vret_out; auto
    end. }
    assert (Hfp : (3 <= fprec Tdouble)%Z)
      by (unfold fprec, Tdouble; simpl; lia).
    pose proof
      (@DWPlusFP_relative_guarantee_from_weak_pre_and_finite_post_cond
         _ Tdouble _ (fst xh) (snd xh) y Hfp Hcond)
      as Hg.
    forward.
    Exists Int.zero.
    unfold default_wrapper_status; simpl; entailer!.
Qed.

Lemma body_dw_plus_fp_strong :
  semax_body Vprog Gprog f_dw_plus_fp_strong dw_plus_fp_strong_spec.
Proof.
start_function.
forward_call (x, xh, y).
Intros vret_fin.
forward_if.
- forward. Exists (Int.repr 3).
  assert (Hthree : Int.repr 3 <> Int.zero) by computable.
  unfold strong_wrapper_status; simpl; entailer!.
- assert_PROP (DWPlusFP_strong_precond (fst xh) (snd xh) y) as HFC.
  { entailer!. apply H. destruct vret_fin; auto. }
  forward_call (s, x, xh, y).
  assert (Hfp : (3 <= fprec Tdouble)%Z)
    by (unfold fprec, Tdouble; simpl; lia).
  pose proof
    (@DWPlusFP_relative_guarantee_from_strong_precond
       _ Tdouble _ (fst xh) (snd xh) y Hfp HFC)
    as Hg.
  forward.
  Exists Int.zero.
  unfold strong_wrapper_status; simpl; entailer!.
Qed.

Lemma body_dw_plus_dw :
  semax_body Vprog Gprog f_dw_plus_dw dw_plus_dw_spec.
Proof.
start_function.
forward_call (x, y, xh, yh).
Intros vret_fin.
forward_if.
- forward. Exists Int.one.
  assert (Hone : Int.one <> Int.zero) by computable.
  unfold default_wrapper_status; simpl; entailer!.
- assert_PROP
    (DWPlusDW_weak_precond (fst xh) (snd xh) (fst yh) (snd yh)) as Hin.
  { entailer!. apply H. destruct vret_fin; auto. }
  forward_call (s, x, y, xh, yh).
  forward_call
    (s, DWPlusDW (fst xh) (snd xh) (fst yh) (snd yh)).
  Intros vret_out.
  forward_if.
  + forward. Exists (Int.repr 2).
    assert (Htwo : Int.repr 2 <> Int.zero) by computable.
    unfold default_wrapper_status; simpl; entailer!.
  + assert_PROP
      (DWPlusDW_weak_pre_and_finite_post_cond
         (fst xh) (snd xh) (fst yh) (snd yh)) as Hcond.
    { unfold DWPlusDW_weak_pre_and_finite_post_cond,
             DWPlusDW_finite_post_cond.
      entailer!.
    match goal with
    | Hfin : vret_out = true -> is_finite_p _ |- _ =>
        apply Hfin; destruct vret_out; auto
    end. }
    assert (Hfp : (3 <= fprec Tdouble)%Z)
      by (unfold fprec, Tdouble; simpl; lia).
    pose proof
      (@DWPlusDW_relative_guarantee_from_weak_pre_and_finite_post_cond
         _ Tdouble _ (fst xh) (snd xh) (fst yh) (snd yh) Hfp Hcond)
      as Hg.
    forward.
    Exists Int.zero.
    unfold default_wrapper_status; simpl; entailer!.
Qed.

Lemma body_dw_plus_dw_strong :
  semax_body Vprog Gprog f_dw_plus_dw_strong dw_plus_dw_strong_spec.
Proof.
start_function.
forward_call (x, y, xh, yh).
Intros vret_fin.
forward_if.
- forward. Exists (Int.repr 3).
  assert (Hthree : Int.repr 3 <> Int.zero) by computable.
  unfold strong_wrapper_status; simpl; entailer!.
- assert_PROP
    (DWPlusDW_strong_precond (fst xh) (snd xh) (fst yh) (snd yh)) as HFC.
  { entailer!. apply H. destruct vret_fin; auto. }
  forward_call (s, x, y, xh, yh).
  assert (Hfp : (3 <= fprec Tdouble)%Z)
    by (unfold fprec, Tdouble; simpl; lia).
  pose proof
    (DWPlusDW_relative_guarantee_from_strong_precond
       (fst xh) (snd xh) (fst yh) (snd yh) Hfp HFC)
    as Hg.
  forward.
  Exists Int.zero.
  unfold strong_wrapper_status; simpl; entailer!.
Qed.
