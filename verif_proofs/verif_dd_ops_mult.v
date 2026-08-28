(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Body proofs for double-word multiplication kernels and public wrappers. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Require Import DDConds common real_extras op_defs.
Require Import DD.accuracy_proofs.dw_opps.DWMulFP_mixed_acc.
Require Import DD.accuracy_proofs.dw_opps.DWMulDW_mixed_acc.
Require Import DD.verif_proofs.verif_objs.dd_ops.
Require Import DD.verif_proofs.DDOpsASI.
Require Import DD.verif_proofs.verif_dd_ops_common.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Lemma body_dw_mult_fp_kernel:
  semax_body Vprog Gprog f_dw_mult_fp_kernel dw_mult_fp_kernel_spec.
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

Lemma body_dw_mult_dw_kernel:
  semax_body Vprog Gprog f_dw_mult_dw_kernel dw_mult_dw_kernel_spec.
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

Lemma body_dw_mult_fp :
  semax_body Vprog Gprog f_dw_mult_fp dw_mult_fp_spec.
Proof.
start_function.
forward_call (x, xh, y).
Intros vret_fin.
set (Post_if :=
  PROP (DWTimesFP_mixed_input_cond (fst xh) (snd xh) y)
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
  assert_PROP (DWTimesFP_mixed_input_cond (fst xh) (snd xh) y) as Hin
    by entailer!.
  forward_call (s, x, xh, y).
  forward_call (s, DWTimesFP3 (fst xh) (snd xh) y).
  Intros vret_out.
  set (Post_out :=
    PROP (DWTimesFP_mixed_cond (fst xh) (snd xh) y)
    LOCAL (temp _st s; temp _x x; temp _y (Vfloat y))
    SEP (data_at Tsh dword
           (f2val (DWTimesFP3 (fst xh) (snd xh) y)) s;
         data_at Tsh dword (f2val xh) x)).
  forward_if Post_out.
  + forward_call (Int.repr 1).
    unfold Post_out. entailer!.
  + forward.
    unfold Post_out, DWTimesFP_mixed_cond, DWTimesFP_result_finite.
    entailer!.
    match goal with
    | Hfin : vret_out = true -> is_finite_p _ |- _ =>
        apply Hfin; destruct vret_out; auto
    end.
  + unfold Post_out.
    assert_PROP (DWTimesFP_mixed_cond (fst xh) (snd xh) y) as Hcond
      by entailer!.
    assert (Hfp : (3 <= fprec Tdouble)%Z)
      by (unfold fprec, Tdouble; simpl; lia).
    pose proof
      (@DWTimesFP_mixed_guarantee_from_cond
         _ Tdouble _ (fst xh) (snd xh) y Hfp Hcond)
      as Hg.
    entailer!!.
Qed.

Lemma body_dw_mult_fp_strong :
  semax_body Vprog Gprog f_dw_mult_fp_strong dw_mult_fp_strong_spec.
Proof.
start_function.
forward_call (x, xh, y).
Intros vret_fin.
set (Post_if :=
  PROP (DWTimesFP_mixed_safe_input_cond (fst xh) (snd xh) y)
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
  assert_PROP (DWTimesFP_mixed_safe_input_cond (fst xh) (snd xh) y) as HFC by entailer!.
  forward_call (s, x, xh, y).
  assert (Hfp : (3 <= fprec Tdouble)%Z)
    by (unfold fprec, Tdouble; simpl; lia).
  pose proof
    (@DWTimesFP_mixed_guarantee_from_safe_input_cond
       _ Tdouble _ (fst xh) (snd xh) y Hfp HFC)
    as Hg.
  entailer!!.
Qed.

Lemma body_dw_mult_dw :
  semax_body Vprog Gprog f_dw_mult_dw dw_mult_dw_spec.
Proof.
start_function.
forward_call (x, y, xh, yh).
Intros vret_fin.
set (Post_if :=
  PROP (DWTimesDW_mixed_input_cond (fst xh) (snd xh) (fst yh) (snd yh))
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
    (DWTimesDW_mixed_input_cond (fst xh) (snd xh) (fst yh) (snd yh)) as Hin
    by entailer!.
  forward_call (s, x, y, xh, yh).
  forward_call
    (s, DWTimesDW3 (fst xh) (snd xh) (fst yh) (snd yh)).
  Intros vret_out.
  set (Post_out :=
    PROP (DWTimesDW_mixed_cond (fst xh) (snd xh) (fst yh) (snd yh))
    LOCAL (temp _st s; temp _x x; temp _y y)
    SEP (data_at Tsh dword
           (f2val (DWTimesDW3 (fst xh) (snd xh) (fst yh) (snd yh))) s;
         data_at Tsh dword (f2val xh) x;
         data_at Tsh dword (f2val yh) y)).
  forward_if Post_out.
  + forward_call (Int.repr 1).
    unfold Post_out. entailer!.
  + forward.
    unfold Post_out, DWTimesDW_mixed_cond, DWTimesDW_result_finite.
    entailer!.
    match goal with
    | Hfin : vret_out = true -> is_finite_p _ |- _ =>
        apply Hfin; destruct vret_out; auto
    end.
  + unfold Post_out.
    assert_PROP
      (DWTimesDW_mixed_cond (fst xh) (snd xh) (fst yh) (snd yh)) as Hcond
      by entailer!.
    assert (Hp5 : (5 <= fprec Tdouble)%Z)
      by (unfold fprec, Tdouble; simpl; lia).
    pose proof
      (@DWTimesDW_mixed_guarantee_from_cond
         _ Tdouble _ (fst xh) (snd xh) (fst yh) (snd yh) Hp5 Hcond)
      as Hg.
    entailer!!.
Qed.

Lemma body_dw_mult_dw_strong :
  semax_body Vprog Gprog f_dw_mult_dw_strong dw_mult_dw_strong_spec.
Proof.
start_function.
forward_call (x, y, xh, yh).
Intros vret_fin.
set (Post_if :=
  PROP (DWTimesDW_mixed_safe_input_cond (fst xh) (snd xh) (fst yh) (snd yh))
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
    (DWTimesDW_mixed_safe_input_cond (fst xh) (snd xh) (fst yh) (snd yh)) as HFC by entailer!.
  forward_call (s, x, y, xh, yh).
  assert (Hp5 : (5 <= fprec Tdouble)%Z)
    by (unfold fprec, Tdouble; simpl; lia).
  pose proof
    (@DWTimesDW_mixed_guarantee_from_safe_input_cond
       _ Tdouble _ (fst xh) (snd xh) (fst yh) (snd yh) Hp5 HFC)
    as Hg.
  entailer!!.
Qed.
