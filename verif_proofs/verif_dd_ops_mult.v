(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Body proofs for double-word multiplication operations and guarded wrappers. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Require Import DDConds common real_extras op_defs.
Require Import DD.accuracy_proofs.dw_opps.DWMulFP_acc.
Require Import DD.accuracy_proofs.dw_opps.DWMulDW_acc.
Require Import DD.verif_proofs.verif_objs.dd_ops.
Require Import DD.verif_proofs.DDOpsASI.
Require Import DD.verif_proofs.verif_dd_ops_common.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

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

Lemma body_dw_mult_fp9_guarded :
  semax_body Vprog Gprog f_dw_mult_fp9_guarded dw_mult_fp9_guarded_spec.
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
  (* The whole-range mixed bound is the public API for DW x FP: the guard only
     establishes DWTimesFP_mixed_safe_input_cond (no underflow disjunct), which is exactly
     what DWTimesFP_mixed_guarantee_from_cond needs once finiteness is derived. *)
  pose proof
    (@DWTimesFP_mixed_guarantee_from_safe_input_cond
       _ Tdouble _ (fst xh) (snd xh) y Hfp HFC)
    as Hg.
  entailer!!.
Qed.

Lemma body_dw_mult_dw12_guarded :
  semax_body Vprog Gprog f_dw_mult_dw12_guarded dw_mult_dw12_guarded_spec.
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
  (* The whole-range mixed bound is the public API for DW x DW: the guard only
     establishes DWTimesDW_mixed_safe_input_cond (no underflow disjunct), which is exactly
     what DWTimesDW_mixed_accuracy_from_cond needs once finiteness is derived. *)
  pose proof
    (@DWTimesDW_mixed_guarantee_from_safe_input_cond
       _ Tdouble _ (fst xh) (snd xh) (fst yh) (snd yh) Hp5 HFC)
    as Hg.
  entailer!!.
Qed.
