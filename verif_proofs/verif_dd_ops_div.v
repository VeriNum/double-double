(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Body proofs for double-word division operations and guarded wrappers. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Require Import DDConds common real_extras op_defs.
Require Import DD.verif_proofs.dd_float_reconcile.
Require Import DD.accuracy_proofs.dw_opps.DWDivFP_mixed_acc.
Require Import DD.accuracy_proofs.dw_opps.DWDivDW_mixed_acc.
Require Import DD.verif_proofs.verif_objs.dd_ops.
Require Import DD.verif_proofs.DDOpsASI.
Require Import DD.verif_proofs.verif_dd_ops_common.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

(* Leaf reconciliation lemmas BDIV_Td/BMULT_Td/BOPP_Td/BFMA_Td/Zconst1_Td are
   factored into dd_float_reconcile (imported above); body_dw_div_dw18 uses
   them to make the stored value and the postcondition syntactically equal. *)

(* Verification of the call sequence implementing [DWDivDW3].  Each callee
   returns its model result without an arithmetic precondition.  The struct
   arguments produced by earlier calls are passed as explicit witnesses
   because Coq cannot infer them through projections of [f2val]. *)
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
(* dw_mult_fp9(&delta, &e, th): witness (s, x, xh, y) = (v_delta, v_e, e pair, th) *)
match goal with |- context [temp _th (Vfloat ?T)] =>
 match goal with |- context [data_at _ _ (f2val ?E) v_e] =>
   forward_call (v_delta, v_e, E, T) end end.
(* dw_plus_fp(&m, &delta, th): witness (v_m, v_delta, delta pair, th) *)
match goal with |- context [temp _th (Vfloat ?T)] =>
 match goal with |- context [data_at _ _ (f2val ?D) v_delta] =>
   forward_call (v_m, v_delta, D, T) end end.
(* dw_mult_dw12(z, x, &m): witness (s, x, v_m, xh, m pair) *)
match goal with |- context [data_at _ _ (f2val ?M) v_m] =>
   forward_call (s, x, v_m, xh, M) end.
(* Rewrite the postcondition's DWDivDW3 term into the exact composition the
   cascade produced, so both `data_at` values become syntactically identical
   and the closing entailer needs no whole term conversion between B and
   CompCert floating-point operations. *)
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

(* body_dw_div_fp15: the callees (fast_2mult, fast_2sum) require no preconditions,
   so the forward cascade needs no cond discharge.  The C directly performs the
   subtractions/additions of Algorithm 15, so -- unlike body_dw_div_dw18, whose
   arithmetic is hidden inside dw_mult_fp9 / dw_plus_fp / dw_mult_dw12 -- the
   stored value is Fast2Sum th tl with th = BDIV xh y and tl the raw
   BPLUS/BMINUS/BDIV cascade.  We rewrite DWDivFP3 into that exact CompCert float
   composition (BDIV/BMINUS/BPLUS reconciled to Float.div/sub/add) so the two
   data_at values become syntactically identical for the closing entailer. *)
Lemma body_dw_div_fp15: semax_body Vprog Gprog f_dw_div_fp15 dw_div_fp15_spec.
Proof.
start_function.
forward.            (* t'5 = x->s *)
forward.            (* th  = t'5 / y *)
(* fast_2mult(&p, th, y): witness (v_p, th, y) *)
match goal with |- context [temp _th (Vfloat ?T)] =>
  forward_call (v_p, T, y) end.
forward.            (* t'3 = x->s *)
forward.            (* t'4 = p.s  *)
forward.            (* dh  = t'3 - t'4 *)
forward.            (* t'2 = p.t  *)
forward.            (* dt  = dh - t'2 *)
forward.            (* t'1 = x->t *)
forward.            (* d   = dt + t'1 *)
forward.            (* tl  = d / y *)
(* fast_2sum(z, th, tl): witness (s, th, tl) *)
match goal with |- context [temp _th (Vfloat ?TH)] =>
 match goal with |- context [temp _tl (Vfloat ?TL)] =>
   forward_call (s, TH, TL) end end.
(* Rewrite the postcondition's DWDivFP3 into the produced composition. *)
match goal with |- context [data_at _ _ (f2val ?PROD) s] =>
  replace (DWDivFP3 (fst xh) (snd xh) y) with PROD end.
2:{ unfold DWDivFP3.
    rewrite ?BDIV_Td, ?BMINUS_Td, ?BPLUS_Td.
    destruct (Fast2Mult _ _) as [pih pil]; cbn [fst snd].
    destruct (Fast2Sum _ _) as [zh zl]; cbn [fst snd].
    reflexivity. }
entailer!!.
Qed.

(* DWDivFP (Algorithm 15) guarded wrapper.  Call the check, exit on failure,
   otherwise recover DWDivFP_mixed_safe_input_cond and call
   the unguarded op.  The exported accuracy postcondition is the
   bundled guarantee, which is independent of the regime
   (DWDivFP_mixed_guarantee_from_safe_input_cond), which the safe input cond
   discharges unconditionally; see
   dw_div_fp15_guarded_spec. *)
Lemma body_dw_div_fp15_guarded :
  semax_body Vprog Gprog f_dw_div_fp15_guarded dw_div_fp15_guarded_spec.
Proof.
start_function.
forward_call (x, xh, y).
Intros vret_fin.
set (Post_if :=
  PROP (DWDivFP_mixed_safe_input_cond (fst xh) (snd xh) y)
  LOCAL (temp _z s; temp _x x; temp _y (Vfloat y))
  SEP (data_at_ Tsh dword s;
       data_at Tsh dword (f2val xh) x)).
forward_if Post_if.
- forward_call (Int.repr 1).
  unfold Post_if. entailer!.
- forward.
  unfold Post_if. entailer!.
  apply H. destruct vret_fin; auto.
- unfold Post_if.
  assert_PROP (DWDivFP_mixed_safe_input_cond (fst xh) (snd xh) y) as HFC by entailer!.
  forward_call (s, x, xh, y).
  assert (Hp4 : (4 <= fprec Tdouble)%Z)
    by (unfold fprec, Tdouble; simpl; lia).
  pose proof
    (DWDivFP_mixed_guarantee_from_safe_input_cond
       (fst xh) (snd xh) y Hp4 HFC)
    as Hg.
  entailer!!.
Qed.

(* DWDivDW (Algorithm 18) guarded wrapper.  Same skeleton as
   body_dw_div_fp15_guarded, with a second dword operand: call the check, exit on
   failure (whose PROP(False) postcondition makes that branch vacuously satisfy
   the accuracy claim), otherwise recover DWDivDW_mixed_safe_input_cond from the check's
   boolean and call the unguarded op.  Hp14 is the format side condition
   14 <= fprec Tdouble = 53, discharged here, so the exported mixed bound and the
   output validity both rest on DWDivDW_mixed_safe_input_cond alone -- the condition with no quotient
   underflow floor, which is what dw_div_dw_check establishes.  See
   dw_div_dw18_guarded_spec for why a pure relative form is not the exported
   one. *)
Lemma body_dw_div_dw18_guarded :
  semax_body Vprog Gprog f_dw_div_dw18_guarded dw_div_dw18_guarded_spec.
Proof.
start_function.
forward_call (x, y, xh, yh).
Intros vret_fin.
set (Post_if :=
  PROP (DWDivDW_mixed_safe_input_cond (fst xh) (snd xh) (fst yh) (snd yh))
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
  assert_PROP (DWDivDW_mixed_safe_input_cond (fst xh) (snd xh) (fst yh) (snd yh)) as HFC
    by entailer!.
  forward_call (s, x, y, xh, yh).
  assert (Hp14 : (14 <= fprec Tdouble)%Z)
    by (unfold fprec, Tdouble; simpl; lia).
(* Accuracy and output validity, bundled under a single match on
     the result pair -- see dw_div_dw18_guarded_spec for why the two facts are
     not stated separately here. *)
  pose proof
    (DWDivDW_mixed_guarantee_from_safe_input_cond
       (fst xh) (snd xh) (fst yh) (snd yh) Hp14 HFC)
    as Hg.
  entailer!!.
Qed.
