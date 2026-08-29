(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Body proofs for double-word division kernels and public wrappers. *)

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
   factored into dd_float_reconcile (imported above); body_dw_div_dw_kernel uses
   them to make the stored value and the postcondition syntactically equal. *)

(* Verification of the call sequence implementing [DWDivDW].  Each callee
   returns its model result without an arithmetic precondition.  The struct
   arguments produced by earlier calls are passed as explicit witnesses
   because Coq cannot infer them through projections of [f2val]. *)
Lemma body_dw_div_dw_kernel:
  semax_body Vprog Gprog f_dw_div_dw_kernel dw_div_dw_kernel_spec.
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
(* dw_mult_fp_kernel(&delta, &e, th): witness (s, x, xh, y) =
   (v_delta, v_e, e pair, th). *)
match goal with |- context [temp _th (Vfloat ?T)] =>
 match goal with |- context [data_at _ _ (f2val ?E) v_e] =>
   forward_call (v_delta, v_e, E, T) end end.
(* dw_plus_fp_kernel(&m, &delta, th): witness (v_m, v_delta, delta pair, th) *)
match goal with |- context [temp _th (Vfloat ?T)] =>
 match goal with |- context [data_at _ _ (f2val ?D) v_delta] =>
   forward_call (v_m, v_delta, D, T) end end.
(* dw_mult_dw_kernel(z, x, &m): witness (s, x, v_m, xh, m pair). *)
match goal with |- context [data_at _ _ (f2val ?M) v_m] =>
   forward_call (s, x, v_m, xh, M) end.
(* Rewrite the postcondition's DWDivDW term into the exact composition the
   cascade produced, so both `data_at` values become syntactically identical
   and the closing entailer needs no whole term conversion between B and
   CompCert floating-point operations. *)
match goal with |- context [data_at _ _ (f2val ?PROD) s] =>
  replace (DWDivDW (fst xh) (snd xh) (fst yh) (snd yh)) with PROD end.
2:{ unfold DWDivDW.
    rewrite ?BDIV_Td, ?BFMA_Td, ?BOPP_Td, ?BMULT_Td, ?Zconst1_Td.
    destruct (Fast2Sum _ _)     as [eh el]; cbn [fst snd].
    destruct (DWTimesFP _ _ _) as [dh dl]; cbn [fst snd].
    destruct (DWPlusFP _ _ _)   as [mh ml]; cbn [fst snd].
    reflexivity. }
entailer!!.
Qed.

(* The callees (fast_2mult, fast_2sum) require no preconditions,
   so the forward cascade needs no cond discharge.  The C directly performs the
   subtractions/additions of Algorithm 15, so -- unlike the DW/DW kernel, whose
   arithmetic is hidden inside the multiplication and addition kernels -- the
   stored value is Fast2Sum th tl with th = BDIV xh y and tl the raw
   BPLUS/BMINUS/BDIV cascade.  We rewrite DWDivFP into that exact CompCert float
   composition (BDIV/BMINUS/BPLUS reconciled to Float.div/sub/add) so the two
   data_at values become syntactically identical for the closing entailer. *)
Lemma body_dw_div_fp_kernel:
  semax_body Vprog Gprog f_dw_div_fp_kernel dw_div_fp_kernel_spec.
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
(* Rewrite the postcondition's DWDivFP into the produced composition. *)
match goal with |- context [data_at _ _ (f2val ?PROD) s] =>
  replace (DWDivFP (fst xh) (snd xh) y) with PROD end.
2:{ unfold DWDivFP.
    rewrite ?BDIV_Td, ?BMINUS_Td, ?BPLUS_Td.
    destruct (Fast2Mult _ _) as [pih pil]; cbn [fst snd].
    destruct (Fast2Sum _ _) as [zh zl]; cbn [fst snd].
    reflexivity. }
entailer!!.
Qed.

Lemma body_dw_div_fp :
  semax_body Vprog Gprog f_dw_div_fp dw_div_fp_spec.
Proof.
start_function.
forward_call (x, xh, y).
Intros vret_fin.
set (Post_if :=
  PROP (DWDivFP_weak_precond (fst xh) (snd xh) y)
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
  assert_PROP (DWDivFP_weak_precond (fst xh) (snd xh) y) as Hin
    by entailer!.
  forward_call (s, x, xh, y).
  forward_call (s, DWDivFP (fst xh) (snd xh) y).
  Intros vret_out.
  set (Post_out :=
    PROP (DWDivFP_weak_pre_and_finite_post_cond (fst xh) (snd xh) y)
    LOCAL (temp _z s; temp _x x; temp _y (Vfloat y))
    SEP (data_at Tsh dword
           (f2val (DWDivFP (fst xh) (snd xh) y)) s;
         data_at Tsh dword (f2val xh) x)).
  forward_if Post_out.
  + forward_call (Int.repr 1).
    unfold Post_out. entailer!.
  + forward.
    unfold Post_out, DWDivFP_weak_pre_and_finite_post_cond, DWDivFP_finite_post_cond.
    entailer!.
    match goal with
    | Hfin : vret_out = true -> is_finite_p _ |- _ =>
        apply Hfin; destruct vret_out; auto
    end.
  + unfold Post_out.
    assert_PROP (DWDivFP_weak_pre_and_finite_post_cond (fst xh) (snd xh) y) as Hcond
      by entailer!.
    assert (Hp4 : (4 <= fprec Tdouble)%Z)
      by (unfold fprec, Tdouble; simpl; lia).
    pose proof
      (@DWDivFP_guarantee_from_weak_pre_and_finite_post_cond
         _ Tdouble _ (fst xh) (snd xh) y Hp4 Hcond)
      as Hg.
    entailer!!.
Qed.

Lemma body_dw_div_fp_strong :
  semax_body Vprog Gprog f_dw_div_fp_strong dw_div_fp_strong_spec.
Proof.
start_function.
forward_call (x, xh, y).
Intros vret_fin.
set (Post_if :=
  PROP (DWDivFP_strong_precond (fst xh) (snd xh) y)
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
  assert_PROP (DWDivFP_strong_precond (fst xh) (snd xh) y) as HFC by entailer!.
  forward_call (s, x, xh, y).
  assert (Hp4 : (4 <= fprec Tdouble)%Z)
    by (unfold fprec, Tdouble; simpl; lia).
  pose proof
    (DWDivFP_guarantee_from_strong_precond
       (fst xh) (snd xh) y Hp4 HFC)
    as Hg.
  entailer!!.
Qed.

Lemma body_dw_div_dw :
  semax_body Vprog Gprog f_dw_div_dw dw_div_dw_spec.
Proof.
start_function.
forward_call (x, y, xh, yh).
Intros vret_fin.
set (Post_if :=
  PROP (DWDivDW_weak_precond (fst xh) (snd xh) (fst yh) (snd yh))
  LOCAL (temp _z s; temp _x x; temp _y y)
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
    (DWDivDW_weak_precond (fst xh) (snd xh) (fst yh) (snd yh)) as Hin
    by entailer!.
  forward_call (s, x, y, xh, yh).
  forward_call (s, DWDivDW (fst xh) (snd xh) (fst yh) (snd yh)).
  Intros vret_out.
  set (Post_out :=
    PROP (DWDivDW_weak_pre_and_finite_post_cond (fst xh) (snd xh) (fst yh) (snd yh))
    LOCAL (temp _z s; temp _x x; temp _y y)
    SEP (data_at Tsh dword
           (f2val (DWDivDW (fst xh) (snd xh) (fst yh) (snd yh))) s;
         data_at Tsh dword (f2val xh) x;
         data_at Tsh dword (f2val yh) y)).
  forward_if Post_out.
  + forward_call (Int.repr 1).
    unfold Post_out. entailer!.
  + forward.
    unfold Post_out, DWDivDW_weak_pre_and_finite_post_cond, DWDivDW_finite_post_cond.
    entailer!.
    match goal with
    | Hfin : vret_out = true -> is_finite_p _ |- _ =>
        apply Hfin; destruct vret_out; auto
    end.
  + unfold Post_out.
    assert_PROP
      (DWDivDW_weak_pre_and_finite_post_cond (fst xh) (snd xh) (fst yh) (snd yh)) as Hcond
      by entailer!.
    assert (Hp14 : (14 <= fprec Tdouble)%Z)
      by (unfold fprec, Tdouble; simpl; lia).
    pose proof
      (@DWDivDW_guarantee_from_weak_pre_and_finite_post_cond
         _ Tdouble _ (fst xh) (snd xh) (fst yh) (snd yh) Hp14 Hcond)
      as Hg.
    entailer!!.
Qed.

Lemma body_dw_div_dw_strong :
  semax_body Vprog Gprog f_dw_div_dw_strong dw_div_dw_strong_spec.
Proof.
start_function.
forward_call (x, y, xh, yh).
Intros vret_fin.
set (Post_if :=
  PROP (DWDivDW_strong_precond (fst xh) (snd xh) (fst yh) (snd yh))
  LOCAL (temp _z s; temp _x x; temp _y y)
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
  assert_PROP (DWDivDW_strong_precond (fst xh) (snd xh) (fst yh) (snd yh)) as HFC
    by entailer!.
  forward_call (s, x, y, xh, yh).
  assert (Hp14 : (14 <= fprec Tdouble)%Z)
    by (unfold fprec, Tdouble; simpl; lia).
  pose proof
    (DWDivDW_guarantee_from_strong_precond
       (fst xh) (snd xh) (fst yh) (snd yh) Hp14 HFC)
    as Hg.
  entailer!!.
Qed.
