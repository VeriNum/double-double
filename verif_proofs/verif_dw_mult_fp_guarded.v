(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.

Require Import DDModels common real_extras.
Require Import DD.paper_proofs.DWTimesFP.
Require Import DD.accuracy_proofs.dw_opps.DWMul_acc.
Require Import DD.verif_proofs.verif_objs.dw_mult_fp_guarded.
Require Import DD.verif_proofs.verif_dw_mult_fp.

(* Modeling axiom: the abstract FLX two-product TwoProd of paper_proofs.DWTimesFP
   is the FLX Fast2Mult at this precision.  This is the same assumption the paper
   development carries as the TwoProdE hypothesis (DWTimesFP3_FLX_FLT,
   DWTimesFP9_correct); at the C level it states that the compiled fused product
   realizes the error-free transformation.  It is consistent (one equation on an
   opaque Parameter) and is the instantiation expected by
   DWTimesFP_accuracy_from_cond. *)
Axiom TwoProd_Tdouble :
  DWTimesFP.TwoProd = DWTimesFP.Fast2Mult (fprec Tdouble) choice.

#[export] Instance CompSpecs :
  compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition dword := Tstruct _dword noattr.

Definition f2val (pq: ftype Tdouble * ftype Tdouble) : reptype dword :=
 (Vfloat (fst pq), Vfloat (snd pq)).

(* Re-declare the check spec locally with THIS file's CompSpecs.
   The struct is identical, so the spec is equivalent. *)
Definition dw_mult_fp_check_spec :=
  DECLARE _dw_mult_fp_check
  WITH x : val,
       xh : ftype Tdouble * ftype Tdouble,
       y  : ftype Tdouble
  PRE [ tptr dword, tdouble ]
    PROP()
    PARAMS ( x; Vfloat y )
    SEP( data_at Tsh dword (f2val xh) x )
  POST [ tint ]
    EX b : bool,
    PROP(b = true ->
         DWTimesFP_cond (fst xh) (snd xh) y)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP( data_at Tsh dword (f2val xh) x ).

Definition dw_mult_fp9_guarded_spec :=
  DECLARE _dw_mult_fp9_guarded
  WITH s: val, x: val,
       xh: ftype Tdouble * ftype Tdouble,
       y : ftype Tdouble
  PRE [ tptr dword, tptr dword, tdouble ]
    PROP()
    PARAMS (s; x; Vfloat y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x)
  POST [ tvoid ]
    PROP(DWTimesFP_cond (fst xh) (snd xh) y /\
         (relative_error_DWTimesFP (fst xh) (snd xh) y
           <= 2 * (bpow Zaux.radix2 (- fprec Tdouble)) ^ 2)%R)
    RETURN()
    SEP(data_at Tsh dword
          (f2val (DWTimesFP3 (fst xh) (snd xh) y)) s;
        data_at Tsh dword (f2val xh) x).

Definition exit_spec :=
  DECLARE _exit
  WITH code : int
  PRE [ tint ]
    PROP()
    PARAMS (Vint (Int.repr 1))
    SEP()
  POST [ tvoid ]
    PROP(False)
    LOCAL()
    SEP().

Definition Gprog : funspecs :=
  [exit_spec; dw_mult_fp_check_spec; dw_mult_fp9_spec; dw_mult_fp9_guarded_spec].

(* The guarded wrapper: dw_mult_fp_check(x, y) returns 1, then call
   dw_mult_fp9(s, x, y). The boolean POST of dw_mult_fp_check is
   lifted via assert_PROP into the DWTimesFP_cond hypothesis required
   by dw_mult_fp9_spec's PRE. *)
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
- (* check returned 0 -> exit *)
  forward_call (Int.repr 1).
  unfold Post_if. entailer!.
- (* check returned 1 -> DWTimesFP_cond holds *)
  forward.
  unfold Post_if. entailer!.
  apply H.
  destruct vret_fin; auto.
- (* continuation: call dw_mult_fp9 with the lifted cond *)
  unfold Post_if.
  assert_PROP
    (DWTimesFP_cond (fst xh) (snd xh) y) as HFC by entailer!.
  forward_call (s, x, xh, y).
  assert (Hfp : (3 <= fprec Tdouble)%Z)
    by (unfold fprec, Tdouble; simpl; lia).
  pose proof
    (@DWTimesFP_accuracy_from_cond _ Tdouble _ (fst xh) (snd xh) y
       TwoProd_Tdouble Hfp HFC)
    as Hacc.
  entailer!!.
Qed.
