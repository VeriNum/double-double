(* Copyright 2025 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.

Require Import DDModels common real_extras.
Require Import dw_plus_fp_guarded.
Require Import DD.verif_proofs.verif_dw_plus_fp.

#[export] Instance CompSpecs :
  compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition dword := Tstruct _dword noattr.

Definition f2val (pq: ftype Tdouble * ftype Tdouble) : reptype dword :=
 (Vfloat (fst pq), Vfloat (snd pq)).

(* Re-declare the check spec locally with THIS file's CompSpecs.
   The body proof in verif_fp_utils.v is verified against fp_utils's CompSpecs;
   the structs are identical, so the spec is equivalent. *)
Definition SumResultIsSafeForDWPlusFP
  (xh xl y : ftype Tdouble) : Prop :=
  DWPlusFP_cond xh xl y.

Definition dw_plus_fp_check_spec :=
  DECLARE _dw_plus_fp_check
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
         SumResultIsSafeForDWPlusFP (fst xh) (snd xh) y)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP( data_at Tsh dword (f2val xh) x ).

Definition dw_plus_fp_guarded_spec :=
  DECLARE _dw_plus_fp_guarded
  WITH s: val, x: val,
       xh: ftype Tdouble * ftype Tdouble,
       y : ftype Tdouble
  PRE [ tptr dword, tptr dword, tdouble ]
    PROP()
    PARAMS (s; x; Vfloat y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh dword
          (f2val (DWPlusFP (fst xh) (snd xh) y)) s;
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
  [exit_spec; dw_plus_fp_check_spec; dw_plus_fp_spec; dw_plus_fp_guarded_spec].

(* The guarded wrapper: dw_plus_fp_check(x, y) returns 1, then call
   dw_plus_fp(s, x, y). The boolean POST of dw_plus_fp_check is lifted
   via assert_PROP into the DWPlusFP_cond hypothesis required by
   dw_plus_fp_spec's PRE. *)
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
- (* check returned 0 → exit *)
  forward_call (Int.repr 1).
  unfold Post_if. entailer!.
- (* check returned 1 → DWPlusFP_cond holds *)
  forward.
  unfold Post_if. entailer!.
  unfold SumResultIsSafeForDWPlusFP in H.
  apply H.
  destruct vret_fin; auto.
- (* continuation: call dw_plus_fp with the lifted cond *)
  unfold Post_if.
  assert_PROP
    (DWPlusFP_cond (fst xh) (snd xh) y) as HFC by entailer!.
  forward_call (s, x, xh, y).
  entailer!.
Qed.
