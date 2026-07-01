(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.

Require Import DDModels common real_extras.
Require Import dw_plus_dw_guarded.
Require Import DD.verif_proofs.verif_dw_plus_dw.
Require Import DD.accuracy_proofs.dw_opps.DWPlusDW_acc.

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
Definition dw_plus_dw_check_spec :=
  DECLARE _dw_plus_dw_check
  WITH x : val, y : val,
       xh : ftype Tdouble * ftype Tdouble,
       yh : ftype Tdouble * ftype Tdouble
  PRE [ tptr dword, tptr dword ]
    PROP()
    PARAMS ( x; y )
    SEP( data_at Tsh dword (f2val xh) x;
         data_at Tsh dword (f2val yh) y )
  POST [ tint ]
    EX b : bool,
    PROP(b = true ->
         DWPlusDW_cond (fst xh) (snd xh) (fst yh) (snd yh))
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP( data_at Tsh dword (f2val xh) x;
         data_at Tsh dword (f2val yh) y ).

Definition dw_plus_dw2_guarded_spec :=
  DECLARE _dw_plus_dw2_guarded
  WITH s: val, x: val, y: val,
       xh: ftype Tdouble * ftype Tdouble,
       yh: ftype Tdouble * ftype Tdouble
  PRE [ tptr dword, tptr dword, tptr dword ]
    PROP()
    PARAMS (s; x; y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y)
  POST [ tvoid ]
    PROP(DWPlusDW_cond (fst xh) (snd xh) (fst yh) (snd yh) /\
         (relative_error_DWPlusDW (fst xh) (snd xh) (fst yh) (snd yh)
           <= (3 * (bpow Zaux.radix2 (- fprec Tdouble)) ^ 2)
              / (1 - 4 * (bpow Zaux.radix2 (- fprec Tdouble))))%R)
    RETURN()
    SEP(data_at Tsh dword
          (f2val (AccurateDWPlusDW (fst xh) (snd xh) (fst yh) (snd yh))) s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y).

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
  [exit_spec; dw_plus_dw_check_spec; dw_plus_dw2_spec; dw_plus_dw2_guarded_spec].

(* The guarded wrapper: dw_plus_dw_check(x, y) returns 1, then call
   dw_plus_dw2(s, x, y). The boolean POST of dw_plus_dw_check is lifted
   via assert_PROP into the DWPlusDW_cond hypothesis required by
   dw_plus_dw2_spec's PRE. This proof does NOT depend on the admitted
   Hc_le_sh / Hw_le_vh — it only uses the spec interface. *)
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
- (* check returned 0 → exit *)
  forward_call (Int.repr 1).
  unfold Post_if. entailer!.
- (* check returned 1 → DWPlusDW_cond holds *)
  forward.
  unfold Post_if. entailer!.
  apply H.
  destruct vret_fin; auto.
- (* continuation: call dw_plus_dw2 with the lifted cond *)
  unfold Post_if.
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
