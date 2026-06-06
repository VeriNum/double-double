(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Require Import DDModels.
Require Import DD.verif_proofs.verif_objs.dw_mult_fp.
Require Import DD.verif_proofs.verif_fast_2sum.
Require Import DD.verif_proofs.verif_fast_2mult.

#[export] Instance CompSpecs :
  compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition dword := Tstruct _dword noattr.

Definition f2val (pq: ftype Tdouble * ftype Tdouble) : val*val :=
 (Vfloat (fst pq), Vfloat (snd pq)).

Definition dw_mult_fp9_spec :=
  DECLARE _dw_mult_fp9
  WITH s: val, x : val,
      xh : ftype Tdouble * ftype Tdouble, y : ftype Tdouble
  PRE [tptr dword, tptr dword, tdouble ]
    PROP(DWTimesFP_cond (fst xh) (snd xh) y)   (* threaded cond *)
    PARAMS (s; x; Vfloat y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh dword
          (f2val (DWTimesFP3 (fst xh) (snd xh) y)) s;
        data_at Tsh dword (f2val xh) x).

(* Collect the function-API specs together into Gprog: list funspec *)
Definition Gprog : funspecs := MathASI ++
              [fast_2sum_spec; fast_2mult_spec; dw_mult_fp9_spec].

(* body_dw_mult_fp9: BODY ADMITTED.  Each forward_call to the inner
   fast_2mult / BFMA / fast_2sum must discharge its precondition from
   DWTimesFP_cond:
     - fast_2mult(&ch, xh, y) : Fast2Mult_cond xh y, immediate from
                                DWTimesFP_cond's underflow disjunction
                                and is_finite (BMULT xh y);
     - BFMA xl y ch.t         : finiteness derivable from DWTimesFP_cond
                                via FMA accuracy bounds;
     - fast_2sum(zh, ch.s, c3): Fast2Sum_cond, requires |c3| <= ulp(ch.s)
                                shape argument internal to DWTimesFP3
                                (parallel to the deferred Fast2Sum
                                obligation in body_dw_plus_fp / DWPlusDW).
   Wiring these into the forward_call cascade is parallel to the
   deferred body_dw_plus_fp in verif_dw_plus_fp.v; deferred for the
   same reason. *)
Lemma body_dw_mult_fp9: semax_body Vprog Gprog f_dw_mult_fp9 dw_mult_fp9_spec.
Proof. Admitted.
