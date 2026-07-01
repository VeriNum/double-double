(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Require Import DDModels.
Require Import DD.verif_proofs.verif_objs.dw_mult_fp.

#[export] Instance CompSpecs :
  compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition dword := Tstruct _dword noattr.

Definition f2val (pq: ftype Tdouble * ftype Tdouble) : val*val :=
 (Vfloat (fst pq), Vfloat (snd pq)).

(* Re-declare fast_2mult and fast_2sum specs locally under THIS file's
   CompSpecs.  The body proofs in verif_fast_2mult.v / verif_fast_2sum.v are
   verified under their own (per-program) compspecs; the funspec interface is
   identical — same struct, same args.  Declaring them here keeps the struct
   data_at under the local CompSpecs, so field loads on the local `ch` after
   the fast_2mult call do not trip a compspecs mismatch. *)
Definition fast_2mult_spec :=
  DECLARE _fast_2mult
  WITH st: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr dword, tdouble, tdouble ]
    PROP()
    PARAMS (st; Vfloat a; Vfloat b)
    SEP(data_at_ Tsh dword st)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh dword (f2val (Fast2Mult a b)) st).

Definition fast_2sum_spec :=
  DECLARE _fast_2sum
  WITH s: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr dword, tdouble, tdouble ]
    PROP()
    PARAMS (s; Vfloat a; Vfloat b)
    SEP(data_at_ Tsh dword s)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh dword (f2val (Fast2Sum a b)) s).

Definition dw_mult_fp9_spec :=
  DECLARE _dw_mult_fp9
  WITH s: val, x : val,
      xh : ftype Tdouble * ftype Tdouble, y : ftype Tdouble
  PRE [tptr dword, tptr dword, tdouble ]
    PROP()
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

(* body_dw_mult_fp9: the three inner specs (fast_2mult_spec, the MathASI
   fma spec, fast_2sum_spec) are all precondition-free — each simply returns
   its functional-model result (Fast2Mult / BFMA / Fast2Sum).  So the
   forward_call cascade needs no cond discharge; the DWTimesFP_cond in the
   PRE is carried only for downstream accuracy consumers.  The postcondition
   value is exactly the composition Fast2Sum ch (BFMA xl y cl1) with
   (ch, cl1) = Fast2Mult xh y, i.e. DWTimesFP3.  Mirrors body_dw_mult_dw12. *)
Lemma body_dw_mult_fp9: semax_body Vprog Gprog f_dw_mult_fp9 dw_mult_fp9_spec.
Proof.
start_function.
forward.            (* t'5 = x->s *)
forward_call.       (* fast_2mult(&ch, x->s, y) *)
forward.            (* t'3 = x->t *)
forward.            (* t'4 = ch.t *)
forward_call.       (* fma(x->t, y, ch.t) *)
forward.            (* c3 = t'1 *)
forward.            (* t'2 = ch.s *)
forward_call.       (* fast_2sum(zh, ch.s, c3) *)
unfold f2val, DWTimesFP3, Fast2Mult, Fast2Sum, fst, snd.
entailer!.
Qed.
