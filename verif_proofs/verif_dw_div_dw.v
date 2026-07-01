(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Require Import DDModels.
Require Import DD.verif_proofs.verif_objs.dw_div_dw.

#[export] Instance CompSpecs :
  compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition dword := Tstruct _dword noattr.

Definition f2val (pq: ftype Tdouble * ftype Tdouble) : val*val :=
 (Vfloat (fst pq), Vfloat (snd pq)).

(* --- Specs of the callees, as verified in their own files.  Each is
   precondition-free: it simply returns its functional-model result.
   Re-declared here (rather than imported) so this client proof is
   self-contained and does not depend on the callees' Clight programs. --- *)

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

Definition dw_plus_fp_spec :=
  DECLARE _dw_plus_fp
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
          (f2val (DWPlusFP (fst xh) (snd xh) y)) s;
        data_at Tsh dword (f2val xh) x).

Definition dw_mult_dw12_spec :=
  DECLARE _dw_mult_dw12
  WITH s: val, x : val, y: val,
      xh : ftype Tdouble * ftype Tdouble,
      yh : ftype Tdouble * ftype Tdouble
  PRE [tptr dword, tptr dword, tptr dword ]
    PROP()
    PARAMS (s; x; y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh dword
          (f2val (DWTimesDW3 (fst xh) (snd xh) (fst yh) (snd yh))) s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y).

Definition dw_div_dw18_spec :=
  DECLARE _dw_div_dw18
  WITH s: val, x : val, y: val,
      xh : ftype Tdouble * ftype Tdouble,
      yh : ftype Tdouble * ftype Tdouble
  PRE [tptr dword, tptr dword, tptr dword ] (* c lang types *)
    PROP()
    PARAMS (s; x; y)
    SEP(data_at_ Tsh dword s;
          data_at Tsh dword (f2val xh) x;
          data_at Tsh dword (f2val yh) y)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh dword
          (f2val (DWDivDW3 (fst xh) (snd xh) (fst yh) (snd yh))) s; (* final dword is stored at address s *)
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y). (* initial dwords unchanged *)

(* Collect the function-API specs together into Gprog: list funspec *)
Definition Gprog : funspecs := MathASI ++
              [fast_2sum_spec; dw_mult_fp9_spec; dw_plus_fp_spec;
               dw_mult_dw12_spec; dw_div_dw18_spec].

(* body_dw_div_dw18: the callees (fma from MathASI, fast_2sum, dw_mult_fp9,
   dw_plus_fp, dw_mult_dw12) are all precondition-free -- each returns its
   functional-model result -- so the forward_call cascade needs no cond
   discharge.  The stored value is exactly the composition

     DWTimesDW3 xh xl (fst (DWPlusFP dh dl th)) (snd (DWPlusFP dh dl th))

   with (dh,dl) = DWTimesFP3 eh el th, (eh,el) = Fast2Sum rh rl,
   th = BDIV 1 yh, rh = BFMA (-yh) th 1, rl = BOPP (yl*th),
   i.e. DWDivDW3.  Mirrors body_dw_mult_dw12 / body_dw_mult_fp9.

   The three double-word calls (dw_mult_fp9 / dw_plus_fp / dw_mult_dw12) each
   take a struct argument whose contents were produced by the previous call.
   Their WITH-clause pair (xh) cannot be inferred automatically: unifying the
   spec's `f2val xh` against the stored `f2val <pair>` degenerates into a
   projection unification (`fst xh = fst <pair>`) that Coq leaves open.  We
   therefore read the produced pair (and the divisor th) straight out of the
   goal with `match ... context` and pass them as explicit witnesses. *)
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
(* dw_mult_fp9(&delta, &e, th): witness (s, x, xh, y) = (v_delta, v_e, e-pair, th) *)
match goal with |- context [temp _th (Vfloat ?T)] =>
 match goal with |- context [data_at _ _ (f2val ?E) v_e] =>
   forward_call (v_delta, v_e, E, T) end end.
(* dw_plus_fp(&m, &delta, th): witness (v_m, v_delta, delta-pair, th) *)
match goal with |- context [temp _th (Vfloat ?T)] =>
 match goal with |- context [data_at _ _ (f2val ?D) v_delta] =>
   forward_call (v_m, v_delta, D, T) end end.
(* dw_mult_dw12(z, x, &m): witness (s, x, v_m, xh, m-pair) *)
match goal with |- context [data_at _ _ (f2val ?M) v_m] =>
   forward_call (s, x, v_m, xh, M) end.
unfold f2val, DWDivDW3, DWTimesDW3, DWTimesFP3, DWPlusFP, Fast2Sum,
       Fast2Mult, TwoSumF, fst, snd.
entailer!.
Qed.
