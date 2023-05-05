Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Require Import DDModels.
Require Import dw_mult_fp verif_fast_2sum verif_fast_2mult.

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
  WITH s: val, x : val, xh : ftype Tdouble * ftype Tdouble, y : ftype Tdouble
  PRE [tptr dword, tptr dword, tdouble  ] (* c lang types *)
    PROP()
    PARAMS (s; x; Vfloat y)
    SEP(data_at_ Tsh dword s; data_at Tsh dword (f2val xh) x)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh dword 
          (f2val (DWTimesFP3 (fst xh) (snd xh) y)) s; 
        data_at Tsh dword (f2val xh) x). 

(* Collect the function-API specs together into Gprog: list funspec *)
Definition Gprog1 : funspecs := MathASI ++ 
              [fast_2sum_spec; fast_2mult_spec; dw_mult_fp9_spec].

(* The function satisfies its API spec (with a semax-body proof) *)
Lemma body_dw_mult_dw12: semax_body Vprog Gprog1 f_dw_mult_fp9 dw_mult_fp9_spec.
Proof.
start_function.
forward.
forward_call. 
forward.
forward.
forward_call. 
forward.
forward.
forward_call.
unfold f2val, DWTimesFP3, Fast2Mult, Fast2Sum, fst, snd.
entailer!.
Qed.

