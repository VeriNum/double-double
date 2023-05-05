Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.

Require Import DDModels.
Require Import dw_plus_dw verif_two_sum verif_fast_2sum.

#[export] Instance CompSpecs : 
  compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition dword := Tstruct _dword noattr.

Definition f2val (pq: ftype Tdouble * ftype Tdouble) : val*val :=
 (Vfloat (fst pq), Vfloat (snd pq)).

Definition dw_plus_dw1_spec := 
  DECLARE _dw_plus_dw1
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
          (f2val (SloppyDWPlusDW (fst xh) (snd xh) (fst yh) (snd yh))) s; (* final dword is stored at address s *) 
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y). (* initial dwords unchanged *)

(* Collect the function-API specs together into Gprog: list funspec *)
Definition Gprog1 : funspecs := [fast_2sum_spec; two_sum_spec; dw_plus_dw1_spec].

(* The function satisfies its API spec (with a semax-body proof) *)
Lemma body_dw_plus_dw1: semax_body Vprog Gprog1 f_dw_plus_dw1 dw_plus_dw1_spec.
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
forward.
forward_call.
unfold f2val, SloppyDWPlusDW, TwoSumF, Fast2Sum, fst, snd.
entailer!.
Qed.

Definition dw_plus_dw2_spec := 
  DECLARE _dw_plus_dw2
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
          (f2val (AccurateDWPlusDW (fst xh) (snd xh) (fst yh) (snd yh))) s; (* final dword is stored at address s *) 
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y). (* initial dwords unchanged *)

(* Collect the function-API specs together into Gprog: list funspec *)
Definition Gprog2 : funspecs := [fast_2sum_spec; two_sum_spec; dw_plus_dw2_spec].

(* The function satisfies its API spec (with a semax-body proof) *)
Lemma body_dw_plus_dw2: semax_body Vprog Gprog1 f_dw_plus_dw2 dw_plus_dw2_spec.
Proof.
start_function.
forward.
forward.
forward_call. 
forward.
forward.
forward_call. 
forward.
forward.
forward.
forward.
forward_call.
forward.
forward.
forward.
forward.
forward_call.
unfold f2val, AccurateDWPlusDW, TwoSumF, Fast2Sum, fst, snd.
entailer!.
Qed.




