Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.

Require Import DDModels.
Require Import dw_plus_fp verif_two_sum verif_fast_2sum.

#[export] Instance CompSpecs : 
  compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition dword := Tstruct _dword noattr.

Definition f2val (pq: ftype Tdouble * ftype Tdouble) : val*val :=
 (Vfloat (fst pq), Vfloat (snd pq)).

Definition dw_plus_fp_spec := 
  DECLARE _dw_plus_fp
  WITH s: val, x : val, 
      xh : ftype Tdouble * ftype Tdouble, y : ftype Tdouble
  PRE [tptr dword, tptr dword, tdouble ] (* c lang types *)
    PROP()
    PARAMS (s; x; Vfloat y)
    SEP(data_at_ Tsh dword s; 
          data_at Tsh dword (f2val xh) x) (* preds on mem *)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh dword 
          (f2val (DWPlusFP (fst xh) (snd xh) y)) s; (* final dword is stored at address s *) 
        data_at Tsh dword (f2val xh) x). (* initial dword is unchanged *)

(* Collect the function-API specs together into Gprog: list funspec *)
Definition Gprog : funspecs := [fast_2sum_spec; two_sum_spec; dw_plus_fp_spec].

(* The function satisfies its API spec (with a semax-body proof) *)
Lemma body_dw_plus_fp: semax_body Vprog Gprog f_dw_plus_fp dw_plus_fp_spec.
Proof.
start_function.
forward.
forward_call.
forward. 
forward.
forward.
forward.
forward_call.
forward.
unfold f2val, DWPlusFP, TwoSumF, Fast2Sum, fst, snd.
entailer!.
Qed.




