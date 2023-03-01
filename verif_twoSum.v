Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.

Require Import TwoSumModel.
Require Import twoSum.

#[export] Instance CompSpecs : 
  compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition st_state := Tstruct _state noattr.

Definition f2val (pq: ftype Tdouble * ftype Tdouble) : val*val :=
 (Vfloat (fst pq), Vfloat (snd pq)).

Definition TwoSum := TwoSumF Tdouble.

Definition twoSum_spec := 
  DECLARE _twoSum
  WITH s: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr st_state, tdouble, tdouble ] (* c lang types *)
    PROP()
    PARAMS (s; Vfloat a; Vfloat b)
    SEP(data_at_ Tsh st_state s) (* preds on mem *)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh st_state (f2val (TwoSum a b)) s).

(* Collect the function-API specs together into Gprog: list funspec *)
Definition Gprog : funspecs := [twoSum_spec].

(* The function satisfies its API spec (with a semax-body proof) *)
Lemma body_twoSum: semax_body Vprog Gprog f_twoSum twoSum_spec.
Proof.
start_function.
forward.
forward.
forward.
forward.
forward.
forward.
forward.
forward.
autorewrite with float_elim in *. (* for view only *)
unfold TwoSum, f2val, TwoSumF, fst, snd.
entailer!.
Qed.




