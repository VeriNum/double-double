Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Require Import DDModels.
Require Import fast_2mult.

#[export] Instance CompSpecs : 
  compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition st := Tstruct _dword noattr.

Definition f2val (pq: ftype Tdouble * ftype Tdouble) : val*val :=
 (Vfloat (fst pq), Vfloat (snd pq)).

Definition fast_2mult_spec := 
  DECLARE _fast_2mult
  WITH s: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr st, tdouble, tdouble ] (* c lang types *)
    PROP()
    PARAMS (s; Vfloat a; Vfloat b)
    SEP(data_at_ Tsh st s) (* preds on mem *)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh st (f2val (Fast2Mult a b)) s).

(* Collect the function-API specs together into Gprog: list funspec *)
Definition Gprog : funspecs := MathASI ++ [fast_2mult_spec].

(* The function satisfies its API spec (with a semax-body proof) *)
Lemma body_twoSum: semax_body Vprog Gprog f_fast_2mult fast_2mult_spec.
Proof.
start_function.
forward.
forward.
autorewrite with float_elim in *. (* for view only *)
forward.
forward.
forward.
forward.
forward.
autorewrite with float_elim in *. (* for view only *)
unfold f2val, TwoSumF, fst, snd.
entailer!.
Qed.




