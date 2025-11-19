(* Copyright 2025 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Require Import DDModels common real_extras.
Require Import fast_2mult fp_utils_specs.

#[export] Instance CompSpecs : 
  compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Notation emin := (SpecFloat.emin (fprec Tdouble) (femax Tdouble)).

Definition NoOverflowUnderflow_fast_2mult (a b : ftype Tdouble) : Prop :=
  is_finite (BMULT a b) = true /\ ((FT2R a * FT2R b)%R = 0%R \/
  (bpow Zaux.radix2 (emin + 2 * fprec Tdouble - 1) <= Rabs (FT2R a * FT2R b))%R). 

Definition dword := Tstruct _dword noattr.

Definition f2val (pq: ftype Tdouble * ftype Tdouble) : val*val :=
 (Vfloat (fst pq), Vfloat (snd pq)).

Definition fast_2mult_spec := 
  DECLARE _fast_2mult
  WITH st: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr dword, tdouble, tdouble ] (* c lang types *)
    PROP()
    PARAMS (st; Vfloat a; Vfloat b) (*functions params *)
    SEP(data_at_ Tsh dword st) (* preds on mem *)
  POST [ tvoid ]
    PROP(NoOverflowUnderflow_fast_2mult a b)
    RETURN()
    SEP(data_at Tsh dword (f2val (Fast2Mult a b)) st).

Definition exit_spec :=
  DECLARE _exit
  WITH code : int
  PRE [ tint ]
    PROP()
    PARAMS (Vint (Int.repr 1))   (* matches exit(EXIT_FAILURE) *)
    SEP( )
  POST [ tvoid ]
    PROP(False)    (* exit never returns *)
    LOCAL()
    SEP().

(* Collect the function-API specs together into Gprog: list funspec *)
Definition Gprog : funspecs := MathASI ++ [exit_spec; fast2_mult_check_spec; isfinite_double_spec; fast_2mult_spec].

Definition tbool (b : bool) : int :=
  if b then Int.one else Int.zero.

(* The function satisfies its API spec (with a semax-body proof) *)
Lemma body_fast_2mult: semax_body Vprog Gprog f_fast_2mult fast_2mult_spec.
Proof.
start_function.
forward_call (a,b).
Intros vret_fin.
set (Post_if :=
  PROP (MulResultIsNormal a b)
  LOCAL (temp _st st; temp _a (Vfloat a); temp _b (Vfloat b))
  SEP (data_at Tsh dword (default_val dword) st)).
forward_if Post_if.

-
forward_call (Int.repr 1).
unfold Post_if.
entailer!.

-
forward.
unfold Post_if.
entailer!.
apply H.
destruct vret_fin; auto.

-
unfold Post_if.
forward.
forward.
forward_call.
forward.
entailer!.
Qed.



