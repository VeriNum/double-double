(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Require Import DDModels common real_extras.
Require Import fast_2mult.
Require Import Fast2Mult_acc.

#[export] Instance CompSpecs :
  compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec Tdouble) (femax Tdouble))).

Definition dword := Tstruct _dword noattr.

Definition f2val (pq: ftype Tdouble * ftype Tdouble) : val*val :=
 (Vfloat (fst pq), Vfloat (snd pq)).

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

Definition Gprog : funspecs := MathASI ++ [fast_2mult_spec].

Lemma body_fast_2mult: semax_body Vprog Gprog f_fast_2mult fast_2mult_spec.
Proof.
start_function.
forward. forward. forward_call. forward.
entailer!.
Qed.

Corollary Fast2Mult_acc (a b : ftype Tdouble) :
  Fast2Mult_cond a b ->
  (Rabs (FT2R (Fast2Mult_err a b)) <= / 2 * ulp (FT2R a * FT2R b))%R.
Proof. apply Fast2Mult_accuracy_from_safety. Qed.
