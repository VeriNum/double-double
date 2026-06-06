(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.

Require Import DDModels common.
Require Import TwoSum_acc.
Require Import two_sum.

#[export] Instance CompSpecs :
  compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec Tdouble) (femax Tdouble))).

Definition st := Tstruct _dword noattr.

Definition f2val (pq: ftype Tdouble * ftype Tdouble) : val*val :=
 (Vfloat (fst pq), Vfloat (snd pq)).

Definition two_sum_spec :=
  DECLARE _two_sum
  WITH s: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr st, tdouble, tdouble ]
    PROP()
    PARAMS (s; Vfloat a; Vfloat b)
    SEP(data_at_ Tsh st s)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh st (f2val (TwoSumF a b)) s).

Definition Gprog : funspecs := [two_sum_spec].

Lemma body_two_sum: semax_body Vprog Gprog f_two_sum two_sum_spec.
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
entailer!.
Qed.