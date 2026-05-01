(* Copyright 2025 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.

Require Import DDModels common.
Require Import Fast2Sum_acc.
Require Import fast_2sum.

#[export] Instance CompSpecs :
  compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec Tdouble) (femax Tdouble))).

Definition st := Tstruct _dword noattr.

Definition f2val (pq: ftype Tdouble * ftype Tdouble) : val*val :=
 (Vfloat (fst pq), Vfloat (snd pq)).

Definition fast_2sum_spec :=
  DECLARE _fast_2sum
  WITH s: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr st, tdouble, tdouble ]
    PROP(Fast2Sum_cond a b)
    PARAMS (s; Vfloat a; Vfloat b)
    SEP(data_at_ Tsh st s)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh st (f2val (Fast2Sum a b)) s).

Definition Gprog : funspecs := [fast_2sum_spec].

Lemma body_fast_2sum: semax_body Vprog Gprog f_fast_2sum fast_2sum_spec.
Proof.
start_function.
forward.
forward.
forward.
forward.
entailer!.
Qed.

Corollary Fast2Sum_acc (a b : ftype Tdouble) :
  Fast2Sum_cond a b ->
  (Rabs (FT2R (Fast2Sum_err a b)) <= / 2 * ulp (FT2R a + FT2R b))%R.
Proof. apply FastTwoSum_accuracy_from_cond. Qed.
