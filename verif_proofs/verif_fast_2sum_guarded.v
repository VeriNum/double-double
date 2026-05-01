(* Copyright 2025 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Require Import DDModels common real_extras.
Require Import fast_2sum_guarded fp_utils_specs.
Require Import verif_fast_2sum.

#[export] Instance CompSpecs :
  compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition dword := Tstruct _dword noattr.

Definition f2val (pq: ftype Tdouble * ftype Tdouble) : val*val :=
 (Vfloat (fst pq), Vfloat (snd pq)).

Definition fast_2sum_guarded_spec :=
  DECLARE _fast_2sum_guarded
  WITH p: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr dword, tdouble, tdouble ]
    PROP()
    PARAMS (p; Vfloat a; Vfloat b)
    SEP(data_at_ Tsh dword p)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh dword (f2val (Fast2Sum a b)) p).

Definition exit_spec :=
  DECLARE _exit
  WITH code : int
  PRE [ tint ]
    PROP()
    PARAMS (Vint (Int.repr 1))
    SEP()
  POST [ tvoid ]
    PROP(False)
    LOCAL()
    SEP().

Definition Gprog : funspecs :=
  [exit_spec; fast2_sum_check_spec; fast_2sum_spec; fast_2sum_guarded_spec].

Lemma body_fast_2sum_guarded: semax_body Vprog Gprog f_fast_2sum_guarded fast_2sum_guarded_spec.
Proof.
start_function.
forward_call (a, b).
Intros vret_fin.
set (Post_if :=
  PROP (Fast2Sum_cond a b)
  LOCAL (temp _st p; temp _a (Vfloat a); temp _b (Vfloat b))
  SEP (data_at_ Tsh dword p)).
forward_if Post_if.

- (* then: !fast2_sum_check true → exit *)
  forward_call (Int.repr 1).
  unfold Post_if. entailer!.

- (* else: check returned true, so vret_fin = true *)
  forward.
  unfold Post_if. entailer!.
  unfold SumResultIsSafeForFast2Sum.
  apply H.
  destruct vret_fin; auto.

- (* continuation: call fast_2sum with Fast2Sum_cond from Post_if *)
  unfold Post_if.
  assert_PROP (Fast2Sum_cond a b) as HFC by entailer!.
  forward_call (p, a, b).
  entailer!!.
Qed.
