(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Require Import DDModels common real_extras.
Require Import Fast2Mult_acc.
Require Import fast_2mult_guarded fp_utils_specs.
Require Import verif_fast_2mult.

#[export] Instance CompSpecs :
  compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition dword := Tstruct _dword noattr.

Definition f2val (pq: ftype Tdouble * ftype Tdouble) : val*val :=
 (Vfloat (fst pq), Vfloat (snd pq)).

Definition fast_2mult_guarded_spec :=
  DECLARE _fast_2mult_guarded
  WITH st: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr dword, tdouble, tdouble ]
    PROP()
    PARAMS (st; Vfloat a; Vfloat b)
    SEP(data_at_ Tsh dword st)
  POST [ tvoid ]
    PROP((Rabs (FT2R (Fast2Mult_err a b)) <= / 2 * ulp (FT2R a * FT2R b))%R)
    RETURN()
    SEP(data_at Tsh dword (f2val (Fast2Mult a b)) st).

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
  [exit_spec; fast2_mult_check_spec; fast_2mult_spec; fast_2mult_guarded_spec].

Lemma body_fast_2mult_guarded: semax_body Vprog Gprog f_fast_2mult_guarded fast_2mult_guarded_spec.
Proof.
start_function.
forward_call (a,b).
Intros vret_fin.
set (Post_if :=
  PROP (Fast2Mult_cond a b)
  LOCAL (temp _st st; temp _a (Vfloat a); temp _b (Vfloat b))
  SEP (data_at_ Tsh dword st)).
forward_if Post_if.

- (* then: !fast2_mult_check true → exit *)
  forward_call (Int.repr 1).
  unfold Post_if. entailer!.

- (* else: Sskip; fast2_mult_check returned true, so vret_fin = true *)
  forward.
  unfold Post_if. entailer!.
  apply H.
  destruct vret_fin; auto.

- (* continuation: call fast_2mult with Fast2Mult_cond from Post_if *)
  unfold Post_if.
  assert_PROP (Fast2Mult_cond a b) as HFC by entailer!.
  forward_call (st, a, b).
  entailer!!.
  apply Fast2Mult_accuracy_from_safety, HFC.
Qed.
