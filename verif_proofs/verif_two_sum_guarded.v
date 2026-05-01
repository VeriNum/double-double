(* Copyright 2025 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Require Import DDModels common real_extras.
Require Import two_sum_guarded fp_utils_specs.
Require Import DD.verif_proofs.verif_two_sum.

#[export] Instance CompSpecs :
  compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition dword := Tstruct _dword noattr.

Definition f2val (pq: ftype Tdouble * ftype Tdouble) : val*val :=
 (Vfloat (fst pq), Vfloat (snd pq)).

Definition two_sum_guarded_spec :=
  DECLARE _two_sum_guarded
  WITH p: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr dword, tdouble, tdouble ]
    PROP()
    PARAMS (p; Vfloat a; Vfloat b)
    SEP(data_at_ Tsh dword p)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh dword (f2val (TwoSumF a b)) p).

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
  [exit_spec; two_sum_check_spec; two_sum_spec; two_sum_guarded_spec].

Lemma body_two_sum_guarded: semax_body Vprog Gprog f_two_sum_guarded two_sum_guarded_spec.
Proof.
start_function.
forward_call (a, b).
Intros vret_fin.
set (Post_if :=
  PROP (TwoSum_cond a b)
  LOCAL (temp _st p; temp _a (Vfloat a); temp _b (Vfloat b))
  SEP (data_at_ Tsh dword p)).
forward_if Post_if.

- (* then: !two_sum_check true → exit *)
  forward_call (Int.repr 1).
  unfold Post_if. entailer!.

- (* else: check returned true, so vret_fin = true *)
  forward.
  unfold Post_if. entailer!.
  unfold SumResultIsSafeForTwoSum.
  apply H.
  destruct vret_fin; auto.

- (* continuation: call two_sum with TwoSum_cond from Post_if *)
  unfold Post_if.
  assert_PROP (TwoSum_cond a b) as HFC by entailer!.
  forward_call (p, a, b).
  entailer!!.
Qed.
