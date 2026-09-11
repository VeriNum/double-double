(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Export VST.floyd.proofauto.
Require Export vcfloat.VCFloat.
Require Export vcfloat.FPCompCert.
Require Export VSTlib.spec_math.

Require Export float_acc_lems common real_extras.
From Flocq Require Export Pff2Flocq Core.

Require Export DDConds.
Require Export fp_utils fp_utils_specs.
Require Export float_verif_lemmas.

Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Lemma Vint_b2z_if : forall b : bool,
  Vint (Int.repr (Z.b2z b)) =
  Vint (if b then Int.one else Int.zero).
Proof. intros [|]; reflexivity. Qed.

Definition ldexp_val :=
  Binary.Bldexp (fprec Tdouble) 1024 (fprec_gt_0 Tdouble)
    (fprec_lt_femax Tdouble) BinarySingleNaN.mode_NE
    (Float.of_bits (Int64.repr 4607182418800017408)) 53.

Definition thresh_val :=
  Float.mul (Float.of_bits (Int64.repr 4503599627370496)) ldexp_val.

Lemma thresh_val_finite : is_finite (ftype_of_float thresh_val) = true.
Proof.
  cbv [thresh_val ldexp_val Binary.is_finite Float.mul Float.of_bits
       Bits.b64_of_bits Binary.Bldexp Binary.lift Binary.Bmult]; auto.
Qed.

Lemma thresh_val_FT2R :
  FT2R (ftype_of_float thresh_val) =
  bpow Zaux.radix2 (SpecFloat.emin (fprec Tdouble) (femax Tdouble) + 2 * fprec Tdouble - 1).
Proof.

  cbv [thresh_val ldexp_val ftype_of_float Float.mul Float.of_bits
       Bits.b64_of_bits Binary.Bldexp]; simpl.
  cbv [Binary.lift Binary.Bmult]; simpl.
  cbv [BinarySingleNaN.binary_round_correct BinarySingleNaN.Bmult_correct_aux]; simpl.
  cbv [FT2R]; simpl.
  cbv [F2R]; simpl.
  nra.
Qed.

Definition tbool (b : bool) : int :=
  if b then Int.one else Int.zero.

Definition Checks_Imports : funspecs := [ fabs_spec; ldexp_spec ].

Definition Checks_Internal : funspecs :=
  [ isfinite_double_spec; fast2_mult_exact_check_spec;
    fast2_sum_magnitude_order_check_spec;
    dw_plus_dw_strong_precond_check_spec;
    dw_plus_dw_weak_precond_check_spec;
    dw_times_fp_strong_precond_check_spec; dw_times_fp_weak_precond_check_spec;
    dw_times_dw_strong_precond_check_spec; dw_times_dw_weak_precond_check_spec; dw_plus_fp_strong_precond_check_spec;
    dw_plus_fp_weak_precond_check_spec; isfinite_dword_spec;
    dw_div_fp_strong_check_spec; dw_div_fp_weak_check_spec;
    dw_div_dw_strong_precond_check_spec; dw_div_dw_weak_precond_check_spec ].

Definition Checks_Exports : funspecs :=
  [ isfinite_double_spec;
    fast2_sum_magnitude_order_check_spec; fast2_mult_exact_check_spec;
    isfinite_dword_spec; dw_plus_fp_weak_precond_check_spec;
    dw_plus_fp_strong_precond_check_spec; dw_plus_dw_weak_precond_check_spec; dw_plus_dw_strong_precond_check_spec;
    dw_times_fp_weak_precond_check_spec; dw_times_fp_strong_precond_check_spec;
    dw_times_dw_weak_precond_check_spec; dw_times_dw_strong_precond_check_spec;
    dw_div_fp_weak_check_spec; dw_div_fp_strong_check_spec;
    dw_div_dw_weak_precond_check_spec; dw_div_dw_strong_precond_check_spec ].

Definition Gprog : funspecs := Checks_Imports ++ Checks_Internal.
