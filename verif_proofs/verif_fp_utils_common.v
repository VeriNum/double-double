(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Shared [Vprog], [Gprog], and helper definitions for the split
   [verif_fp_utils_*] body proofs.  Each body proof can be checked
   independently. *)

(* Re-export the VST and floating-point imports so each verif_fp_utils_*.v
   body proof file only needs to Require Import this common file. *)
Require Export VST.floyd.proofauto.
Require Export vcfloat.VCFloat.
Require Export vcfloat.FPCompCert.
Require Export VSTlib.spec_math.

Require Export float_acc_lems common real_extras.
From Flocq Require Export Pff2Flocq Core.

Require Export DDConds.
Require Export fp_utils fp_utils_specs.
Require Export float_verif_lemmas.

(* CompSpecs is imported from fp_utils_specs (#[export] Instance) so that
   specs and body proofs share the same compspecs and VST doesn't see two
   distinct instances. *)
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

(** Convert a Boolean represented as [Z], as used by comparison lemmas, to the
    CompCert integer representation used by C conditionals. *)
Lemma Vint_b2z_if : forall b : bool,
  Vint (Int.repr (Z.b2z b)) =
  Vint (if b then Int.one else Int.zero).
Proof. intros [|]; reflexivity. Qed.

(* ldexp_val defines the IEEE-754 float for ldexp(1.0, 53) = 2^53.
   Used by body_fast2_mult_check.
   Bit pattern 4607182418800017408 = 0x3FF0000000000000 is the encoding
   of 1.0 as a 64-bit double; Bldexp then scales it by 2^53. *)
Definition ldexp_val :=
  Binary.Bldexp (fprec Tdouble) 1024 (fprec_gt_0 Tdouble)
    (fprec_lt_femax Tdouble) BinarySingleNaN.mode_NE
    (Float.of_bits (Int64.repr 4607182418800017408)) 53.

(* thresh_val defines the IEEE-754 float for DBL_MIN * ldexp(1.0, 53) = 2^(-969).
   Bit pattern 4503599627370496 = 0x0010000000000000 is the encoding of
   DBL_MIN (smallest normal double, 2^(-1022)).  The product 2^(-1022) * 2^53
   equals 2^(-969) = bpow 2 (emin + 2*p - 1), the Fast2Mult underflow bound
   from Fast2Mult_exact_cond. *)
Definition thresh_val :=
  Float.mul (Float.of_bits (Int64.repr 4503599627370496)) ldexp_val.

(* thresh_val is a finite (not NaN, not infinite) double; proved by
   computational reduction of the concrete bit patterns. *)
Lemma thresh_val_finite : is_finite (ftype_of_float thresh_val) = true.
Proof.
  cbv [thresh_val ldexp_val Binary.is_finite Float.mul Float.of_bits
       Bits.b64_of_bits Binary.Bldexp Binary.lift Binary.Bmult]; auto.
Qed.

(* The real value of thresh_val equals the Fast2Mult underflow bound
   bpow 2 (emin + 2*p - 1).  This links the concrete C constant to the
   abstract bound in Fast2Mult_exact_cond, allowing Float_cmp_Cle_mul to fire. *)
Lemma thresh_val_FT2R :
  FT2R (ftype_of_float thresh_val) =
  bpow Zaux.radix2 (SpecFloat.emin (fprec Tdouble) (femax Tdouble) + 2 * fprec Tdouble - 1).
Proof.
  (* Unfold in stages: a single large cbv leaves a goal nra cannot close. *)
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

(* VSU spec groupings for the checks translation unit (fp_utils).
   Imports are the two libm functions the checks call (fabs, ldexp); the
   internal check functions are listed in fp_utils prog order.  Gprog is exactly
   the checks VSU's G = Imports ++ internal specs, so these body proofs feed
   directly into solve_SF_internal in Checks_VSU.v. *)
Definition Checks_Imports : funspecs := [ fabs_spec; ldexp_spec ].

Definition Checks_Internal : funspecs :=
  [ isfinite_double_spec; fast2_mult_check_spec; fast2_mult_acc_check_spec;
    fast2_sum_check_spec;
    two_sum_check_spec; dw_plus_dw_check_spec;
    dw_plus_dw_input_check_spec;
    dw_mult_fp_check_spec; dw_mult_dw_check_spec; dw_plus_fp_check_spec;
    dw_plus_fp_input_check_spec; dword_finite_check_spec;
    dw_div_fp_check_spec; dw_div_dw_check_spec ].

(* Public API exported by the checks VSU: every check consumed by the ops VSU. *)
Definition Checks_Exports : funspecs :=
  [ two_sum_check_spec; fast2_sum_check_spec; fast2_mult_check_spec;
    fast2_mult_acc_check_spec;
    dword_finite_check_spec; dw_plus_fp_input_check_spec;
    dw_plus_fp_check_spec; dw_plus_dw_input_check_spec; dw_plus_dw_check_spec;
    dw_mult_fp_check_spec;
    dw_mult_dw_check_spec; dw_div_fp_check_spec; dw_div_dw_check_spec ].

(* Collect the function API specs together into Gprog: list funspec.
   Shared by all body proof files. *)
Definition Gprog : funspecs := Checks_Imports ++ Checks_Internal.
