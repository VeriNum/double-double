(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import compcert.lib.Floats compcert.lib.Integers.
Require Import op_defs.

Lemma BDIV_Td  : forall x y : ftype Tdouble, BDIV  x y = Float.div x y.
Proof. reflexivity. Qed.

Lemma BMULT_Td : forall x y : ftype Tdouble, BMULT x y = Float.mul x y.
Proof. reflexivity. Qed.

Lemma BPLUS_Td : forall x y : ftype Tdouble, BPLUS x y = Float.add x y.
Proof. reflexivity. Qed.

Lemma BMINUS_Td : forall x y : ftype Tdouble, BMINUS x y = Float.sub x y.
Proof. reflexivity. Qed.

Lemma BOPP_Td  : forall x : ftype Tdouble,   BOPP  x   = Float.neg x.
Proof. reflexivity. Qed.

Lemma BFMA_Td  : forall x y z : ftype Tdouble,
  BFMA x y z =
  Binary.Bfma (fprec Tdouble) 1024 (fprec_gt_0 Tdouble) (fprec_lt_femax Tdouble)
    (FMA_NAN.fma_nan_pl (fprec Tdouble) 1024 (fprec_gt_one Tdouble))
    BinarySingleNaN.mode_NE x y z.
Proof. reflexivity. Qed.

Lemma Zconst1_Td : Zconst Tdouble 1 = Float.of_bits (Int64.repr 4607182418800017408).
Proof. apply Binary.B2FF_inj. vm_compute. reflexivity. Qed.
