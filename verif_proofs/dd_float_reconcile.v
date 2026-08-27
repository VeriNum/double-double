(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Leaf reconciliation lemmas: at Tdouble the VCFloat B operators (from
   op_defs / FPCore) are definitionally the CompCert Float operators that the
   C code and `forward` produce.  Each converts cheaply (a single op, no
   nesting).

   These let a composite double word body proof rewrite the whole functional model spec
   term (built from BDIV/BMULT/BOPP/BFMA/Zconst) into the *exact* CompCert float
   composition the forward_call cascade stored, so the two `data_at` values
   become syntactically identical and the closing `entailer!!` needs NO
   whole term conversion between B and CompCert floating-point operations -- that conversion over the deeply
   nested, unshared term does not terminate in practice (>10h). *)

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

(* 1.0 = 0x3FF0000000000000; Zconst and of_bits agree up to an opaque proof
   term for a bound, so this is proved without axioms via B2FF injectivity. *)
Lemma Zconst1_Td : Zconst Tdouble 1 = Float.of_bits (Int64.repr 4607182418800017408).
Proof. apply Binary.B2FF_inj. vm_compute. reflexivity. Qed.
