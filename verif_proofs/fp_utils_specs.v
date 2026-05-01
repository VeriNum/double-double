(* Copyright 2025 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.

Require Import fp_utils op_defs DDModels.

(* The function returns an int, and that int is `1` iff `is_finite x` 
is true; otherwise it's `0`. And it doesn't touch memory.*)
Definition isfinite_double_spec := 
  DECLARE _isfinite_double
  WITH x : ftype Tdouble 
  PRE [ tdouble ] (* c lang types *)
    PROP()
    PARAMS ( Vfloat x ) (* functions params *)
    SEP() (* preds on mem *)
  POST [ tint ]
    EX b : bool,
    PROP(b = true <-> is_finite x = true)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP().


Notation emin := (SpecFloat.emin (fprec Tdouble) (femax Tdouble)).

Definition MulResultIsSafeForFast2Mult (a b : ftype Tdouble) : Prop :=
  Fast2Mult_cond a b.

(* The function returns an int, and that int is `1` iff `is_finite x` 
is true; otherwise it's `0`. And it doesn't touch memory.*)
Definition fast2_mult_check_spec := 
  DECLARE _fast2_mult_check
  WITH x : ftype Tdouble, y : ftype Tdouble 
  PRE [ tdouble, tdouble ] (* c lang types *)
    PROP()
    PARAMS ( Vfloat x; Vfloat y ) (* functions params *)
    SEP() (* preds on mem *)
  POST [ tint ]
    EX b : bool,
    PROP(b = true -> MulResultIsSafeForFast2Mult x y)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP().


Definition SumResultIsSafeForTwoSum (a b : ftype Tdouble) : Prop :=
  TwoSum_cond a b.

Definition two_sum_check_spec :=
  DECLARE _two_sum_check
  WITH x : ftype Tdouble, y : ftype Tdouble
  PRE [ tdouble, tdouble ]
    PROP()
    PARAMS ( Vfloat x; Vfloat y )
    SEP()
  POST [ tint ]
    EX b : bool,
    PROP(b = true -> SumResultIsSafeForTwoSum x y)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP().

Definition SumResultIsSafeForFast2Sum (a b : ftype Tdouble) : Prop :=
  Fast2Sum_cond a b.

Definition fast2_sum_check_spec :=
  DECLARE _fast2_sum_check
  WITH x : ftype Tdouble, y : ftype Tdouble
  PRE [ tdouble, tdouble ]
    PROP()
    PARAMS ( Vfloat x; Vfloat y )
    SEP()
  POST [ tint ]
    EX b : bool,
    PROP(b = true -> SumResultIsSafeForFast2Sum x y)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP().

Definition MulResultIsSafeForFast2Mult2 (a b c : ftype Tdouble) : Prop :=
  Fast2Mult_cond2 a b c.

Definition fast2_mult_check2_spec := 
  DECLARE _fast2_mult_check2
  WITH x : ftype Tdouble, y : ftype Tdouble, z : ftype Tdouble  
  PRE [ tdouble, tdouble, tdouble ] (* c lang types *)
    PROP()
    PARAMS ( Vfloat x; Vfloat y; Vfloat z ) (* functions params *)
    SEP() (* preds on mem *)
  POST [ tint ]
    EX b : bool,
    PROP(b = true -> MulResultIsSafeForFast2Mult2 x y z)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP().