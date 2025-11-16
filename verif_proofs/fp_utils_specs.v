Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.

Require Import fp_utils.

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

(* The function returns an int, and that int is `1` iff `is_finite x` 
is true; otherwise it's `0`. And it doesn't touch memory.*)
Definition isnormal_mul_double_spec := 
  DECLARE _isnormal_mul_double
  WITH x : ftype Tdouble, y : ftype Tdouble 
  PRE [ tdouble, tdouble ] (* c lang types *)
    PROP()
    PARAMS ( Vfloat x; Vfloat y ) (* functions params *)
    SEP() (* preds on mem *)
  POST [ tint ]
    EX b : bool,
    PROP(b = true <-> bpow Zaux.radix2 (emin + 2 * fprec Tdouble - 1) <= Rabs (FT2R x * FT2R y))
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP().