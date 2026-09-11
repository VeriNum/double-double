(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.

Require Import fp_utils op_defs DDConds common.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Definition isfinite_double_spec :=
  DECLARE _isfinite_double
  WITH x : ftype Tdouble
  PRE [ tdouble ]
    PROP()
    PARAMS ( Vfloat x )
    SEP()
  POST [ tint ]
    EX b : bool,
    PROP(b = true <-> is_finite x = true)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP().

Notation emin := (SpecFloat.emin (fprec Tdouble) (femax Tdouble)).

Definition fast2_mult_exact_check_spec :=
  DECLARE _fast2_mult_exact_check
  WITH x : ftype Tdouble, y : ftype Tdouble
  PRE [ tdouble, tdouble ]
    PROP()
    PARAMS ( Vfloat x; Vfloat y )
    SEP()
  POST [ tint ]
    EX b : bool,
    PROP(b = true -> Fast2Mult_exact_cond x y)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP().

Definition Fast2Sum_magnitude_order_cond (a b : ftype Tdouble) : Prop :=
  is_finite (BPLUS a b) = true /\ (Rabs (FT2R b) <= Rabs (FT2R a))%R.

Definition fast2_sum_magnitude_order_check_spec :=
  DECLARE _fast2_sum_magnitude_order_check
  WITH x : ftype Tdouble, y : ftype Tdouble
  PRE [ tdouble, tdouble ]
    PROP()
    PARAMS ( Vfloat x; Vfloat y )
    SEP()
  POST [ tint ]
    EX b : bool,
    PROP(b = true -> Fast2Sum_magnitude_order_cond x y)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP().

Definition dword := Tstruct _dword noattr.

Definition f2val (pq : ftype Tdouble * ftype Tdouble) : reptype dword :=
  (Vfloat (fst pq), Vfloat (snd pq)).

Definition isfinite_dword_spec :=
  DECLARE _isfinite_dword
  WITH x : val, value : ftype Tdouble * ftype Tdouble
  PRE [ tptr dword ]
    PROP()
    PARAMS (x)
    SEP(data_at Tsh dword (f2val value) x)
  POST [ tint ]
    EX b : bool,
    PROP(b = true -> is_finite_p value)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP(data_at Tsh dword (f2val value) x).

Definition dw_plus_fp_weak_precond_check_spec :=
  DECLARE _dw_plus_fp_weak_precond_check
  WITH x : val,
       value : ftype Tdouble * ftype Tdouble,
       y : ftype Tdouble
  PRE [ tptr dword, tdouble ]
    PROP()
    PARAMS (x; Vfloat y)
    SEP(data_at Tsh dword (f2val value) x)
  POST [ tint ]
    EX b : bool,
    PROP(b = true -> DWPlusFP_weak_precond (fst value) (snd value) y)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP(data_at Tsh dword (f2val value) x).

Definition dw_plus_dw_strong_precond_check_spec :=
  DECLARE _dw_plus_dw_strong_precond_check
  WITH x : val, y : val,
       xh : ftype Tdouble * ftype Tdouble,
       yh : ftype Tdouble * ftype Tdouble
  PRE [ tptr dword, tptr dword ]
    PROP()
    PARAMS ( x; y )
    SEP( data_at Tsh dword (f2val xh) x;
         data_at Tsh dword (f2val yh) y )
  POST [ tint ]
    EX b : bool,
    PROP(b = true ->
         DWPlusDW_strong_precond (fst xh) (snd xh) (fst yh) (snd yh))
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP( data_at Tsh dword (f2val xh) x;
         data_at Tsh dword (f2val yh) y ).

Definition dw_plus_dw_weak_precond_check_spec :=
  DECLARE _dw_plus_dw_weak_precond_check
  WITH x : val, y : val,
       xh : ftype Tdouble * ftype Tdouble,
       yh : ftype Tdouble * ftype Tdouble
  PRE [ tptr dword, tptr dword ]
    PROP()
    PARAMS (x; y)
    SEP(data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y)
  POST [ tint ]
    EX b : bool,
    PROP(b = true ->
         DWPlusDW_weak_precond (fst xh) (snd xh) (fst yh) (snd yh))
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP(data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y).

Definition dw_plus_fp_strong_precond_check_spec :=
  DECLARE _dw_plus_fp_strong_precond_check
  WITH x : val,
       xh : ftype Tdouble * ftype Tdouble,
       y  : ftype Tdouble
  PRE [ tptr dword, tdouble ]
    PROP()
    PARAMS ( x; Vfloat y )
    SEP( data_at Tsh dword (f2val xh) x )
  POST [ tint ]
    EX b : bool,
    PROP(b = true ->
         DWPlusFP_strong_precond (fst xh) (snd xh) y)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP( data_at Tsh dword (f2val xh) x ).

Definition dw_div_fp_strong_check_spec :=
  DECLARE _dw_div_fp_strong_check
  WITH x : val,
       xh : ftype Tdouble * ftype Tdouble,
       y  : ftype Tdouble
  PRE [ tptr dword, tdouble ]
    PROP()
    PARAMS ( x; Vfloat y )
    SEP( data_at Tsh dword (f2val xh) x )
  POST [ tint ]
    EX b : bool,
    PROP(b = true ->
         DWDivFP_strong_precond (fst xh) (snd xh) y)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP( data_at Tsh dword (f2val xh) x ).

Definition dw_div_fp_weak_check_spec :=
  DECLARE _dw_div_fp_weak_check
  WITH x : val,
       xh : ftype Tdouble * ftype Tdouble,
       y  : ftype Tdouble
  PRE [ tptr dword, tdouble ]
    PROP() PARAMS (x; Vfloat y)
    SEP(data_at Tsh dword (f2val xh) x)
  POST [ tint ]
    EX b : bool,
    PROP(b = true ->
         is_finite (fst xh) = true /\
         is_finite (snd xh) = true /\
         is_finite y = true /\
         DWDivFP_weak_precond (fst xh) (snd xh) y)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP(data_at Tsh dword (f2val xh) x).

Definition dw_times_fp_strong_precond_check_spec :=
  DECLARE _dw_times_fp_strong_precond_check
  WITH x : val,
       xh : ftype Tdouble * ftype Tdouble,
       y  : ftype Tdouble
  PRE [ tptr dword, tdouble ]
    PROP()
    PARAMS ( x; Vfloat y )
    SEP( data_at Tsh dword (f2val xh) x )
  POST [ tint ]
    EX b : bool,
    PROP(b = true ->
         DWTimesFP_strong_precond (fst xh) (snd xh) y)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP( data_at Tsh dword (f2val xh) x ).

Definition dw_times_fp_weak_precond_check_spec :=
  DECLARE _dw_times_fp_weak_precond_check
  WITH x : val,
       xh : ftype Tdouble * ftype Tdouble,
       y  : ftype Tdouble
  PRE [ tptr dword, tdouble ]
    PROP() PARAMS (x; Vfloat y)
    SEP(data_at Tsh dword (f2val xh) x)
  POST [ tint ]
    EX b : bool,
    PROP(b = true -> DWTimesFP_weak_precond (fst xh) (snd xh) y)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP(data_at Tsh dword (f2val xh) x).

Definition dw_times_dw_strong_precond_check_spec :=
  DECLARE _dw_times_dw_strong_precond_check
  WITH x : val, y : val,
       xh : ftype Tdouble * ftype Tdouble,
       yh : ftype Tdouble * ftype Tdouble
  PRE [ tptr dword, tptr dword ]
    PROP()
    PARAMS ( x; y )
    SEP( data_at Tsh dword (f2val xh) x;
         data_at Tsh dword (f2val yh) y )
  POST [ tint ]
    EX b : bool,
    PROP(b = true ->
         DWTimesDW_strong_precond (fst xh) (snd xh) (fst yh) (snd yh))
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP( data_at Tsh dword (f2val xh) x;
         data_at Tsh dword (f2val yh) y ).

Definition dw_times_dw_weak_precond_check_spec :=
  DECLARE _dw_times_dw_weak_precond_check
  WITH x : val, y : val,
       xh : ftype Tdouble * ftype Tdouble,
       yh : ftype Tdouble * ftype Tdouble
  PRE [ tptr dword, tptr dword ]
    PROP() PARAMS (x; y)
    SEP(data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y)
  POST [ tint ]
    EX b : bool,
    PROP(b = true ->
         DWTimesDW_weak_precond (fst xh) (snd xh) (fst yh) (snd yh))
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP(data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y).

Definition dw_div_dw_strong_precond_check_spec :=
  DECLARE _dw_div_dw_strong_precond_check
  WITH x : val, y : val,
       xh : ftype Tdouble * ftype Tdouble,
       yh : ftype Tdouble * ftype Tdouble
  PRE [ tptr dword, tptr dword ]
    PROP()
    PARAMS ( x; y )
    SEP( data_at Tsh dword (f2val xh) x;
         data_at Tsh dword (f2val yh) y )
  POST [ tint ]
    EX b : bool,
    PROP(b = true ->
         DWDivDW_strong_precond (fst xh) (snd xh) (fst yh) (snd yh))
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP( data_at Tsh dword (f2val xh) x;
         data_at Tsh dword (f2val yh) y ).

Definition dw_div_dw_weak_precond_check_spec :=
  DECLARE _dw_div_dw_weak_precond_check
  WITH x : val, y : val,
       xh : ftype Tdouble * ftype Tdouble,
       yh : ftype Tdouble * ftype Tdouble
  PRE [ tptr dword, tptr dword ]
    PROP() PARAMS (x; y)
    SEP(data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y)
  POST [ tint ]
    EX b : bool,
    PROP(b = true ->
         DWDivDW_weak_precond (fst xh) (snd xh) (fst yh) (snd yh))
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP(data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y).
