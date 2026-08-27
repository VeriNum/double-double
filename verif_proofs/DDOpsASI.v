(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Abstract Spec Interface (ASI) for the double-word *operations* translation
   unit (dd_ops.c / verif_objs/dd_ops.v).  Every op / guarded wrapper funspec is
   DECLAREd here exactly once, under the dd_ops program's CompSpecs, so that the
   body proof file (verif_dd_ops.v) and the VSU builder (Ops_VSU.v) reference
   the *same* funspec terms.  The check_* funspecs mirror fp_utils_specs.v
   verbatim (same WITH/PRE/POST) so the ops VSU's Imports match the checks VSU's
   Exports at link time.  fma is provided by MathASI; exit is a libc external. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.

Require Import VSTlib.spec_math.   (* Provides fma_spec. *)
Require Import DDConds common real_extras.
Require Import DD.accuracy_proofs.dw_opps.DWPlusFP_relative_acc.
Require Import DD.accuracy_proofs.dw_opps.DWPlusDW_relative_acc.
Require Import DD.accuracy_proofs.dw_opps.DWMulFP_mixed_acc.
Require Import DD.accuracy_proofs.dw_opps.DWMulDW_mixed_acc.
Require Import DD.accuracy_proofs.dw_opps.DWDivFP_mixed_acc.
Require Import DD.accuracy_proofs.dw_opps.DWDivDW_mixed_acc.
Require Import DD.verif_proofs.verif_objs.dd_ops.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope logic.

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec Tdouble) (femax Tdouble))).

Definition dword := Tstruct _dword noattr.

Definition f2val (pq: ftype Tdouble * ftype Tdouble) : reptype dword :=
 (Vfloat (fst pq), Vfloat (snd pq)).

(* ======================================================================== *)
(*  Leaf primitives                                                          *)
(* ======================================================================== *)

Definition two_sum_spec :=
  DECLARE _two_sum
  WITH s: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr dword, tdouble, tdouble ]
    PROP() PARAMS (s; Vfloat a; Vfloat b) SEP(data_at_ Tsh dword s)
  POST [ tvoid ]
    PROP() RETURN() SEP(data_at Tsh dword (f2val (TwoSumF a b)) s).

Definition fast_2sum_spec :=
  DECLARE _fast_2sum
  WITH s: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr dword, tdouble, tdouble ]
    PROP() PARAMS (s; Vfloat a; Vfloat b) SEP(data_at_ Tsh dword s)
  POST [ tvoid ]
    PROP() RETURN() SEP(data_at Tsh dword (f2val (Fast2Sum a b)) s).

Definition fast_2mult_spec :=
  DECLARE _fast_2mult
  WITH s: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr dword, tdouble, tdouble ]
    PROP() PARAMS (s; Vfloat a; Vfloat b) SEP(data_at_ Tsh dword s)
  POST [ tvoid ]
    PROP() RETURN() SEP(data_at Tsh dword (f2val (Fast2Mult a b)) s).

(* ======================================================================== *)
(*  Composite operations                                                     *)
(* ======================================================================== *)

Definition dw_plus_fp_spec :=
  DECLARE _dw_plus_fp
  WITH s: val, x : val,
      xh : ftype Tdouble * ftype Tdouble, y : ftype Tdouble
  PRE [tptr dword, tptr dword, tdouble ]
    PROP()
    PARAMS (s; x; Vfloat y)
    SEP(data_at_ Tsh dword s;
          data_at Tsh dword (f2val xh) x)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh dword (f2val (DWPlusFP (fst xh) (snd xh) y)) s;
        data_at Tsh dword (f2val xh) x).

Definition dw_plus_dw2_spec :=
  DECLARE _dw_plus_dw2
  WITH s: val, x : val, y: val,
      xh : ftype Tdouble * ftype Tdouble,
      yh : ftype Tdouble * ftype Tdouble
  PRE [tptr dword, tptr dword, tptr dword ]
    PROP()
    PARAMS (s; x; y)
    SEP(data_at_ Tsh dword s;
          data_at Tsh dword (f2val xh) x;
          data_at Tsh dword (f2val yh) y)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh dword
          (f2val (AccurateDWPlusDW (fst xh) (snd xh) (fst yh) (snd yh))) s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y).

Definition dw_mult_fp9_spec :=
  DECLARE _dw_mult_fp9
  WITH s: val, x : val,
      xh : ftype Tdouble * ftype Tdouble, y : ftype Tdouble
  PRE [tptr dword, tptr dword, tdouble ]
    PROP()
    PARAMS (s; x; Vfloat y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh dword (f2val (DWTimesFP3 (fst xh) (snd xh) y)) s;
        data_at Tsh dword (f2val xh) x).

Definition dw_mult_dw12_spec := 
  DECLARE _dw_mult_dw12
  WITH s: val, x : val, y: val,
      xh : ftype Tdouble * ftype Tdouble, 
      yh : ftype Tdouble * ftype Tdouble
  PRE [tptr dword, tptr dword, tptr dword ] (* c lang types *)
    PROP()
    PARAMS (s; x; y)
    SEP(data_at_ Tsh dword s; 
          data_at Tsh dword (f2val xh) x;
          data_at Tsh dword (f2val yh) y)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh dword 
          (f2val (DWTimesDW3 (fst xh) (snd xh) (fst yh) (snd yh))) s; 
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y). 

Definition dw_div_dw18_spec :=
  DECLARE _dw_div_dw18
  WITH s: val, x : val, y: val,
      xh : ftype Tdouble * ftype Tdouble,
      yh : ftype Tdouble * ftype Tdouble
  PRE [tptr dword, tptr dword, tptr dword ]
    PROP()
    PARAMS (s; x; y)
    SEP(data_at_ Tsh dword s;
          data_at Tsh dword (f2val xh) x;
          data_at Tsh dword (f2val yh) y)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh dword
          (f2val (DWDivDW3 (fst xh) (snd xh) (fst yh) (snd yh))) s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y).

Definition dw_div_fp15_spec :=
  DECLARE _dw_div_fp15
  WITH s: val, x : val,
      xh : ftype Tdouble * ftype Tdouble, y : ftype Tdouble
  PRE [tptr dword, tptr dword, tdouble ]
    PROP()
    PARAMS (s; x; Vfloat y)
    SEP(data_at_ Tsh dword s;
          data_at Tsh dword (f2val xh) x)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh dword (f2val (DWDivFP3 (fst xh) (snd xh) y)) s;
        data_at Tsh dword (f2val xh) x).


(* ======================================================================== *)
(*  Guarded wrappers (exported public API)                                   *)
(* ======================================================================== *)

Definition two_sum_guarded_spec :=
  DECLARE _two_sum_guarded
  WITH p: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr dword, tdouble, tdouble ]
    PROP() PARAMS (p; Vfloat a; Vfloat b) SEP(data_at_ Tsh dword p)
  POST [ tvoid ]
    PROP((Rabs (FT2R (TwoSumF_err a b)) <= / 2 * ulp (FT2R a + FT2R b))%R)
    RETURN()
    SEP(data_at Tsh dword (f2val (TwoSumF a b)) p).

Definition fast_2sum_guarded_spec :=
  DECLARE _fast_2sum_guarded
  WITH p: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr dword, tdouble, tdouble ]
    PROP() PARAMS (p; Vfloat a; Vfloat b) SEP(data_at_ Tsh dword p)
  POST [ tvoid ]
    PROP((Rabs (FT2R (Fast2Sum_err a b)) <= / 2 * ulp (FT2R a + FT2R b))%R)
    RETURN()
    SEP(data_at Tsh dword (f2val (Fast2Sum a b)) p).

(* Tier A full Fast2Mult wrapper: error term bound, exact reconstruction, and
   output double-word property. *)
Definition fast_2mult_guarded_spec :=
  DECLARE _fast_2mult_guarded
  WITH st: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr dword, tdouble, tdouble ]
    PROP() PARAMS (st; Vfloat a; Vfloat b) SEP(data_at_ Tsh dword st)
  POST [ tvoid ]
    PROP((Rabs (FT2R (Fast2Mult_err a b)) <= / 2 * ulp (FT2R a * FT2R b))%R
         /\ (FT2R (Fast2Mult_mul a b) + FT2R (Fast2Mult_err a b) = FT2R a * FT2R b)%R
         /\ double_word_prop (Fast2Mult_mul a b) (Fast2Mult_err a b))
    RETURN()
    SEP(data_at Tsh dword (f2val (Fast2Mult a b)) st).

(* The Tier B wrapper exposes a bound on the returned error component.  Its
   finiteness guard does not support exact reconstruction or prove that the
   output is a valid double-word. *)
Definition fast_2mult_acc_guarded_spec :=
  DECLARE _fast_2mult_acc_guarded
  WITH st: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr dword, tdouble, tdouble ]
    PROP() PARAMS (st; Vfloat a; Vfloat b) SEP(data_at_ Tsh dword st)
  POST [ tvoid ]
    PROP((Rabs (FT2R (Fast2Mult_err a b)) <= / 2 * ulp (FT2R a * FT2R b))%R)
    RETURN()
    SEP(data_at Tsh dword (f2val (Fast2Mult a b)) st).

Definition dw_plus_fp_guarded_spec :=
  DECLARE _dw_plus_fp_guarded
  WITH s: val, x: val,
       xh: ftype Tdouble * ftype Tdouble,
       y : ftype Tdouble
  PRE [ tptr dword, tptr dword, tdouble ]
    PROP()
    PARAMS (s; x; Vfloat y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x)
  POST [ tvoid ]
    PROP(DWPlusFP_relative_guarantee (fst xh) (snd xh) y)
    RETURN()
    SEP(data_at Tsh dword (f2val (DWPlusFP (fst xh) (snd xh) y)) s;
        data_at Tsh dword (f2val xh) x).

Definition dw_plus_dw2_guarded_spec :=
  DECLARE _dw_plus_dw2_guarded
  WITH s: val, x: val, y: val,
       xh: ftype Tdouble * ftype Tdouble,
       yh: ftype Tdouble * ftype Tdouble
  PRE [ tptr dword, tptr dword, tptr dword ]
    PROP()
    PARAMS (s; x; y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y)
  POST [ tvoid ]
    PROP(DWPlusDW_relative_guarantee
           (fst xh) (snd xh) (fst yh) (snd yh))
    RETURN()
    SEP(data_at Tsh dword
          (f2val (AccurateDWPlusDW (fst xh) (snd xh) (fst yh) (snd yh))) s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y).

(* Guarded DW by FP multiplication exports
   [DWTimesFP_mixed_guarantee_from_safe_input_cond].  Its bound is
   [2u^2|P| + 2.51*eta] and includes output validity.  The runtime check permits
   the [Fast2Mult] underflow gap, unlike the pure relative interface. *)
Definition dw_mult_fp9_guarded_spec :=
  DECLARE _dw_mult_fp9_guarded
  WITH s: val, x: val,
       xh: ftype Tdouble * ftype Tdouble,
       y : ftype Tdouble
  PRE [ tptr dword, tptr dword, tdouble ]
    PROP()
    PARAMS (s; x; Vfloat y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x)
  POST [ tvoid ]
    PROP(DWTimesFP_mixed_guarantee (fst xh) (snd xh) y)
    RETURN()
    SEP(data_at Tsh dword (f2val (DWTimesFP3 (fst xh) (snd xh) y)) s;
        data_at Tsh dword (f2val xh) x).

(* Guarded DW by DW multiplication exports
   [DWTimesDW_mixed_guarantee_from_safe_input_cond].  Its bound is
   [4u^2|P| + 2.5*eta] and includes output validity.  The runtime check permits
   the [Fast2Mult] underflow gap.  In that gap, the final sum lies on the
   FLT/FIX lattice and [Fast2Sum] remains exact. *)
Definition dw_mult_dw12_guarded_spec :=
  DECLARE _dw_mult_dw12_guarded
  WITH s: val, x: val, y: val,
       xh: ftype Tdouble * ftype Tdouble,
       yh: ftype Tdouble * ftype Tdouble
  PRE [ tptr dword, tptr dword, tptr dword ]
    PROP()
    PARAMS (s; x; y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y)
  POST [ tvoid ]
    PROP(DWTimesDW_mixed_guarantee
           (fst xh) (snd xh) (fst yh) (snd yh))
    RETURN()
    SEP(data_at Tsh dword
          (f2val (DWTimesDW3 (fst xh) (snd xh) (fst yh) (snd yh))) s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y).

(* Guarded DW by FP division exports
   [DWDivFP_mixed_guarantee_from_safe_input_cond].  Its bound is
   [3u^2|Q| + eta] and includes output validity.  The condition has no lower
   quotient bound, so it admits subnormal quotients.  The pure relative theorem
   requires normality facts about computed nodes and is not exported here. *)
Definition dw_div_fp15_guarded_spec :=
  DECLARE _dw_div_fp15_guarded
  WITH s: val, x: val,
       xh: ftype Tdouble * ftype Tdouble,
       y : ftype Tdouble
  PRE [ tptr dword, tptr dword, tdouble ]
    PROP()
    PARAMS (s; x; Vfloat y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x)
  POST [ tvoid ]
    PROP(DWDivFP_mixed_guarantee (fst xh) (snd xh) y)
    RETURN()
    SEP(data_at Tsh dword (f2val (DWDivFP3 (fst xh) (snd xh) y)) s;
        data_at Tsh dword (f2val xh) x).

(* Guarded DW by DW division exports
   [DWDivDW_mixed_guarantee_from_safe_input_cond].  Its bound is
   [9.8u^2|Q| + 2.5*eta] and includes output validity.  The named guarantee
   keeps repeated occurrences of the large [DWDivDW3] term out of the VST
   specification.  The runtime check establishes the safe input condition;
   the format condition [14 <= fprec Tdouble] is discharged in the body proof.
   The pure relative theorem requires normality facts about computed nodes. *)
Definition dw_div_dw18_guarded_spec :=
  DECLARE _dw_div_dw18_guarded
  WITH s: val, x: val, y: val,
       xh: ftype Tdouble * ftype Tdouble,
       yh: ftype Tdouble * ftype Tdouble
  PRE [ tptr dword, tptr dword, tptr dword ]
    PROP()
    PARAMS (s; x; y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y)
  POST [ tvoid ]
    PROP(DWDivDW_mixed_guarantee (fst xh) (snd xh) (fst yh) (snd yh))
    RETURN()
    SEP(data_at Tsh dword
          (f2val (DWDivDW3 (fst xh) (snd xh) (fst yh) (snd yh))) s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y).

(* ======================================================================== *)
(*  Imported check specs (mirror fp_utils_specs.v verbatim)                  *)
(* ======================================================================== *)

(* Copy of fp_utils_specs.SumResultIsSafeForFast2Sum (a Prop independent of CompSpecs);
   defined here to avoid importing fp_utils_specs (which would clash on dword /
   f2val / the check spec names and bring a second CompSpecs into scope).
   Convertible to the original, so the link's funspec match still succeeds. *)
Definition SumResultIsSafeForFast2Sum (a b : ftype Tdouble) : Prop :=
  is_finite (BPLUS a b) = true /\ (Rabs (FT2R b) <= Rabs (FT2R a))%R.

Definition two_sum_check_spec :=
  DECLARE _two_sum_check
  WITH x : ftype Tdouble, y : ftype Tdouble
  PRE [ tdouble, tdouble ]
    PROP() PARAMS ( Vfloat x; Vfloat y ) SEP()
  POST [ tint ]
    EX b : bool,
    PROP(b = true -> TwoSum_exact_cond x y)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP().

Definition fast2_sum_check_spec :=
  DECLARE _fast2_sum_check
  WITH x : ftype Tdouble, y : ftype Tdouble
  PRE [ tdouble, tdouble ]
    PROP() PARAMS ( Vfloat x; Vfloat y ) SEP()
  POST [ tint ]
    EX b : bool,
    PROP(b = true -> SumResultIsSafeForFast2Sum x y)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP().

Definition fast2_mult_check_spec :=
  DECLARE _fast2_mult_check
  WITH x : ftype Tdouble, y : ftype Tdouble
  PRE [ tdouble, tdouble ]
    PROP() PARAMS ( Vfloat x; Vfloat y ) SEP()
  POST [ tint ]
    EX b : bool,
    PROP(b = true -> Fast2Mult_exact_cond x y)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP().

(* This Tier B check confirms that the rounded product is finite and therefore
   certifies the weaker Fast2Mult_acc_only_cond.  Mirrors
   fp_utils_specs.fast2_mult_acc_check_spec. *)
Definition fast2_mult_acc_check_spec :=
  DECLARE _fast2_mult_acc_check
  WITH x : ftype Tdouble, y : ftype Tdouble
  PRE [ tdouble, tdouble ]
    PROP() PARAMS ( Vfloat x; Vfloat y ) SEP()
  POST [ tint ]
    EX b : bool,
    PROP(b = true -> Fast2Mult_acc_only_cond x y)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP().

Definition dw_plus_fp_check_spec :=
  DECLARE _dw_plus_fp_check
  WITH x : val,
       xh : ftype Tdouble * ftype Tdouble,
       y  : ftype Tdouble
  PRE [ tptr dword, tdouble ]
    PROP() PARAMS ( x; Vfloat y ) SEP( data_at Tsh dword (f2val xh) x )
  POST [ tint ]
    EX b : bool,
    PROP(b = true -> DWPlusFP_safe_input_cond (fst xh) (snd xh) y)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP( data_at Tsh dword (f2val xh) x ).

Definition dw_plus_dw_check_spec :=
  DECLARE _dw_plus_dw_check
  WITH x : val, y : val,
       xh : ftype Tdouble * ftype Tdouble,
       yh : ftype Tdouble * ftype Tdouble
  PRE [ tptr dword, tptr dword ]
    PROP() PARAMS ( x; y )
    SEP( data_at Tsh dword (f2val xh) x;
         data_at Tsh dword (f2val yh) y )
  POST [ tint ]
    EX b : bool,
    PROP(b = true -> DWPlusDW_safe_input_cond (fst xh) (snd xh) (fst yh) (snd yh))
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP( data_at Tsh dword (f2val xh) x;
         data_at Tsh dword (f2val yh) y ).

Definition dw_mult_fp_check_spec :=
  DECLARE _dw_mult_fp_check
  WITH x : val,
       xh : ftype Tdouble * ftype Tdouble,
       y  : ftype Tdouble
  PRE [ tptr dword, tdouble ]
    PROP() PARAMS ( x; Vfloat y ) SEP( data_at Tsh dword (f2val xh) x )
  POST [ tint ]
    EX b : bool,
    PROP(b = true -> DWTimesFP_mixed_safe_input_cond (fst xh) (snd xh) y)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP( data_at Tsh dword (f2val xh) x ).

Definition dw_mult_dw_check_spec :=
  DECLARE _dw_mult_dw_check
  WITH x : val, y : val,
       xh : ftype Tdouble * ftype Tdouble,
       yh : ftype Tdouble * ftype Tdouble
  PRE [ tptr dword, tptr dword ]
    PROP() PARAMS ( x; y )
    SEP( data_at Tsh dword (f2val xh) x;
         data_at Tsh dword (f2val yh) y )
  POST [ tint ]
    EX b : bool,
    PROP(b = true -> DWTimesDW_mixed_safe_input_cond (fst xh) (snd xh) (fst yh) (snd yh))
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP( data_at Tsh dword (f2val xh) x;
         data_at Tsh dword (f2val yh) y ).

(* Minimal cond: no quotient floor at all; the caller gets the whole range
   mixed bound, not the normal range pure 3u^2 one.  See
   dw_div_fp15_guarded_spec above and DDConds.DWDivFP_mixed_safe_input_cond. *)
Definition dw_div_fp_check_spec :=
  DECLARE _dw_div_fp_check
  WITH x : val,
       xh : ftype Tdouble * ftype Tdouble,
       y  : ftype Tdouble
  PRE [ tptr dword, tdouble ]
    PROP() PARAMS ( x; Vfloat y ) SEP( data_at Tsh dword (f2val xh) x )
  POST [ tint ]
    EX b : bool,
    PROP(b = true -> DWDivFP_mixed_safe_input_cond (fst xh) (snd xh) y)
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP( data_at Tsh dword (f2val xh) x ).

Definition dw_div_dw_check_spec :=
  DECLARE _dw_div_dw_check
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
         DWDivDW_mixed_safe_input_cond (fst xh) (snd xh) (fst yh) (snd yh))
    RETURN (Vint (if b then Int.one else Int.zero))
    SEP( data_at Tsh dword (f2val xh) x;
         data_at Tsh dword (f2val yh) y ).

(* ======================================================================== *)
(*  libc external.                                                           *)
(* ======================================================================== *)

Definition exit_spec :=
  DECLARE _exit
  WITH code : int
  PRE [ tint ]
    PROP() PARAMS (Vint (Int.repr 1)) SEP()
  POST [ tvoid ]
    PROP(False) LOCAL() SEP().

(* ======================================================================== *)
(*  Spec groupings for the ops VSU (and its body proof Gprog)                *)
(* ======================================================================== *)

(* Externals the ops TU calls but does not define: fma (libm), exit (libc),
   and the six runtime checks (provided by the checks VSU at link time). *)
Definition Ops_Imports : funspecs :=
  [ fma_spec; exit_spec;
    two_sum_check_spec; fast2_sum_check_spec; fast2_mult_check_spec;
    fast2_mult_acc_check_spec;
    dw_plus_fp_check_spec; dw_plus_dw_check_spec; dw_mult_fp_check_spec;
    dw_mult_dw_check_spec; dw_div_fp_check_spec; dw_div_dw_check_spec ].

(* Specs of the internal functions, in dd_ops prog order. *)
Definition Ops_Internal : funspecs :=
  [ two_sum_spec; fast_2sum_spec; fast_2mult_spec;
    dw_plus_fp_spec; dw_plus_dw2_spec; dw_mult_fp9_spec;
    two_sum_guarded_spec; fast_2sum_guarded_spec; fast_2mult_guarded_spec;
    fast_2mult_acc_guarded_spec;
    dw_plus_fp_guarded_spec; dw_plus_dw2_guarded_spec; dw_mult_fp9_guarded_spec;
    dw_mult_dw12_spec; dw_mult_dw12_guarded_spec; dw_div_dw18_spec;
    dw_div_dw18_guarded_spec;
    dw_div_fp15_spec; dw_div_fp15_guarded_spec ].

(* Public API exported by the ops VSU: the nine guarded wrappers plus the
   Tier B Fast2Mult wrapper whose contract contains only the error bound. *)
Definition Ops_Exports : funspecs :=
  [ two_sum_guarded_spec; fast_2sum_guarded_spec; fast_2mult_guarded_spec;
    fast_2mult_acc_guarded_spec;
    dw_plus_fp_guarded_spec; dw_plus_dw2_guarded_spec; dw_mult_fp9_guarded_spec;
    dw_mult_dw12_guarded_spec; dw_div_fp15_guarded_spec;
    dw_div_dw18_guarded_spec ].
