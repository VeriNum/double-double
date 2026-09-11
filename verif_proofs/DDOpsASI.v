(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Abstract Spec Interface (ASI) for the double-word *operations* translation
   unit (dd_ops.c / verif_objs/dd_ops.v).  Every kernel and public wrapper funspec is
   DECLAREd here exactly once, under the dd_ops program's CompSpecs, so that the
   body proof files and the VSU builder reference the same funspec terms.
   Runtime-check funspecs are imported from [fp_utils_specs.v], their canonical
   definition site.  fma is provided by MathASI; exit is a libc external. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.

Require Import VSTlib.spec_math.   (* Provides fma_spec. *)
Require Import DDConds common real_extras.
Require Import TwoSum_acc Fast2Sum_acc.
Require Import DD.accuracy_proofs.dw_opps.DWPlusFP_relative_acc.
Require Import DD.accuracy_proofs.dw_opps.DWPlusDW_relative_acc.
Require Import DD.accuracy_proofs.dw_opps.DWTimesFP_mixed_acc.
Require Import DD.accuracy_proofs.dw_opps.DWTimesDW_mixed_acc.
Require Import DD.accuracy_proofs.dw_opps.DWDivFP_mixed_acc.
Require Import DD.accuracy_proofs.dw_opps.DWDivDW_mixed_acc.
Require Import DD.verif_proofs.verif_objs.dd_ops.
Require DD.verif_proofs.fp_utils_specs.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope logic.

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec Tdouble) (femax Tdouble))).

Definition dword := Tstruct _dword noattr.

Definition f2val (pq: ftype Tdouble * ftype Tdouble) : reptype dword :=
 (Vfloat (fst pq), Vfloat (snd pq)).

Definition weak_wrapper_status (status : int) : Prop :=
  status = Int.zero \/ status = Int.one.

Definition default_wrapper_status (status : int) : Prop :=
  status = Int.zero \/ status = Int.one \/ status = Int.repr 2.

Definition strong_wrapper_status (status : int) : Prop :=
  status = Int.zero \/ status = Int.repr 3.

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

Definition fast_2sum_kernel_spec :=
  DECLARE _fast_2sum_kernel
  WITH s: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr dword, tdouble, tdouble ]
    PROP() PARAMS (s; Vfloat a; Vfloat b) SEP(data_at_ Tsh dword s)
  POST [ tvoid ]
    PROP() RETURN() SEP(data_at Tsh dword (f2val (Fast2Sum a b)) s).

Definition fast_2mult_kernel_spec :=
  DECLARE _fast_2mult_kernel
  WITH s: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr dword, tdouble, tdouble ]
    PROP() PARAMS (s; Vfloat a; Vfloat b) SEP(data_at_ Tsh dword s)
  POST [ tvoid ]
    PROP() RETURN() SEP(data_at Tsh dword (f2val (Fast2Mult a b)) s).

(* ======================================================================== *)
(*  Composite operations                                                     *)
(* ======================================================================== *)

Definition dw_plus_fp_kernel_spec :=
  DECLARE _dw_plus_fp_kernel
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

Definition dw_plus_fp_spec :=
  DECLARE _dw_plus_fp
  WITH s: val, x : val,
      xh : ftype Tdouble * ftype Tdouble, y : ftype Tdouble
  PRE [tptr dword, tptr dword, tdouble ]
    PROP()
    PARAMS (s; x; Vfloat y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x)
  POST [ tint ]
    EX status : int,
    PROP(default_wrapper_status status;
         status = Int.zero ->
           DWPlusFP_relative_guarantee (fst xh) (snd xh) y)
    RETURN(Vint status)
    SEP((if Int.eq status Int.zero
         then data_at Tsh dword
                (f2val (DWPlusFP (fst xh) (snd xh) y)) s
         else data_at_ Tsh dword s);
        data_at Tsh dword (f2val xh) x).

Definition dw_plus_fp_strong_spec :=
  DECLARE _dw_plus_fp_strong
  WITH s: val, x : val,
      xh : ftype Tdouble * ftype Tdouble, y : ftype Tdouble
  PRE [tptr dword, tptr dword, tdouble ]
    PROP()
    PARAMS (s; x; Vfloat y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x)
  POST [ tint ]
    EX status : int,
    PROP(strong_wrapper_status status;
         status = Int.zero ->
           DWPlusFP_relative_guarantee (fst xh) (snd xh) y)
    RETURN(Vint status)
    SEP((if Int.eq status Int.zero
         then data_at Tsh dword
                (f2val (DWPlusFP (fst xh) (snd xh) y)) s
         else data_at_ Tsh dword s);
        data_at Tsh dword (f2val xh) x).

Definition dw_plus_dw_kernel_spec :=
  DECLARE _dw_plus_dw_kernel
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
          (f2val (DWPlusDW (fst xh) (snd xh) (fst yh) (snd yh))) s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y).

Definition dw_times_fp_kernel_spec :=
  DECLARE _dw_times_fp_kernel
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
    SEP(data_at Tsh dword (f2val (DWTimesFP (fst xh) (snd xh) y)) s;
        data_at Tsh dword (f2val xh) x).

Definition dw_times_dw_kernel_spec :=
  DECLARE _dw_times_dw_kernel
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
          (f2val (DWTimesDW (fst xh) (snd xh) (fst yh) (snd yh))) s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y). 

Definition dw_div_dw_kernel_spec :=
  DECLARE _dw_div_dw_kernel
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
          (f2val (DWDivDW (fst xh) (snd xh) (fst yh) (snd yh))) s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y).

Definition dw_div_fp_kernel_spec :=
  DECLARE _dw_div_fp_kernel
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
    SEP(data_at Tsh dword (f2val (DWDivFP (fst xh) (snd xh) y)) s;
        data_at Tsh dword (f2val xh) x).


(* ======================================================================== *)
(*  Public wrappers                                                          *)
(* ======================================================================== *)

Definition fast_2sum_spec :=
  DECLARE _fast_2sum
  WITH p: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr dword, tdouble, tdouble ]
    PROP() PARAMS (p; Vfloat a; Vfloat b) SEP(data_at_ Tsh dword p)
  POST [ tint ]
    EX status : int,
    PROP(weak_wrapper_status status;
         status = Int.zero -> Fast2Sum_exact_guarantee a b)
    RETURN(Vint status)
    SEP(if Int.eq status Int.zero
        then data_at Tsh dword (f2val (Fast2Sum a b)) p
        else data_at_ Tsh dword p).

(* Tier A full Fast2Mult wrapper: error term bound, exact reconstruction, and
   output double-word property. *)
Definition fast_2mult_spec :=
  DECLARE _fast_2mult
  WITH st: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr dword, tdouble, tdouble ]
    PROP() PARAMS (st; Vfloat a; Vfloat b) SEP(data_at_ Tsh dword st)
  POST [ tint ]
    EX status : int,
    PROP(weak_wrapper_status status;
         status = Int.zero ->
           (Rabs (FT2R (Fast2Mult_err a b)) <=
              / 2 * ulp (FT2R a * FT2R b))%R /\
           (FT2R (Fast2Mult_mul a b) + FT2R (Fast2Mult_err a b) =
              FT2R a * FT2R b)%R /\
           double_word_prop (Fast2Mult_mul a b) (Fast2Mult_err a b))
    RETURN(Vint status)
    SEP(if Int.eq status Int.zero
        then data_at Tsh dword (f2val (Fast2Mult a b)) st
        else data_at_ Tsh dword st).

(* The Tier B wrapper exposes a bound on the returned error component.  Its
   finiteness guard does not support exact reconstruction or prove that the
   output is a valid double-word. *)
Definition fast_2mult_acc_spec :=
  DECLARE _fast_2mult_acc
  WITH st: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr dword, tdouble, tdouble ]
    PROP() PARAMS (st; Vfloat a; Vfloat b) SEP(data_at_ Tsh dword st)
  POST [ tvoid ]
    PROP((Rabs (FT2R (Fast2Mult_err a b)) <= / 2 * ulp (FT2R a * FT2R b))%R)
    RETURN()
    SEP(data_at Tsh dword (f2val (Fast2Mult a b)) st).

Definition dw_plus_dw_spec :=
  DECLARE _dw_plus_dw
  WITH s: val, x: val, y: val,
       xh: ftype Tdouble * ftype Tdouble,
       yh: ftype Tdouble * ftype Tdouble
  PRE [ tptr dword, tptr dword, tptr dword ]
    PROP()
    PARAMS (s; x; y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y)
  POST [ tint ]
    EX status : int,
    PROP(default_wrapper_status status;
         status = Int.zero ->
           DWPlusDW_relative_guarantee
             (fst xh) (snd xh) (fst yh) (snd yh))
    RETURN(Vint status)
    SEP((if Int.eq status Int.zero
         then data_at Tsh dword
                (f2val (DWPlusDW (fst xh) (snd xh) (fst yh) (snd yh))) s
         else data_at_ Tsh dword s);
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y).

Definition dw_plus_dw_strong_spec :=
  DECLARE _dw_plus_dw_strong
  WITH s: val, x: val, y: val,
       xh: ftype Tdouble * ftype Tdouble,
       yh: ftype Tdouble * ftype Tdouble
  PRE [ tptr dword, tptr dword, tptr dword ]
    PROP()
    PARAMS (s; x; y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y)
  POST [ tint ]
    EX status : int,
    PROP(strong_wrapper_status status;
         status = Int.zero ->
           DWPlusDW_relative_guarantee
             (fst xh) (snd xh) (fst yh) (snd yh))
    RETURN(Vint status)
    SEP((if Int.eq status Int.zero
         then data_at Tsh dword
                (f2val (DWPlusDW (fst xh) (snd xh) (fst yh) (snd yh))) s
         else data_at_ Tsh dword s);
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y).

Definition dw_times_fp_spec :=
  DECLARE _dw_times_fp
  WITH s: val, x: val,
       xh: ftype Tdouble * ftype Tdouble,
       y : ftype Tdouble
  PRE [ tptr dword, tptr dword, tdouble ]
    PROP()
    PARAMS (s; x; Vfloat y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x)
  POST [ tint ]
    EX status : int,
    PROP(default_wrapper_status status;
         status = Int.zero -> DWTimesFP_guarantee (fst xh) (snd xh) y)
    RETURN(Vint status)
    SEP((if Int.eq status Int.zero
         then data_at Tsh dword
                (f2val (DWTimesFP (fst xh) (snd xh) y)) s
         else data_at_ Tsh dword s);
        data_at Tsh dword (f2val xh) x).

Definition dw_times_fp_strong_spec :=
  DECLARE _dw_times_fp_strong
  WITH s: val, x: val,
       xh: ftype Tdouble * ftype Tdouble,
       y : ftype Tdouble
  PRE [ tptr dword, tptr dword, tdouble ]
    PROP()
    PARAMS (s; x; Vfloat y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x)
  POST [ tint ]
    EX status : int,
    PROP(strong_wrapper_status status;
         status = Int.zero -> DWTimesFP_guarantee (fst xh) (snd xh) y)
    RETURN(Vint status)
    SEP((if Int.eq status Int.zero
         then data_at Tsh dword
                (f2val (DWTimesFP (fst xh) (snd xh) y)) s
         else data_at_ Tsh dword s);
        data_at Tsh dword (f2val xh) x).

Definition dw_times_dw_spec :=
  DECLARE _dw_times_dw
  WITH s: val, x: val, y: val,
       xh: ftype Tdouble * ftype Tdouble,
       yh: ftype Tdouble * ftype Tdouble
  PRE [ tptr dword, tptr dword, tptr dword ]
    PROP()
    PARAMS (s; x; y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y)
  POST [ tint ]
    EX status : int,
    PROP(default_wrapper_status status;
         status = Int.zero ->
           DWTimesDW_guarantee (fst xh) (snd xh) (fst yh) (snd yh))
    RETURN(Vint status)
    SEP((if Int.eq status Int.zero
         then data_at Tsh dword
                (f2val (DWTimesDW (fst xh) (snd xh) (fst yh) (snd yh))) s
         else data_at_ Tsh dword s);
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y).

Definition dw_times_dw_strong_spec :=
  DECLARE _dw_times_dw_strong
  WITH s: val, x: val, y: val,
       xh: ftype Tdouble * ftype Tdouble,
       yh: ftype Tdouble * ftype Tdouble
  PRE [ tptr dword, tptr dword, tptr dword ]
    PROP()
    PARAMS (s; x; y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y)
  POST [ tint ]
    EX status : int,
    PROP(strong_wrapper_status status;
         status = Int.zero ->
           DWTimesDW_guarantee (fst xh) (snd xh) (fst yh) (snd yh))
    RETURN(Vint status)
    SEP((if Int.eq status Int.zero
         then data_at Tsh dword
                (f2val (DWTimesDW (fst xh) (snd xh) (fst yh) (snd yh))) s
         else data_at_ Tsh dword s);
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y).

Definition dw_div_fp_spec :=
  DECLARE _dw_div_fp
  WITH s: val, x: val,
       xh: ftype Tdouble * ftype Tdouble,
       y : ftype Tdouble
  PRE [ tptr dword, tptr dword, tdouble ]
    PROP()
    PARAMS (s; x; Vfloat y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x)
  POST [ tint ]
    EX status : int,
    PROP(default_wrapper_status status;
         status = Int.zero -> DWDivFP_guarantee (fst xh) (snd xh) y)
    RETURN(Vint status)
    SEP((if Int.eq status Int.zero
         then data_at Tsh dword
                (f2val (DWDivFP (fst xh) (snd xh) y)) s
         else data_at_ Tsh dword s);
        data_at Tsh dword (f2val xh) x).

Definition dw_div_fp_strong_spec :=
  DECLARE _dw_div_fp_strong
  WITH s: val, x: val,
       xh: ftype Tdouble * ftype Tdouble,
       y : ftype Tdouble
  PRE [ tptr dword, tptr dword, tdouble ]
    PROP()
    PARAMS (s; x; Vfloat y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x)
  POST [ tint ]
    EX status : int,
    PROP(strong_wrapper_status status;
         status = Int.zero -> DWDivFP_guarantee (fst xh) (snd xh) y)
    RETURN(Vint status)
    SEP((if Int.eq status Int.zero
         then data_at Tsh dword
                (f2val (DWDivFP (fst xh) (snd xh) y)) s
         else data_at_ Tsh dword s);
        data_at Tsh dword (f2val xh) x).

Definition dw_div_dw_spec :=
  DECLARE _dw_div_dw
  WITH s: val, x: val, y: val,
       xh: ftype Tdouble * ftype Tdouble,
       yh: ftype Tdouble * ftype Tdouble
  PRE [ tptr dword, tptr dword, tptr dword ]
    PROP()
    PARAMS (s; x; y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y)
  POST [ tint ]
    EX status : int,
    PROP(default_wrapper_status status;
         status = Int.zero ->
           DWDivDW_guarantee (fst xh) (snd xh) (fst yh) (snd yh))
    RETURN(Vint status)
    SEP((if Int.eq status Int.zero
         then data_at Tsh dword
                (f2val (DWDivDW (fst xh) (snd xh) (fst yh) (snd yh))) s
         else data_at_ Tsh dword s);
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y).

Definition dw_div_dw_strong_spec :=
  DECLARE _dw_div_dw_strong
  WITH s: val, x: val, y: val,
       xh: ftype Tdouble * ftype Tdouble,
       yh: ftype Tdouble * ftype Tdouble
  PRE [ tptr dword, tptr dword, tptr dword ]
    PROP()
    PARAMS (s; x; y)
    SEP(data_at_ Tsh dword s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y)
  POST [ tint ]
    EX status : int,
    PROP(strong_wrapper_status status;
         status = Int.zero ->
           DWDivDW_guarantee (fst xh) (snd xh) (fst yh) (snd yh))
    RETURN(Vint status)
    SEP((if Int.eq status Int.zero
         then data_at Tsh dword
                (f2val (DWDivDW (fst xh) (snd xh) (fst yh) (snd yh))) s
         else data_at_ Tsh dword s);
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y).

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

(* Externals the ops TU calls but does not define: fma, exit, and the runtime
   checks provided by the checks VSU at link time. *)
Definition Ops_Imports : funspecs :=
  [ fma_spec; exit_spec;
    fp_utils_specs.fast2_sum_magnitude_order_check_spec;
    fp_utils_specs.fast2_mult_exact_check_spec;
    fp_utils_specs.fast2_mult_product_finite_check_spec;
    fp_utils_specs.isfinite_dword_spec;
    fp_utils_specs.dw_plus_fp_weak_precond_check_spec;
    fp_utils_specs.dw_plus_fp_strong_precond_check_spec;
    fp_utils_specs.dw_plus_dw_weak_precond_check_spec;
    fp_utils_specs.dw_plus_dw_strong_precond_check_spec;
    fp_utils_specs.dw_times_fp_weak_precond_check_spec;
    fp_utils_specs.dw_times_fp_strong_precond_check_spec;
    fp_utils_specs.dw_times_dw_weak_precond_check_spec;
    fp_utils_specs.dw_times_dw_strong_precond_check_spec;
    fp_utils_specs.dw_div_fp_weak_check_spec;
    fp_utils_specs.dw_div_fp_strong_check_spec;
    fp_utils_specs.dw_div_dw_weak_precond_check_spec;
    fp_utils_specs.dw_div_dw_strong_precond_check_spec ].

(* Specs of the internal functions, in dd_ops prog order. *)
Definition Ops_Internal : funspecs :=
  [ two_sum_spec; fast_2sum_kernel_spec; fast_2mult_kernel_spec;
    dw_plus_fp_kernel_spec; dw_plus_fp_spec; dw_plus_fp_strong_spec;
    dw_plus_dw_kernel_spec; dw_plus_dw_spec; dw_plus_dw_strong_spec;
    dw_times_fp_kernel_spec;
    fast_2sum_spec; fast_2mult_spec;
    fast_2mult_acc_spec;
    dw_times_fp_spec; dw_times_fp_strong_spec;
    dw_times_dw_kernel_spec; dw_times_dw_spec; dw_times_dw_strong_spec;
    dw_div_dw_kernel_spec; dw_div_dw_spec; dw_div_dw_strong_spec;
    dw_div_fp_kernel_spec; dw_div_fp_spec; dw_div_fp_strong_spec ].

(* Updated double-word operations expose default and strong interfaces with
   the same guarantee. *)
Definition Ops_Exports : funspecs :=
  [ two_sum_spec; fast_2sum_spec; fast_2mult_spec;
    dw_plus_fp_spec; dw_plus_fp_strong_spec;
    dw_plus_dw_spec; dw_plus_dw_strong_spec;
    dw_times_fp_spec; dw_times_fp_strong_spec;
    dw_times_dw_spec; dw_times_dw_strong_spec;
    dw_div_fp_spec; dw_div_fp_strong_spec;
    dw_div_dw_spec; dw_div_dw_strong_spec ].
