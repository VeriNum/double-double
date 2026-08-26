(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Abstract Spec Interface (ASI) for the double-word *operations* translation
   unit (dd_ops.c / verif_objs/dd_ops.v).  Every op / guarded-wrapper funspec is
   DECLAREd here exactly once, under the dd_ops program's CompSpecs, so that the
   body-proof file (verif_dd_ops.v) and the VSU builder (Ops_VSU.v) reference
   the *same* funspec terms.  The check_* funspecs mirror fp_utils_specs.v
   verbatim (same WITH/PRE/POST) so the ops VSU's Imports match the checks VSU's
   Exports at link time.  fma is provided by MathASI; exit is a libc external. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.

Require Import VSTlib.spec_math.   (* fma_spec *)
Require Import DDConds common real_extras.
Require Import DD.accuracy_proofs.dw_opps.DWPlusFP_acc.
Require Import DD.accuracy_proofs.dw_opps.DWPlusDW_acc.
Require Import DD.accuracy_proofs.dw_opps.DWMulFP_acc.
Require Import DD.accuracy_proofs.dw_opps.DWMulDW_acc.
Require Import DD.accuracy_proofs.dw_opps.DWDivFP_acc.
Require Import DD.accuracy_proofs.dw_opps.DWDivFP_subnormal.
Require Import DD.accuracy_proofs.dw_opps.DWDivDW_acc.
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

(* Tier A full Fast2Mult wrapper: error-term bound, exact reconstruction, and
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
   output is a valid double word. *)
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
    PROP((relative_error_DWPlusFP (fst xh) (snd xh) y
           <= 2 * (bpow Zaux.radix2 (- fprec Tdouble)) ^ 2)%R)
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
    PROP((relative_error_DWPlusDW (fst xh) (snd xh) (fst yh) (snd yh)
           <= (3 * (bpow Zaux.radix2 (- fprec Tdouble)) ^ 2)
              / (1 - 4 * (bpow Zaux.radix2 (- fprec Tdouble))))%R)
    RETURN()
    SEP(data_at Tsh dword
          (f2val (AccurateDWPlusDW (fst xh) (snd xh) (fst yh) (snd yh))) s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y).

(* The public API for DW x FP is the WHOLE-RANGE mixed bound

     |(zh+zl) - (xh+xl)*y| <= 2u^2 |(xh+xl)*y| + 2.51*eta,   eta = 2^emin,

   i.e. DWMulFP_acc.DWTimesFP3_error_mixed_flat, reached here through its
   cond-level form DWTimesFP_mixed_accuracy_from_cond_acc.  The PRE is empty:
   dw_mult_fp9_guarded's runtime check makes the POST unconditional, and the
   check now tests only DWTimesFP_mixed_safe_input_cond -- no underflow disjunct -- so inputs
   whose leading product falls in the Fast2Mult underflow gap are computed rather
   than rejected.  The price is stated in the bound: the 2.51*eta floor term is
   carried in every regime, including the normal one where the sharper pure 2u^2
   relative bound (DWTimesFP_accuracy_from_cond, which needs the gap excluded)
   would hold. *)
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
    PROP((absolute_error_DWTimesFP (fst xh) (snd xh) y
           <= 2 * (bpow Zaux.radix2 (- fprec Tdouble)) ^ 2 *
                Rabs ((FT2R (fst xh) + FT2R (snd xh)) * FT2R y)
              + 251/100 * bpow Zaux.radix2 (@common.emin Tdouble))%R
         /\ double_word_prop (fst (DWTimesFP3 (fst xh) (snd xh) y))
                             (snd (DWTimesFP3 (fst xh) (snd xh) y)))
    RETURN()
    SEP(data_at Tsh dword (f2val (DWTimesFP3 (fst xh) (snd xh) y)) s;
        data_at Tsh dword (f2val xh) x).

(* The public API for DW x DW is the WHOLE-RANGE mixed bound

     |(zh+zl) - (xh+xl)*(yh+yl)|
        <= 4u^2 |(xh+xl)*(yh+yl)| + 2.5*eta,   eta = 2^emin,

   i.e. DWMulDW_acc.DWTimesDW3_error_mixed_floor_acc, reached here through its
   cond-level form DWTimesDW_mixed_accuracy_from_cond_acc.  The PRE is empty:
   dw_mult_dw12_guarded's runtime check makes the POST unconditional, and the
   check now tests only DWTimesDW_mixed_safe_input_cond -- no underflow disjunct -- so inputs
   whose leading product falls in the Fast2Mult underflow gap are computed rather
   than rejected.  The price is stated in the bound: the 2.5*eta floor term is
   carried in every regime, including the normal one where the sharper pure 8u^2
   relative bound (DWTimesDW_accuracy_from_cond, which needs the gap excluded)
   would hold.

   Output double-word closure survives the weakening: it needs only that the
   closing Fast2Sum preserves its sum, which holds above the threshold via the
   ordering |cl3| <= |ch| and inside the gap because failure of that ordering
   forces the exact sum onto the FLT/FIX lattice at emin, where Fast2Sum is
   exact anyway (DWTimesDW3_double_word_from_cond_acc). *)
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
    PROP((absolute_error_DWTimesDW (fst xh) (snd xh) (fst yh) (snd yh)
           <= 4 * (bpow Zaux.radix2 (- fprec Tdouble)) ^ 2 *
                Rabs ((FT2R (fst xh) + FT2R (snd xh)) *
                      (FT2R (fst yh) + FT2R (snd yh)))
              + 5/2 * bpow Zaux.radix2 (@common.emin Tdouble))%R
         /\ double_word_prop
              (fst (DWTimesDW3 (fst xh) (snd xh) (fst yh) (snd yh)))
              (snd (DWTimesDW3 (fst xh) (snd xh) (fst yh) (snd yh))))
    RETURN()
    SEP(data_at Tsh dword
          (f2val (DWTimesDW3 (fst xh) (snd xh) (fst yh) (snd yh))) s;
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y).

(* DWDivFP (Algorithm 15) guarded wrapper.  Unlike the plus/mult wrappers, the
   quotient's accuracy cannot be a clean relative 3u^2 bound: the closing
   division d/y can be subnormal (0 for exact division), so the underflow regime
   contributes one 2^emin absolute term.  The exported bound is therefore the
   regime-independent combined bound proven as
   DWDivFP_mixed_guarantee_from_safe_input_cond:
     |zh+zl - (xh+xl)/y| <= 3u^2 |(xh+xl)/y| + 2^emin,
   which holds unconditionally once the runtime check discharges
   DWDivFP_mixed_safe_input_cond.  Note the cond is the MINIMAL one: it carries no quotient
   floor at all, so the wrapper accepts every quotient magnitude the format can
   represent -- subnormal quotients included.  The POST below is unchanged by
   that relaxation, and the constant on the 2^emin term is unchanged too: the
   mixed bound was always what this wrapper exported, and only the set of inputs
   it accepts got wider.  (What the floor used to buy was the PURE relative
   bound 6u^2, which is not exported here and remains on DWDivFP_relative_error_input_cond.)

   The bundled POST also carries output double-word closure, matching
   dw_mult_fp9_guarded_spec and dw_mult_dw12_guarded_spec.  Closure holds in
   every regime the guard admits --
   including a subnormal quotient, where the usual ordering |tl| <= |th| can
   fail and exactness of the closing Fast2Sum comes instead from th + tl landing
   back on the 2^emin lattice. *)
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

(* DWDivDW (Algorithm 18) guarded wrapper.  The exported guarantee is
   DWDivDW_acc.DWDivDW_mixed_guarantee: the WHOLE-RANGE mixed
   relative/physical-floor bound TOGETHER WITH double-word closure of the
   result,

     |(zh+zl) - Q| <= 9.8 u^2 |Q| + 2.5 * 2^emin  /\  double_word_prop zh zl,

   with Q = (xh+xl)/(yh+yl), proven as
   DWDivDW_mixed_guarantee_from_safe_input_cond.  This
   matches dw_mult_dw12_guarded_spec and dw_div_fp15_guarded_spec, which export
   the same pair of facts.

   WHY IT IS ONE NAMED Prop RATHER THAN TWO SPELLED-OUT CONJUNCTS, unlike those
   two siblings: DWDivDW3 is by far the largest definition in the library
   (reciprocal prologue + DWTimesFP3 + DWPlusFP + a closing DWTimesDW3), and the
   two facts stated separately mention `fst (DWDivDW3 ...)` and
   `snd (DWDivDW3 ...)` twice each -- four copies of that application in this
   funspec, on top of the one in the SEP clause.  OpsVSU's solve_SF_dd
   obligations are superlinear in that count.  Measured, compiling
   verif_proofs/vsu/Ops_VSU.v on this machine:

     two spelled-out conjuncts (5 copies)   killed at 2h17m, still running
     bound only, no closure (3 copies)      16m01s
     this bundled form (2 copies)           15m45s

   DWDivDW_mixed_guarantee matches the result pair ONCE, so the whole PROP
   carries a single occurrence -- fewer than the error bound alone used to
   contribute, which is why exporting closure here costs nothing.  DWTimesDW3 and DWDivFP3 are small enough that
   their specs pay nothing for the spelled-out form.

   The 9.8 is the paper's own FLX coefficient (DWDivDW.DWDDW3_correct), so this
   guarantee has the same shape and the same constant as its three siblings:
   2u^2|P| for DW x FP, 4u^2|P| for DW x DW, 3u^2|Q| for DW/FP.  What buys it is
   conjunct 7 of DWDivDW_mixed_safe_input_cond, |yh| <= 2^(femax-p-5): that says
   eta*|yh| <= u^2/4, which is exactly what pays for the reciprocal
   reconstruction's own underflow floor once the closing multiply by X scales it
   up.  Three binades looser and the charge is 8x larger and the constant is
   12.33 -- see the DWDivDW_relative_error_input_cond doc comment in DDConds.v.

   WHY NOT the pure relative 13.9 u^2 form (relative_errorDWDivDW3_from_cond_
   combined) that this spec used to export: that theorem needs the full
   DWDivDW_relative_error_input_cond, whose quotient underflow floor 2^(emin+2p-1) <= |xh/yh| rejects
   every quotient below 2^-969.  dw_div_dw_check no longer tests for it, and
   establishes only DWDivDW_mixed_safe_input_cond; absorbing the 2.5*2^emin floor into
   u^2|Q| would cost 2.5*2.0003 on top of 9.8, over 13.9.  The trade is
   deliberate: the guard now admits the entire underflowing-quotient range, and
   the mixed bound is strictly sharper than 13.9 u^2 wherever 2^emin sits below
   its maximum -- i.e. everywhere the quotient is comfortably normal.

   The theorem's other hypothesis, Hp14 : 14 <= fprec t, is a format side
   condition rather than an input condition -- at Tdouble it is 14 <= 53 and the
   body proof discharges it inline -- so the guarantee rests on DWDivDW_mixed_safe_input_cond
   alone, which is precisely what dw_div_dw_check establishes. *)
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

(* Copy of fp_utils_specs.SumResultIsSafeForFast2Sum (a CompSpecs-free Prop);
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
    PROP(b = true -> DWPlusFP_relative_error_input_cond (fst xh) (snd xh) y)
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
    PROP(b = true -> DWPlusDW_relative_error_input_cond (fst xh) (snd xh) (fst yh) (snd yh))
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

(* Minimal cond: no quotient floor at all; the caller gets the mixed bound,
   not the pure 6u^2 one.  See dw_div_fp15_guarded_spec above and
   DDConds.DWDivFP_mixed_safe_input_cond. *)
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
(*  libc external                                                            *)
(* ======================================================================== *)

Definition exit_spec :=
  DECLARE _exit
  WITH code : int
  PRE [ tint ]
    PROP() PARAMS (Vint (Int.repr 1)) SEP()
  POST [ tvoid ]
    PROP(False) LOCAL() SEP().

(* ======================================================================== *)
(*  Spec groupings for the ops VSU (and its body-proof Gprog)                *)
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
