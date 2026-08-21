(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* This file contains the floating-point functional models in IEEE-754
  format for the 2Sum and Fast2Mult implementations.*)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs common.


Section TwoSumModel.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Definition TwoSumF (a b : ftype t) :=
let s  := BPLUS a b in
let a' := BMINUS s b in
let b' := BMINUS s a' in
let da := BMINUS a a' in
let db := BMINUS b b' in (BPLUS a b, BPLUS da db).

Definition TwoSumF_err (a b : ftype t) := snd (TwoSumF a b).
Definition TwoSumF_sum (a b : ftype t) := fst (TwoSumF a b).

End TwoSumModel.

Section FastTwoSumModel.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Definition Fast2Sum (a b : ftype t) :=
let s := BPLUS a b in
let z := BMINUS s a in 
let t := BMINUS b z in (s, t).

Definition Fast2Sum_err (a b : ftype t) := snd (Fast2Sum a b).
Definition Fast2Sum_sum (a b : ftype t) := fst (Fast2Sum a b).

End FastTwoSumModel.


Section Fast2MultModel.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

(** Algorithm 3 : Fast2Mult *)
Definition Fast2Mult (a b : ftype t) :=
let m := BMULT a b in
let p := BFMA a b (BOPP m) in (m, p).

Definition Fast2Mult_err (a b : ftype t) := snd (Fast2Mult a b).
Definition Fast2Mult_mul (a b : ftype t) := fst (Fast2Mult a b).

End Fast2MultModel.


Section TwoSumCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation fexp  := (SpecFloat.fexp (fprec t) (femax t)).
Notation Omega := (bpow Zaux.radix2 (femax t)).

Definition TwoSum_cond (a b : ftype t) : Prop :=
  is_finite (BPLUS a b) = true /\
  is_finite (BMINUS a b) = true /\
  Rabs (FT2R b) < Ulp.pred Zaux.radix2 fexp Omega.

End TwoSumCond.


Section Fast2SumCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

(* Sufficient condition for fast_2sum(a,b) to be correct (s + t = a + b,
   with s = round(a+b)).  Stated with ulp, which is well-behaved at 0
   (ulp 0 = bpow emin, the minimum):
     - ulp b <= ulp a   covers both the Dekker case |b| <= |a| (ulp_le) and
                        Boldo's exponent case (ulp b <= ulp a <-> cexp b <=
                        cexp a for nonzero b,a).  It also subsumes b = 0,
                        since ulp 0 <= ulp a always.
     - a = 0            (Fast2Sum0f: fast_2sum(0,b) is exact).
   The old `|b| <= |a|` precondition implies `ulp b <= ulp a` by ulp_le, so
   any caller that established it still discharges this by `left; ulp_le`. *)
Definition Fast2Sum_cond (a b : ftype t) : Prop :=
  is_finite (BPLUS a b) = true /\
  ((Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (FT2R b) <=
    Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (FT2R a))%R \/
   FT2R a = 0%R).

End Fast2SumCond.


Section Fast2MultCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Definition Fast2Mult_cond (a b : ftype t) : Prop :=
  is_finite (BMULT a b) = true /\
  (FT2R a * FT2R b = 0 \/
   bpow Zaux.radix2 (SpecFloat.emin (fprec t) (femax t) + 2 * fprec t - 1)
   <= Rabs (FT2R a * FT2R b)).

(* Fast2Mult_cond2 strengthens Fast2Mult_cond's finiteness clause from
   is_finite (BMULT a b) to is_finite (BPLUS (BMULT a b) c): the ROUNDED
   product fl(a*b) accumulated with a third addend c, i.e. fl(fl(a*b) + c),
   must be finite (the underflow disjunct on the exact product a*b is
   unchanged).

   This is the precondition for an FMA-FREE multiply-then-add step
   fl(fl(a*b) + c) — the shape CompCert lowers fma(a,b,c) to when no fused
   instruction is emitted (Float.mul followed by Float.add; see
   verif_fp_utils_fast2_mult_check2.v).  The runtime guard fast2_mult_check2
   and its verification (fast2_mult_check2_spec) discharge exactly this cond.

   NOTE (status): no accuracy proof currently consumes Fast2Mult_cond2.  The
   present DW algorithms compute their error/accumulation terms with the fused
   BFMA (via Fast2Mult_err) and derive finiteness from the plain
   is_finite (BMULT a b) of Fast2Mult_cond (see Fast2Mult_acc.v and
   DWMulDW_acc.v).  cond2 is retained as the ready-made precondition for a
   future non-FMA product-then-add path; if that path is never added, cond2,
   fast2_mult_check2_spec, and verif_fp_utils_fast2_mult_check2.v can be
   dropped and un-wired from Checks_VSU / Gprog. *)
Definition Fast2Mult_cond2 (a b c : ftype t) : Prop :=
  is_finite (BPLUS (BMULT a b) c) = true /\
  (FT2R a * FT2R b = 0 \/
   bpow Zaux.radix2 (SpecFloat.emin (fprec t) (femax t) + 2 * fprec t - 1)
   <= Rabs (FT2R a * FT2R b)).

(* Fast2Mult_cond_acc is the "accurate-only" precondition: it drops the
   underflow-safety conjunct of Fast2Mult_cond (the `a*b = 0 \/ threshold <=
   |a*b|` disjunction) and keeps only overflow-safety (finiteness of the
   rounded product).  It suffices for the accuracy bound
   |Fast2Mult_err a b| <= 1/2 ulp(a*b) — which holds in every regime — but NOT
   for the error-free / double-word properties (mul + err = a*b), which need
   the underflow disjunct of the full Fast2Mult_cond.  See Fast2Mult_acc.v:
   Fast2Mult_accuracy_from_cond_acc (this cond) vs Fast2Mult_correct_from_cond
   (the full cond). *)
Definition Fast2Mult_cond_acc (a b : ftype t) : Prop :=
  is_finite (BMULT a b) = true.

Lemma Fast2Mult_cond_acc_of_cond (a b : ftype t) :
  Fast2Mult_cond a b -> Fast2Mult_cond_acc a b.
Proof. intros [Hfin _]; exact Hfin. Qed.

End Fast2MultCond.


Section DWord.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

(** Definition 1.4 *)
Definition double_word : ftype t -> ftype t -> Type :=
  fun xh xl => FT2R xh = rounded t (FT2R xh + FT2R xl).

(* Propositional double_word, suitable for VST PROP clauses. *)
Definition double_word_prop (xh xl : ftype t) : Prop :=
  FT2R xh = rounded t (FT2R xh + FT2R xl).

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))).

End DWord.


Section DWPlusDWCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation Omega := (bpow Zaux.radix2 (femax t)).

Definition DWPlusDW_cond (xh xl yh yl : ftype t) : Prop :=
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite yh = true /\
  is_finite yl = true /\
  double_word_prop xh xl /\
  double_word_prop yh yl /\
  Rabs (FT2R xh) <= /4 * Omega /\
  Rabs (FT2R yh) <= /4 * Omega.

End DWPlusDWCond.


Section DWPlusFPCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation Omega := (bpow Zaux.radix2 (femax t)).

(* High-part-only precondition for DWPlusFP, matching DWPlusDW_cond's shape.
   The DW relation forces |xl| <= ulp(xh)/2, so no separate magnitude bound
   on xl is required.  is_finite xl is NOT implied by double_word_prop
   (which lives in R via FT2R), so it must be asserted explicitly. *)
Definition DWPlusFP_cond (xh xl y : ftype t) : Prop :=
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite y  = true /\
  double_word_prop xh xl /\
  Rabs (FT2R xh) <= /4 * Omega /\
  Rabs (FT2R y)  <= /4 * Omega.

End DWPlusFPCond.


Section DWTimesFPCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation Omega := (bpow Zaux.radix2 (femax t)).

(* Precondition for DWTimesFP3 (Algorithm 9).  Minimal, non-redundant form:
     - Fast2Mult_cond xh y : the leading product satisfies the leaf condition
       (finiteness of BMULT xh y + the underflow disjunction) needed to make the
       internal Fast2Mult error-free and obtain the relative accuracy bound.  Via
       BMULT_finite_e this ALSO supplies is_finite xh and is_finite y, so those
       are not listed separately;
     - is_finite xl and the double-word relation on (xh, xl);
     - the product-magnitude bound |xh*y| <= Omega/2 = 2^(femax-1).  This is the
       overflow headroom that keeps the cross term and the closing Fast2Sum
       finite (Fast2Mult_cond alone only gives |xh*y| < Omega, under which the
       closing Fast2Sum can still overflow).  Omega/2 is the largest clean
       power-of-two that is provably sufficient: at |xh*y| ~ Omega the closing
       correction (a few ulp) tips RN(ch.s + c3) over Omega.  A caller may
       establish it from the square-root-scale factor bounds |xh|,|y| <=
       2^(femax/2-1) (aux_factor_prod gives the stronger |xh*y| <= Omega/4). *)
Definition DWTimesFP_cond (xh xl y : ftype t) : Prop :=
  is_finite xl = true /\
  double_word_prop xh xl /\
  Fast2Mult_cond xh y /\
  Rabs (FT2R xh * FT2R y) <= /2 * Omega.

(* DWTimesFP_cond_acc is the "accurate-only" precondition for DWTimesFP3: it
   weakens Fast2Mult_cond to Fast2Mult_cond_acc, i.e. it drops the underflow
   disjunct (FT2R xh * FT2R y = 0 \/ 2^(emin+2*p-1) <= |FT2R xh * FT2R y|) and
   keeps only overflow safety.  Exactly the DWTimesFP analogue of
   Fast2Mult_cond_acc vs Fast2Mult_cond above.

   It suffices for the whole-range MIXED bound

     |(zh+zl) - (xh+xl)*y| <= 2u^2 |(xh+xl)*y| + 2.51*eta

   (DWMulFP_acc.DWTimesFP3_error_mixed_flat) and for output double-word closure
   (DWTimesFP3_double_word_mixed), because both hold in EVERY regime given only
   the double-word relation and finiteness of the computed pair -- and the three
   conjuncts below are what a runtime guard needs to establish that finiteness.
   It does NOT suffice for the pure 2u^2 relative bound, which is available only
   when the nonzero underflow gap is excluded; that remains the province of the
   full DWTimesFP_cond (see DWMulFP_acc.DWTimesFP_cond_no_gap).

   This is the cond discharged by the runtime guard dw_mult_fp_check and carried
   by the exported funspec dw_mult_fp9_guarded_spec. *)
Definition DWTimesFP_cond_acc (xh xl y : ftype t) : Prop :=
  is_finite xl = true /\
  double_word_prop xh xl /\
  Fast2Mult_cond_acc xh y /\
  Rabs (FT2R xh * FT2R y) <= /2 * Omega.

Lemma DWTimesFP_cond_acc_of_cond (xh xl y : ftype t) :
  DWTimesFP_cond xh xl y -> DWTimesFP_cond_acc xh xl y.
Proof.
  intros (Hfxl & Hdwp & Hf2m & Hreal).
  repeat split; try assumption.
  exact (Fast2Mult_cond_acc_of_cond xh y Hf2m).
Qed.

End DWTimesFPCond.


Section DWTimesDWCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation Omega := (bpow Zaux.radix2 (femax t)).

(* Precondition for DWTimesDW3 (Algorithm 12).  Double-word analog of
   DWTimesFP_cond, in the same minimal form:
     - Fast2Mult_cond xh yh : leaf condition on the high product (also supplies
       is_finite xh and is_finite yh via BMULT_finite_e, so those are not listed);
     - is_finite xl, is_finite yl and the double-word relations on both pairs;
     - the product-magnitude bound |xh*yh| <= Omega/2 = 2^(femax-1) for overflow
       headroom (Omega/2 is the largest clean power-of-two that keeps the closing
       Fast2Sum finite; established by a caller from |xh|,|yh| <= 2^(femax/2-1)
       via aux_factor_prod, which gives the stronger |xh*yh| <= Omega/4). *)
Definition DWTimesDW_cond (xh xl yh yl : ftype t) : Prop :=
  is_finite xl = true /\
  is_finite yl = true /\
  double_word_prop xh xl /\
  double_word_prop yh yl /\
  Fast2Mult_cond xh yh /\
  Rabs (FT2R xh * FT2R yh) <= /2 * Omega.

(* DWTimesDW_cond_acc is the "accurate-only" precondition for DWTimesDW3, the
   exact analogue of DWTimesFP_cond_acc above: it weakens Fast2Mult_cond to
   Fast2Mult_cond_acc, dropping the underflow disjunct
   (FT2R xh * FT2R yh = 0 \/ 2^(emin+2*p-1) <= |FT2R xh * FT2R yh|) and keeping
   only overflow safety.

   It suffices for the whole-range MIXED bound

     |(zh+zl) - (xh+xl)*(yh+yl)| <= 4u^2 |(xh+xl)*(yh+yl)| + 5/2*eta

   and for output double-word closure, because both hold in EVERY regime given
   only the two double-word relations and finiteness of the computed pair -- and
   the conjuncts below are what a runtime guard needs to establish that
   finiteness (DWMulDW_acc.DWTimesDW3_finite_acc).  It does NOT suffice for the
   pure 8u^2 relative bound (DWTimesDW_accuracy_from_cond), which is available
   only when the nonzero underflow gap is excluded; that remains the province of
   the full DWTimesDW_cond.

   This is the cond discharged by the runtime guard dw_mult_dw_check and carried
   by the exported funspec dw_mult_dw12_guarded_spec, exactly as
   DWTimesFP_cond_acc is for dw_mult_fp_check / dw_mult_fp9_guarded_spec.  The
   full DWTimesDW_cond remains in use inside DWDivDW_acc, whose reciprocal
   refinement needs the underflow disjunct for the error-free product step. *)
Definition DWTimesDW_cond_acc (xh xl yh yl : ftype t) : Prop :=
  is_finite xl = true /\
  is_finite yl = true /\
  double_word_prop xh xl /\
  double_word_prop yh yl /\
  Fast2Mult_cond_acc xh yh /\
  Rabs (FT2R xh * FT2R yh) <= /2 * Omega.

Lemma DWTimesDW_cond_acc_of_cond (xh xl yh yl : ftype t) :
  DWTimesDW_cond xh xl yh yl -> DWTimesDW_cond_acc xh xl yh yl.
Proof.
  intros (Hfxl & Hfyl & Hdwx & Hdwy & Hf2m & Hreal).
  repeat split; try assumption.
  exact (Fast2Mult_cond_acc_of_cond xh yh Hf2m).
Qed.

End DWTimesDWCond.


Section DWDivFPCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin  := (SpecFloat.emin (fprec t) (femax t)).
Notation Omega := (bpow Zaux.radix2 (femax t)).

(* Precondition for DWDivFP3 (Algorithm 15).  Division needs two no-overflow
   bounds, both referencing only the components xh, y:
   - the QUOTIENT bound |xh/y| <= Omega/4 = bpow(femax-2) covers the nodes whose
     magnitude is the quotient (th = round(xh/y), tl = d/y, closing th+tl);
   - the |xh| bound covers the intermediate product node pih = round(th*y) ~ xh,
     which can overflow even under the quotient bound (e.g. xh = Omega, y = 4).
   Unlike the mul-style split into two square-root bounds on xh and 1/y (which
   would exclude valid small-magnitude or large-matched divisions), this is the
   precise no-overflow condition and rejects only inputs that actually overflow.
   The underflow bound on the quotient is the analog of the product underflow
   bound in DWTimesFP_cond / DWTimesDW_cond, and it forces y <> 0.

   This is the STRONG cond: its quotient floor 2^(emin+2p-1) is what buys the
   pure relative 6u^2 bound (DWDivFP_acc.DWDivFP3_accuracy).  The runtime guard
   discharges only the relaxed DWDivFP_cond_acc below, whose quotient floor is
   2^(emin+p-1); see that definition for the division of labour. *)
Definition DWDivFP_cond (xh xl y : ftype t) : Prop :=
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite y  = true /\
  double_word_prop xh xl /\
  bpow Zaux.radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R xh / FT2R y) /\
  Rabs (FT2R xh)          <= bpow Zaux.radix2 (femax t - 2) /\
  Rabs (FT2R xh / FT2R y) <= bpow Zaux.radix2 (femax t - 2) /\
  (* Product-node underflow bound: |xh| bounded below so that the Fast2Mult
     product th*y ~ xh stays above the TwoProd-exactness threshold emin+2p-1.
     Unlike the quotient bound, this reaches |xh| itself (a normal quotient can
     coexist with a subnormal product when y is tiny), and it is a genuine
     caller-checkable input condition.  The extra binade over emin+2p-1 absorbs
     the (1-u) factor in |th*y| >= |xh|(1-u) from thy_residual. *)
  bpow Zaux.radix2 (emin + 2 * fprec t) <= Rabs (FT2R xh).

(* DWDivFP_cond_acc is the "accurate-only" precondition for DWDivFP3, the
   division analogue of DWTimesFP_cond_acc above: it relaxes the QUOTIENT
   underflow floor from emin+2p-1 to emin+p-1, which is exactly what Layer 1
   asks for -- UF_th, and thy_residual's ulp v <= |v| * 2^(1-p), both of which
   need |xh/y| >= 2^(emin+p-1) and no more.  Below that the leading quotient
   node th = BDIV xh y is subnormal and the FLX->FLT bridge for it fails, so
   this is the floor of the proof architecture, not a tuning knob.

   Clause 8, the product-node floor 2^(emin+2p) <= |xh|, is UNCHANGED: it is a
   different bound, on the internal node pih = round(th*y) ~ xh, and it is what
   makes that node TwoProd-exact (DWDivFP_acc.cond_UF_prod).  A normal quotient
   can coexist with a subnormal product when y is tiny, so neither floor
   implies the other.

   It suffices for the whole-range MIXED bound

     |(zh+zl) - (xh+xl)/y| <= 3u^2 |(xh+xl)/y| + 2^emin

   (DWDivFP_acc.relative_errorDWDivFP3_from_cond_combined_acc) and for output
   double-word closure (DWDivFP3_is_DW_from_cond_acc), because the closing
   division d/y is unconstrained by either cond -- it is 0 for exact division --
   so the underflow leg is paid for by a single-node perturbation either way.
   It does NOT suffice for the pure 6u^2 relative bound
   (DWDivFP_acc.DWDivFP3_accuracy), which needs the quotient held clear of the
   underflow floor so that one floor ulp can be charged against it at 3u^2
   (DWDivFP_cond_eta_le_3u2_quotient); that remains the province of the full
   DWDivFP_cond.

   For Tdouble the relaxation moves the quotient floor from 2^-969 to
   2^-1022 = DBL_MIN, the smallest normal double, widening the runtime-admitted
   quotient range by 53 binades.  This is the cond discharged by the runtime
   guard dw_div_fp_check and carried by the exported funspec
   dw_div_fp15_guarded_spec, exactly as DWTimesFP_cond_acc is for
   dw_mult_fp_check / dw_mult_fp9_guarded_spec.

   The conjunct order and count deliberately match DWDivFP_cond, so that the
   destructuring pattern used throughout DWDivFP_acc.v applies unchanged to
   both. *)
Definition DWDivFP_cond_acc (xh xl y : ftype t) : Prop :=
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite y  = true /\
  double_word_prop xh xl /\
  bpow Zaux.radix2 (emin + fprec t - 1) <= Rabs (FT2R xh / FT2R y) /\
  Rabs (FT2R xh)          <= bpow Zaux.radix2 (femax t - 2) /\
  Rabs (FT2R xh / FT2R y) <= bpow Zaux.radix2 (femax t - 2) /\
  bpow Zaux.radix2 (emin + 2 * fprec t) <= Rabs (FT2R xh).

Lemma DWDivFP_cond_acc_of_cond (xh xl y : ftype t) :
  DWDivFP_cond xh xl y -> DWDivFP_cond_acc xh xl y.
Proof.
  intros (Hfxh & Hfxl & Hfy & Hdwp & Hquot & Hxhb & Hqub & Hxhlb).
  repeat split; try assumption.
  eapply Rle_trans; [| exact Hquot].
  apply bpow_le. pose proof (fprec_gt_one t). lia.
Qed.

End DWDivFPCond.

Section DWDivDWCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin  := (SpecFloat.emin (fprec t) (femax t)).

(** Guard condition for reciprocal-bootstrap double-word division.

    The two lower bounds serve different purposes: [1/yh] keeps the reciprocal
    construction in range, while [xh/yh] keeps the final multiplication in
    range.  Residual quantities such as [yl*th] and [rh+rl] are deliberately
    not lower-bounded because they may legitimately be zero; those nodes form
    the later normal/denormal case split. *)
Definition DWDivDW_cond (xh xl yh yl : ftype t) : Prop :=
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite yh = true /\
  is_finite yl = true /\
  double_word_prop xh xl /\
  double_word_prop yh yl /\
  bpow Zaux.radix2 (emin + 2 * fprec t - 1) <= Rabs (1 / FT2R yh) /\
  bpow Zaux.radix2 (emin + 2 * fprec t - 1)
    <= Rabs (FT2R xh / FT2R yh) /\
  bpow Zaux.radix2 (emin + 2 * fprec t) <= Rabs (FT2R yh) /\
  Rabs (FT2R xh) <= bpow Zaux.radix2 (femax t - 2) /\
  Rabs (FT2R yh) <= bpow Zaux.radix2 (femax t - 2) /\
  Rabs (FT2R xh / FT2R yh) <= bpow Zaux.radix2 (femax t - 2).

End DWDivDWCond.


Section DWops.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

(** Algorithm 4 : Addition of DW number and FP number *)
Definition DWPlusFP (xh xl y : ftype t) := 
let (sh, sl) := TwoSumF xh y in
let v:= BPLUS xl sl in
let (zh, zl) := Fast2Sum sh v in (zh, zl).

(** Algorithm 4p : Addition of DW number and FP number *)
Definition DWPlusFP' (xh xl y : ftype t) := 
let xhp := BPLUS xh xl in
let (sh, sl) := TwoSumF xhp y in
let v:= BPLUS xl sl in
let (zh, zl) := Fast2Sum sh v in (zh, zl).

(** Algorithm 5 : Addition of two DW numbers *)
Definition SloppyDWPlusDW (xh xl yh yl : ftype t) := 
let (sh, sl) := TwoSumF xh yh in
let v:= BPLUS xl yl in
let w:= BPLUS sl v in
let (zh, zl) := Fast2Sum sh w in (zh, zl).

(** Algorithm 6 : Addition of two DW numbers *)
Definition AccurateDWPlusDW (xh xl yh yl : ftype t) := 
let (sh, sl) := TwoSumF xh yh in
let (th, tl) := TwoSumF xl yl in
let c:= BPLUS sl th in
let (vh, vl) := Fast2Sum sh c in 
let w:= BPLUS tl vl in
let (zh, zl) := Fast2Sum vh w in (zh, zl).

(** Algorithm 7 : Multiplication of a DW number by a FP number *)
Definition DWTimesFP1 (xh xl y : ftype t) := 
let (ch, cl1) := Fast2Mult xh y in
let cl2 := BMULT xl y in
let (th, tl1) := Fast2Sum ch cl2 in 
let tl2 := BMULT tl1 cl1 in
let (zh, zl) := Fast2Sum th tl2 in (zh, zl).

(** Algorithm 8 : Multiplication of a DW number by a FP number *)
Definition DWTimesFP2 (xh xl y : ftype t) := 
let (ch, cl1) := Fast2Mult xh y in
let cl2 := BMULT xl y in
let cl3 := BPLUS cl1 cl2 in
let (zh, zl) := Fast2Sum ch cl3 in (zh, zl).

(** Algorithm 9 : Multiplication of a DW number by a FP number*)
Definition DWTimesFP3 (xh xl y : ftype t) := 
let (ch, cl1) := Fast2Mult xh y in
let cl3 := BFMA xl y cl1 in
let (zh, zl) := Fast2Sum ch cl3 in (zh, zl).

(** Algorithm 10 : Multiplication of a DW number by a DW number*)
Definition DWTimesDW1 (xh xl yh yl : ftype t) := 
let (ch, cl1) := Fast2Mult xh yh in
let tl1 := BMULT xh yl in
let tl2 := BMULT xl yh in
let cl2 := BPLUS tl1 tl2 in
let cl3 := BPLUS cl1 cl2 in 
let (zh, zl) := Fast2Sum ch cl3 in (zh, zl).

(** Algorithm 11 : Multiplication of a DW number by a DW number*)
Definition DWTimesDW2 (xh xl yh yl : ftype t) := 
let (ch, cl1) := Fast2Mult xh yh in
let tl        := BMULT xh yl in
let cl2       := BFMA  xl yh tl in
let cl3       := BPLUS cl1 cl2 in
let (zh,zl)   := Fast2Sum ch cl3 in (zh, zl).

(** Algorithm 12 : Multiplication of a DW number by a DW number *)
Definition DWTimesDW3 (xh xl yh yl : ftype t) := 
let (ch, cl1) := Fast2Mult xh yh in
let tl0 := BMULT xl yl in 
let tl1 := BFMA xh yl tl0 in
let cl2 := BFMA xl yh tl1 in
let cl3 := BPLUS cl1 cl2 in
let (zh, zl) := Fast2Sum ch cl3 in (zh, zl).

(** Algorithm 13 : Division of a DW number by a FP number*)
Definition DWDivFP1 (xh xl y : ftype t) :=
let th := BDIV xh y in
let (pih, pil) := Fast2Mult th y in
let (dh, d1) := TwoSumF xh (BOPP pih) in
let d2 := BMINUS xl pil in
let dl := BPLUS d1 d2 in
let d  := BPLUS dh dl in
let tl := BDIV d y in
let (zh, zl) := Fast2Sum th tl in (zh, zl).

(** Algorithm 14 : Division of a DW number by a FP number*)
Definition DWDivFP2 (xh xl y : ftype t) :=
let th := BDIV xh y in
let (pih, pil) := Fast2Mult th y in
let dh := BMINUS xh pih in
let dl := BMINUS xl pil in
let d  := BPLUS dh dl in
let tl := BDIV d y in
let (zh, zl) := Fast2Sum th tl in (zh, zl).

(** Algorithm 15 : Division of a DW number by a FP number*)
Definition DWDivFP3 (xh xl y : ftype t) :=
let th := BDIV xh y in
let (pih, pil) := Fast2Mult th y in
let dh := BMINUS xh pih in
let dt := BMINUS dh pil in
let d  := BPLUS dt xl in
let tl := BDIV d y in
let (zh, zl) := Fast2Sum th tl in (zh, zl).

(** Algorithm 16 : Division of a DW number by a DW number*)
Definition DWDivDW1 (xh xl yh yl : ftype t) :=
let th := BDIV xh yh in
let (rh, rl) := DWTimesFP1 yh yl th in
let (pih, pil) := TwoSumF xh (BOPP rh) in
let dh := BMINUS pil rl in
let dl := BPLUS dh xl in
let d  := BPLUS pih dl in
let tl := BDIV d yh in
let (zh, zl) := Fast2Sum th tl in (zh, zl).

(** Algorithm 17 : Division of a DW number by a DW number*)
Definition DWDivDW2 (xh xl yh yl : ftype t) :=
let th := BDIV xh yh in
let (rh, rl) := DWTimesFP1 yh yl th in
let pih := BMINUS xh rh in
let dl  := BMINUS xl rl in
let d   := BPLUS pih dl in
let tl  := BDIV d yh in
let (zh, zl) := Fast2Sum th tl in (zh, zl).

(** Algorithm 18 : Division of a DW number by a DW number*)
Definition DWDivDW3 (xh xl yh yl : ftype t) :=
let th := BDIV (Zconst t 1) yh in
let rh := BFMA (BOPP yh) th (Zconst t 1) in
let rl := BOPP (BMULT yl th) in
let (eh, el) := Fast2Sum rh rl in
let (dh, dl) := DWTimesFP3 eh el th in
let (mh, ml) := DWPlusFP dh dl th in
let (zh, zl) := DWTimesDW3 xh xl mh ml in (zh, zl).

End DWops.
