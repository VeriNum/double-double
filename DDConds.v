(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* This file contains the preconditions for the floating-point functional
   models in DDModels.v. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs common.
Require Export DDModels.


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
   discharges only DWDivFP_cond_min below, which has no quotient floor and buys
   the whole-range mixed bound; the normal-quotient proof helper now lives in
   DWDivFP_acc.v as DWDivFP_normal_quotient_input_cond. *)
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

(* DWDivFP_cond_min drops the quotient floor ENTIRELY, replacing it by
   finiteness of the leading quotient node.  That conjunct is the division
   analogue of Fast2Mult_cond_acc (which is likewise just
   `is_finite (BMULT a b) = true`), and it does the same double duty:

     - it forces FT2R y <> 0, which every proof in DWDivFP_acc previously got
       from the quotient floor;
     - it supplies the th-node finiteness that th_finite previously derived
       from the quotient CEILING plus y <> 0.

   Unlike DWDivFP_normal_quotient_input_cond in DWDivFP_acc.v, this cond admits
   a SUBNORMAL quotient.  The mixed bound survives with the SAME constant,

     |(zh+zl) - (xh+xl)/y| <= 3u^2 |(xh+xl)/y| + 2^emin,

   because once |xh/y| < 2^(emin+p-1) the whole computation sits on the
   2^emin lattice: the correction tl rounds within half an ulp of the exact
   one, and the closing Fast2Sum is exact because th + tl is again a lattice
   point.  Proven, together with output double-word closure and finiteness, in
   DWDivFP_subnormal.v (DWDivFP3_subnormal_leg); the normal branch is
   unchanged and still routes through DWDivFP_normal_quotient_input_cond.

   Clause 8, the product-node floor 2^(emin+2p) <= |xh|, is again UNCHANGED and
   is NOT removable: it is what makes the division residual representable to
   relative accuracy u, hence what makes DWDivFP3 a double-word algorithm at
   all.  Dropping it costs the u^2 bound outright -- xh = 7*eta, y = 3*eta is a
   double word with a perfectly normal quotient 7/3 on which the algorithm
   returns zl = 0 and a relative error of u/2, violating 3u^2|Q| + c*eta for
   every constant c.  It also, in this branch, is what forces |y| > 2^(p+1),
   without which the closing division node has no bound.

   This is the cond discharged by the runtime guard dw_div_fp_check. *)
Definition DWDivFP_cond_min (xh xl y : ftype t) : Prop :=
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite y  = true /\
  double_word_prop xh xl /\
  is_finite (BDIV xh y) = true /\
  Rabs (FT2R xh)          <= bpow Zaux.radix2 (femax t - 2) /\
  Rabs (FT2R xh / FT2R y) <= bpow Zaux.radix2 (femax t - 2) /\
  bpow Zaux.radix2 (emin + 2 * fprec t) <= Rabs (FT2R xh).

End DWDivFPCond.

Section DWDivDWCond.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin  := (SpecFloat.emin (fprec t) (femax t)).

(** Guard condition for reciprocal-bootstrap double-word division.

    The two lower bounds serve different purposes: [1/yh] keeps the reciprocal
    construction in range, while [xh/yh] keeps the final multiplication in
    range.  Residual quantities such as [yl*th] and [rh+rl] are deliberately
    not lower-bounded because they may legitimately be zero; those nodes form
    the later normal/denormal case split.

    NO-OVERFLOW BOUNDS: only the quotient ceiling survives.  This cond used to
    carry three [<= 2^(femax-2)] conjuncts, on |xh|, |yh| and |xh/yh|.  Two of
    them are gone.

    - |yh| <= 2^(femax-2) was REDUNDANT.  The reciprocal conjunct already is an
      upper bound on |yh|, and a strictly stronger one: for yh <> 0 -- which
      that conjunct itself forces, since Rocq's [1/0 = 0] makes it false at
      yh = 0 -- it reads

        Rabs (FT2R yh) <= 2^(-(emin+2p-1)) = 2^(femax-p-2)

      using emin = 3 - femax - p, i.e. the same bound tightened by p binades.
      [DWDivDW_acc.DWDivDW_cond_yh_upper] recovers the weaker form for clients
      that want it.  The runtime guard [dw_div_dw_check] already exploited this
      -- it tests |y->s| <= 2^969 and derived |y->s| <= 2^1022 from it -- so the
      two conjuncts were never independent.

    - |xh| <= 2^(femax-2) was UNUSED.  It is not implied by anything, but no
      theorem in DWDivDW_acc.v ever read it, finiteness
      ([DWDivDW3_finite_from_cond]) included, and the reason is structural: xh
      only ever enters the algorithm multiplied by mh ~ 1/yh (the closing
      ch = BMULT xh mh, tl1 = BFMA xh ml tl0, and xl likewise), so the quotient
      ceiling below already bounds every node xh reaches.  Accuracy, output
      double-word closure and finiteness were all re-verified without it.  The
      guard's xh_hi test is consequently dead and can be deleted whenever
      clightgen is next re-run. *)
Definition DWDivDW_cond (xh xl yh yl : ftype t) : Prop :=
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite yh = true /\
  is_finite yl = true /\
  double_word_prop xh xl /\
  double_word_prop yh yl /\
  Rabs (FT2R yh) <= bpow Zaux.radix2 (femax t - fprec t - 5) /\
  bpow Zaux.radix2 (emin + 2 * fprec t - 1)
    <= Rabs (FT2R xh / FT2R yh) /\
  bpow Zaux.radix2 (emin + 2 * fprec t) <= Rabs (FT2R yh) /\
  Rabs (FT2R xh / FT2R yh) <= bpow Zaux.radix2 (femax t - 2).

(** [DWDivDW_cond_acc] is the "accurate-only" precondition for [DWDivDW3], the
    DW/DW analogue of [DWDivFP_cond_min] above.  It DROPS conjunct 8 of
    [DWDivDW_cond], the quotient underflow floor

      2^(emin+2p-1) <= |xh/yh|,

    outright.  Every remaining conjunct keeps its position, so a destructuring
    pattern for [DWDivDW_cond] applies to [DWDivDW_cond_acc] verbatim up to
    conjunct 7, and shifts by one from conjunct 8 on.  (The conds are ten and
    nine conjuncts long respectively, not twelve and eleven: the separate |yh|
    and |xh| upper bounds were removed as redundant and unused -- see the note
    on [DWDivDW_cond] above.)

    WHY CONJUNCT 8 GOES.  It was needed in exactly one place: the closing
    [DWTimesDW3 xh xl mh ml] block, whose old proof had to establish the
    magnitude ordering |cl3| <= |ch| by hand, and paid for it with a lower
    bound on the closing product |xh*mh| >= |xh/yh|/2.  That whole argument is
    now [DWMulDW_acc.DWTimesDW3_error_mixed_floor_acc], which covers the WHOLE
    range from double-word inputs and finiteness alone.  The price is the
    closing block's floor rising from [2*eta] to [5/2*eta], hence the exported
    mixed bound

      |(zh+zl) - (xh+xl)/(yh+yl)| <= 9.8 u^2 |Q| + 5/2 eta

    ([DWDivDW_acc.DWDivDW3_error_mixed_acc]) together with output double-word
    closure ([DWDivDW3_double_word_from_cond_acc]).  For Tdouble this admits
    every quotient below 2^-969 -- i.e. the entire underflowing-quotient range
    the mixed bound was built to cover, which the old guard rejected.

    The [u^2] coefficient does not depend on conjunct 8: that conjunct never
    entered the two arm budgets, only the trailing physical-floor constant.
    The pure relative bound [relative_errorDWDivDW3_from_cond_combined]
    (16.5 u^2) still needs the full [DWDivDW_cond]: absorbing [5/2*eta] into
    [u^2|Q|] costs 2.5*2.0003 on top of the mixed coefficient, so that theorem
    keeps the old [2*eta] closing route, which conjunct 8 pays for.

    WHY CONJUNCTS 7 AND 9 STAY, AND WHERE CONJUNCT 7's EXPONENT COMES FROM.

    Conjuncts 7 and 9 are the two sides of one window on the divisor,

      2^(emin+2p) <= |yh| <= 2^(femax-p-5)        (Tdouble: 2^-968 .. 2^966),

    and neither is an underflow floor on a residual node.  Conjunct 7 used to
    be written as [2^(emin+2p-1) <= |1/yh|], which for yh <> 0 is the same
    kind of statement one exponent looser; it is now stated directly on |yh|,
    so the cond never mentions 1/FT2R yh and the guard needs no rounded-to-
    exact reciprocal transfer.  Nonzero-ness comes from conjunct 9.

    CONJUNCT 7 IS THE EXPORTED COEFFICIENT.  Since eta = 2^emin and u = 2^-p,
    conjunct 7 says exactly

      eta * |yh| <= u^2 / 4.

    The reciprocal reconstruction (mh,ml) carries an absolute underflow floor
    of its own, |M - 1/Y| <= a u^2/|Y| + fr*eta
    ([DWDivDW_reciprocal_error_scaled_floor_param]), so the closing
    multiplication by X contributes fr*eta*|X|; and since |X| = |Q|*|Y|
    identically,

      eta*|X| <= c u^2 |Q|   <->   eta*|Y| <= c u^2

    whenever Q <> 0, with |Y| = |yh|(1+O(u)).  Conjunct 7 IS that inequality,
    not merely a sufficient condition for it, so its exponent and the exported
    u^2 coefficient move together:

      |yh| <= 2^(femax-p-2-k)  ==>  charge = fr * 2^(1-k),   fr = 1 or 2.

    At k = 0 -- where this cond sat until now -- the charge is 2.0 on the
    ordered arm and 4.0 on the unordered one, and the exported coefficient was
    12.33.  Nothing rearranges that away: the floor fr is REPRESENTATIONAL,
    not algorithmic.  At the window's edge |th| ~ 2^(emin+2p-1), so the
    refinement product eh*th sits one binade above the smallest normal and its
    exact value needs bits below 2^emin -- ANY double-word D misses E*th by up
    to eta/2, whatever algorithm produces it.  With the paper's own FLX budget
    assembled from 5 (closing DWTimesDW12, relaxed from its actual <4u^2)
    + 2.298 (Newton residual) + 0.5 (rl rounding) + 2 (DWPlusFP) = 9.798, the
    only slack a runtime proof has over 9.8 is the 5 -> 4 closing gain, i.e.
    1.0 -- less than the charge.  So 9.8 is out of reach at k <= 1 however the
    analysis is arranged, and k = 3 is what this cond takes: charge 0.25,
    arm budgets 9.56 (ordered) and 7.60 (unordered), exported 9.8 with slack.

    The price is 3 binades off the TOP of the divisor range, an overflow-side
    restriction.  Underflow whole-range coverage is untouched: there is still
    no floor on the quotient (that is conjunct 8, dropped by
    [DWDivDW_cond_acc] below).

    Conjunct 9, [2^(emin+2p) <= |yh|], is likewise not an underflow floor.
    Since emin = 3 - femax - p it is literally

      |1/yh| <= 2^(femax-p-3),

    the p+3 binades of overflow headroom that the reciprocal node
    th = BDIV 1 yh and everything scaled by it (dh ~ u*th, mh ~ th) require;
    [DWDivDW_cond_reciprocal_upper_tight] uses it at exactly that strength.
    It does double duty twice more:

      - together with conjunct 7 it forces emin+2p <= femax-p-5, hence
        p <= femax-4 and so [emin+2p <= 0], hence [eta <= u^2]
        ([DWDivDW_cond_eta_le_u2]).  That is what lets the reciprocal
        residual's one rounding be charged at 1.001*u^2 with no floor ulp at
        all (only [p < femax] is available otherwise, giving eta <= 4u^2,
        which does not fit).
      - it is what makes the FMA residual rh = 1 - yh*th exactly
        representable ([DWDivDW_rh_exact_from_cond], via
        [DWDivDW_cond_emin_le]).

    Only ~3 of those p+3 binades of headroom are structurally needed (mh is
    th*(1+3u), and every other th-scaled node is far smaller), so conjunct 9
    could in principle come down to "yh is normal", 2^(emin+p-1) -- 54 binades
    lower for Tdouble.  What blocks it is the eta <= u^2 derivation above,
    which would then have to become an explicit format side condition
    p + 3 <= femax on every theorem in the chain.  That is a separate change;
    the lower bound never enters the error budget either way.

    Replacing conjunct 9 by finiteness of th in the style of
    [DWDivFP_cond_min] would recover yh <> 0 and th-finiteness but none of
    those uses -- and unlike DW/FP division, which forms th = BDIV xh y and is
    therefore covered by its quotient ceiling, DW/DW has an explicit
    reciprocal node, so SOME lower bound on |yh| is structural here.  There is
    consequently no separate [DWDivDW_cond_min] tier: [DWDivDW_cond_acc] is
    the minimum.

    This is the cond the runtime guard [dw_div_dw_check] should discharge. *)
Definition DWDivDW_cond_acc (xh xl yh yl : ftype t) : Prop :=
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite yh = true /\
  is_finite yl = true /\
  double_word_prop xh xl /\
  double_word_prop yh yl /\
  Rabs (FT2R yh) <= bpow Zaux.radix2 (femax t - fprec t - 5) /\
  bpow Zaux.radix2 (emin + 2 * fprec t) <= Rabs (FT2R yh) /\
  Rabs (FT2R xh / FT2R yh) <= bpow Zaux.radix2 (femax t - 2).

Lemma DWDivDW_cond_acc_of_cond (xh xl yh yl : ftype t) :
  DWDivDW_cond xh xl yh yl -> DWDivDW_cond_acc xh xl yh yl.
Proof.
  intros (Fxh & Fxl & Fyh & Fyl & DWx & DWy & Hyhhi & _ & Hylo &
          Hratiohi).
  repeat split; assumption.
Qed.

End DWDivDWCond.
