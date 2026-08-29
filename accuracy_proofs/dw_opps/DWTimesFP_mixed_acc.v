(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Whole range mixed error and output validity results for [DWTimesFP].

    This file imports the common runtime model facts and normal range relative
    result from [DWTimesFP_relative_acc], then handles the Fast2Mult underflow
    gap and exposes the mixed guarantee ladder. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common FLT_helpers.
Require Import DWTimesFP DDConds DWord_defs Fast2Mult_acc TwoSum_acc Fast2Sum_acc.
Require Import DW_acc_lemmas DWTimesFP_relative_acc.
From Flocq Require Import Pff2Flocq Core.
From Stdlib Require Import Reals.Reals Logic.FunctionalExtensionality.
Require Import mathcomp.ssreflect.ssreflect.

Set Bullet Behavior "Strict Subproofs".

Opaque DWTimesFP.TwoProd.
Arguments DWTimesFP.TwoProd : simpl never.

(** Whole range mixed accuracy.  Below the TwoProd exactness threshold
    [2^(emin+2p-1)], the product residual need not be representable; the
    absolute [eta] term accounts for that underflow regime. *)

(** Algorithm 9's closing Fast2Sum is exact as soon as its two inputs are
    ordered by magnitude.  No precision bound, no input condition and no regime
    hypothesis is needed -- [FastTwoSum_correct] applies directly.

    This is the prerequisite for splitting the refinement block on the
    ordering: in the ordered arm the two Fast2Sum roundings of
    [DWDivDW_refinement_product_value_error_tight_floor] vanish, taking its
    floor from [2*eta] down to [eta]. *)
Lemma DWTimesFP_sum_exact_of_ord {NANS : Nans} {t : type}
    {STD : is_standard t} (ah al b : ftype t) :
  is_finite_p (DWTimesFP ah al b) ->
  Rabs (FT2R (BFMA al b (Fast2Mult_err ah b))) <=
    Rabs (FT2R (Fast2Mult_mul ah b)) ->
  FT2R (fst (DWTimesFP ah al b)) +
  FT2R (snd (DWTimesFP ah al b)) =
    FT2R (Fast2Mult_mul ah b) +
    FT2R (BFMA al b (Fast2Mult_err ah b)).
Proof.
move => FIN Hord.
set ch := Fast2Mult_mul ah b.
set cl1 := Fast2Mult_err ah b.
set cl3 := BFMA al b cl1.
have Fe : is_finite_p (Fast2Sum ch cl3).
{ unfold DWTimesFP in FIN.
  unfold ch, cl1, cl3, Fast2Mult_mul, Fast2Mult_err, Fast2Mult in *.
  exact FIN. }
fold ch cl1 cl3 in Hord.
have Hsum := FastTwoSum_correct ch cl3 (proj1 Fe) Hord.
change (FT2R (snd (DWTimesFP ah al b)) =
  FT2R ch + FT2R cl3 - FT2R (fst (DWTimesFP ah al b))) in Hsum.
lra.
Qed.

(** If Algorithm 9's closing Fast2Sum preserves its two inputs, its returned
    pair is a double-word: the high component is exactly the rounding of that
    preserved sum. *)
Local Lemma DWTimesFP_double_word_of_sum {NANS : Nans} {t : type}
    {STD : is_standard t} (ah al b : ftype t) :
  is_finite_p (DWTimesFP ah al b) ->
  let ch := Fast2Mult_mul ah b in
  let cl3 := BFMA al b (Fast2Mult_err ah b) in
  FT2R (fst (DWTimesFP ah al b))+FT2R (snd (DWTimesFP ah al b))=
    FT2R ch+FT2R cl3 ->
  double_word_prop (fst (DWTimesFP ah al b))
                   (snd (DWTimesFP ah al b)).
Proof.
move => FIN /= Hsum.
set ch := Fast2Mult_mul ah b.
set cl3 := BFMA al b (Fast2Mult_err ah b).
set d := DWTimesFP ah al b.
fold d ch cl3 in Hsum.
unfold double_word_prop, rounded. fold d.
rewrite Hsum.
change (FT2R (fst d)=round radix2
  (SpecFloat.fexp (fprec t) (femax t))
  (Znearest choice) (FT2R ch+FT2R cl3)).
have Hfst : fst d=BPLUS ch cl3 by reflexivity.
rewrite Hfst. symmetry. apply BPLUS_round_correct. exact (proj1 FIN).
Qed.

(* ---------- the gap regime: below the TwoProd exactness threshold ---------- *)

(** In the gap below Fast2Mult's exactness threshold, the compensated core of
    Algorithm 9 has only a floor error.  This is the value before its
    closing Fast2Sum; no ordinary [u^2] term is introduced in this regime. *)
Local Lemma DWTimesFP_core_error_floor_gap {NANS : Nans} {t : type}
    {STD : is_standard t} (ah al b : ftype t) :
  (3 <= fprec t)%Z -> double_word_prop ah al ->
  is_finite_p (DWTimesFP ah al b) ->
  ~ bpow radix2 (@common.emin t+2*fprec t-1) <=
      Rabs (FT2R ah*FT2R b) ->
  let ch := Fast2Mult_mul ah b in
  let cl3 := BFMA al b (Fast2Mult_err ah b) in
  Rabs ((FT2R ch+FT2R cl3)-
        (FT2R ah+FT2R al)*FT2R b)
    <= 251/100*bpow radix2 (@common.emin t).
Proof.
move => Hp3 DWa FIN Hgap /=.
set x := (FT2R ah*FT2R b)%R.
set ch := Fast2Mult_mul ah b.
set cl1 := Fast2Mult_err ah b.
set cl3 := BFMA al b cl1.
set u := bpow radix2 (-fprec t).
set eta := bpow radix2 (@common.emin t).
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /8.
{ unfold u. have -> : (/8:R)=bpow radix2 (-3) by (simpl;lra).
  apply bpow_le; lia. }
have Heta0 : 0 < eta by apply bpow_gt_0.
have Ffast := DWTimesFP_fast2mult_finite ah al b FIN.
have Fch : is_finite ch=true by exact (proj1 Ffast).
have Fcl1 : is_finite cl1=true by exact (proj2 Ffast).
have Fcl3 := DWTimesFP_correction_finite ah al b FIN; fold cl1 cl3 in Fcl3.
have Hdelta := Fast2Mult_sum_error_floor ah b Hp3 Ffast.
fold x ch cl1 eta in Hdelta.
have Hchr : FT2R ch=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) x.
{ unfold ch, Fast2Mult_mul, Fast2Mult. symmetry.
  apply BMULT_round_correct. exact Fch. }
have Hxe := round_FLT_error_rel_emin (t:=t) x.
fold u eta in Hxe. rewrite -Hchr in Hxe.
have Hr : Rabs (x-FT2R ch)<=u*Rabs x+/2*eta.
{ rewrite Rabs_minus_sym. exact Hxe. }
have Hcl1 : Rabs (FT2R cl1)<=
    u*Rabs x+1501/1000*eta.
{ have Htri := Rabs_triang
      (FT2R cl1-(x-FT2R ch)) (x-FT2R ch).
  replace (FT2R cl1-(x-FT2R ch)+(x-FT2R ch))%R with
      (FT2R cl1)%R in Htri by ring.
  have Heq : FT2R cl1-(x-FT2R ch)=
      FT2R ch+FT2R cl1-x by ring.
  rewrite Heq in Htri.
  eapply Rle_trans; [exact Htri|].
  eapply Rle_trans.
  - apply Rplus_le_compat; [exact Hdelta|exact Hr].
  - nra. }
have Hal := @dw_low_le_u_high t STD ah al DWa.
fold u in Hal.
have Halb : Rabs (FT2R al*FT2R b)<=u*Rabs x.
{ unfold x. rewrite !Rabs_mult.
  have H := Rmult_le_compat_r (Rabs (FT2R b)) _ _
    (Rabs_pos _) Hal.
  eapply Rle_trans; [exact H|]. right; ring. }
set w := (FT2R al*FT2R b+FT2R cl1)%R.
have Hw : Rabs w<=2*u*Rabs x+1501/1000*eta.
{ unfold w. eapply Rle_trans; [apply Rabs_triang|]. nra. }
have Hcl3r : FT2R cl3=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) w.
{ unfold cl3. rewrite -(BFMA_round_correct t al b cl1 Fcl3).
  unfold w. f_equal; ring. }
have He3 := round_FLT_error_rel_emin (t:=t) w.
fold u eta in He3. rewrite -Hcl3r in He3.
have Huw := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Hw.
have Hscale : u^2*bpow radix2
    (@common.emin t+2*fprec t-1)=/2*eta.
{ replace (u^2)%R with (u*u)%R by ring.
  unfold u, eta. rewrite -bpow_plus -bpow_plus.
  replace (-fprec t+-fprec t+
      (@common.emin t+2*fprec t-1))%Z with
      (@common.emin t-1)%Z by ring.
  rewrite (bpow_plus radix2 (@common.emin t) (-1)).
  change (bpow radix2 (-1)) with (/2:R). ring. }
have HxB : Rabs x < bpow radix2
    (@common.emin t+2*fprec t-1) by apply Rnot_le_lt.
have Hu20 : 0 < u^2 by nra.
have HuB := Rmult_lt_compat_l (u^2) _ _ Hu20 HxB.
rewrite Hscale in HuB.
change (Rabs ((FT2R ch+FT2R cl3)-
  (FT2R ah+FT2R al)*FT2R b)<=251/100*eta).
have Heq : (FT2R ch+FT2R cl3)-
    (FT2R ah+FT2R al)*FT2R b =
  (FT2R ch+FT2R cl1-x)+(FT2R cl3-w) by (unfold x,w;ring).
rewrite Heq. eapply Rle_trans; [apply Rabs_triang|].
eapply Rle_trans.
- apply Rplus_le_compat; [exact Hdelta|exact He3].
- nra.
Qed.

(** Full Algorithm 9 in the Fast2Mult gap.  If the closing Fast2Sum ordering
    holds it is exact.  If it fails, the leading and low terms are both within
    six floor ulps, where their common fixed-point lattice makes Fast2Sum exact
    as well.  Thus the compensated core's [2.51] ulps are the whole cost. *)
Local Lemma DWTimesFP_error_floor_gap {NANS : Nans} {t : type}
    {STD : is_standard t} (ah al b : ftype t) :
  (3 <= fprec t)%Z -> double_word_prop ah al ->
  is_finite_p (DWTimesFP ah al b) ->
  ~ bpow radix2 (@common.emin t+2*fprec t-1) <=
      Rabs (FT2R ah*FT2R b) ->
  Rabs ((FT2R (fst (DWTimesFP ah al b))+
         FT2R (snd (DWTimesFP ah al b)))-
        (FT2R ah+FT2R al)*FT2R b)
    <= 251/100*bpow radix2 (@common.emin t) /\
  double_word_prop (fst (DWTimesFP ah al b))
                   (snd (DWTimesFP ah al b)).
Proof.
move => Hp3 DWa FIN Hgap.
set x := (FT2R ah*FT2R b)%R.
set P := Rabs x.
set ch := Fast2Mult_mul ah b.
set cl1 := Fast2Mult_err ah b.
set cl3 := BFMA al b cl1.
set d := DWTimesFP ah al b.
set u := bpow radix2 (-fprec t).
set eta := bpow radix2 (@common.emin t).
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /8.
{ unfold u. have -> : (/8:R)=bpow radix2 (-3) by (simpl;lra).
  apply bpow_le; lia. }
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have Heta0 : 0 < eta by apply bpow_gt_0.
have Ffast := DWTimesFP_fast2mult_finite ah al b FIN.
have Fch : is_finite ch=true by exact (proj1 Ffast).
have Fcl1 : is_finite cl1=true by exact (proj2 Ffast).
have Fcl3 := DWTimesFP_correction_finite ah al b FIN; fold cl1 cl3 in Fcl3.
have Hcore := DWTimesFP_core_error_floor_gap ah al b
  Hp3 DWa FIN Hgap.
fold ch cl3 eta in Hcore. cbv zeta in Hcore.
have Hdelta := Fast2Mult_sum_error_floor ah b Hp3 Ffast.
fold x ch cl1 eta in Hdelta.
have Hchr : FT2R ch=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) x.
{ unfold ch, Fast2Mult_mul, Fast2Mult. symmetry.
  apply BMULT_round_correct. exact Fch. }
have Hxe := round_FLT_error_rel_emin (t:=t) x.
fold u eta in Hxe. rewrite -Hchr in Hxe.
fold P in Hxe.
have Hr : Rabs (x-FT2R ch)<=u*P+/2*eta.
{ rewrite Rabs_minus_sym. exact Hxe. }
have Hchlo : (1-u)*P-/2*eta<=Rabs (FT2R ch).
{ have Hrev := Rabs_triang_inv x (x-FT2R ch).
  replace (x-(x-FT2R ch))%R with (FT2R ch) in Hrev by ring.
  fold P in Hrev. nra. }
have Hchup : Rabs (FT2R ch)<=(1+u)*P+/2*eta.
{ have Htri := Rabs_triang (FT2R ch-x) x.
  replace (FT2R ch-x+x)%R with (FT2R ch) in Htri by ring.
  fold P in Htri. nra. }
have Hcl1 : Rabs (FT2R cl1)<=u*P+1501/1000*eta.
{ have Htri := Rabs_triang
      (FT2R cl1-(x-FT2R ch)) (x-FT2R ch).
  replace (FT2R cl1-(x-FT2R ch)+(x-FT2R ch))%R with
      (FT2R cl1)%R in Htri by ring.
  have Heq : FT2R cl1-(x-FT2R ch)=
      FT2R ch+FT2R cl1-x by ring.
  rewrite Heq in Htri. nra. }
have Hal := @dw_low_le_u_high t STD ah al DWa.
fold u in Hal.
have Halb : Rabs (FT2R al*FT2R b)<=u*P.
{ unfold P,x. rewrite !Rabs_mult.
  have H := Rmult_le_compat_r (Rabs (FT2R b)) _ _
    (Rabs_pos _) Hal.
  eapply Rle_trans; [exact H|]. right; ring. }
set w := (FT2R al*FT2R b+FT2R cl1)%R.
have Hw : Rabs w<=2*u*P+1501/1000*eta.
{ unfold w. eapply Rle_trans; [apply Rabs_triang|]. nra. }
have Hcl3r : FT2R cl3=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) w.
{ unfold cl3. rewrite -(BFMA_round_correct t al b cl1 Fcl3).
  unfold w. f_equal; ring. }
have He3 := round_FLT_error_rel_emin (t:=t) w.
fold u eta in He3. rewrite -Hcl3r in He3.
have Hcl3up : Rabs (FT2R cl3)<=
    (1+u)*(2*u*P+1501/1000*eta)+/2*eta.
{ have Htri := Rabs_triang (FT2R cl3-w) w.
  replace (FT2R cl3-w+w)%R with (FT2R cl3) in Htri by ring.
  have Huw := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Hw.
  nra. }
have Fe : is_finite_p (Fast2Sum ch cl3).
{ unfold d, DWTimesFP in FIN. fold ch cl1 cl3 in FIN. exact FIN. }
destruct (Rle_dec (Rabs (FT2R cl3)) (Rabs (FT2R ch)))
    as [Hord|Hnord].
- have Hsum := FastTwoSum_correct ch cl3 (proj1 Fe) Hord.
  change (FT2R (snd d)=FT2R ch+FT2R cl3-FT2R (fst d)) in Hsum.
  split.
  +
  change (Rabs ((FT2R (fst d)+FT2R (snd d))-
    (FT2R ah+FT2R al)*FT2R b)<=251/100*eta).
  rewrite Hsum.
  replace (FT2R (fst d)+(FT2R ch+FT2R cl3-FT2R (fst d))-
    (FT2R ah+FT2R al)*FT2R b)%R with
    ((FT2R ch+FT2R cl3)-(FT2R ah+FT2R al)*FT2R b)%R by ring.
  eapply Rle_trans; [exact Hcore|]. nra.
  + exact (Fast2Sum_is_DW ch cl3 (proj1 Fe) Hord).
- (* Unordered closing Fast2Sum.  |cl3| > |ch| can only happen when the
     leading product is tiny: |cl3| <= (1+u)(2uP + 1.501eta) + eta/2 while
     |ch| >= (1-u)P - eta/2, and at u <= 1/8 those cross only below
    4.5281*eta, so P < 4.6*eta.  The exact sum ch + cl3 is then within
     one binade of the subnormal range -- bound it through the compensated
     core error, not by the triangle inequality on |ch| and |cl3|
     separately, which would overshoot 2^(emin+3) -- and the shared
     FLT/FIX lattice at exponent emin makes Fast2Sum exact. *)
  have HuP' : u*P<=/8*P.
  { have H := Rmult_le_compat_r P _ _ HP0 Hu. nra. }
  have Hueta' : u*eta<=/8*eta.
  { have H := Rmult_le_compat_r eta _ _ (Rlt_le _ _ Heta0) Hu. nra. }
  have Hu2P : u*(u*P)<=/64*P.
  { have H := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) HuP'.
    have H2 : (/8*(u*P)<=/8*(/8*P))%R by nra.
    nra. }
  have HsmallP : P<46/10*eta.
  { apply Rnot_le_lt. move => HPbig.
    have Hcl3coarse : Rabs (FT2R cl3)<=9/32*P+22/10*eta.
    { eapply Rle_trans; [exact Hcl3up|]. nra. }
    have Hchcoarse : 7/8*P-/2*eta<=Rabs (FT2R ch).
    { eapply Rle_trans; [|exact Hchlo]. nra. }
    have Hcontra : Rabs (FT2R cl3)<=Rabs (FT2R ch) by nra.
    exact (Hnord Hcontra). }
  have Halb' : Rabs ((FT2R ah+FT2R al)*FT2R b)<=(1+u)*P.
  { replace ((FT2R ah+FT2R al)*FT2R b)%R with
        (x+FT2R al*FT2R b)%R by (unfold x; ring).
    eapply Rle_trans; [apply Rabs_triang|].
    fold P. nra. }
  have Hbig8 : 8*eta<=bpow radix2 (@common.emin t+fprec t).
  { unfold eta. have -> : (8:R)=bpow radix2 3 by (simpl;lra).
    rewrite -bpow_plus. apply bpow_le; lia. }
  have Hsumsmall : Rabs (FT2R ch+FT2R cl3)<=
      bpow radix2 (@common.emin t+fprec t).
  { have Htri2 := Rabs_triang
        ((FT2R ch+FT2R cl3)-(FT2R ah+FT2R al)*FT2R b)
        ((FT2R ah+FT2R al)*FT2R b).
    replace ((FT2R ch+FT2R cl3)-(FT2R ah+FT2R al)*FT2R b+
        (FT2R ah+FT2R al)*FT2R b)%R with (FT2R ch+FT2R cl3)%R
      in Htri2 by ring.
    have Hstep : Rabs (FT2R ch+FT2R cl3)<=251/100*eta+(1+u)*P.
    { eapply Rle_trans; [exact Htri2|].
      apply Rplus_le_compat; [exact Hcore|exact Halb']. }
    (* 2.51*eta + (1+u)*P < 2.51*eta + (9/8)*4.6*eta = 7.685*eta <= 8*eta.
       Linear in the atoms eta, P and u*P, so lra suffices. *)
    have Hstep2 : 251/100*eta+(1+u)*P<=8*eta.
    { have H1 : ((1+u)*P = P+u*P)%R by ring.
      rewrite H1. lra. }
    eapply Rle_trans; [exact Hstep|].
    eapply Rle_trans; [exact Hstep2|exact Hbig8]. }
  have Hsum := Fast2Sum_sum_exact_of_sum_small ch cl3 Fe Hsumsmall.
  fold d in Hsum.
  split.
  + change (Rabs ((FT2R (fst d)+FT2R (snd d))-
      (FT2R ah+FT2R al)*FT2R b)<=251/100*eta).
    rewrite Hsum. exact Hcore.
  + exact (DWTimesFP_double_word_of_sum ah al b FIN Hsum).
Qed.

(* ---------- public assembly: the whole range mixed API ---------- *)

(* Normal arm.  Above the TwoProd exactness threshold the product residual
   is representable and the entire Algorithm 9 error is relative, with no
   physical floor contribution: this is the local relative accuracy core
   cleared of its division by the exact product. *)
Local Lemma DWTimesFP_error_normal_arm {NANS : Nans} {t : type}
    {STD : is_standard t} (ah al b : ftype t) :
  (3 <= fprec t)%Z -> double_word_prop ah al ->
  is_finite_p (DWTimesFP ah al b) ->
  bpow radix2 (@common.emin t+2*fprec t-1) <=
    Rabs (FT2R ah*FT2R b) ->
  Rabs ((FT2R (fst (DWTimesFP ah al b))+
         FT2R (snd (DWTimesFP ah al b)))-
        (FT2R ah+FT2R al)*FT2R b)
    <= 2*bpow radix2 (-fprec t)^2*
         Rabs ((FT2R ah+FT2R al)*FT2R b).
Proof.
move => Hp3 DWa FIN Hbig.
move: (xryr_ne_0_of_big ah al b DWa Hbig) => [_ [Hyne [Hxrne Hne]]].
have Hrel := DWTimesFP_relative_accuracy_core ah al b DWa FIN Hp3 (or_intror Hbig).
unfold relative_error_DWTimesFP in Hrel.
set E := (FT2R (fst (DWTimesFP ah al b))+
          FT2R (snd (DWTimesFP ah al b))-
          (FT2R ah+FT2R al)*FT2R b)%R.
set Q := ((FT2R ah+FT2R al)*FT2R b)%R.
fold E Q in Hrel. fold Q.
have Heq : Rabs E = Rabs (E/Q)*Rabs Q.
{ rewrite -Rabs_mult. f_equal. field. exact Hne. }
rewrite Heq.
have Hmul := Rmult_le_compat_r (Rabs Q) _ _ (Rabs_pos _) Hrel.
eapply Rle_trans; [exact Hmul|]. right; ring.
Qed.

(* The public whole range result bundles the conventional mixed bound with
   output validity.  The single local core below performs the only normal/gap
   split used to establish that bundle. *)
Definition DWTimesFP_guarantee {NANS : Nans} {t : type}
    {STD : is_standard t} (xh xl y : ftype t) : Prop :=
  let '(zh, zl) := DWTimesFP xh xl y in
  Rabs
    (FT2R zh + FT2R zl - (FT2R xh + FT2R xl) * FT2R y)
    <= 2 * bpow Zaux.radix2 (- fprec t) ^ 2 *
         Rabs ((FT2R xh + FT2R xl) * FT2R y) +
       251 / 100 * bpow Zaux.radix2 (@common.emin t) /\
  double_word_prop zh zl.

Local Lemma DWTimesFP_guarantee_core {NANS : Nans} {t : type}
    {STD : is_standard t} (xh xl y : ftype t) :
  (3 <= fprec t)%Z ->
  double_word_prop xh xl ->
  is_finite_p (DWTimesFP xh xl y) ->
  DWTimesFP_guarantee xh xl y.
Proof.
move => Hp3 DWa FIN.
destruct (Rle_dec
  (bpow radix2 (@common.emin t + 2*fprec t - 1))
  (Rabs (FT2R xh * FT2R y))) as [Hbig | Hgap].
- have Hnormal := DWTimesFP_error_normal_arm xh xl y Hp3 DWa FIN Hbig.
  have Heta : 0 <= 251/100*bpow radix2 (@common.emin t).
  { have := bpow_ge_0 radix2 (@common.emin t). nra. }
  have Hacc :
    Rabs ((FT2R (fst (DWTimesFP xh xl y)) +
           FT2R (snd (DWTimesFP xh xl y))) -
          (FT2R xh + FT2R xl) * FT2R y)
    <= 2*bpow radix2 (-fprec t)^2 *
         Rabs ((FT2R xh + FT2R xl) * FT2R y) +
       251/100*bpow radix2 (@common.emin t) by lra.
  have Fmul := DWTimesFP_mul_finite xh xl y FIN.
  have Fcl3 := DWTimesFP_correction_finite xh xl y FIN.
  have Hord := aux_cl3_le_ch xh xl y DWa Fmul Fcl3 Hbig.
  have Hdw : double_word_prop (fst (DWTimesFP xh xl y))
      (snd (DWTimesFP xh xl y))
    by exact (DWTimesFP_double_word_from_pre
      xh xl y (proj1 FIN) Hord).
  unfold DWTimesFP_guarantee.
  revert Hacc Hdw.
  destruct (DWTimesFP xh xl y) as [zh zl].
  cbn [fst snd]. intros Hacc Hdw. exact (conj Hacc Hdw).
- have [Hfloor Hdw] := DWTimesFP_error_floor_gap
    xh xl y Hp3 DWa FIN Hgap.
  have Hu2 : 0 <= 2*bpow radix2 (-fprec t)^2 *
      Rabs ((FT2R xh + FT2R xl) * FT2R y).
  { have := bpow_ge_0 radix2 (-fprec t).
    have := Rabs_pos ((FT2R xh + FT2R xl) * FT2R y). nra. }
  have Hacc :
    Rabs ((FT2R (fst (DWTimesFP xh xl y)) +
           FT2R (snd (DWTimesFP xh xl y))) -
          (FT2R xh + FT2R xl) * FT2R y)
    <= 2*bpow radix2 (-fprec t)^2 *
         Rabs ((FT2R xh + FT2R xl) * FT2R y) +
       251/100*bpow radix2 (@common.emin t) by lra.
  unfold DWTimesFP_guarantee.
  revert Hacc Hdw.
  destruct (DWTimesFP xh xl y) as [zh zl].
  cbn [fst snd]. intros Hacc Hdw. exact (conj Hacc Hdw).
Qed.

(* Public mixed interface.  [DWTimesFP_weak_pre_and_finite_post_cond] combines the input
   double-word property with result finiteness.  The following theorems expose
   accuracy, output validity, and their conjunction.  A caller may instead
   establish [DWTimesFP_strong_precond] before the operation.  Neither
   route excludes the [Fast2Mult] underflow gap. *)

Lemma DWTimesFP_weak_pre_and_finite_post_cond_of_strong_precond {NANS : Nans} {t : type}
    {STD : is_standard t} (xh xl y : ftype t) :
  DWTimesFP_strong_precond xh xl y ->
  DWTimesFP_weak_pre_and_finite_post_cond xh xl y.
Proof.
move => Hsafe.
have Hfin := DWTimesFP_finite_post_cond_from_strong_precond xh xl y Hsafe.
move: Hsafe => [_ [Hdw _]].
unfold DWTimesFP_weak_pre_and_finite_post_cond, DWTimesFP_weak_precond,
       DWTimesFP_finite_post_cond.
exact (conj Hdw Hfin).
Qed.

Theorem DWTimesFP_accuracy_from_weak_pre_and_finite_post_cond
    {NANS : Nans} {t : type} {STD : is_standard t}
    (xh xl y : ftype t) :
  (3 <= fprec t)%Z ->
  DWTimesFP_weak_pre_and_finite_post_cond xh xl y ->
  Rabs
    (FT2R (fst (DWTimesFP xh xl y)) +
       FT2R (snd (DWTimesFP xh xl y)) -
       (FT2R xh + FT2R xl) * FT2R y)
    <= 2 * bpow Zaux.radix2 (- fprec t) ^ 2 *
         Rabs ((FT2R xh + FT2R xl) * FT2R y) +
       251 / 100 * bpow Zaux.radix2 (@common.emin t).
Proof.
move => Hp3 [DWa FIN].
have Hguarantee :=
  DWTimesFP_guarantee_core xh xl y Hp3 DWa FIN.
unfold DWTimesFP_guarantee in Hguarantee.
destruct (DWTimesFP xh xl y) as [zh zl].
exact (proj1 Hguarantee).
Qed.

Theorem DWTimesFP_double_word_from_weak_pre_and_finite_post_cond
    {NANS : Nans} {t : type} {STD : is_standard t}
    (xh xl y : ftype t) :
  (3 <= fprec t)%Z ->
  DWTimesFP_weak_pre_and_finite_post_cond xh xl y ->
  double_word_prop (fst (DWTimesFP xh xl y))
                   (snd (DWTimesFP xh xl y)).
Proof.
move => Hp3 [DWa FIN].
have Hguarantee :=
  DWTimesFP_guarantee_core xh xl y Hp3 DWa FIN.
unfold DWTimesFP_guarantee in Hguarantee.
destruct (DWTimesFP xh xl y) as [zh zl].
exact (proj2 Hguarantee).
Qed.

Theorem DWTimesFP_guarantee_from_weak_pre_and_finite_post_cond
    {NANS : Nans} {t : type} {STD : is_standard t}
    (xh xl y : ftype t) :
  (3 <= fprec t)%Z ->
  DWTimesFP_weak_pre_and_finite_post_cond xh xl y ->
  DWTimesFP_guarantee xh xl y.
Proof.
intros Hp3 Hcond.
have Hacc :=
  DWTimesFP_accuracy_from_weak_pre_and_finite_post_cond xh xl y Hp3 Hcond.
have Hdw :=
  DWTimesFP_double_word_from_weak_pre_and_finite_post_cond xh xl y Hp3 Hcond.
unfold DWTimesFP_guarantee.
revert Hacc Hdw.
destruct (DWTimesFP xh xl y) as [zh zl].
cbn [fst snd]. intros Hacc Hdw. exact (conj Hacc Hdw).
Qed.

Theorem DWTimesFP_guarantee_from_strong_precond
    {NANS : Nans} {t : type} {STD : is_standard t}
    (xh xl y : ftype t) :
  (3 <= fprec t)%Z ->
  DWTimesFP_strong_precond xh xl y ->
  DWTimesFP_guarantee xh xl y.
Proof.
intros Hp3 Hsafe.
apply DWTimesFP_guarantee_from_weak_pre_and_finite_post_cond; [exact Hp3 |].
exact (DWTimesFP_weak_pre_and_finite_post_cond_of_strong_precond xh xl y Hsafe).
Qed.

Lemma DWTimesFP_inputs_finite_of_finite_post_cond {NANS : Nans} {t : type}
    {STD : is_standard t} (xh xl y : ftype t) :
  DWTimesFP_finite_post_cond xh xl y ->
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite y = true.
Proof.
unfold DWTimesFP_finite_post_cond.
move => Hfin.
have [Hfxh Hfy] := BMULT_finite_e t xh y
  (DWTimesFP_mul_finite xh xl y Hfin).
exact (conj Hfxh (conj (DWTimesFP_xl_finite xh xl y Hfin) Hfy)).
Qed.
