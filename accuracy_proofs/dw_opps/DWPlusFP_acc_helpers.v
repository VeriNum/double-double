(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** This file contains helper lemmas for accuracy proofs 
for double-word  plus a (double-word, floating-point number *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common FLT_lemmas.
Require Import DWPlus DDModels DWord_defs.
Require Import TwoSum_acc Fast2Sum_acc.
From Flocq Require Import Pff2Flocq Core.

Require Import mathcomp.ssreflect.ssreflect.

(* for choice functions : choice = fun x0 : Z => negb (Z.even x0) *)
From Stdlib Require Import Logic.FunctionalExtensionality.

Section FiniteFactsDWPlusFP.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Variables (xh xl y : ftype t).

Hypothesis FIN : is_finite_p (DWPlusFP xh xl y). 

Ltac prove_finite := 
  move: FIN;
  rewrite /DWPlusFP/is_finite_p //=;
  move => [];
  subexpr_finite => //
  .

Fact FIN3 : is_finite (BPLUS xh y) = true.
Proof. prove_finite. Qed.

Fact FINxh : is_finite xh = true.
Proof. prove_finite. Qed.

Fact FIN1 : is_finite_p (TwoSumF xh y).
Proof.
Proof. prove_finite. Qed.

Let sl := snd (TwoSumF xh y).

Fact FIN2 : is_finite (BPLUS xl sl) = true.
Proof. prove_finite. Qed.

Fact FINxl : is_finite xl = true.
Proof. prove_finite. Qed.

End FiniteFactsDWPlusFP.

Section  CorrectDWPlusFP'.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Let ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 
Let emin :=  (@common.emin t).

Variables (xh xl y : ftype t).

Hypothesis  xE : double_word xh xl.
Hypothesis FIN : is_finite_p (DWPlusFP xh xl y). 
Hypothesis Hp3 : (3 <= fprec t)%Z.

Theorem DWPlusFP_eq :
  DWPlus.DWPlusFP (fprec t) choice (FT2R xh) (FT2R xl) (FT2R y) = F2Rp (DWPlusFP xh xl y).
Proof.
have FIN3: (is_finite_p (TwoSumF xh y)) by
apply: (FIN1 _ xl _) => //.
have FIN4 : is_finite (BPLUS xl (snd (TwoSumF xh y))) = true by
apply: FIN2 => //.
move : FIN. move => [].
rewrite /DWPlus.DWPlusFP/DWPlusFP/fst/snd.
replace  (TwoSumF xh y ) with
  (fst (TwoSumF xh y), snd (TwoSumF xh y )) => //.
replace
(Fast2Sum (fst (TwoSumF xh y)) (BPLUS xl (snd (TwoSumF xh y))))
with 
(fst (Fast2Sum (fst (TwoSumF xh y)) (BPLUS xl (snd (TwoSumF xh y)))),
snd (Fast2Sum (fst (TwoSumF xh y)) (BPLUS xl (snd (TwoSumF xh y))))) => //.
move => FIN1 FIN2. 
have Heq: (TwoSum (fprec t) choice (FT2R xh) (FT2R y)) =
  (TwoSum_sum (fprec t) choice (FT2R xh) (FT2R y) ,
    TwoSum_err (fprec t) choice (FT2R xh) (FT2R y) ) => //.
have Herr : TwoSum_err (fprec t) choice (FT2R xh) (FT2R y) = FT2R (snd (TwoSumF xh y)).
{ pose proof TwoSumEq_FLT xh y FIN3. rewrite Heq in H. 
inversion H. rewrite H2 /TwoSumF => //. } 
have Hsum : TwoSum_sum (fprec t) choice (FT2R xh) (FT2R y) = FT2R (fst (TwoSumF xh y)).
{ pose proof TwoSumEq_FLT xh y FIN3. rewrite Heq in H. 
inversion H. rewrite H1 /TwoSumF => //. } 

rewrite Herr Hsum.
destruct (Req_dec (FT2R xh + FT2R y) 0).
{ apply TwoSumF_eq in H => //.
inversion H.
rewrite Fast2Sum_2sum0' => //; 
rewrite /TwoSumF/fst/snd.
rewrite H2 H1 Rplus_0_r.
rewrite F2Sum.Fast2Sum0f round_generic => //. 
1,2,3: rewrite -!B2R_float_of_ftype.
all: try apply (generic_format_FLX_FLT radix2 emin);
try apply Binary.generic_format_B2R.
now rewrite H2 H1. } 

destruct (Rle_or_lt 
(bpow radix2 (emin + fprec t - 1))  
(Rabs
  (FT2R xl +
   FT2R (snd (TwoSumF xh y))))) as [HUF|HUF].

{ rewrite -FastTwoSumEq_FLT => //; f_equal.
BPLUS_correct t xl (snd (TwoSumF xh y)).
rewrite (round_FLT_FLX radix2 (@common.emin t)) => //.
by rewrite !B2R_float_of_ftype. }

rewrite -FastTwoSumEq_FLT => //; f_equal.
rewrite BPLUS_UF_exact => //.
rewrite round_generic => //; f_equal.
apply: (generic_format_FLX_FLT _ emin).
apply: Plus_error.FLT_format_plus_small.
1,2 : rewrite -!B2R_float_of_ftype;
  apply: Binary.generic_format_B2R.
 
refine (Rle_trans _ _ _ (Rlt_le _ _ _) _ ). apply HUF.
apply bpow_le; lia.
Qed.

Lemma DWPlusFP_double_word : 
double_word (fst (DWPlusFP xh xl y)) (snd (DWPlusFP xh xl y)).
Proof.
apply DWdouble_word_dw => [//=|].
have Hp : (1 < fprec t)%Z by lia.
have Hch: choice = (fun n : Z => negb (Z.even n)) by
apply functional_extensionality; rewrite /choice //=.
pose proof (DWPlusFP_correct Hp Hch Hp3).
specialize (H (FT2R xh) (FT2R xl) (FT2R y)).
pose proof DWPlusFP_eq.
move: H0.
destruct (DWPlus.DWPlusFP _ _ (FT2R xh) (FT2R xl) (FT2R y)).
destruct (DWPlusFP xh xl y).
simpl in *. rewrite /F2Rp. move => H1. inversion H1; subst.
apply H.
rewrite -B2R_float_of_ftype.
apply (@generic_format_FLX_FLT radix2 emin),
   Binary.generic_format_B2R.
apply dw_word_DWdouble => //.
Qed.

End CorrectDWPlusFP'.

Section FiniteDWPlusFP.
Context {NANS: Nans} {t : type} {STD: is_standard t}.
Variables (xh xl y : ftype t).

Hypothesis DWx : double_word xh xl.

(* No-overflow bound for the TwoSum sum [round (xh + y)], expressed via the
   relative-error model [round (xh + y) = (xh + y) * (1 + d1)].  The relative
   error [d1] returned by [FLT_plus_error_N_ex] is bounded by
   [u_ro / (1 + u_ro)] with [u_ro = /2 * 2^(1 - fprec t)]; since [fprec t >= 2]
   we have [|d1| <= /4], and with [|xh| <= Omega/2], [|y| <= Omega/4] the product
   is at most [(3/4) * (5/4) * Omega = (15/16) * Omega < Omega].  This is the
   type-generic replacement for the [interval]-based overflow check (which
   relied on [femax t = 1024]). *)
Lemma sum_round_no_overflow (d1 : R)
  (Hd1 : Rabs d1 <= /2 * bpow radix2 (Z.pos_sub 1 (fprecp t))
                     / (1 + /2 * bpow radix2 (Z.pos_sub 1 (fprecp t))))
  (Hxh : Rabs (FT2R xh) <= /2 * bpow radix2 (femax t))
  (Hy  : Rabs (FT2R y)  <= /4 * bpow radix2 (femax t)) :
  Rabs ((FT2R xh + FT2R y) * (1 + d1)) < bpow radix2 (femax t).
Proof.
have HM : (0 < bpow radix2 (femax t))%R by apply bpow_gt_0.
(* The relative error d1 is at most 1/4, since u_ro = /2*2^(1-fprec) <= /4. *)
have Hupos : (0 < /2 * bpow radix2 (Z.pos_sub 1 (fprecp t)))%R.
{ have := bpow_gt_0 radix2 (Z.pos_sub 1 (fprecp t)). lra. }
have Hu4 : (/2 * bpow radix2 (Z.pos_sub 1 (fprecp t)) <= /4)%R.
{ have hb : (bpow radix2 (Z.pos_sub 1 (fprecp t)) <= bpow radix2 (-1))%R.
  { apply bpow_le. rewrite <- Pos2Z.add_pos_neg.
    have H := fprec_gt_one t; rewrite fprec_eq in H; lia. }
  have h2 : (bpow radix2 (-1) = /2)%R by (simpl; lra).
  lra. }
have Hd1' : (Rabs d1 <= /4)%R.
{ refine (Rle_trans _ _ _ Hd1 _).
  apply Rcomplements.Rle_div_l; lra. }
(* |xh + y| <= (3/4)*Omega, |1 + d1| <= 5/4, so the product is < Omega *)
rewrite Rabs_mult.
apply (Rle_lt_trans _ ((3/4 * bpow radix2 (femax t)) * (5/4))).
- apply Rmult_le_compat; try apply Rabs_pos.
  + eapply Rle_trans; [apply Rabs_triang|]. lra.
  + eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_R1. lra.
- nra.
Qed.

Lemma TwoSumF_sum_finite
(HFINxh: Binary.is_finite (fprec t) (femax t) (float_of_ftype xh) = true)
(HFINy : Binary.is_finite (fprec t) (femax t) (float_of_ftype y) = true)
(Hxh : Rabs (FT2R xh) <= /2 * (bpow radix2 (femax t)))
(Hy :  Rabs (FT2R y)  <= /4 * (bpow radix2 (femax t))) :
let sh := TwoSumF_sum xh y in
Binary.is_finite (fprec t) (femax t) (float_of_ftype sh) = true.
Proof.
rewrite /TwoSumF_sum/TwoSumF_err/TwoSumF/fst/snd => //.
set xh' := float_of_ftype xh.
set y' := float_of_ftype y.
have Hov1: 
        (Rabs
           (round radix2 (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
              (Binary.B2R (fprec t) (femax t) xh' + Binary.B2R (fprec t) (femax t) y'))) <
        (bpow radix2 (femax t)).
pose proof
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R xh)
  (FT2R y) ).
destruct H as (d1 & Hd & B).  
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite !B2R_float_of_ftype.
rewrite B. clear B.  
move: Hd . unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
apply sum_round_no_overflow => //.
pose proof 
  (@Binary.Bplus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
  BinarySingleNaN.mode_NE xh' y'
  HFINxh HFINy) as Hp.
move: Hp.
rewrite Rlt_bool_true =>//. move =>  [] A [] Hp _; auto.
rewrite -Hp  /BPLUS /BINOP float_of_ftype_of_float /xh'/y' => //.
Qed.

Notation fexp:= ((SpecFloat.fexp (fprec t) (femax t))).

Lemma TwoSumF_err_finite_bnd
(Hxh : Rabs (FT2R xh) <= /4 * (bpow radix2 (femax t))):
Rabs (FT2R xh) <=  (/ 2 * bpow radix2 (femax t)) .
Proof.
have Hpos : (0 < bpow radix2 (femax t)) by apply bpow_gt_0.
refine (Rle_trans _ _ _ Hxh _); nra.
Qed.

(** ** Interval-free no-overflow toolkit.

   To check that the rounded sub-expressions of [TwoSumF_err] stay below the
   overflow threshold [Omega = bpow radix2 (femax t)] for an arbitrary type [t]
   (where [Omega] is not a literal, so [interval] does not apply), we expand
   each rounding via its relative-error model and bound the result
   compositionally.  Each [b_*] lemma states [Rabs z <= c]; [mag] chains them
   over an arithmetic tree, never forming the triple products that defeat [nra],
   and [nob_close] finishes with [lra] on a pure-[Omega] inequality. *)

(* u_ro = /2 * 2^(1-fprec) <= /8 (as fprec t >= 3); the FLT bound u_ro/(1+u_ro)
   is also <= /8.  The bound /8 (rather than /4, which only needs fprec >= 2) is
   what makes the deepest sub-expression of the error term ([err], with three
   nested roundings) provably below the overflow threshold by the compositional
   bound below: the three [(1 + d)] factors compound to [(9/8)^3], and the input
   magnitudes [Omega/4] then keep the product strictly under [Omega]. *)
Lemma rel_le_eighth (Hp3 : (3 <= fprec t)%Z) : (default_rel t <= /8)%R.
Proof.
rewrite /default_rel.
have he : (/4 = bpow radix2 (-2))%R by (simpl; lra).
have hb : (bpow radix2 (- fprec t + 1) <= /4)%R.
{ rewrite he; apply bpow_le; lia. }
lra.
Qed.

Lemma reldiv_le_eighth (Hp3 : (3 <= fprec t)%Z) :
  (Relative.u_ro radix2 (fprec t) / (1 + Relative.u_ro radix2 (fprec t)) <= /8)%R.
Proof.
have hb0 : (0 < Relative.u_ro radix2 (fprec t))%R.
{ rewrite /Relative.u_ro. have := bpow_gt_0 radix2 (- fprec t + 1). lra. }
have hb : (Relative.u_ro radix2 (fprec t) <= /8)%R.
{ rewrite /Relative.u_ro -/(default_rel t). apply rel_le_eighth, Hp3. }
have hden : (0 < 1 + Relative.u_ro radix2 (fprec t))%R by lra.
apply Rcomplements.Rle_div_l; nra.
Qed.

(* Compositional magnitude bounds. *)
Lemma b_plus (a b ca cb : R) :
  Rabs a <= ca -> Rabs b <= cb -> Rabs (a + b) <= ca + cb.
Proof. move => Ha Hb. eapply Rle_trans; [apply Rabs_triang|]. lra. Qed.

Lemma b_minus (a b ca cb : R) :
  Rabs a <= ca -> Rabs b <= cb -> Rabs (a - b) <= ca + cb.
Proof. move => Ha Hb. eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_Ropp. lra. Qed.

Lemma b_opp (a c : R) : Rabs a <= c -> Rabs (- a) <= c.
Proof. move => H. rewrite Rabs_Ropp //. Qed.

Lemma b_mul1d (a d ca : R) :
  Rabs a <= ca -> Rabs d <= /8 -> Rabs (a * (1 + d)) <= ca * (9/8).
Proof.
move => Ha Hd. rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos.
- exact Ha.
- eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_R1. lra.
Qed.

Lemma b_muld (a d ca : R) :
  Rabs a <= ca -> Rabs d <= /8 -> Rabs (a * d) <= ca * (/8).
Proof.
move => Ha Hd. rewrite Rabs_mult.
apply Rmult_le_compat; try apply Rabs_pos; [exact Ha|exact Hd].
Qed.

Ltac mag :=
  match goal with
  | |- Rabs (?a + ?b) <= _ => eapply b_plus; [mag|mag]
  | |- Rabs (?a - ?b) <= _ => eapply b_minus; [mag|mag]
  | |- Rabs (- ?a) <= _ => apply b_opp; mag
  | |- Rabs (?a * (1 + ?d)) <= _ => eapply b_mul1d; [mag | assumption]
  | |- Rabs (?a * ?d) <= _ => eapply b_muld; [mag | assumption]
  | |- Rabs ?x <= _ => eassumption
  end.

(* [lra] runs after the [mag] bracket closes so the [Rle_lt_trans] evar is
   instantiated. *)
Ltac nob_close :=
  generalize (bpow_gt_0 radix2 (femax t)); intro;
  eapply Rle_lt_trans; [ mag | ]; lra.

(* Normalise relative-error hypotheses to the uniform bound [Rabs d <= /8].
   Requires a hypothesis [Hp3 : 3 <= fprec t] in context. *)
Ltac eighth_bounds :=
  match goal with HP : (3 <= fprec t)%Z |- _ =>
  repeat match goal with
  | H : Rabs ?d <= default_rel t |- _ =>
      apply (fun h => Rle_trans _ _ _ h (rel_le_eighth HP)) in H
  | H : Rabs ?d <= Relative.u_ro radix2 (fprec t)
                    / (1 + Relative.u_ro radix2 (fprec t)) |- _ =>
      apply (fun h => Rle_trans _ _ _ h (reldiv_le_eighth HP)) in H
  end end.

(* Reduce a no-overflow obligation to its structured real expression:
   introduce the relative error of the pending round, then expand the FT2R of
   every finite sub-term. *)
Ltac gf_side :=
  try apply Generic_fmt.generic_format_opp;
  rewrite -B2R_float_of_ftype; apply Binary.generic_format_B2R.

Ltac show_nob :=
  rewrite /Bplus_no_overflow/Bminus_no_overflow;
  match goal with
  | |- Rabs (round ?r ?f ?m (?A + ?B)) < _ =>
    let H := fresh in
    destruct (Plus_error.FLT_plus_error_N_ex radix2 (SpecFloat.emin (fprec t)(femax t))
      (fprec t) (fun x0 : Z => negb (Z.even x0)) A B) as (?d & ?Hd & H);
    [ gf_side .. | rewrite H; clear H ]
  | |- Rabs (round ?r ?f ?m (?A - ?B)) < _ =>
    let H := fresh in
    destruct (Plus_error.FLT_plus_error_N_ex radix2 (SpecFloat.emin (fprec t)(femax t))
      (fprec t) (fun x0 : Z => negb (Z.even x0)) A (-B)) as (?d & ?Hd & H);
    [ gf_side .. | replace (A - B) with (A + - B) by ring; rewrite H; clear H ]
  end.

Ltac expand_ft2r :=
  repeat match goal with
  | H : is_finite (BPLUS ?a ?b) = true |- context [FT2R (BPLUS ?a ?b)] =>
      let E := fresh "E" in
      destruct (BPLUS_accurate' _ _ _ H) as (?d & ?Hd & E); rewrite E; clear E
  | H : is_finite (BMINUS ?a ?b) = true |- context [FT2R (BMINUS ?a ?b)] =>
      let E := fresh "E" in
      destruct (BMINUS_accurate' _ _ _ H) as (?d & ?Hd & E); rewrite E; clear E
  end.

(* Per-shape no-overflow lemmas for the five rounded sub-expressions of
   [TwoSumF_err xh y].  Each exposes the relevant TwoSum cancellation with
   [ring], then bounds the residual with [mag]/[nob_close].  Inputs satisfy
   [|xh|,|y| <= Omega/4]; relative errors satisfy [|d| <= /8]. *)
Lemma nofl_a' (d1 d0 : R)
  (Hd1 : Rabs d1 <= /8) (Hd0 : Rabs d0 <= /8)
  (Hxh : Rabs (FT2R xh) <= /4 * bpow radix2 (femax t))
  (Hy  : Rabs (FT2R y)  <= /4 * bpow radix2 (femax t)) :
  Rabs (((FT2R xh + FT2R y) * (1 + d1) - FT2R y) * (1 + d0)) < bpow radix2 (femax t).
Proof.
replace (((FT2R xh + FT2R y) * (1 + d1) - FT2R y) * (1 + d0))
  with ((FT2R xh + (FT2R xh + FT2R y) * d1) * (1 + d0)) by ring.
nob_close.
Qed.

Lemma nofl_b' (d3 d2 d1 d0 : R)
  (Hd3 : Rabs d3 <= /8) (Hd2 : Rabs d2 <= /8) (Hd1 : Rabs d1 <= /8) (Hd0 : Rabs d0 <= /8)
  (Hxh : Rabs (FT2R xh) <= /4 * bpow radix2 (femax t))
  (Hy  : Rabs (FT2R y)  <= /4 * bpow radix2 (femax t)) :
  Rabs (((FT2R xh + FT2R y) * (1 + d1)
         - ((FT2R xh + FT2R y) * (1 + d3) - FT2R y) * (1 + d2)) * (1 + d0))
    < bpow radix2 (femax t).
Proof.
replace (((FT2R xh + FT2R y) * (1 + d1)
          - ((FT2R xh + FT2R y) * (1 + d3) - FT2R y) * (1 + d2)) * (1 + d0))
  with ((FT2R y + (FT2R xh + FT2R y) * d1 - FT2R xh * d2
         - (FT2R xh + FT2R y) * d3 - (FT2R xh + FT2R y) * d3 * d2) * (1 + d0)) by ring.
nob_close.
Qed.

Lemma nofl_da (d1 d0 d : R)
  (Hd1 : Rabs d1 <= /8) (Hd0 : Rabs d0 <= /8) (Hd : Rabs d <= /8)
  (Hxh : Rabs (FT2R xh) <= /4 * bpow radix2 (femax t))
  (Hy  : Rabs (FT2R y)  <= /4 * bpow radix2 (femax t)) :
  Rabs ((FT2R xh - ((FT2R xh + FT2R y) * (1 + d1) - FT2R y) * (1 + d0)) * (1 + d))
    < bpow radix2 (femax t).
Proof.
replace ((FT2R xh - ((FT2R xh + FT2R y) * (1 + d1) - FT2R y) * (1 + d0)) * (1 + d))
  with ((- (FT2R xh * d0) - (FT2R xh + FT2R y) * d1 * (1 + d0)) * (1 + d)) by ring.
nob_close.
Qed.

Lemma nofl_db (d3 d2 d1 d0 d : R)
  (Hd3 : Rabs d3 <= /8) (Hd2 : Rabs d2 <= /8) (Hd1 : Rabs d1 <= /8)
  (Hd0 : Rabs d0 <= /8) (Hd : Rabs d <= /8)
  (Hxh : Rabs (FT2R xh) <= /4 * bpow radix2 (femax t))
  (Hy  : Rabs (FT2R y)  <= /4 * bpow radix2 (femax t)) :
  Rabs ((FT2R y - ((FT2R xh + FT2R y) * (1 + d1)
         - ((FT2R xh + FT2R y) * (1 + d3) - FT2R y) * (1 + d2)) * (1 + d0)) * (1 + d))
    < bpow radix2 (femax t).
Proof.
replace ((FT2R y - ((FT2R xh + FT2R y) * (1 + d1)
          - ((FT2R xh + FT2R y) * (1 + d3) - FT2R y) * (1 + d2)) * (1 + d0)) * (1 + d))
  with ((- ((FT2R xh + FT2R y) * d1) + FT2R xh * d2 + (FT2R xh + FT2R y) * d3
         + (FT2R xh + FT2R y) * d3 * d2
         - (FT2R y + (FT2R xh + FT2R y) * d1 - FT2R xh * d2
            - (FT2R xh + FT2R y) * d3 - (FT2R xh + FT2R y) * d3 * d2) * d0) * (1 + d)) by ring.
nob_close.
Qed.

Lemma nofl_err (d7 d6 d5 d4 d3 d2 d1 d0 d : R)
  (Hd7 : Rabs d7 <= /8) (Hd6 : Rabs d6 <= /8) (Hd5 : Rabs d5 <= /8) (Hd4 : Rabs d4 <= /8)
  (Hd3 : Rabs d3 <= /8) (Hd2 : Rabs d2 <= /8) (Hd1 : Rabs d1 <= /8) (Hd0 : Rabs d0 <= /8)
  (Hd : Rabs d <= /8)
  (Hxh : Rabs (FT2R xh) <= /4 * bpow radix2 (femax t))
  (Hy  : Rabs (FT2R y)  <= /4 * bpow radix2 (femax t)) :
  Rabs (((FT2R xh - ((FT2R xh + FT2R y) * (1 + d2) - FT2R y) * (1 + d1)) * (1 + d0)
         + (FT2R y - ((FT2R xh + FT2R y) * (1 + d5)
            - ((FT2R xh + FT2R y) * (1 + d7) - FT2R y) * (1 + d6)) * (1 + d4)) * (1 + d3))
        * (1 + d)) < bpow radix2 (femax t).
Proof.
replace (((FT2R xh - ((FT2R xh + FT2R y) * (1 + d2) - FT2R y) * (1 + d1)) * (1 + d0)
          + (FT2R y - ((FT2R xh + FT2R y) * (1 + d5)
             - ((FT2R xh + FT2R y) * (1 + d7) - FT2R y) * (1 + d6)) * (1 + d4)) * (1 + d3))
         * (1 + d))
  with (((- (FT2R xh * d1) - (FT2R xh + FT2R y) * d2 * (1 + d1)) * (1 + d0)
         + (- ((FT2R xh + FT2R y) * d5) + FT2R xh * d6 + (FT2R xh + FT2R y) * d7
            + (FT2R xh + FT2R y) * d7 * d6
            - (FT2R y + (FT2R xh + FT2R y) * d5 - FT2R xh * d6
               - (FT2R xh + FT2R y) * d7 - (FT2R xh + FT2R y) * d7 * d6) * d4) * (1 + d3))
        * (1 + d)) by ring.
nob_close.
Qed.



Lemma TwoSumF_err_finite
(HFINxh: Binary.is_finite (fprec t) (femax t) (float_of_ftype xh) = true)
(HFINy : Binary.is_finite (fprec t) (femax t) (float_of_ftype y) = true)
(Hp3 : (3 <= fprec t)%Z)
(Hxh : Rabs (FT2R xh) <= /4 * (bpow radix2 (femax t)))
(Hy : Rabs (FT2R y) <= /4 * (bpow radix2 (femax t))):
let sl := TwoSumF_err xh y in
Binary.is_finite (fprec t) (femax t) (float_of_ftype sl) = true.
Proof.
rewrite /TwoSumF_err/TwoSumF/fst/snd => //.
rewrite -is_finite_Binary.
rewrite -is_finite_Binary in HFINxh.
rewrite -is_finite_Binary in HFINy.
(* Establish finiteness of every rounded sub-expression bottom-up via the
   FT2R-level no-overflow lemmas, discharging each no-overflow obligation with
   the matching per-shape bound. *)
have FINs : is_finite (BPLUS xh y) = true.
{ apply no_overflow_sum_is_finite; [exact HFINxh|exact HFINy|].
  show_nob. expand_ft2r. eighth_bounds. nob_close. }
have FINa : is_finite (BMINUS (BPLUS xh y) y) = true.
{ apply no_overflow_minus_is_finite; [exact FINs|exact HFINy|].
  show_nob. expand_ft2r. eighth_bounds. apply nofl_a'; assumption. }
have FINb : is_finite (BMINUS (BPLUS xh y) (BMINUS (BPLUS xh y) y)) = true.
{ apply no_overflow_minus_is_finite; [exact FINs|exact FINa|].
  show_nob. expand_ft2r. eighth_bounds. apply nofl_b'; assumption. }
have FINda : is_finite (BMINUS xh (BMINUS (BPLUS xh y) y)) = true.
{ apply no_overflow_minus_is_finite; [exact HFINxh|exact FINa|].
  show_nob. expand_ft2r. eighth_bounds. apply nofl_da; assumption. }
have FINdb : is_finite (BMINUS y (BMINUS (BPLUS xh y) (BMINUS (BPLUS xh y) y))) = true.
{ apply no_overflow_minus_is_finite; [exact HFINy|exact FINb|].
  show_nob. expand_ft2r. eighth_bounds. apply nofl_db; assumption. }
apply no_overflow_sum_is_finite; [exact FINda|exact FINdb|].
show_nob. expand_ft2r. eighth_bounds. apply nofl_err; assumption.
Qed.
Theorem is_finite_p_TwoSum
(HFINxh: Binary.is_finite (fprec t) (femax t) (float_of_ftype xh) = true)
(HFINy : Binary.is_finite (fprec t) (femax t) (float_of_ftype y) = true)
(Hp3 : (3 <= fprec t)%Z)
(Hxh : Rabs (FT2R xh) <= /4 * (bpow radix2 (femax t)))
(Hy :  Rabs (FT2R y)  <= /4 * (bpow radix2 (femax t)))  :
is_finite_p (TwoSumF xh y).
Proof.
rewrite /is_finite_p; split.
{ rewrite is_finite_Binary.
  apply TwoSumF_sum_finite; try assumption.
  (* the sum needs the [/2] high-part bound, supplied from [/4] by the bnd lemma *)
  apply TwoSumF_err_finite_bnd; assumption. }
rewrite is_finite_Binary.
apply TwoSumF_err_finite; assumption.
Qed.

Let sh := TwoSumF_sum xh y.
Let sl := TwoSumF_err xh y.

Lemma xl_bnd 
(Hxh : Rabs (FT2R xh) <= /2 * (bpow radix2 (femax t))) :
Rabs (FT2R xl) <= / 2 * bpow radix2 (femax t - fprec t).
Proof.
apply dw_ulp in DWx.
refine (Rle_trans _ _ _  DWx _).
apply Rmult_le_compat_l; try nra.
(* ulp (FT2R xh) <= 2^(femax - fprec), since |xh| <= 2^(femax-1) = (1/2)*Omega *)
have Hxhb : Rabs (FT2R xh) <= bpow radix2 (femax t - 1).
{ refine (Rle_trans _ _ _ Hxh _).
  have -> : (femax t - 1 = -1 + femax t)%Z by ring.
  rewrite bpow_plus; simpl; lra. }
refine (Rle_trans _ (ulp radix2 (SpecFloat.fexp (fprec t) (femax t))
                       (bpow radix2 (femax t - 1))) _ _ _).
- apply ulp_le.
  + apply BinarySingleNaN.fexp_correct, (fprec_gt_0 t).
  + apply FLT_exp_monotone.
  + rewrite (Rabs_pos_eq (bpow radix2 (femax t - 1))); [exact Hxhb | apply bpow_ge_0].
- rewrite ulp_bpow.
  apply bpow_le.
  have -> : (femax t - 1 + 1 = femax t)%Z by ring.
  rewrite /SpecFloat.fexp /SpecFloat.emin.
  pose proof (fprec_lt_femax t); pose proof (fprec_gt_one t).
  apply Z.max_lub; lia.
Qed.

Theorem DWPlusFP_zh_finite
(HFINxh: Binary.is_finite (fprec t) (femax t) (float_of_ftype xh) = true)
(HFINxl: Binary.is_finite (fprec t) (femax t) (float_of_ftype xl) = true)
(HFINy : Binary.is_finite (fprec t) (femax t) (float_of_ftype y) = true)
(Hp3 : (3 <= fprec t)%Z)
(Hxhl : Rabs (FT2R xh) <= /4 * (bpow radix2 (femax t)))
(Hy :  Rabs (FT2R y)  <= /4 * (bpow radix2 (femax t))):
let zh := Fast2Sum_sum sh (BPLUS xl sl) in
 Binary.is_finite (fprec t) (femax t) (float_of_ftype zh) = true.
Proof.
(* zh = Fast2Sum_sum sh (BPLUS xl sl) = BPLUS sh (BPLUS xl sl). *)
rewrite /Fast2Sum_sum/fst/Fast2Sum.
(* [is_finite] copies of the operand-finiteness hypotheses for the
   FT2R-level no-overflow lemmas (the [TwoSum*] lemmas keep the [Binary] form). *)
have Fxl : is_finite xl = true by (rewrite is_finite_Binary; exact HFINxl).
have Hxh2 : Rabs (FT2R xh) <= /2 * bpow radix2 (femax t)
  by (apply TwoSumF_err_finite_bnd; assumption).
(* sh and sl are finite *)
have FINsh : is_finite sh = true.
{ rewrite is_finite_Binary. apply TwoSumF_sum_finite; assumption. }
have FINsl : is_finite sl = true.
{ rewrite is_finite_Binary. apply TwoSumF_err_finite; assumption. }
(* magnitude bounds: |xl|, |sl| <= Omega/16 (uses fprec t >= 3) *)
have Hxl16 : Rabs (FT2R xl) <= /16 * bpow radix2 (femax t).
{ refine (Rle_trans _ _ _ (xl_bnd Hxh2) _).
  have -> : (/16 * bpow radix2 (femax t) = /2 * bpow radix2 (femax t - 3))%R.
  { have -> : (femax t - 3 = -3 + femax t)%Z by ring.
    rewrite bpow_plus; simpl; lra. }
  apply Rmult_le_compat_l; [lra|]. apply bpow_le; lia. }
have Hsl16 : Rabs (FT2R sl) <= /16 * bpow radix2 (femax t).
{ destruct (TwoSumF_error xh y (is_finite_p_TwoSum HFINxh HFINy Hp3 Hxhl Hy))
    as (del & Bsl & Hdel).
  fold sl in Bsl. rewrite Bsl Rabs_mult.
  have HM : (0 < bpow radix2 (femax t))%R by apply bpow_gt_0.
  have Hxy : Rabs (FT2R xh + FT2R y) <= /2 * bpow radix2 (femax t)
    by (eapply Rle_trans; [apply Rabs_triang|]; lra).
  apply (fun h => Rle_trans _ _ _ h (rel_le_eighth Hp3)) in Hdel.
  apply (Rle_trans _ (/2 * bpow radix2 (femax t) * /8)); [|lra].
  apply Rmult_le_compat; try apply Rabs_pos; assumption. }
(* finiteness *)
rewrite -is_finite_Binary.
have FINxlsl : is_finite (BPLUS xl sl) = true.
{ apply no_overflow_sum_is_finite; [exact Fxl|exact FINsl|].
  show_nob. eighth_bounds. nob_close. }
have Esh : sh = BPLUS xh y by reflexivity.
have FBxy : is_finite (BPLUS xh y) = true by (rewrite -Esh; exact FINsh).
(* drop the loose [/2] bound so [mag] uses the tight [/4] input bound on xh *)
clear Hxh2.
apply no_overflow_sum_is_finite; [exact FINsh|exact FINxlsl|].
rewrite Esh.
show_nob. expand_ft2r. eighth_bounds. nob_close.
Qed.

Theorem DWPlusFP_zl_finite
(HFINxh: Binary.is_finite (fprec t) (femax t) (float_of_ftype xh) = true)
(HFINxl: Binary.is_finite (fprec t) (femax t) (float_of_ftype xl) = true)
(HFINy : Binary.is_finite (fprec t) (femax t) (float_of_ftype y) = true)
(Hp3 : (3 <= fprec t)%Z)
(Hxhl : Rabs (FT2R xh) <= /4 * (bpow radix2 (femax t)))
(Hy :  Rabs (FT2R y)  <= /4 * (bpow radix2 (femax t))) :
let zl := Fast2Sum_err sh (BPLUS xl sl) in
Binary.is_finite (fprec t) (femax t) (float_of_ftype zl) = true.
Proof.
(* zl = Fast2Sum_err sh (xl+sl) = BMINUS (xl+sl) (BMINUS (BPLUS sh (xl+sl)) sh). *)
rewrite /Fast2Sum_err/snd/Fast2Sum.
have Hxh2 : Rabs (FT2R xh) <= /2 * bpow radix2 (femax t)
  by (apply TwoSumF_err_finite_bnd; assumption).
have Fxl : is_finite xl = true by (rewrite is_finite_Binary; exact HFINxl).
have FINsh : is_finite sh = true.
{ rewrite is_finite_Binary. apply TwoSumF_sum_finite; assumption. }
have FINsl : is_finite sl = true.
{ rewrite is_finite_Binary. apply TwoSumF_err_finite; assumption. }
(* |xl|, |sl| <= Omega/16 *)
have Hxl16 : Rabs (FT2R xl) <= /16 * bpow radix2 (femax t).
{ refine (Rle_trans _ _ _ (xl_bnd Hxh2) _).
  have -> : (/16 * bpow radix2 (femax t) = /2 * bpow radix2 (femax t - 3))%R.
  { have -> : (femax t - 3 = -3 + femax t)%Z by ring.
    rewrite bpow_plus; simpl; lra. }
  apply Rmult_le_compat_l; [lra|]. apply bpow_le; lia. }
have Hsl16 : Rabs (FT2R sl) <= /16 * bpow radix2 (femax t).
{ destruct (TwoSumF_error xh y (is_finite_p_TwoSum HFINxh HFINy Hp3 Hxhl Hy))
    as (del & Bsl & Hdel).
  fold sl in Bsl. rewrite Bsl Rabs_mult.
  have HM : (0 < bpow radix2 (femax t))%R by apply bpow_gt_0.
  have Hxy : Rabs (FT2R xh + FT2R y) <= /2 * bpow radix2 (femax t)
    by (eapply Rle_trans; [apply Rabs_triang|]; lra).
  apply (fun h => Rle_trans _ _ _ h (rel_le_eighth Hp3)) in Hdel.
  apply (Rle_trans _ (/2 * bpow radix2 (femax t) * /8)); [|lra].
  apply Rmult_le_compat; try apply Rabs_pos; assumption. }
(* finiteness of v := xl+sl and zh := sh+v *)
have FINv : is_finite (BPLUS xl sl) = true.
{ apply no_overflow_sum_is_finite; [exact Fxl|exact FINsl|].
  show_nob. eighth_bounds. nob_close. }
have FINzh : is_finite (BPLUS sh (BPLUS xl sl)) = true.
{ rewrite is_finite_Binary.
  pose proof (DWPlusFP_zh_finite HFINxh HFINxl HFINy Hp3 Hxhl Hy) as Hz.
  revert Hz. rewrite /Fast2Sum_sum/fst/Fast2Sum //. }
(* magnitude bounds for sh and v=xl+sl *)
have Hsh : Rabs (FT2R sh) <= 9/16 * bpow radix2 (femax t).
{ have FBxy : is_finite (BPLUS xh y) = true.
  { rewrite is_finite_Binary. apply TwoSumF_sum_finite; assumption. }
  destruct (BPLUS_accurate' _ _ _ FBxy) as (ds & Hds & E).
  have Esh : FT2R sh = FT2R (BPLUS xh y) by reflexivity.
  rewrite Esh E Rabs_mult.
  apply (fun h => Rle_trans _ _ _ h (rel_le_eighth Hp3)) in Hds.
  apply (Rle_trans _ ((/2 * bpow radix2 (femax t)) * (1 + /8))); [|lra].
  apply Rmult_le_compat; try apply Rabs_pos.
  - eapply Rle_trans; [apply Rabs_triang|]; lra.
  - eapply Rle_trans; [apply Rabs_triang|]; rewrite Rabs_R1; lra. }
have Hv : Rabs (FT2R (BPLUS xl sl)) <= 9/64 * bpow radix2 (femax t).
{ destruct (BPLUS_accurate' _ _ _ FINv) as (dv & Hdv & E).
  rewrite E Rabs_mult.
  apply (fun h => Rle_trans _ _ _ h (rel_le_eighth Hp3)) in Hdv.
  apply (Rle_trans _ ((/8 * bpow radix2 (femax t)) * (1 + /8))); [|lra].
  apply Rmult_le_compat; try apply Rabs_pos.
  - eapply Rle_trans; [apply Rabs_triang|]; lra.
  - eapply Rle_trans; [apply Rabs_triang|]; rewrite Rabs_R1; lra. }
(* r = BMINUS (BPLUS sh (xl+sl)) sh is finite (r ~ xl+sl, via cancellation) *)
have FINr : is_finite (BMINUS (BPLUS sh (BPLUS xl sl)) sh) = true.
{ apply no_overflow_minus_is_finite; [exact FINzh|exact FINsh|].
  rewrite /Bminus_no_overflow.
  destruct (Plus_error.FLT_plus_error_N_ex Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
    (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R (BPLUS sh (BPLUS xl sl))) (- FT2R sh))
    as (dr & Hdr & E); [gf_side|gf_side|].
  replace (FT2R (BPLUS sh (BPLUS xl sl)) - FT2R sh)
    with (FT2R (BPLUS sh (BPLUS xl sl)) + - FT2R sh) by ring.
  rewrite E; clear E.
  destruct (BPLUS_accurate' _ _ _ FINzh) as (dz & Hdz & E); rewrite E; clear E.
  have Hdr8 : Rabs dr <= /8 by (eapply Rle_trans; [apply Hdr|apply reldiv_le_eighth, Hp3]).
  have Hdz8 : Rabs dz <= /8 by (eapply Rle_trans; [apply Hdz|apply rel_le_eighth, Hp3]).
  replace (((FT2R sh + FT2R (BPLUS xl sl)) * (1 + dz) + - FT2R sh) * (1 + dr))
    with ((FT2R (BPLUS xl sl) + (FT2R sh + FT2R (BPLUS xl sl)) * dz) * (1 + dr)) by ring.
  nob_close. }
(* zl = BMINUS (xl+sl) r is finite (zl ~ 0, via cancellation) *)
rewrite -is_finite_Binary.
apply no_overflow_minus_is_finite; [exact FINv|exact FINr|].
rewrite /Bminus_no_overflow.
destruct (Plus_error.FLT_plus_error_N_ex Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
  (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R (BPLUS xl sl))
  (- FT2R (BMINUS (BPLUS sh (BPLUS xl sl)) sh)))
  as (dl & Hdl & E); [gf_side|gf_side|].
replace (FT2R (BPLUS xl sl) - FT2R (BMINUS (BPLUS sh (BPLUS xl sl)) sh))
  with (FT2R (BPLUS xl sl) + - FT2R (BMINUS (BPLUS sh (BPLUS xl sl)) sh)) by ring.
rewrite E; clear E.
destruct (BMINUS_accurate' _ _ _ FINr) as (dr & Hdr & E); rewrite E; clear E.
destruct (BPLUS_accurate' _ _ _ FINzh) as (dz & Hdz & E); rewrite E; clear E.
have Hdl8 : Rabs dl <= /8 by (eapply Rle_trans; [apply Hdl|apply reldiv_le_eighth, Hp3]).
have Hdr8 : Rabs dr <= /8 by (eapply Rle_trans; [apply Hdr|apply rel_le_eighth, Hp3]).
have Hdz8 : Rabs dz <= /8 by (eapply Rle_trans; [apply Hdz|apply rel_le_eighth, Hp3]).
replace ((FT2R (BPLUS xl sl)
          + - (((FT2R sh + FT2R (BPLUS xl sl)) * (1 + dz) - FT2R sh) * (1 + dr))) * (1 + dl))
  with ((- (FT2R (BPLUS xl sl) * dr) - (FT2R sh + FT2R (BPLUS xl sl)) * dz * (1 + dr)) * (1 + dl)) by ring.
nob_close.
Qed.

Let zh := Fast2Sum_sum sh (BPLUS xl sl) .
Let zl := Fast2Sum_err sh (BPLUS xl sl) .

Theorem DWPlusFP_finite
(HFINxh: Binary.is_finite (fprec t) (femax t) (float_of_ftype xh) = true)
(HFINxl: Binary.is_finite (fprec t) (femax t) (float_of_ftype xl) = true)
(HFINy : Binary.is_finite (fprec t) (femax t) (float_of_ftype y) = true)
(Hp3 : (3 <= fprec t)%Z)
(Hxhl : Rabs (FT2R xh) <= /4 * (bpow radix2 (femax t)))
(Hy :  Rabs (FT2R y)  <= /4 * (bpow radix2 (femax t))):
is_finite_p (DWPlusFP xh xl y).
Proof.
rewrite /is_finite_p/DWPlusFP.
replace (TwoSumF _ _) with (sh,sl) => //.
replace (Fast2Sum _ _) with (zh,zl) => //.
rewrite /fst/snd. split.
- rewrite is_finite_Binary. apply DWPlusFP_zh_finite; assumption.
- rewrite is_finite_Binary. apply DWPlusFP_zl_finite; assumption.
Qed.

End FiniteDWPlusFP.

Section ZeroCasesDWPlusFP.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Variables (xh xl y : ftype t).

Let zh := (FT2R (fst (DWPlusFP xh xl y))).
Let zl := (FT2R (snd (DWPlusFP xh xl y))).
Let xr := (FT2R xh + FT2R xl).
Let yr := (FT2R y).

Hypothesis  DWx : double_word xh xl.
Hypothesis FIN : is_finite_p (DWPlusFP xh xl y).
Hypothesis Hp3 : (3 <= fprec t)%Z.

Lemma DWPlusFP_0 : xr + yr = 0 -> zh + zl = 0.
Proof.
move => H0. 
pose proof DWPlusFP_eq xh xl y FIN.
rewrite /F2Rp in H. 
destruct (Req_dec xr 0).
{ have xh0: FT2R xh = 0.
move: DWx; rewrite /double_word. 
fold xr; by rewrite H1 /rounded round_0.
(* cases on underflow *)
destruct (Rle_or_lt (bpow radix2 (@emin t + fprec t - 1)) (Rabs xr)).
{  have Hv2: 
Valid_rnd (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
  by apply BinarySingleNaN.valid_rnd_round_mode.
have Hxl: FT2R xl = 0.
move: H2 DWx; subst xr; rewrite /double_word xh0; move => H2.
rewrite /rounded round_FLT_FLX Rplus_0_l => //. move => Hz. 
apply: ( @eq_0_round_0_FLX radix2 (fprec t) _ 
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) Hv2) => //.
fold ( @emin t); by rewrite Rplus_0_l in H2.
rewrite DWPlusFP0f in H => //; try lia. fold zl zh in H.
inversion H. move : H0; subst xr. rewrite H1; subst yr; nra.
- by apply: (dw_word_DWdouble xh xl y DWx).
- rewrite -!B2R_float_of_ftype;
  apply: generic_format_FLX_FLT;
  apply: Binary.generic_format_B2R. }

rewrite DWPlusFP0f in H => //; try lia. fold zl zh in H.
inversion H. move : H0; subst xr. rewrite H1; subst yr; nra.
- by apply: (dw_word_DWdouble xh xl y DWx).
- rewrite -!B2R_float_of_ftype;
  apply: generic_format_FLX_FLT;
  apply: Binary.generic_format_B2R. }

move: H. 
unfold DWPlus.DWPlusFP.
rewrite DWPlus.TwoSum_correct => //.
rewrite -!Rplus_assoc.
replace (FT2R xl + FT2R xh) with xr. fold yr.
rewrite H0 Rplus_0_l. 
rewrite F2Sum.Fast2Sum0 => //. fold zl zh. move => Hz.
inversion Hz => //=; lra.
move => x.
apply round_NE_opp.
apply Fth; lia.
rewrite /TwoSum_sum/fst/TwoSum.
rewrite round_NE_opp.
rewrite Bayleyaux.round_round => //; lia.
subst xr. rewrite Rplus_comm => //. lia.
1,2 : rewrite -!B2R_float_of_ftype;
apply: generic_format_FLX_FLT;
  apply: Binary.generic_format_B2R.
Qed.

End ZeroCasesDWPlusFP.
