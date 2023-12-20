Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common.
Require Import DWPlus DDModels Fast2Mult_acc TwoSum_acc DWPlus_acc.
From Flocq Require Import Pff2Flocq Core.

Require Import mathcomp.ssreflect.ssreflect.

(* for choice functions : choice = fun x0 : Z => negb (Z.even x0) *)
Require Import Logic.FunctionalExtensionality.

Require Import Interval.Tactic.

Require Import List.
Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

Section VCFloat. 


Definition fprecDD := 106%Z.
Definition femaxDD := femax Tdouble.
Fact fprec_le_femax_DD : FPCore.ZLT fprecDD (femax Tdouble). 
  Proof. rewrite //fprecDD; simpl. Qed.
Fact nstd_prf2 : Is_true (negb (106 =? 1)%positive). 
  Proof. by simpl. Qed.

(* overflow threshold for 106 bit prec, round-to-nearest *)
Definition dd_ov :=
  (bpow radix2 femaxDD - bpow radix2 (femaxDD - fprecDD)).

Definition dd_rep : Type := (ftype Tdouble * ftype Tdouble)%type. 

Definition f_lb : ftype Tdouble :=
(Zconst Tdouble (-Z.pow 2 (femax Tdouble - 3))).

Definition f_ub : ftype Tdouble :=
(Zconst Tdouble (Z.pow 2 (femax Tdouble - 3))).

Definition finite_bnds := 
    ((f_lb, true), (f_ub, true)).

Lemma finite_bnds_y_1 y :
compare Lt true f_lb y = true  -> 
compare Lt true y f_ub = true  -> 
Rabs (FT2R y) < /4 * (bpow radix2 (femax Tdouble)).
Proof.
rewrite /compare/compare'/extend_comp. simpl. 
intros.
destruct y.
1,2,3: rewrite /FT2R; simpl; rewrite Rabs_R0; nra.
revert H H0.
destruct (Binary.Bcompare 53 1024 _ f_ub) as
 [[| |] |] eqn:?H; try discriminate.
destruct (Binary.Bcompare 53 1024 f_lb _) as
 [[| |] |] eqn:?H; try discriminate.
move => _ _.
rewrite !Binary.Bcompare_correct in H, H0;
try reflexivity.
match type of H with Some ?A = Some ?B => 
  assert (A = B) by congruence end.
match type of H0 with Some ?A = Some ?B => 
  assert (A = B) by congruence end.
symmetry in H, H0.
apply Rcompare_Lt_inv in H1, H2.
apply Rabs_lt. split.
refine (Rlt_trans _ _  _ _ _).
2: apply H2. simpl. interval.
refine (Rlt_trans _ _  _ H1 _).
simpl; interval.
Qed.

Lemma finite_bnds_y_2 y :
compare Lt true y f_ub = true  -> 
compare Lt true f_lb y = true  -> 
is_finite y = true.
Proof.
rewrite /compare/compare'/extend_comp. simpl. 
intros.
destruct y. 
4 : simpl; auto.
all: simpl in H.
all: rewrite /FT2R; simpl; try discriminate; auto.
simpl in H0. destruct s; auto. 
Qed.


Inductive dd_pred {NANS: Nans}  := 
    double_double_finite : 
          forall (a: dd_rep), 
            Binary.is_finite (fprec Tdouble) (femax Tdouble) (fst a) = true ->
            Binary.is_finite (fprec Tdouble) (femax Tdouble) (snd a) = true ->
            Rabs (FT2R (fst a) + FT2R (snd a)) <= dd_ov -> 
            rounded Tdouble (FT2R (fst a) + FT2R (snd a)) = FT2R (fst a) -> 
            dd_pred 
  | double_double_ex : 
          forall (a: dd_rep),
            (Binary.is_finite (fprec Tdouble) (femax Tdouble) (fst a) = false \/ 
             Binary.is_finite (fprec Tdouble) (femax Tdouble) (snd a) = false) \/
            dd_ov < Rabs (FT2R (fst a) + FT2R (snd a)) -> 
            dd_pred.

Definition dd_zero_ := 
  (Binary.B754_zero (fprec Tdouble) 1024 true, 
Binary.B754_zero (fprec Tdouble) 1024 true).

Definition dd_zero {NANS: Nans}  : dd_pred.
 apply (double_double_finite dd_zero_);
rewrite /dd_zero_ => //=;
rewrite -B2R_float_of_ftype => //=.
rewrite Rplus_0_l Rabs_R0 /dd_ov; simpl; nra.
by rewrite Rplus_0_l /rounded round_0.
Defined.

Definition dd2f  {NANS: Nans} (x : dd_pred) 
  : option (float radix2):= 
  match x with 
    | double_double_finite a _ _ _ _ => Some (Operations.Fplus (B2F (fst a)) (B2F (snd a)))
    | double_double_ex _ a => None
  end
.

Definition dd_compare {NANS: Nans} (x y: dd_pred) : 
      option comparison := 
  match dd2f x, dd2f y with 
    | Some a, Some b => 
        Some (Rcompare (F2R a) (F2R b))
    | _ , _ => None
  end
.

Definition dd_is_finite_compare  {NANS: Nans} x :
  match dd2f x with 
  | Some xh => dd_compare x x = Some Eq 
  | _ => True 
  end.
destruct x => //=.
f_equal. rewrite /dd_compare/dd2f.
f_equal.  apply Rcompare_Eq => //.
Defined.

Definition dd_nonstd_nonempty_finite {NANS: Nans} :
match dd2f dd_zero with
| Some xh => True 
| _ => False
end.
rewrite /dd2f => //=.
Defined.

Definition DD_compare_correct2' {NANS: Nans}  x y a b :
      dd2f x = Some a ->
      dd2f y = Some b ->
      dd_compare x y = Some (Rcompare (F2R a) (F2R b)).
rewrite /dd2f/dd_compare. destruct x, y; simpl;
  try (move => H1 H2; try discriminate H1; try discriminate H2).
inversion H1; inversion H2. clear H1 H2. subst.
repeat f_equal; by rewrite B2F_F2R_B2R.
Defined.


Definition dd_bounds {NANS: Nans} x :
(-(bpow radix2 (femax Tdouble) - 
      bpow radix2 ((femax Tdouble) - Z.pos 106%positive)) <=
match dd2f x with Some f => F2R f | None => R0 end <=
bpow radix2 (femax Tdouble) - 
    bpow radix2 ((femax Tdouble) - Z.pos 106%positive)).
rewrite /dd2f. destruct x, a;
simpl; apply Stdlib.Rabs_def2_le.
rewrite Operations.F2R_plus -!B2F_F2R_B2R. 
rewrite -!B2R_float_of_ftype in r.
refine (Rle_trans _ _ _ r _).
rewrite /dd_ov. simpl; nra.
rewrite Rabs_R0; nra.
Defined.


Definition double_double {NANS : Nans} : type. 
pose (NONSTD 106 (femax Tdouble) fprec_le_femax_DD nstd_prf2
  dd_pred dd_zero dd2f dd_compare 
  dd_is_finite_compare DD_compare_correct2' 
  dd_nonstd_nonempty_finite dd_bounds).
pose (GTYPE 106 (femax Tdouble) fprec_le_femax_DD nstd_prf2
  (Some n)).
assumption.
Defined.


Definition dd_lb {NANS: Nans} : ftype double_double.
rewrite /ftype/double_double => //=.
set y := (Zconst Tdouble (-Z.pow 2 (femax Tdouble - 3))).
set y1:= @neg_zero Tdouble.
have Hr : IEEE754_extra.integer_representable (fprec Tdouble) 
  (femax Tdouble) (- 2 ^ (femax Tdouble - 3)).
{ apply IEEE754_extra.integer_representable_opp.
apply (@IEEE754_extra.integer_representable_2p (fprec Tdouble)
  (femax Tdouble) (fprec_gt_0 Tdouble) (fprec_lt_femax Tdouble) 
( (femax Tdouble - 3))); split; simpl; lia. }
destruct (@IEEE754_extra.BofZ_representable
(fprec Tdouble)
  (femax Tdouble) (Pos2Z.is_pos (fprecp Tdouble)) (fprec_lt_femax Tdouble)
( -2 ^ (femax Tdouble - 3))) as ( A & B & _); auto.
have Hy : FT2R y = IZR (-2 ^ (femax Tdouble - 3)).
{ subst y . rewrite /Zconst; auto. }
have Hy1 : FT2R (ftype_of_float y1) = 0.
by subst y1; rewrite /neg_zero/FT2R; simpl; nra.
simpl in Hy1.
apply (double_double_finite (y,y1)); auto. 
rewrite /fst/snd Hy1 Hy Rplus_0_r opp_IZR Rabs_Ropp
  Rabs_pos_eq /dd_ov; simpl; nra.
rewrite /rounded /fst/snd Hy1 Rplus_0_r round_generic; auto.
apply Binary.generic_format_B2R. 
Defined.


Definition dd_ub {NANS: Nans} : ftype double_double.
rewrite /ftype/double_double => //=.
set y := (Zconst Tdouble (Z.pow 2 (femax Tdouble - 3))).
set y1:= @neg_zero Tdouble.
have Hr : IEEE754_extra.integer_representable (fprec Tdouble) 
  (femax Tdouble) (2 ^ (femax Tdouble - 3)).
{ apply (@IEEE754_extra.integer_representable_2p (fprec Tdouble)
  (femax Tdouble) (fprec_gt_0 Tdouble) (fprec_lt_femax Tdouble) 
( (femax Tdouble - 3))); split; simpl; lia. }
destruct (@IEEE754_extra.BofZ_representable
(fprec Tdouble)
  (femax Tdouble) (Pos2Z.is_pos (fprecp Tdouble)) (fprec_lt_femax Tdouble)
( 2 ^ (femax Tdouble - 3))) as ( A & B & _); auto.
have Hy : FT2R y = IZR (2 ^ (femax Tdouble - 3)).
{ subst y . rewrite /Zconst; auto. } 
have Hy1 : FT2R (ftype_of_float y1) = 0.
subst y1.  rewrite /neg_zero/FT2R; simpl; nra.
simpl in Hy1.
apply (double_double_finite (y,y1)); auto. 
rewrite /fst/snd Hy1 Hy Rplus_0_r
  Rabs_pos_eq /dd_ov; simpl; nra.
rewrite /rounded /fst/snd Hy1 Rplus_0_r round_generic; auto.
apply Binary.generic_format_B2R. 
Defined.


Lemma dd_ub_implies {N : Nans}  (x : ftype double_double) :
compare Lt true x dd_ub = true -> 
compare Lt true dd_lb x = true -> 
is_finite x = true.
Proof.
destruct x. easy. simpl => //.
Qed.


Definition dd_finite_bnds {NANS: Nans} := 
    ((dd_lb, true), (dd_ub, true)).

Definition DWplusFP_bnds2' {NANS: Nans} : klist bounds [double_double; Tdouble]:=
   Kcons (dd_finite_bnds) (Kcons (finite_bnds) Knil).

Lemma bounded_finite {N: Nans} {t} b m e
  (p: SpecFloat.bounded (fprec t) (femax t) m e = true):  
  Binary.is_finite _ _ (Binary.B754_finite (fprec t) (femax t) b m e p) = true.
Proof. easy. Qed.

Definition DD2Fp {NANS : Nans} (x : ftype double_double):=
match x with
| double_double_finite a _ _ _ _ => Some (fst a, snd a)
| double_double_ex _ _ => None
end. 

Lemma is_finite_or  (a : ftype Tdouble) : 
  {is_finite a = true} + {is_finite a = false}.
Proof. rewrite is_finite_Binary. destruct a; simpl; auto. Qed.

Definition ddPlusFP {NANS: Nans} :  
  ftype double_double -> ftype Tdouble -> ftype double_double.
move=> x y.
destruct x, a; [| apply (double_double_ex (f,f0) o)].
set (z1:= FT2R (fst (DWPlusFP f f0 y)) + FT2R (snd (DWPlusFP f f0 y))).
destruct (Rle_lt_dec (Rabs z1) dd_ov);
  try (refine (double_double_ex (DWPlusFP f f0 y) _); right; apply r0).
destruct (is_finite_or (fst (DWPlusFP f f0 y)));
  try (refine (double_double_ex (DWPlusFP f f0 y) _ ); left; left; apply e2). 
destruct (is_finite_or (snd (DWPlusFP f f0 y)));
  try (refine (double_double_ex (DWPlusFP f f0 y) _ ); left; right; apply e3).
- refine (double_double_finite (DWPlusFP f f0 y) e2 e3 r0 _).
  symmetry. apply DWPlusFP_double_word => //.
Defined. 

Lemma ddPlusFP_finite {NANS: Nans} 
  (x : ftype double_double) (y : ftype Tdouble) : 
  forall a,  
  DD2Fp x = Some a ->
  is_finite (fst (DWPlusFP (fst a) (snd a) y)) = true -> 
  is_finite (snd (DWPlusFP (fst a) (snd a) y)) = true -> 
  Rabs (FT2R (fst (DWPlusFP (fst a) (snd a) y)) + FT2R (snd (DWPlusFP (fst a) (snd a) y))) <= dd_ov -> 
  is_finite (ddPlusFP x y) = true.
Proof.
intros a Ha Hf Hb.
destruct x; try discriminate Ha.
move : Ha. 
rewrite /DD2Fp. intros H; inversion H; clear H.
destruct a; inversion H1; clear H1; subst.
rewrite /ddPlusFP.
destruct a0. intros Hov.
remember (Rle_lt_dec _ _ ) as Hle.
destruct Hle => //.
remember (is_finite_or _ ) as HO.
destruct HO => //.
remember (is_finite_or (snd (DWPlusFP f f0 y))) as H1.
destruct H1 => //.
rewrite -Hb e3 => //.
rewrite -Hf e2 => //.
exfalso. clear HeqHle.
apply Rlt_not_le in r0 => //.
Qed.

Lemma ddPlusFP_eq {NANS: Nans} 
  (x : ftype double_double) (y : ftype Tdouble) :
  forall a,  
  DD2Fp x = Some a->
  is_finite (ddPlusFP x y) = true -> 
  DD2Fp (ddPlusFP x y) = Some (DDModels.DWPlusFP (fst a) (snd a) y).
Proof.
intros a H0. 
destruct x.
2: simpl; try discriminate H0; auto.
move: H0.
rewrite /DD2Fp/ddPlusFP;
   destruct a0.
rewrite {1}/fst{1}/snd. 
intros H; inversion H; clear H.
destruct a; inversion H1; subst; clear H1.
remember (Rle_lt_dec _ _ ) as Hle.
destruct Hle => //.
remember (is_finite_or _ ) as HF.
destruct HF => //.
remember (is_finite_or (snd (DWPlusFP f1 f2 y)) ) as HF.
destruct HF => //.
Qed.

Lemma Rcompare_refl x :
Rcompare x x = Eq.
Proof. by apply Rcompare_Eq. Qed.

Lemma ddPlusFP_nans {NANS: Nans} 
  (x : ftype double_double) (y : ftype Tdouble) :
  is_nan y = true -> 
  is_nan (ddPlusFP x y) = true.
Proof.
intros ?. destruct x.
destruct y; try discriminate.
destruct a. simpl in e, e0.
clear H. 
rewrite /ddPlusFP.
remember (Rle_lt_dec _ _) as HD;
  destruct HD; clear HeqHD.
{ remember (is_finite_or _) as HF;
  destruct HF; clear HeqHF.
remember (is_finite_or _) as HF;
  destruct HF; clear HeqHF.
rewrite /is_nan/double_double/nonstd_is_nan
  /nonstd_compare/dd_compare/dd2f.
rewrite Rcompare_refl.
rewrite -e3. clear e4.
destruct f, f0; try discriminate H; try discriminate H0;
simpl; auto.
rewrite /is_nan/double_double/nonstd_is_nan
  /nonstd_compare/dd_compare/dd2f => //. 
rewrite /is_nan/double_double/nonstd_is_nan
  /nonstd_compare/dd_compare/dd2f => //. }
rewrite /is_nan/double_double/nonstd_is_nan
  /nonstd_compare/dd_compare/dd2f/ddPlusFP => //. 
destruct a => //.
Qed.


Theorem ff_congr {NANS: Nans} : 
@floatfunc_congr [double_double; Tdouble] double_double (@ddPlusFP NANS).
Proof.
rewrite /floatfunc_congr.
intros.
inversion H. clear H; subst.
inversion H5. clear H5; subst.
inversion H8. clear H8; subst.
apply Eqdep.EqdepTheory.inj_pair2 in H1, H6, H3, H2, H, H0;  
 subst.
hnf in H4, H7.
move: H4 H7. 
remember (nonstd_is_nan ah) as Hah.
destruct Hah; rewrite -HeqHah.
remember (nonstd_is_nan bh) as Hbh;
destruct Hbh; rewrite -HeqHbh;
intros; try contradiction.
{ move: HeqHah. rewrite /nonstd_is_nan.
destruct ah. rewrite /nonstd_compare/dd_compare/dd2f.
rewrite Rcompare_refl; discriminate.
move: HeqHbh. rewrite /nonstd_is_nan.
destruct bh. rewrite /nonstd_compare/dd_compare/dd2f.
rewrite Rcompare_refl; discriminate.
rewrite /nonstd_compare/dd_compare/dd2f.
intros _ _.
destruct ah0, bh0; subst.
all : destruct a,a0;
destruct f, f0 => //. }

move: HeqHah. rewrite /nonstd_is_nan.
destruct ah; rewrite /nonstd_compare/dd_compare/dd2f;
try rewrite Rcompare_refl; try (intros H; discriminate H).
intros _.
destruct bh;
try (intros H; contradiction).
rewrite Rcompare_refl; intros.
inversion H4; subst; clear H4.
assert (e = e2) by (apply Coq.Logic.ProofIrrelevance.proof_irrelevance);
  subst;
assert (e0 = e3) by (apply Coq.Logic.ProofIrrelevance.proof_irrelevance);
  subst;
assert (e1 = e4) by (apply Coq.Logic.ProofIrrelevance.proof_irrelevance);
  subst;
assert (r = r0) by (apply Coq.Logic.ProofIrrelevance.proof_irrelevance);
  subst.

destruct ah0, bh0; subst;
  try contradiction; try apply float_equiv_refl.
{ destruct a0.
destruct f,f0; try discriminate;
try simpl; auto.

all: 
rewrite /nonstd_is_nan/nonstd_compare/dd_compare/dd2f;
cbv [eq_rect_r eq_rect eq_sym applyk_aux f_equal];

repeat match goal with |-context[ddPlusFP ?a ?b] =>
  let HA := fresh in let HB:= fresh in 
  remember (ddPlusFP a b) as HA;
  destruct HA;
  [pose proof ddPlusFP_nans a b as HB;
  try specialize (HB eq_refl);
  move : HB; rewrite /is_nan/double_double/nonstd_is_nan
    /nonstd_compare/dd_compare/dd2f; move => HB;
      match goal with 
        H: double_double_finite _ _ _ _ _ = ddPlusFP _ _ |- _ => 
        rewrite -H Rcompare_refl in HB; discriminate HB
      end | auto ]
end. 
}

destruct H7 as (H & H7);
destruct H7; subst.
assert (e0 = e5) by (apply Coq.Logic.ProofIrrelevance.proof_irrelevance);
  subst;
apply float_equiv_refl.
Qed.



Lemma DWPlusFP_finite {N : Nans} : 
forall x y a e1 e2 e3 e4
(H1 : x = double_double_finite a e1 e2 e3 e4)
(HA : is_finite (fst (DWPlusFP (fst a) (snd a) y)) = true)
(HB : is_finite (snd (DWPlusFP (fst a) (snd a) y)) = true)
(HC : Rabs (FT2R (fst (DWPlusFP (fst a) (snd a) y)) + FT2R (snd (DWPlusFP (fst a) (snd a) y))) <= dd_ov),
is_finite (ddPlusFP x y) = true.
Proof.
intros. remember (ddPlusFP _ _).
destruct f => //.
destruct o; simpl.

{ move : Heqf. rewrite /ddPlusFP.
destruct x => //.
inversion H1; subst; clear H1.
destruct a. 
destruct (Rle_lt_dec _ _) => //.
destruct (is_finite_or _) => //.
destruct (is_finite_or _) => //.

1,2: intros H1; inversion H1; subst; clear H1.
rewrite -e7 -HB => //.
rewrite -e6 -HA => //.
intros H1; inversion H1; subst; clear H1. 
destruct o.
rewrite -H -HA => //. 
rewrite -H -HB => //.  }

move : Heqf. rewrite /ddPlusFP.
destruct x => //.
inversion H1; subst; clear H1.
destruct a. 
destruct (Rle_lt_dec _ _) => //.
destruct (is_finite_or _) => //. 
destruct (is_finite_or _) => //. 

1,2: intros H1; inversion H1; subst; clear H1.
rewrite -e7 -HB => //.
rewrite -e6 -HA => //.
intros H1; inversion H1; subst; clear H1. 
apply Rlt_not_le in r => //.
Qed.

Lemma is_finite_bound_ {N : Nans} : forall (f f0 : ftype Tdouble)
(e : is_finite f = true)
(e' : is_finite f0 = true)
(e0 : Rabs (FT2R (fst (f, f0)) + FT2R (snd (f, f0))) <= dd_ov)
(e1 : rounded Tdouble (FT2R f + FT2R f0) = FT2R f)
(HA : compare Lt true dd_lb (double_double_finite (f, f0) e e' e0 e1) = true)
(HB : @compare double_double Lt true (double_double_finite (f, f0) e e' e0 e1) dd_ub = true) 
(Hf : is_finite f = true )
(Hf0 : is_finite f0 = true)
(Hd1 : Rabs (rounded Tdouble (FT2R f + FT2R f0)) <= dd_ov)
(Hdw : double_word f f0)
(Hp3 : (3 <= fprec Tdouble)%Z),
 Rabs (FT2R f + FT2R f0) < / 4 * bpow radix2 (femax Tdouble).
Proof.
intros.
move : HA HB.
rewrite /compare/extend_comp/compare'//=/dd_compare.
remember dd_lb as b1; destruct b1.
rewrite /dd2f.
remember (Rcompare _ _ ) as R1.
destruct R1; try (intros H; discriminate H).
intros _.
move: Heqb1.
cbv [dd_lb eq_ind_r eq_ind eq_sym].
match goal with 
  |-context [IEEE754_extra.BofZ_representable ?a ?b ?c ?d ?e ?h] => 
  let H := fresh in set (H:= h) ; destruct H
end.
let A:= fresh in let a0:= fresh in  
remember (IEEE754_extra.BofZ_representable 
  _ _ _ _ _ (conj _ _ )) as A;
destruct A as (a0 & A); destruct A. 
intros Heqb1; inversion Heqb1; subst; 
  clear Heqb1 HeqH e2 e3 e4 e5.
symmetry in HeqR1; apply Rcompare_Lt_inv in HeqR1.
rewrite !Operations.F2R_plus in HeqR1.
simpl in HeqR1.
remember dd_ub as b2; destruct b2; 
  try (intros H; discriminate H).
rewrite Operations.F2R_plus.
remember (Rcompare _ _ ) as R1.
destruct R1; try (intros H; discriminate H);
  intros _.
move: Heqb2.
cbv [dd_ub eq_ind_r eq_ind eq_sym].
match goal with 
  |-context [IEEE754_extra.BofZ_representable ?a ?b ?c ?d ?e ?h] => 
  let H := fresh in set (H:= h) ; destruct H
end.
let A:= fresh in let a0:= fresh in  
remember (IEEE754_extra.BofZ_representable 
  _ _ _ _ _ (conj _ _ )) as A;
destruct A as (a0 & A); destruct A. 
intros Heqb2; inversion Heqb2; subst; 
  clear Heqb2 HeqH e2 e3 e4 e5.
symmetry in HeqR0; apply Rcompare_Lt_inv in HeqR0.
rewrite Operations.F2R_plus in HeqR0.
simpl in HeqR0.
rewrite !FT2R_ftype_of_float !B2F_F2R_B2R. 
apply Rabs_lt; split.
eapply Rlt_trans. 
2: apply HeqR1. interval.
eapply Rlt_trans. 
apply HeqR0. interval.
rewrite /dd2f; intros H; try discriminate H.
Qed.


Definition DWPlusFP_ff {NANS: Nans} : floatfunc 
                  [double_double ;Tdouble] double_double
    DWplusFP_bnds2' (fun xhl y => xhl + y)%R.
apply (Build_floatfunc [double_double; Tdouble] 
                double_double _ _ 
          (ddPlusFP)
          2%N 1%N).
intros x ? y ?.
{ simpl in H, H0.
rewrite !andb_true_iff in H H0.
destruct H as [HA HB].
destruct H0 as [HC HD].
pose proof dd_ub_implies x HB HA as Hb.
destruct x;
simpl in Hb;
try discriminate;
clear Hb.
destruct a.
simpl in e, e0. 
unfold acc_prop.
split; try lia.
split; try lia.

(* double_word f f0 *)
have Hdw :  double_word f f0 by rewrite /double_word e1.

(* (3 <= fprec Tdouble)%Z *)
have Hp3 : (3 <= fprec Tdouble)%Z  by cbv; intros; discriminate.

(* Rabs (FT2R f + FT2R f0) < / 4 * bpow radix2 (femax Tdouble) *)
have Hb : Rabs (FT2R f + FT2R f0) < / 4 * bpow radix2 (femax Tdouble). 
  apply (is_finite_bound_ f f0 e e0 r e1); auto.
rewrite e1; simpl.
destruct f; try discriminate e. 
rewrite -B2R_float_of_ftype; simpl; rewrite Rabs_R0 /dd_ov; simpl;
  nra.
rewrite -B2R_float_of_ftype; simpl; rewrite /dd_ov; simpl.
rewrite F2R_cond_Zopp /cond_Ropp.
destruct s. rewrite Rabs_Ropp.
apply Rlt_le. rewrite Rabs_pos_eq.
refine (Rle_lt_trans _ _ _  _ _).
 eapply 
  Binary.bounded_le_emax_minus_prec. 
apply fprec_gt_0. apply e3. simpl; nra.
apply F2R_ge_0 => //.
rewrite -F2R_Zabs. simpl. 
refine (Rle_trans _ _ _ _ _).
 eapply 
  Binary.bounded_le_emax_minus_prec. 
apply fprec_gt_0. apply e3. simpl; nra.

(* Rabs (FT2R y) < / 4 * bpow radix2 (femax Tdouble). *)
have Hy : Rabs (FT2R y) < / 4 * bpow radix2 (femax Tdouble).
apply finite_bnds_y_1 => //.

(* is_finite_p (DWPlusFP f f0 y)  *)
have HFin : is_finite_p (DWPlusFP f f0 y) by 
  apply (DWPlus_acc.DWPlusFP_finite f f0 y Hdw e e0
  (finite_bnds_y_2 y HD HC) Hb
  (finite_bnds_y_1 y HC HD)); auto.

(* double_word (fst (DWPlusFP f f0 y)) (snd (DWPlusFP f f0 y)) *)
have Hdw1: 
double_word (fst (DWPlusFP f f0 y)) (snd (DWPlusFP f f0 y)).
pose proof DWPlusFP_double_word as Hdw2.
move: Hdw2; rewrite /double_word/rounded; move => Hdw2.
rewrite -Hdw2; clear Hdw2 => //. 

(* is_finite (ddPlusFP (double_double_finite (f, f0) e e0) y) = true.*)
have HFin2 : 
  is_finite (ddPlusFP (double_double_finite (f, f0) e e0 r e1) y) = true.
move: Hdw1. rewrite /double_word/rounded; intros H.
pose proof DWPlusFP_finite as H1.
have A :  is_finite (fst (DWPlusFP f f0 y)) = true by 
  rewrite /is_finite_p in HFin; destruct HFin.
have B :  is_finite (snd (DWPlusFP f f0 y)) = true by 
  rewrite /is_finite_p in HFin; destruct HFin.


apply (H1 (double_double_finite (f, f0) e e0 r e1) y
  (f, f0) e e0 r e1); try reflexivity; clear H1; auto.

rewrite {2}/fst{1}/snd;
rewrite {2}/fst{2}/snd.

destruct ( relative_errorDWPlusFP_correct' f f0 y
  Hdw HFin Hp3) 
as (del & A1 & B1). 
rewrite A1 Rabs_mult.

have: 
(Rabs (FT2R f + FT2R f0) + Rabs (FT2R y)) * Rabs (1 + del) <= dd_ov.
eapply Rle_trans.
eapply Rmult_le_compat.
apply Rplus_le_le_0_compat.
1-3: apply Rabs_pos.
eapply Rplus_le_compat.
apply Rlt_le. apply Hb.
apply Rlt_le. apply Hy.
have: Rabs ( 1 + del) <= 1 + 2 * bpow radix2 (- fprec Tdouble) ^ 2.
eapply Rle_trans; [apply Rabs_triang | ].
apply Rplus_le_compat. interval. nra.
intros. apply H0.
simpl.
rewrite /dd_ov. simpl. nra.
intros.
eapply Rle_trans.
apply Rmult_le_compat;
  try apply Rabs_pos.
apply Rabs_triang.
apply Rle_refl.
auto.

(* first conjunct of goal *)
split; auto.
(* main conjunct *)
destruct (
relative_errorDWPlusFP_correct' f f0 y
  Hdw HFin Hp3) 
as (del & A1 & B1). 
exists del, 0; repeat split.
simpl. rewrite /FPCore.default_rel.
move : B1; simpl; nra.
rewrite Rabs_R0 /FPCore.default_abs; simpl; nra.

rewrite Rplus_0_r.
pose proof ddPlusFP_eq
  (double_double_finite (f, f0) e e0 r e1) y (f,f0) as H1.
move : H1.  rewrite /DD2Fp. 
rewrite HFin2.
let H:= fresh in 
remember (ddPlusFP (double_double_finite (f, f0) e e0 r e1) y) as
  H; destruct H; simpl.
intros H1.
specialize (H1 eq_refl eq_refl).
apply Prune.Some_inj in H1.
rewrite /FT2R; simpl; rewrite /nonstd_to_R. 
rewrite /nonstd_to_F/dd2f !Operations.F2R_plus.
rewrite -!B2F_F2R_B2R .
destruct (DWPlusFP f f0 y), a. simpl in A1, H1.
rewrite /fst/snd. inversion H1; subst; clear H1; auto.

intros H1. specialize (H1 eq_refl eq_refl);
  discriminate H1. }

apply ff_congr.
Qed.

End VCFloat.