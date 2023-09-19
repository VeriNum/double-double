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
Section VCFloat.

Definition fprecDD := 106%Z.
Fact fprec_le_femax_DD : FPCore.ZLT fprecDD (femax Tdouble). 
  Proof. rewrite //fprecDD; simpl. Qed.
Fact nstd_prf2 : Is_true (negb (106 =? 1)%positive). 
  Proof. by simpl. Qed.

Definition dd_ov :=
(bpow radix2 (femax Tdouble) - 
      bpow radix2 ((femax Tdouble) - Z.pos 106%positive)).

Definition DD2F (x : ftype Tdouble * ftype Tdouble ) 
  : option (float radix2):= 
let xhi := fst x in let xlo := snd x in
if Rlt_bool (Rabs (F2R (Operations.Fplus (FT2F xhi) (FT2F xlo)))) dd_ov 
  && is_finite xhi && is_finite xlo
then
 Some (Operations.Fplus (FT2F xhi) (FT2F xlo)) else None.


(**  a double word number is an unevaluated sum *)
Definition DD2R (x : ftype Tdouble * ftype Tdouble ) := 
    FT2R (fst x) + FT2R (snd x).

Definition DD_compare (x y: ftype Tdouble * ftype Tdouble) : 
      option comparison := 
  let xhi := fst x in let xlo := snd x in
  let yhi := fst y in let ylo := snd y in
  let x' := (Operations.Fplus (FT2F xhi) (FT2F xlo)) in
  let y' := (Operations.Fplus (FT2F yhi) (FT2F ylo)) in
  Some (Rcompare (FPCore.F2R radix2 x') (FPCore.F2R radix2 y')).

Lemma DD_compare_refl x :
  let xhi := fst x in let xlo := snd x in
  let x' := (Operations.Fplus (FT2F xhi) (FT2F xlo)) in
DD_compare x x =  Some (Rcompare (FPCore.F2R radix2 x') (FPCore.F2R radix2 x')).
Proof. intros. rewrite /DD_compare. f_equal. Qed.

Definition DD_is_finite (x : ftype Tdouble * ftype Tdouble ) := 
  match DD2F x with
  | Some xh => if is_finite (fst x) then True else False
  | None => False 
  end.

Definition DD_is_finite_compare x :
  match DD2F x with 
  | Some xh => DD_compare x x = Some Eq 
  | _ => True 
  end.
destruct x. rewrite /DD2F/DD_compare.
remember (Rlt_bool _ dd_ov) as b.
destruct b => //=; f_equal.
remember (Binary.is_finite 53 1024 f 
        && Binary.is_finite 53 1024 f0).
destruct b => //=; f_equal.
all: by apply Rcompare_Eq. 
Defined.

Definition DD_compare_correct x y a b :
      DD2F x = Some a ->
      DD2F y = Some b ->
      DD_compare x y = Some (Rcompare (F2R a) (F2R b)).
rewrite /DD2F/DD_compare. 
remember (Rlt_bool _ dd_ov) as fb.
destruct fb => //=. 
remember ( _ && _).
destruct b0 => //=. 
move => H1.
match goal with |-context[Rlt_bool ?a ?b] => 
  remember (Rlt_bool a b) as fb0  end.
destruct fb0 => //=.
match goal with |-context[?a && ?b] => 
  remember (a && b) as fb0  end.
destruct fb0 => //=.
move => H2.
simpl in H1, H2;
inversion H1; inversion H2 => //=. f_equal.
rewrite !FPCore.F2R_eq=> //=.
Defined.

Definition DD_zero := 
  (Binary.B754_zero (fprec Tdouble) 1024 true, 
Binary.B754_zero (fprec Tdouble) 1024 true).

Fact F2R0 :
@F2R Zaux.radix2 {| Fnum := 0; Fexp := 0 |} = 0.
Proof. rewrite /F2R //=; nra. Qed.

Definition DD_nonstd_nonempty_finite :
match DD2F DD_zero with
| Some xh => True 
| _ => False
end.
rewrite /DD2F/DD_zero F2R0 => //=.
rewrite Rlt_bool_true => //=.
rewrite Rabs_R0 /dd_ov. simpl; nra.
Defined.

Definition DD_bounds x :
(-(bpow radix2 (femax Tdouble) - 
      bpow radix2 ((femax Tdouble) - Z.pos 106%positive)) <=
match DD2F x with Some f => F2R f | None => R0 end <=
bpow radix2 (femax Tdouble) - 
    bpow radix2 ((femax Tdouble) - Z.pos 106%positive)).
rewrite /DD2F. 
remember (is_finite (fst x)) as b1.
remember (is_finite (snd x)) as b2.
remember (Rlt_bool _ _ ) as b0.
destruct b1 => //=; try nra. 
{ apply Stdlib.Rabs_def2_le.
pose proof Binary.bounded_le_emax_minus_prec.
destruct x,f,f0 => //=; simpl in Heqb0; try discriminate. 
1,2: subst b0;  rewrite Rlt_bool_true => //=.
1,2: try rewrite Operations.F2R_plus 
  F2R0 Rplus_0_l /dd_ov Rabs_R0; simpl; try nra.
all: destruct b2 => //=; try nra.
1,2,3: try (rewrite Operations.F2R_plus 
  F2R0 Rplus_0_l); rewrite /dd_ov Rabs_R0; simpl; try nra.
1,2: subst b0;  rewrite Rlt_bool_true => //=.
1,2: try (rewrite Operations.F2R_plus 
  F2R0 Rplus_0_l); rewrite /dd_ov Rabs_R0; simpl; try nra.
1,2: try (rewrite Operations.F2R_plus 
  F2R0 Rplus_0_l); rewrite /dd_ov => //=.
rewrite F2R_cond_Zopp /cond_Ropp => //=.
destruct s0. rewrite Rabs_Ropp.
apply Rlt_le. rewrite Rabs_pos_eq.
refine (Rle_lt_trans _ _ _  _ _).
 eapply 
  Binary.bounded_le_emax_minus_prec. 
apply fprec_gt_0. apply e0. simpl; nra.
apply F2R_ge_0 => //.

rewrite Rabs_pos_eq.
refine (Rle_trans _ _ _  _ _).
 eapply 
  Binary.bounded_le_emax_minus_prec. 
apply fprec_gt_0. apply e0. simpl; nra.
apply F2R_ge_0 => //.

rewrite F2R_cond_Zopp /cond_Ropp => //=.
destruct s0. rewrite Rabs_Ropp.
rewrite Rabs_pos_eq.
refine (Rle_lt_trans _ _ _  _ _).
 eapply 
  Binary.bounded_le_emax_minus_prec. 
apply fprec_gt_0. apply e0. simpl; nra.
apply F2R_ge_0 => //.

rewrite Rabs_pos_eq.
refine (Rle_lt_trans _ _ _  _ _).
eapply 
  Binary.bounded_le_emax_minus_prec. 
apply fprec_gt_0. apply e0. simpl; nra.
apply F2R_ge_0 => //.

destruct b0 => //=. 
1,2: try (rewrite Operations.F2R_plus 
  F2R0 Rplus_0_r); rewrite /dd_ov => //=. 
rewrite F2R_cond_Zopp /cond_Ropp => //=.
destruct s. rewrite Rabs_Ropp.
apply Rlt_le. rewrite Rabs_pos_eq.
refine (Rle_lt_trans _ _ _  _ _).
 eapply 
  Binary.bounded_le_emax_minus_prec. 
apply fprec_gt_0. apply e0. simpl; nra.
apply F2R_ge_0 => //.

apply Rlt_le. rewrite Rabs_pos_eq.
refine (Rle_lt_trans _ _ _  _ _).
 eapply 
  Binary.bounded_le_emax_minus_prec. 
apply fprec_gt_0. apply e0. simpl; nra.
apply F2R_ge_0 => //.

rewrite Rabs_R0. nra.

destruct b0 => //=. 
1,2: try (rewrite Operations.F2R_plus 
  F2R0 Rplus_0_r); rewrite /dd_ov => //=. 
1,2: rewrite Rabs_R0; nra.

destruct b0 => //=. 
1,2: try (rewrite Operations.F2R_plus 
  F2R0 Rplus_0_r); rewrite /dd_ov => //=. 
1,2: rewrite Rabs_R0; nra.

destruct b0 => //=. 
move: Heqb0.
try (rewrite Operations.F2R_plus ); 
  rewrite /dd_ov => //=. rewrite /Rlt_bool => //=.
remember (Rcompare _ _) . intros.
destruct c => //. 
symmetry in Heqc.
apply Rcompare_Lt_inv in Heqc; nra. 

rewrite Rabs_R0; nra. } 

apply Stdlib.Rabs_def2_le.
pose proof Binary.bounded_le_emax_minus_prec.
destruct x,f,f0 => //=; simpl in Heqb0; try discriminate. 
1,2: subst b0;  rewrite Rlt_bool_true => //=.
1,2: try rewrite Operations.F2R_plus 
  F2R0 Rplus_0_l /dd_ov Rabs_R0; simpl; try nra.
all: destruct b2 => //=; try nra.
1,2,3: try (rewrite Operations.F2R_plus 
  F2R0 Rplus_0_l); rewrite /dd_ov Rabs_R0; simpl; try nra.
1,2: subst b0;  rewrite Rlt_bool_true => //=.
1,3: rewrite Rabs_R0; nra.
1,2: try (rewrite Operations.F2R_plus 
  F2R0 Rplus_0_l); rewrite /dd_ov ; simpl; try nra.
rewrite Rabs_R0; nra.
rewrite F2R_cond_Zopp /cond_Ropp => //=.
destruct s0. rewrite Rabs_Ropp.
rewrite Rabs_pos_eq.
refine (Rle_lt_trans _ _ _  _ _).
 eapply 
  Binary.bounded_le_emax_minus_prec. 
apply fprec_gt_0. apply e0. simpl; nra.
apply F2R_ge_0 => //.

rewrite Rabs_pos_eq.
refine (Rle_lt_trans _ _ _  _ _).
 eapply 
  Binary.bounded_le_emax_minus_prec. 
apply fprec_gt_0. apply e0. simpl; nra.
apply F2R_ge_0 => //.

all: rewrite andb_false_r. 
all: try rewrite andb_false_l.
all: rewrite Rabs_R0; nra.
Defined.

Definition dd_rep : Type := (ftype Tdouble * ftype Tdouble)%type. 

Definition double_double : type. 
pose (NONSTD 106 (femax Tdouble) fprec_le_femax_DD nstd_prf2
  dd_rep DD_zero DD2F DD_compare 
  DD_is_finite_compare DD_compare_correct 
  DD_nonstd_nonempty_finite DD_bounds).
pose (GTYPE 106 (femax Tdouble) fprec_le_femax_DD nstd_prf2
  (Some n)).
assumption.
Defined.

Definition f_lb : ftype Tdouble :=
(Zconst Tdouble (-Z.pow 2 (femax Tdouble - 3))).
(*  ftype_of_float (Binary.B754_infinity _ _ true). *)

Definition f_ub : ftype Tdouble :=
(Zconst Tdouble (Z.pow 2 (femax Tdouble - 3))).
(*  ftype_of_float (Binary.B754_infinity _ _ false). *)

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
2: apply H2. simpl; interval.
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

Notation ulp :=  (Ulp.ulp Zaux.radix2 
  (SpecFloat.fexp (fprec Tdouble) (femax Tdouble))).

Lemma Rlt_compat2 a b c d:
 0 < a -> 0 < b -> 0< c -> a <= b -> c < d -> a * c < b * d.
Proof.  intros. nra. Qed. 


Definition dd_pred (a: dd_rep) : Prop := 
  is_finite (fst a) = true /\ is_finite (snd a) = true
  /\ Rabs (FT2R (fst a) + FT2R (snd a)) < dd_ov
  /\ Rabs (FT2R (fst a)) < /4 * (bpow radix2 (femax Tdouble))
  /\ (0 <>  (FT2R (fst a)) ->  
  bpow radix2 (@emin Tdouble + fprec Tdouble - 1) <= 
          Rabs (FT2R (fst a)))
  /\ (0 <> (FT2R (fst a) + FT2R (snd a)) ->  
  bpow radix2 (@emin Tdouble + fprec Tdouble - 1) <= 
          Rabs (FT2R (fst a) + FT2R (snd a)))
  /\ Rabs (FT2R (snd a)) <= /4 * ulp (FT2R (fst a)).

Fact dd_pred_double_word_aux0 a :
  bpow radix2 (@emin Tdouble + fprec Tdouble - 1) <= 
          Rabs (FT2R (fst a)) -> 
  bpow radix2 (@emin Tdouble + fprec Tdouble - 1) <= 
          Rabs (FT2R (fst a) + FT2R (snd a)) ->
  Rabs (FT2R (snd a)) <= /4 * ulp (FT2R (fst a)) -> 
  Bayleyaux.is_pow radix2 (FT2R (fst a)) -> 
  FT2R (fst a) <> 0 -> 
 FT2R (fst a) = rounded Tdouble (@FT2R Tdouble (fst a) + @FT2R Tdouble (snd a)).
Proof.
intros H1 H2 H3.
rewrite /rounded round_FLT_FLX => //=.
symmetry. apply rxpu2pow => //=.
move: H3. 
rewrite !ulp_neq_0 => //. 
rewrite cexp_FLT_FLX; try nra.
simpl in H1. simpl => //.
Qed.

Fact dd_pred_double_word_aux0' a :
  bpow radix2 (@emin Tdouble + fprec Tdouble - 1) <= 
          Rabs (FT2R (fst a)) -> 
  bpow radix2 (@emin Tdouble + fprec Tdouble - 1) <= 
          Rabs (FT2R (fst a) + FT2R (snd a)) ->
  Rabs (FT2R (snd a)) <= /4 * ulp (FT2R (fst a)) -> 
  ~Bayleyaux.is_pow radix2 (FT2R (fst a)) -> 
  FT2R (fst a) <> 0 -> 
 FT2R (fst a) = rounded Tdouble (@FT2R Tdouble (fst a) + @FT2R Tdouble (snd a)).
Proof.
intros H1 H2 H3.
rewrite /rounded round_FLT_FLX => //=.
symmetry. apply rulp2p => //=.
eapply generic_format_FLX_FLT.
apply Binary.generic_format_B2R.
move: H3. 
rewrite !ulp_neq_0 => //. 
rewrite cexp_FLT_FLX; try nra.
move => H3. 
rewrite Rmult_comm.
rewrite Rmult_comm in H3.
refine (Rle_lt_trans _ _ _ H3 _).
apply Rlt_compat2; try nra;
  try apply bpow_gt_0.
simpl in H1. simpl => //.
Qed.

Fact dd_pred_double_word_aux1 a :
  Rabs (FT2R (snd a)) <= /4 * ulp (FT2R (fst a)) -> 
  FT2R (fst a) = 0 -> 
 FT2R (fst a) = rounded Tdouble (@FT2R Tdouble (fst a) + @FT2R Tdouble (snd a)).
Proof.
intros H3 H5.
destruct (Req_dec (FT2R (snd a)) 0).
{  rewrite H5 H Rplus_0_l /rounded round_0. nra. }
rewrite H5 in H3. rewrite H5.
rewrite Rplus_0_l.
apply Rdichotomy in H. destruct H.
apply Ropp_gt_lt_0_contravar in H.
rewrite /rounded.
change (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) with
   ZnearestE.  
assert ( - round radix2 (SpecFloat.fexp (fprec Tdouble) 
    (femax Tdouble)) ZnearestE (FT2R (snd a)) = - 0); [|nra].
rewrite -round_NE_opp. field_simplify.
apply IEEE754_extra.round_NE_underflows => //.
rewrite ulp_FLT_0 in H3; split; try nra.
apply Rabs_le_inv in H3. destruct H3.
apply Ropp_le_contravar in H0.
rewrite Ropp_involutive in H0.
refine (Rle_trans _ _ _ _ _ ).
apply H0. replace (/4) with (bpow radix2 (-2)) => //=; nra.
symmetry.
apply IEEE754_extra.round_NE_underflows => //.
rewrite ulp_FLT_0 in H3; split; try nra.
apply Rabs_le_inv in H3. destruct H3.
refine (Rle_trans _ _ _ _ _ ).
apply H1. replace (/4) with (bpow radix2 (-2)) => //=; nra.
Qed.


Fact dd_pred_double_word_aux2 a :
  bpow radix2 (@emin Tdouble + fprec Tdouble - 1) <= 
          Rabs (FT2R (fst a)) -> 
  Rabs (FT2R (snd a)) <= /4 * ulp (FT2R (fst a)) -> 
  FT2R (fst a) + FT2R (snd a) = 0 -> 
  FT2R (fst a) = rounded Tdouble (@FT2R Tdouble (fst a) + @FT2R Tdouble (snd a)).
Proof.
intros H2 H3 H5.
destruct (Req_dec (FT2R (snd a)) 0).
{ rewrite H in H5; rewrite H.
rewrite Rplus_0_r in H5. 
rewrite H5 Rplus_0_l /rounded round_0; nra. }
apply Rplus_opp_r_uniq in H5.

have Hd: FT2R (fst a) <> 0.
rewrite H5 in H; nra. 

have H':
bpow radix2 (@emin Tdouble + fprec Tdouble - 1) <= Rabs (FT2R (fst a)) by
apply H2.

rewrite H5 in H3. rewrite -ulp_opp in H3.
destruct H3. 
have Hf: (Rabs (FT2R (snd a)) < Rabs (FT2R (snd a))); try nra.
rewrite H5.
rewrite -ulp_abs in H0.
refine (Rlt_trans _ _ _ H0 _).
replace (Rabs (- FT2R (fst a))) with
  ((Rabs (- FT2R (fst a))) * 1) by nra.
rewrite Rmult_comm.
apply Rlt_compat2; try nra.
rewrite Rmult_1_r.
rewrite !ulp_neq_0 => //.  
rewrite cexp_FLT_FLX => //. 
apply bpow_gt_0. simpl.
rewrite Rabs_Rabsolu Rabs_Ropp. 
simpl in H'. nra. 
rewrite Rabs_Ropp. apply Rabs_no_R0 => //.
rewrite Rabs_Ropp. apply Rabs_pos_lt => //.
rewrite Rmult_1_r.
apply ulp_le_id. rewrite Rabs_Ropp. 
apply Rabs_pos_lt => //.
apply generic_format_abs, generic_format_opp.
apply Binary.generic_format_B2R.

apply Rdichotomy in H. destruct H.
exfalso.
have Hf: ( ulp (FT2R (fst a)) <= / 4 * ulp (FT2R (fst a))).
rewrite ulp_opp in H0. rewrite -H0 Rabs_Ropp.
refine (Rle_trans _ _ _ _ _).
apply ulp_le_id; try nra. 
apply Binary.generic_format_B2R.
apply Rle_abs.
field_simplify in Hf. 
move: Hf. 
rewrite !ulp_neq_0 => //.  
rewrite cexp_FLT_FLX => //. 
move=> Hf.
pose proof bpow_gt_0 radix2
  (cexp radix2 (FLX_exp (fprec Tdouble)) (FT2R (fst a))). nra.

exfalso.
have Hf: ( ulp (FT2R (fst a)) <= / 4 * ulp (FT2R (fst a))).
rewrite  -ulp_opp -H5.
refine (Rle_trans _ _ _ _ _).
apply ulp_le_id; try nra. 
apply Binary.generic_format_B2R.
rewrite -H5 in H0.
refine (Rle_trans _ _ _ _ _).
apply Rle_abs. nra. 
field_simplify in Hf. 
move: Hf. 
rewrite !ulp_neq_0 => //.  
rewrite cexp_FLT_FLX => //. 
move=> Hf.
pose proof bpow_gt_0 radix2
  (cexp radix2 (FLX_exp (fprec Tdouble)) (FT2R (fst a))). nra.
Qed.

Fact dd_pred_double_word a :
  dd_pred a -> double_word (fst a) (snd a).
Proof.
rewrite /dd_pred/double_word; 
 move => [] FIN1 [] FIN2 [] Hov [] A [] H1 [] H2 H3.
destruct (Bayleyaux.is_pow_dec radix2 (FT2R (fst a))).
{ symmetry. rewrite /rounded. 
destruct (Req_dec (FT2R (fst a)) 0).
symmetry. apply dd_pred_double_word_aux1 => //.
destruct (Req_dec (FT2R (fst a) + FT2R (snd a)) 0).
symmetry. apply dd_pred_double_word_aux2 => //.
apply H1. apply not_eq_sym; apply H.
symmetry. apply dd_pred_double_word_aux0 => //.
apply H1. apply not_eq_sym; apply H.
apply H2. apply not_eq_sym; apply H0. } 
symmetry. rewrite /rounded. 
destruct (Req_dec (FT2R (fst a)) 0).
symmetry. apply dd_pred_double_word_aux1 => //.
destruct (Req_dec (FT2R (fst a) + FT2R (snd a)) 0).
symmetry. apply dd_pred_double_word_aux2 => //.
apply H1. apply not_eq_sym; apply H.
symmetry. apply dd_pred_double_word_aux0' => //.
apply H1. apply not_eq_sym; apply H.
apply H2. apply not_eq_sym; apply H0.
Qed.

Definition dd_rep1 : Type := 
 { a : dd_rep | dd_pred a }.

Definition DD_zero' : dd_rep1.
 set P := dd_pred.
 assert (P DD_zero). rewrite /DD_zero/P/dd_pred/FT2R => //=.
 rewrite Rplus_0_l Rabs_R0; repeat split; try nra.
 rewrite /dd_ov. simpl; nra.
 apply Rmult_le_pos; try lra.
 apply ulp_ge_0.
 apply (exist _ _ H). 
Defined.


Definition DD2F' (x : dd_rep1) 
  : option (float radix2):= let s:= (proj1_sig x) in
let xhi := fst s in let xlo := snd s in
if Rlt_bool (Rabs (F2R (Operations.Fplus (FT2F xhi) (FT2F xlo)))) dd_ov
(*    &&  is_finite xhi && is_finite xlo *) &&
(if negb (Req_bool (FT2R xhi + FT2R xlo) 0) then
     Rle_bool (bpow radix2 (@emin Tdouble + fprec Tdouble - 1)) (Rabs (FT2R xhi + FT2R xlo))
  else true)
then
 Some (Operations.Fplus (FT2F xhi) (FT2F xlo)) else None.

Definition DD_compare' (x y: dd_rep1) : 
      option comparison := 
  let sx:= (proj1_sig x) in
  let sy:= (proj1_sig y) in
  let xhi := fst sx in let xlo := snd sx in
  let yhi := fst sy in let ylo := snd sy in
  let x' := (Operations.Fplus (FT2F xhi) (FT2F xlo)) in
  let y' := (Operations.Fplus (FT2F yhi) (FT2F ylo)) in
  Some (Rcompare (FPCore.F2R radix2 x') (FPCore.F2R radix2 y')).

Lemma DD_compare'_refl (a : dd_rep1) :
  let sx:= (proj1_sig a) in
  let xhi := fst sx in let xlo := snd sx in
  let x' := (Operations.Fplus (FT2F xhi) (FT2F xlo)) in
DD_compare' a a = Some (Rcompare (FPCore.F2R radix2 x') (FPCore.F2R radix2 x')).
Proof.
intros. rewrite /DD_compare'. f_equal.
Qed.

Definition DD_is_finite_compare' x :
  match DD2F' x with 
  | Some xh => DD_compare' x x = Some Eq 
  | _ => True 
  end.
destruct x. destruct x , f, f0; 
  rewrite /DD_compare'/DD2F'/DD2R/FT2R => //=; f_equal;
match goal with |-  context[ Rlt_bool ?a ?b] =>
  destruct (Rlt_bool a b) => //= end;
match goal with |-  context[ Rle_bool ?a ?b] =>
  destruct (Rle_bool a b) => //= end;
match goal with |-  context[ Req_bool ?a ?b ] =>
  destruct (Req_bool a b) => //= end;
f_equal; by apply Rcompare_Eq .
Defined.

Definition DD_compare_correct' x y a b :
      DD2F' x = Some a ->
      DD2F' y = Some b ->
      DD_compare' x y = Some (Rcompare (F2R a) (F2R b)).
rewrite /DD2F'/DD_compare'. destruct x, y. 
destruct x, x0 => //=.
move => H1 H2. 
simpl in H1, H2;
move : H1 H2.
repeat match goal with |-  context[ Rlt_bool ?a ?b] =>
  destruct (Rlt_bool a b) => //= end;
repeat match goal with |-  context[ Req_bool ?a ?b ] =>
  destruct (Req_bool a b) => //= end;
repeat match goal with |-  context[ Rle_bool ?a ?b ] =>
  destruct (Rle_bool a b) => //= end;
destruct f, f0, f1, f2 => //=;
move =>  H1 H2;
inversion H1; inversion H2 => //=;
try rewrite Rmult_0_l;
try rewrite !FPCore.F2R_eq=> //=;
f_equal => //=;
rewrite !Operations.F2R_plus;
try rewrite !F2R_0 => //=;
try rewrite !Rplus_0_l => //=;
try rewrite !Rplus_0_r => //=.
Defined.



Definition DD_nonstd_nonempty_finite' :
match DD2F' DD_zero' with
| Some xh => True 
| _ => False
end.
rewrite /DD2F'/DD_zero' => //=.
rewrite Rlt_bool_true.
match goal with |-  context[ Rle_bool ?a ?b] =>
  destruct (Rle_bool a b) => //= end.
match goal with |-  context[ Req_bool ?a ?b ] =>
  destruct (Req_bool a b) => //= end.
rewrite Req_bool_true => //=.
rewrite /FT2R => //=; nra.
rewrite F2R0 Rabs_R0 /dd_ov; simpl; nra.
Defined.


Definition DD_bounds' x :
(-(bpow radix2 (femax Tdouble) - 
      bpow radix2 ((femax Tdouble) - Z.pos 106%positive)) <=
match DD2F' x with Some f => F2R f | None => R0 end <=
bpow radix2 (femax Tdouble) - 
    bpow radix2 ((femax Tdouble) - Z.pos 106%positive)).
rewrite /DD2F'. 

remember (Rlt_bool
(Rabs (F2R (Operations.Fplus 
    (FT2F (fst (proj1_sig x))) (FT2F (snd (proj1_sig x)))))) dd_ov).
destruct b => //=; try nra.

remember (Req_bool (FT2R (fst (proj1_sig x)) + FT2R (snd (proj1_sig x))) 0).
destruct b => //=; try nra. 
move: Heqb0. rewrite /Req_bool. 
remember (Rcompare _ _ ). destruct c => //=; move => _.
symmetry in Heqc. apply Rcompare_Eq_inv in Heqc.
rewrite Operations.F2R_plus -!B2F_F2R_B2R.
move: Heqc. rewrite /FT2R => //=. move => Heqc.
rewrite Heqc; nra. 

remember (Rle_bool (/ IZR (Z.pow_pos 2 1022)) 
    (Rabs (FT2R (fst (proj1_sig x)) + FT2R (snd (proj1_sig x))))).
destruct b => //=; try nra.
apply Rabs_le_inv. 
move: Heqb. rewrite /Rlt_bool. 
remember (Rcompare _ _ ). destruct c => //=; move => _.
symmetry in Heqc. apply Rcompare_Lt_inv in Heqc.
move: Heqc. rewrite /FT2R => //=; move => Heqc.
refine (Rle_trans _ _ _ _ _).
apply Rlt_le in Heqc.
apply Heqc. unfold dd_ov. simpl; nra.
Defined.


Definition double_double' : type. 
pose (NONSTD 106 (femax Tdouble) fprec_le_femax_DD nstd_prf2
  dd_rep1 DD_zero' DD2F' DD_compare' 
  DD_is_finite_compare' DD_compare_correct' 
  DD_nonstd_nonempty_finite' DD_bounds').
pose (GTYPE 106 (femax Tdouble) fprec_le_femax_DD nstd_prf2
  (Some n)).
assumption.
Defined.


Definition dd_lb : ftype double_double'.
rewrite /ftype/double_double' => //=.
rewrite /dd_rep1.
set y := (Zconst Tdouble (-Z.pow 2 (femax Tdouble - 3))).
have Hy : FT2R y = IZR (-2 ^ (femax Tdouble - 3)).
{ subst y . rewrite /Zconst. 
destruct (@IEEE754_extra.BofZ_representable
(fprec Tdouble)
  (femax Tdouble) (Pos2Z.is_pos (fprecp Tdouble)) (fprec_lt_femax Tdouble)
( -2 ^ (femax Tdouble - 3))) as ( A & _).
apply IEEE754_extra.integer_representable_opp.
apply (@IEEE754_extra.integer_representable_2p (fprec Tdouble)
  (femax Tdouble) (fprec_gt_0 Tdouble) (fprec_lt_femax Tdouble) 
( (femax Tdouble - 3))); split; simpl; lia.
rewrite FT2R_ftype_of_float A; simpl;
  nra. } 
set y1:= @neg_zero Tdouble.
have Hy1 : FT2R (ftype_of_float y1) = 0.
subst y1.  rewrite /neg_zero/FT2R. simpl. nra.
set Y:= (y, y1). assert (dd_pred Y).
rewrite /Y/dd_pred/fst/snd; repeat split; intros.
rewrite Hy1 /dd_ov Rplus_0_r. simpl. rewrite Hy.
apply Rabs_lt; split; simpl; nra.
rewrite Hy ;
rewrite Ropp_Ropp_IZR Rabs_Ropp Rabs_pos_eq; simpl; nra.
simpl in Hy1. 
rewrite Hy ;
rewrite Ropp_Ropp_IZR Rabs_Ropp Rabs_pos_eq; simpl; nra.
simpl in Hy1. 
rewrite Hy Hy1. 
simpl. interval.
rewrite Hy1 Rabs_R0. 
apply Rmult_le_pos; try nra.
apply Ulp.ulp_ge_0.
 apply (exist _ _ H). 
Defined.

Definition dd_ub : ftype double_double'.
rewrite /ftype/double_double' => //=.
rewrite /dd_rep1.
set y := (Zconst Tdouble (Z.pow 2 (femax Tdouble - 3))).
have Hy : FT2R y = IZR (2 ^ (femax Tdouble - 3)).
{ subst y . rewrite /Zconst. 
destruct (@IEEE754_extra.BofZ_representable
(fprec Tdouble)
  (femax Tdouble) (Pos2Z.is_pos (fprecp Tdouble)) (fprec_lt_femax Tdouble)
( 2 ^ (femax Tdouble - 3))) as ( A & _).
apply (@IEEE754_extra.integer_representable_2p (fprec Tdouble)
  (femax Tdouble) (fprec_gt_0 Tdouble) (fprec_lt_femax Tdouble) 
( (femax Tdouble - 3))); split; simpl; lia.
rewrite FT2R_ftype_of_float A; simpl;
  nra. } 
set y1:= @neg_zero Tdouble.
have Hy1 : FT2R (ftype_of_float y1) = 0.
subst y1.  rewrite /neg_zero/FT2R. simpl. nra.
set Y:= (y, y1). assert (dd_pred Y).
rewrite /Y/dd_pred/fst/snd; repeat split; intros.
rewrite Hy1 /dd_ov Rplus_0_r. simpl. rewrite Hy.
apply Rabs_lt; split; simpl; nra.
rewrite Hy ;
rewrite  Rabs_pos_eq; simpl; nra.
simpl in Hy1. 
rewrite Hy ;
rewrite  Rabs_pos_eq; simpl; nra.
simpl in Hy1. 
rewrite Hy Hy1. 
simpl. interval.
rewrite Hy1 Rabs_R0. 
apply Rmult_le_pos; try nra.
apply Ulp.ulp_ge_0.
 apply (exist _ _ H). 
Defined.


 Lemma dd_ub_implies x :
compare Lt true x dd_ub = true -> 
compare Lt true dd_lb x = true -> 
Rabs (FT2R (fst (proj1_sig x))) < /4 * (bpow radix2 (femax Tdouble)).
Proof.
destruct x, x.
rewrite /compare/compare'/extend_comp. simpl. 
rewrite !Rmult_1_r.
match goal with |- context [ (Rcompare ?a ?b  )] =>
  set ubnd:= b;
  remember (Rcompare a ubnd)
end. 
match goal with |- context [ (Rcompare ?a ?b )] =>
  set lbnd:= a;
  remember (Rcompare lbnd b)
end. 
destruct d as ( A & B & C & D & E) => //.
Qed.

 Lemma dd_ub_implies' x :
compare Lt true x dd_ub = true -> 
compare Lt true dd_lb x = true -> 
Rabs (@FT2R double_double (proj1_sig x)) < /4 * (bpow radix2 (femax Tdouble)).
Proof.
destruct x, x.
rewrite /compare/compare'/extend_comp. simpl. 
rewrite !Rmult_1_r.
match goal with |- context [ (Rcompare ?a ?b  )] =>
  set ubnd:= b;
  remember (Rcompare a ubnd)
end. 
match goal with |- context [ (Rcompare ?a ?b )] =>
  set lbnd:= a;
  remember (Rcompare lbnd b)
end. 
destruct c, c0 => //=. move => _  _.
rewrite FPCore.F2R_eq in Heqc, Heqc0.
rewrite Operations.F2R_plus in Heqc, Heqc0.
rewrite /FT2R/nonstd_to_R => //=.
remember (DD2F _ ). destruct o.
rewrite /DD2F in Heqo.
rewrite Rlt_bool_true in Heqo.
destruct d as (A & B & C & D).
rewrite A B in Heqo. clear A B C D.
simpl in Heqo.
inversion Heqo.
rewrite Operations.F2R_plus.
symmetry in Heqc, Heqc0. 
apply Rcompare_Lt_inv in Heqc, Heqc0.
apply Rabs_lt; split.
refine (Rlt_trans _ _ _ _ _).
2: apply  Heqc0. subst lbnd. nra.
refine (Rlt_trans _ _ _ _ _).
apply  Heqc. subst ubnd. nra.

rewrite Operations.F2R_plus /dd_ov. simpl.
symmetry in Heqc, Heqc0. 
apply Rcompare_Lt_inv in Heqc, Heqc0.
apply Rabs_lt; split.
refine (Rlt_trans _ _ _ _ _).
2: apply  Heqc0. subst lbnd. nra.
refine (Rlt_trans _ _ _ _ _).
apply  Heqc. subst ubnd. nra.

rewrite Rabs_R0. nra.
Qed.

Definition finite_bnds2 := 
    ((dd_lb, true), (dd_ub, true)).

Definition DWplusFP_bnds' : klist bounds [double_double'; Tdouble]:=
   Kcons (finite_bnds2) (Kcons (finite_bnds) Knil).

Definition DWPlusFP' {NANS: Nans}
  (x : ftype double_double') (y : ftype Tdouble) :=
  let xs := proj1_sig x in 
  DWPlusFP (fst xs) (snd xs) y.

Lemma Rcompare_refl x :
Rcompare x x = Eq.
Proof. by apply Rcompare_Eq. Qed.

Theorem ff_congr {NANS: Nans} : 
@floatfunc_congr [double_double'; Tdouble] double_double (@DWPlusFP' NANS).
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
rewrite /nonstd_is_nan/nonstd_compare.
rewrite !DD_compare'_refl !Rcompare_refl.
move => Heq. 
subst.

destruct ah0, bh0 => //;
move => Heq'; subst;
try apply float_equiv_refl.


{  admit.
(* rewrite /float_equiv/nonstd_is_nan => //=.
remember (Rcompare _ _ ). destruct c.
symmetry in Heqc.
apply Rcompare_Eq_inv in Heqc.
simpl in Heqc.
rewrite FPCore.F2R_eq in Heqc.
rewrite Operations.F2R_plus in Heqc. simpl in Heqc.

remember (Rcompare _ _ ). destruct c.
simpl in Heqc. *)
(* {
rewrite Heqc.


have Hj:
(Binary.B754_nan (fprec Tdouble) (femax Tdouble) s pl e) =
(Binary.B754_nan (fprec Tdouble) (femax Tdouble) s0 pl0 e0).
Search float_equiv. Search binary_float_equiv. Search Binary.nan_pl.
} 
 *) }
destruct Heq', H0; subst.
have Hj:
(Binary.B754_finite (fprec Tdouble) (femax Tdouble) s0 m0 e1 e2) =
(Binary.B754_finite (fprec Tdouble) (femax Tdouble) s0 m0 e1 e0).
apply binary_float_equiv_eq => //.
rewrite Hj.
apply float_equiv_refl.
Admitted.

Definition DWPlusFP_ff {NANS: Nans} : floatfunc 
                  [double_double' ;Tdouble] double_double
    DWplusFP_bnds' (fun xhl y => xhl + y)%R.
apply (Build_floatfunc [double_double';Tdouble] 
                double_double _ _ 
          (DWPlusFP')
          2%N 1%N).
intros x ? y ?.

{ simpl in H, H0.
rewrite !andb_true_iff in H H0.
destruct H as [HA HB].
destruct H0 as [HC HD].
rewrite/DWPlusFP'.

pose proof dd_ub_implies' x HB HA as Hb.
simpl in Hb. 

destruct x,x => //=.

pose proof (dd_pred_double_word (f, f0) d).

destruct d as (A & B & C & D & E).

have Hp :
is_finite (fst (DWPlusFP f f0 y)) = true 
    /\ is_finite (snd (DWPlusFP f f0 y)) = true.
pose proof DWPlusFP_finite f f0 y X A B
  (finite_bnds_y_2 y HD HC) D
  (finite_bnds_y_1 y HC HD).
rewrite /is_finite_p in H => //.

have Hov:
Rabs (F2R (FT2F (fst (DWPlusFP f f0 y))) + 
  F2R (FT2F (snd (DWPlusFP f f0 y)))) < dd_ov.

have Hpr : 
(3 <= fprec Tdouble)%Z . 
change (fprec Tdouble) with 53%Z. lia.
destruct (
relative_errorDWPlusFP_correct' f f0 y
  X Hp Hpr) as (d & Heq &Hd).
destruct Hp as (FIN1 & FIN2).
rewrite -!FPCore.F2R_eq !F2R_FT2F Heq.
clear HA HB Hb.
pose proof   (finite_bnds_y_1 y HC HD) as Hy.
rewrite /dd_ov.
move: Hd  D Hy. simpl. intros.
pose proof xl_bnd f f0 X D.
interval with (i_prec 128).

have HFIN: 
 match DD2F (DWPlusFP f f0 y) with
 | Some _ => true
 | None => false
 end = true .
{
rewrite /DD2F. rewrite Operations.F2R_plus.
match goal with |- context [if ?a && ?b then _ else _] => 
remember (a && b)
end. destruct b => //=.

destruct Hp as (FIN1 & FIN2).
rewrite FIN1 FIN2 Rlt_bool_true in Heqb; auto. } 

rewrite HFIN.
simpl; repeat split; try lia. 

destruct (
  relative_errorDWPlusFP_correct' f f0 y) 
as (del & A1 & B1)=> //. 


exists del, 0; repeat split.
simpl. rewrite /FPCore.default_rel.
move : B1; simpl; nra.
rewrite Rabs_R0 /FPCore.default_abs. simpl. nra.

have H1: @FT2R double_double (DWPlusFP f f0 y) = 
  FT2R (fst (DWPlusFP f f0 y)) + FT2R (snd (DWPlusFP f f0 y)).


set (k:= FT2R (fst (DWPlusFP f f0 y)) + FT2R (snd (DWPlusFP f f0 y))).
rewrite /(@FT2R double_double)/nonstd_to_R; simpl.
remember (DD2F (DWPlusFP f f0 y)). destruct o.
subst k. move: Heqo. rewrite /DD2F.
remember (_ && _). 
rewrite Rlt_bool_true in Heqb.
destruct Hp as (FIN1 & FIN2). 
rewrite FIN1 FIN2 in Heqb. simpl in Heqb.
 rewrite Heqb.
set f2:=
(Operations.Fplus (FT2F (fst (DWPlusFP f f0 y))) (FT2F (snd (DWPlusFP f f0 y)))).
 intros.
inversion Heqo. subst f2.
rewrite Operations.F2R_plus.
by rewrite -!F2R_FT2F !FPCore.F2R_eq.

by rewrite Operations.F2R_plus.

discriminate.

rewrite H1.

have H2:
@FT2R double_double' (exist (fun a : dd_rep => dd_pred a) 
  (f, f0) (conj A (conj B (conj C (conj D E))))) =
(FT2R f + FT2R f0).

rewrite /(@FT2R double_double')/nonstd_to_R; simpl.
rewrite /DD2F'. simpl.
remember (_ && _). 

rewrite Rlt_bool_true in Heqb.
destruct Hp as (FIN1 & FIN2).

remember (negb _ ). destruct b0.
symmetry in Heqb0.
rewrite negb_true_iff in Heqb0.
rewrite /Req_bool in Heqb0.

remember (Rcompare _ _).
destruct c. symmetry in Heqc. 
apply Rcompare_Eq_inv in Heqc.

remember (Rle_bool _ _ ).
destruct b0. subst b. simpl.

discriminate.
discriminate.

remember (Rle_bool _ _ ).
destruct b0. subst b. simpl.

rewrite Operations.F2R_plus.
by rewrite -!F2R_FT2F !FPCore.F2R_eq.

subst b. simpl.
destruct E as (D1 & D2 & D3).
rewrite /Rle_bool in Heqb1.
remember (Rcompare (/ IZR (Z.pow_pos 2 1022)) (Rabs (FT2R f + FT2R f0))).
destruct c. discriminate. discriminate.
symmetry in Heqc0, Heqc.
apply Rcompare_Lt_inv in  Heqc.
apply Rcompare_Gt_inv in  Heqc0.
apply Rlt_not_eq, not_eq_sym in Heqc.
clear HA HB H Hb.
specialize (D2 Heqc).
simpl in D2; nra.


remember (Rle_bool _ _ ).
destruct b0. subst b. simpl.

rewrite Operations.F2R_plus.
by rewrite -!F2R_FT2F !FPCore.F2R_eq.

subst b. simpl.
destruct E as (D1 & D2 & D3).
rewrite /Rle_bool in Heqb1.
remember (Rcompare (/ IZR (Z.pow_pos 2 1022)) (Rabs (FT2R f + FT2R f0))).
destruct c. discriminate. discriminate.
symmetry in Heqc0, Heqc.
apply Rcompare_Gt_inv in  Heqc.
apply Rcompare_Gt_inv in  Heqc0.
apply Rgt_not_eq, not_eq_sym in Heqc.
clear HA HB H Hb.
specialize (D2 Heqc).
simpl in D2; nra.

subst b; simpl.
rewrite Operations.F2R_plus.
by rewrite -!F2R_FT2F !FPCore.F2R_eq.

 
rewrite Operations.F2R_plus.
simpl in C. clear HA HB Hb H.
move: C.  
by rewrite -!B2F_F2R_B2R  !B2R_float_of_ftype.

by rewrite H2 Rplus_0_r. } 

apply ff_congr.
Qed.

End VCFloat.