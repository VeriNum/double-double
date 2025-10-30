(** This file contains accuracy proofs for double-word 
plus a (double-word, floating-point number *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common.
Require Import DWPlus DDModels DWord_defs Fast2Mult_acc TwoSum_acc.
From Flocq Require Import Pff2Flocq Core.

Require Import mathcomp.ssreflect.ssreflect.

(* for choice functions : choice = fun x0 : Z => negb (Z.even x0) *)
Require Import Logic.FunctionalExtensionality.

Section CorrectDWPlusFP.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Variables (xh xl y : ftype t).

Theorem DWdouble_word_dw:
DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl) -> 
double_word xh xl.
Proof.
rewrite /DWPlus.double_word/double_word => [] [] [].
move => Fxh Fxl .
destruct (Rlt_or_le (Rabs (FT2R xh + FT2R xl)) 
                (bpow radix2 ((@emin t) + fprec t -1))).
{ have Hg: 
  generic_format radix2 (FLT_exp (@emin t) (fprec t)) (FT2R xh + FT2R xl).
  { apply Plus_error.FLT_format_plus_small.
  apply fprec_gt_0. 
  1,2 : rewrite -B2R_float_of_ftype;
    apply Binary.generic_format_B2R.
  eapply Rle_trans. apply Rlt_le. apply H.
  apply bpow_le; fold (@emin t); lia. }
rewrite /rounded !round_generic => //. 
apply: generic_format_FLX_FLT. apply Hg. } 
rewrite /rounded round_FLT_FLX => //.
Qed.


Theorem dw_word_DWdouble:
double_word xh xl -> 
DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl).
Proof.
rewrite /DWPlus.double_word/double_word.
destruct (Rlt_or_le (Rabs (FT2R xh + FT2R xl)) 
                (bpow radix2 (@emin t + fprec t -1))).
{ have Hg: 
  generic_format radix2 (FLT_exp (@emin t) (fprec t)) (FT2R xh + FT2R xl).
  { apply Plus_error.FLT_format_plus_small.
  apply fprec_gt_0.
  1,2 : rewrite -B2R_float_of_ftype;
    apply: Binary.generic_format_B2R.
  eapply Rle_trans. apply Rlt_le. apply H.
  apply bpow_le; fold (@emin t); lia. }
rewrite /rounded round_generic => //.
move=> H1. have Hx0 : FT2R xl = 0.
assert (FT2R xh + 0 = FT2R xh + FT2R xl) by nra.
apply Rplus_eq_reg_l in H0 => //.
rewrite Hx0 ; repeat split => //. Search (Generic_fmt.round _ _ _ (_ + _) = _).
rewrite Hx0 Rplus_0_r in Hg.
apply: generic_format_FLX_FLT. apply Hg. 
apply generic_format_0.
rewrite round_generic; try lra.
rewrite Hx0 Rplus_0_r in Hg.
rewrite Rplus_0_r.
apply: generic_format_FLX_FLT. apply Hg. } 
rewrite /rounded round_FLT_FLX => //.
move => H1; repeat split => //.
all:  rewrite -B2R_float_of_ftype; apply (generic_format_FLX_FLT radix2 (@emin t));
 apply Binary.generic_format_B2R.
Qed.

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

End CorrectDWPlusFP.

Section  CorrectDWPlusFP'.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Let ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 
Notation u   := (bpow Zaux.radix2 (- fprec t)).

Fact fexp_not_FTZ :  Exp_not_FTZ fexp.
Proof.
rewrite /Exp_not_FTZ/fexp; intros.
have H1: (1 - fprec t <= 0)%Z.
pose proof (@fprec_lb t); lia.
destruct (Z.le_ge_cases  (e - fprec t) (SpecFloat.emin (fprec t) (femax t))).
apply Z.max_r in H; rewrite H => //.
destruct (Z.le_ge_cases  (SpecFloat.emin (fprec t) (femax t) + 1 - fprec t)
   (SpecFloat.emin (fprec t) (femax t))) => //.
apply Z.max_r in H0; rewrite H0; try lia => //.
apply Z.max_l in H0; rewrite H0; try lia => //.
apply Z.max_l in H; rewrite H => //.
destruct (Z.le_ge_cases  (e - fprec t + 1 - fprec t) 
  (SpecFloat.emin (fprec t) (femax t))) .
apply Z.max_r in H0; rewrite H0; try lia => //.
apply Z.max_l in H0; rewrite H0; try lia => //.
Qed.

(* Lemma 2.1 *)
Lemma roundN_plus_ulp_FLT  (a b : ftype t) : 
      ( (FT2R a + FT2R b) <> 0) ->
        Rmax (ulp (FT2R a) /2) (ulp (FT2R b)/ 2) <= Rabs (rounded t (FT2R a + FT2R b)).
Proof.
move=> sn0.
have Hv: Valid_exp fexp by apply FLT.FLT_exp_valid.
have Hexp: Exp_not_FTZ fexp by apply  fexp_not_FTZ.
have Hv2: 
Valid_rnd (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
  by apply BinarySingleNaN.valid_rnd_round_mode.
have Ha: generic_format radix2 fexp (FT2R a) by
  rewrite -!B2R_float_of_ftype; apply Binary.generic_format_B2R. 
have Hb: generic_format radix2 fexp (FT2R b) by 
  rewrite -!B2R_float_of_ftype; apply Binary.generic_format_B2R. 
have Hrnd: rounded t (FT2R a + FT2R b) <> 0.
rewrite /rounded; apply Plus_error.round_plus_neq_0 => //.
have Hbpow : 
bpow radix2 (@emin t) / 2 <=
bpow radix2 (@emin t) .
  apply Rdiv_le_left; try nra.
  refine (Rle_trans _ _ _ _  (Rmult_le_compat_l _ 1 _ _ _ ));
  try nra. apply bpow_ge_0.
destruct (Req_dec (FT2R a) 0). 
{ move : sn0. rewrite H Rplus_0_l. 
  move=> sn0. 
  rewrite /rounded round_generic => //.
  apply Rmax_lub.
  refine (Rle_trans _ (ulp 0) _ _ _ ).
  rewrite /ulp ulp_FLT_0 => //. 
  refine (Rle_trans _ _ _ _ (ulp_le_abs radix2 fexp _ _ _)) => //.
  apply ulp_ge_ulp_0 => //.
  apply Rdiv_le_left; try nra.
  refine (Rle_trans _ _ _ _  (Rmult_le_compat_l _ 1 _ _ _ ));
    try nra.  rewrite Rmult_1_r. apply ulp_le_abs => //. 
  apply Rabs_pos. } 
destruct (Req_dec (FT2R b) 0). 
{ move : sn0. rewrite H0 Rplus_0_r. 
  move=> sn0. 
  rewrite /rounded round_generic => //.
  apply Rmax_lub.
  apply Rdiv_le_left; try nra.
  refine (Rle_trans _ _ _ _  (Rmult_le_compat_l _ 1 _ _ _ ));
    try nra.  rewrite Rmult_1_r. apply ulp_le_abs => //. 
  apply Rabs_pos.
  refine (Rle_trans _ (ulp 0) _ _ _ ).
  rewrite /ulp ulp_FLT_0 => //.
  refine (Rle_trans _ _ _ _ (ulp_le_abs radix2 fexp _ _ _)) => //.
  apply ulp_ge_ulp_0 => //. } 
unfold Rmax.
destruct (Rle_dec (ulp (FT2R a) /2) (ulp (FT2R b) / 2)).
destruct (Rle_or_lt (bpow radix2 (@emin t + fprec t)) (Rabs (FT2R b))).
{ rewrite Rplus_comm.
  refine (Rle_trans _ _ _ _  _).
  2: apply round_plus_ge_ulp => //.
  replace (FT2R b / IZR radix2) with (FT2R b  * bpow radix2 (-1)) => //.
  rewrite ulp_FLT_exact_shift /ulp/fexp/FLT_exp => //=. 
  field_simplify; try nra. 
  apply mag_ge_bpow => //.
  eapply Rle_trans.
  2: apply H1. apply bpow_le. rewrite /emin. lia.
  have : 
  (SpecFloat.emin (fprec t) (femax t) + fprec t + 1  <= mag radix2 (FT2R b))%Z.
  apply mag_ge_bpow => //.
  eapply Rle_trans.
  2: apply H1. apply bpow_le. rewrite /emin. lia.
  lia. rewrite Rplus_comm => //. } 
rewrite Rplus_comm.
  refine (Rle_trans _ _ _ _  _).
2: apply round_plus_ge_ulp => //.
rewrite /ulp !ulp_FLT_small => //.
  refine (Rlt_trans _ _ _ _ H1). 
rewrite Rabs_div_Raux.
apply Rdiv_lt_left.
apply Rabs_pos_lt.
apply not_0_IZR => //.
  refine (Rle_lt_trans _ _ _ _  (Rmult_lt_compat_l _ 1 _ _ _ ));
    try nra.  
apply Rabs_pos_lt => //.
simpl; rewrite Rabs_right; try nra.
apply not_0_IZR => //.
rewrite Rplus_comm => //.
apply Rnot_le_lt in n.
destruct (Rle_or_lt (bpow radix2 (@emin t + fprec t)) (Rabs (FT2R a))).
{ refine (Rle_trans _ _ _ _  _).
  2: apply round_plus_ge_ulp => //.
  replace (FT2R a / IZR radix2) with (FT2R a  * bpow radix2 (-1)) => //.
  rewrite ulp_FLT_exact_shift /ulp/fexp/FLT_exp => //=. 
  field_simplify; try nra. 
  apply mag_ge_bpow => //.
  eapply Rle_trans.
  2: apply H1. apply bpow_le. rewrite /emin. lia.
  have : 
  (SpecFloat.emin (fprec t) (femax t) + fprec t + 1  <= mag radix2 (FT2R a))%Z.
  apply mag_ge_bpow => //.
  eapply Rle_trans.
  2: apply H1. apply bpow_le. rewrite /emin. lia.
  lia. } 
refine (Rle_trans _ _ _ _  _).
2: apply round_plus_ge_ulp => //.
rewrite /ulp !ulp_FLT_small => //.
  refine (Rlt_trans _ _ _ _ H1). 
rewrite Rabs_div_Raux.
apply Rdiv_lt_left.
apply Rabs_pos_lt.
apply not_0_IZR => //.
  refine (Rle_lt_trans _ _ _ _  (Rmult_lt_compat_l _ 1 _ _ _ ));
    try nra.  
apply Rabs_pos_lt => //.
simpl; rewrite Rabs_right; try nra.
apply not_0_IZR => //.
Qed.


Let rnd_p {t} := round radix2 (FLX_exp (fprec t)) (Znearest choice).
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
apply DWdouble_word_dw.
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

Lemma DWPlusFP_double_word' : 
rounded t (FT2R (fst (DWPlusFP xh xl y)) + FT2R (snd (DWPlusFP xh xl y)) ) = 
  FT2R (fst (DWPlusFP xh xl y)).
Proof.
symmetry. apply DWPlusFP_double_word.
Qed.

End CorrectDWPlusFP'.

Section DWPlusFPFinite.
Context {NANS: Nans} .
Variables (xh xl y : ftype Tdouble).

Hypothesis DWx : double_word xh  xl.
Notation t:= Tdouble.

Require Import Interval.Tactic.

Lemma TwoSumF_sum_finite
(HFINxh: Binary.is_finite (fprec t) (femax t) (float_of_ftype xh) = true) 
(HFINy : Binary.is_finite (fprec t) (femax t) (float_of_ftype y) = true) 
(Hxh : Rabs (FT2R xh) <= /2 * (bpow radix2 (femax t)))
(Hy :  Rabs (FT2R y)  < /4 * (bpow radix2 (femax t))) : 
let sh := TwoSumF_sum xh y in
Binary.is_finite (fprec t) (femax t) (float_of_ftype sh) = true.
Proof.
rewrite /TwoSumF_sum/TwoSumF_err/TwoSumF/fst/snd => //.
have Hov1: 
        (Rabs
           (round radix2 (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
              (Binary.B2R (fprec t) (femax t) xh + Binary.B2R (fprec t) (femax t) y))) <
        (bpow radix2 (femax t)).
pose proof
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R xh)
  (FT2R y) ).
destruct H as (d1 & Hd & B).  
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.  
move: Hd . unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
match goal with |- Rabs ?a < _ =>
field_simplify a; interval with (i_prec 128)
end. 

 pose proof 
  (@Binary.Bplus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
  BinarySingleNaN.mode_NE xh y
  HFINxh HFINy) as Hp.
move: Hp.
rewrite Rlt_bool_true. move =>  [] A [] Hp _; auto.
auto. 
Qed.

Notation fexp:= ((SpecFloat.fexp (fprec t) (femax t))).

Lemma TwoSumF_err_finite_ubnd
(Hxh : Rabs (FT2R xh + FT2R xl) < /4 * (bpow radix2 (femax t))):
  FT2R xh <=  / 2 * bpow radix2 (femax t).
Proof.
have Hbnd : - / 4 * bpow radix2 (femax t) - FT2R xl <= 
                FT2R xh  <= / 4 * bpow radix2 (femax t) - FT2R xl.
{ destruct (Req_dec 0 (FT2R xh)).
rewrite -H Rplus_0_l in Hxh.
apply Rabs_lt_inv in Hxh. split; destruct Hxh; nra.
apply not_eq_sym in H.
apply dw_le in DWx => //. apply Rabs_le_inv in DWx.
apply Rabs_lt_inv in Hxh. split; destruct Hxh.
by apply Rcomplements.Rlt_minus_l in H0; nra.
by apply Rcomplements.Rlt_minus_r in H1; nra.  }

have HDWx :  double_word xh xl by assumption.

have A:  2 * FT2R xh <= 
   / 2 * bpow radix2 (femax t) + ulp radix2 fexp (FT2R xh).
{ destruct Hbnd. 
replace (2 * FT2R xh) with (FT2R xh * 2) by nra.
apply Rcomplements.Rle_div_r; try nra. field_simplify.
refine (Rle_trans _ _ _ H0  _). 
apply Rcomplements.Rle_div_l; try nra; field_simplify.
apply Rplus_le_compat_l.
apply dw_ulp in HDWx. 
  apply Rabs_le_inv in HDWx. destruct HDWx. 
nra. }
 
destruct (Req_dec 0 (FT2R xh)).

(** case 1/2: FT2R xh = 0 *)
{ rewrite -H; nra. } 
(** case 2/2: FT2R xh <> 0 *)
apply not_eq_sym in H.
apply dw_le in DWx => //. apply Rabs_le_inv in DWx.
destruct (Rlt_dec (FT2R xh) 0).

(** case 1/2 : FT2R xh < 0 *)
{ pose proof Rabs_left (FT2R xh)  r as H1. 
move: DWx. rewrite H1 Ropp_involutive. move => HDWx'.
have B : 2 * FT2R xh <=  / 2 * bpow radix2 (femax t) - FT2R xh ; [| nra].
refine (Rle_trans _ _ _ A _). 
apply Rplus_le_compat_l; rewrite -ulp_opp. 
apply  ulp_le_id; try nra.
apply generic_format_opp.
apply Binary.generic_format_B2R. }
(** case 2/2: 0 <= FT2R xh *) 
apply Rnot_lt_le in n. apply Rle_ge in n.
pose proof Rabs_right (FT2R xh) n as H1. 
move: DWx. rewrite H1. move => HDWx'.

have B :  2 * FT2R xh <=  / 2 * bpow radix2 (femax t) + FT2R xh ; [| nra].
refine (Rle_trans _ _ _ A _).
apply Rplus_le_compat_l.
apply  ulp_le_id; try nra.
apply Binary.generic_format_B2R.
Qed.



Lemma TwoSumF_err_finite_lbnd
(Hxh : Rabs (FT2R xh + FT2R xl) < /4 * (bpow radix2 (femax t))):
 - (/ 2 * bpow radix2 (femax t)) <= FT2R xh.
Proof.
have Hbnd : - / 4 * bpow radix2 (femax t) - FT2R xl <= 
                FT2R xh  <= / 4 * bpow radix2 (femax t) - FT2R xl.
{ destruct (Req_dec 0 (FT2R xh)).
rewrite -H Rplus_0_l in Hxh.
apply Rabs_lt_inv in Hxh. split; destruct Hxh; nra.
apply not_eq_sym in H.
apply dw_le in DWx => //. apply Rabs_le_inv in DWx.
apply Rabs_lt_inv in Hxh. split; destruct Hxh.
by apply Rcomplements.Rlt_minus_l in H0; nra.
by apply Rcomplements.Rlt_minus_r in H1; nra.  }

have HDWx :  double_word xh xl by assumption.

have A: - / 2 * bpow radix2 (femax t) 
  - ulp radix2 fexp (FT2R xh) <= 2 * FT2R xh.
{ destruct Hbnd.
replace (2 * FT2R xh) with (FT2R xh * 2) by nra.
apply Rcomplements.Rle_div_l; try nra. field_simplify.
refine (Rle_trans _ _ _ _  _). 2: apply H.
apply Rcomplements.Rle_div_l; try nra; field_simplify.
apply Rplus_le_compat_l.
apply dw_ulp in HDWx. 
  apply Rabs_le_inv in HDWx. destruct HDWx.
apply Ropp_le_contravar; nra. }
 
destruct (Req_dec 0 (FT2R xh)).

(** case 1/2: FT2R xh = 0 *)
{ rewrite -H; nra. } 
(** case 2/2: FT2R xh <> 0 *)
apply not_eq_sym in H.
apply dw_le in DWx => //. apply Rabs_le_inv in DWx.
destruct (Rlt_dec (FT2R xh) 0).

(** case 1/2 : FT2R xh < 0 *)
{ pose proof Rabs_left (FT2R xh)  r as H1. 
move: DWx. rewrite H1 Ropp_involutive. move => HDWx'.
have B : - / 2 * bpow radix2 (femax t) 
    + FT2R xh <= 2 * FT2R xh; [| nra].
refine (Rle_trans _ _ _ _  _). 2: apply A.
apply Rplus_le_compat_l, Ropp_le_cancel.
rewrite Ropp_involutive -ulp_opp. 
apply  ulp_le_id; try nra.
apply generic_format_opp.
apply Binary.generic_format_B2R. }
(** case 2/2: 0 <= FT2R xh *) 
apply Rnot_lt_le in n. apply Rle_ge in n.
pose proof Rabs_right (FT2R xh) n as H1. 
move: DWx. rewrite H1. move => HDWx'.

have B : - / 2 * bpow radix2 (femax t) 
    - FT2R xh <= 2 * FT2R xh; [| nra].
refine (Rle_trans _ _ _ _  _). 2: apply A.
apply Rplus_le_compat_l, Ropp_le_cancel.
rewrite !Ropp_involutive. 
apply  ulp_le_id; try nra.
apply Binary.generic_format_B2R.
Qed.

Lemma TwoSumF_err_finite_bnd
(Hxh : Rabs (FT2R xh + FT2R xl) < /4 * (bpow radix2 (femax t))):
Rabs (FT2R xh) <=  (/ 2 * bpow radix2 (femax t)) .
Proof.
apply Rabs_le; split;
 [apply TwoSumF_err_finite_lbnd |  apply TwoSumF_err_finite_ubnd] => //.
Qed.

Lemma TwoSumF_err_finite'
(HFINxh: Binary.is_finite (fprec t) (femax t) (float_of_ftype xh) = true) 
(HFINy : Binary.is_finite (fprec t) (femax t) (float_of_ftype y) = true) 
(Hy : Rabs (FT2R y) < /4 * (bpow radix2 (femax t)))
(Hxh : Rabs (FT2R xh + FT2R xl) < /4 * (bpow radix2 (femax t))):
let sl := TwoSumF_err xh y in
Binary.is_finite (fprec t) (femax t) (float_of_ftype sl) = true.
Proof.
rewrite /TwoSumF_sum/TwoSumF_err/TwoSumF/fst/snd => //.
have HA:  
Rabs (FT2R xh) <= / 2 * IZR (Z.pow_pos 2 1024) by 
  (apply TwoSumF_err_finite_bnd ;nra).
have HFIN : Binary.is_finite (fprec t) (femax t) (float_of_ftype (BPLUS xh y)) = true by
   apply TwoSumF_sum_finite => //. 

have Hxhb:  FT2R xh <=  / 2 * bpow radix2 (femax t).
apply TwoSumF_err_finite_ubnd => //.

pose proof
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R (BPLUS xh y))
  (-FT2R y) ).

have Hov1: 
        (Rabs
           (round radix2 (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
              (Binary.B2R (fprec t) (femax t) (xh + y)%F64 - Binary.B2R (fprec t) (femax t) y))) <
        (bpow radix2 (femax t)).
{ destruct H as (d1 & Hd & B).  
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.  
rewrite -is_finite_Binary in HFIN.
destruct (BPLUS_accurate' _ _ _ HFIN) as (d6 & Hd6 & B).
rewrite B. clear B. 
move: Hd  Hd6. unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxhb, Hy.
simpl in Hxhb.
match goal with |- Rabs ?a < _ =>
field_simplify a;
interval with (i_prec 128)
end. }

have FIN1 : is_finite (xh + y - y)%F64 = true.
pose proof 
  (@Binary.Bminus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
  BinarySingleNaN.mode_NE ( xh + y)%F64 y
  HFIN HFINy) as Hp.
move: Hp.
rewrite Rlt_bool_true. move =>  [] A [] Hp _; auto.
auto. clear H.
(* *)
pose proof
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R (BPLUS xh y))
  (-FT2R (xh + y - y)%F64) ).

have Hov2: 
        (Rabs
           (round radix2 (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
              (Binary.B2R (fprec t) (femax t) (xh + y)%F64 - Binary.B2R (fprec t) (femax t) 
                (xh + y - y)%F64))) <
        (bpow radix2 (femax t)).
{ destruct H as (d1 & Hd & B).  
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.
destruct (BMINUS_accurate' _ _ _ FIN1) as (d2 & Hd2 & B).
rewrite B. clear B. 
rewrite -is_finite_Binary in HFIN.
destruct (BPLUS_accurate' _ _ _ HFIN) as (d3 & Hd3 & B).
rewrite B. clear B. 
move: Hd  Hd2 Hd3. unfold  default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
match goal with |- Rabs ?a < _ =>
field_simplify a;
interval with (i_prec 128)
end. }

have FIN2 : is_finite (xh + y - (xh + y - y))%F64 = true.
rewrite is_finite_Binary in FIN1.
pose proof 
  (@Binary.Bminus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
  BinarySingleNaN.mode_NE ( xh + y)%F64 (xh + y - y)%F64
  HFIN FIN1 ) as Hp.
move: Hp.
rewrite Rlt_bool_true. move =>  [] A [] Hp _; auto.
auto.
clear H.
(* *)
pose proof
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R y)
  (-FT2R (xh + y - (xh + y - y))%F64) ).

have Hov3: 
        (Rabs
           (round radix2 (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
              (Binary.B2R (fprec t) (femax t) y - Binary.B2R (fprec t) (femax t) 
                (xh + y - (xh + y - y))%F64))) <
        (bpow radix2 (femax t)).
{ destruct H as (d1 & Hd & B).  
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.
destruct (BMINUS_accurate' _ _ _ FIN2) as (d2 & Hd2 & B).
rewrite B. clear B. 
destruct (BMINUS_accurate' _ _ _ FIN1) as (d4 & Hd4 & B).
rewrite B. clear B.
rewrite -is_finite_Binary in HFIN.
destruct (BPLUS_accurate' _ _ _ HFIN) as (d3 & Hd3 & B).
rewrite B. clear B.
move: Hd  Hd2 Hd3 Hd4. unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
match goal with |- Rabs ?a < _ =>
field_simplify a;
interval with (i_prec 128)
end. } 

have FINR : is_finite (y - (xh + y - (xh + y - y)))%F64 = true.
rewrite is_finite_Binary in FIN2.
pose proof 
  (@Binary.Bminus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
  BinarySingleNaN.mode_NE y (xh + y - (xh + y - y))%F64
  HFINy FIN2 ) as Hp.
move: Hp.
rewrite Rlt_bool_true. move =>  [] A [] Hp _; auto.
auto.
clear H.
(* *)
pose proof
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R xh)
  (-FT2R (xh + y - y)%F64) ).

have Hov4: 
        (Rabs
           (round radix2 (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
              (Binary.B2R (fprec t) (femax t) xh - Binary.B2R (fprec t) (femax t) 
                (xh + y - y)%F64))) <
        (bpow radix2 (femax t)).
{ destruct H as (d1 & Hd & B).  
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.
destruct (BMINUS_accurate' _ _ _ FIN1) as (d2 & Hd2 & B).
rewrite B. clear B. 
rewrite -is_finite_Binary in HFIN.
destruct (BPLUS_accurate' _ _ _ HFIN) as (d3 & Hd3 & B).
rewrite B. clear B. 
move: Hd Hd2 Hd3. unfold  default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
match goal with |- Rabs ?a < _ =>
field_simplify a;
interval with (i_prec 128)
end. } 

have FINL : is_finite (xh - (xh + y - y))%F64 = true.
rewrite is_finite_Binary in FIN1.
pose proof 
  (@Binary.Bminus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
  BinarySingleNaN.mode_NE xh (xh + y - y)%F64
  HFINxh FIN1 ) as Hp.
move: Hp.
rewrite Rlt_bool_true. move =>  [] A [] Hp _; auto.
auto.
clear H.
(* *)
pose proof (Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R (xh - (xh + y - y))%F64)
  (FT2R (y - (xh + y - (xh + y - y)))%F64) ).

have HOV1: 
Rabs (round radix2 (SpecFloat.fexp (fprec t) (femax t)) 
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
(FT2R (xh - (xh + y - y))%F64 + FT2R (y - (xh + y - (xh + y - y)))%F64)) < bpow radix2 (femax t).

destruct H as (d1 & Hd & B).
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.  

pose proof (@BMINUS_accurate' _ _ _ y (xh + y - (xh + y - y))%F64).
destruct H as (d2 & Hd2 & B). auto.
rewrite B. clear B.

pose proof (@BMINUS_accurate' _ _ _ (xh + y)%F64 (xh + y - y)%F64).
destruct H as (d3 & Hd3 & B). auto.
rewrite B. clear B.

pose proof (@BMINUS_accurate' _ _ _ xh (xh + y - y)%F64).
destruct H as (d4 & Hd4 & B). auto.
rewrite B. clear B.

pose proof (@BMINUS_accurate' _ _ _ (xh + y)%F64 y).
destruct H as (d5 & Hd5 & B). auto.
rewrite B. clear B.

rewrite -is_finite_Binary in HFIN.
destruct (BPLUS_accurate' _ _ _ HFIN) as (d6 & Hd6 & B).
rewrite B. clear B. 

move: Hd Hd2 Hd3 Hd4 Hd5 Hd6. unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
match goal with |- Rabs ?a < _ =>
field_simplify a;
interval with (i_prec 128)
end.


pose proof 
  (@Binary.Bplus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
  BinarySingleNaN.mode_NE ( (xh - (xh + y - y))%F64) 
  (y - (xh + y - (xh + y - y)))%F64
  FINL FINR) as Hp.
move: Hp.
rewrite Rlt_bool_true. move =>  [] A [] Hp _; auto.
auto.
Qed.


Lemma TwoSumF_err_finite
(HFINxh: Binary.is_finite (fprec t) (femax t) (float_of_ftype xh) = true) 
(HFINy : Binary.is_finite (fprec t) (femax t) (float_of_ftype y) = true) 
(Hxh : Rabs (FT2R xh + FT2R xl) < / 4 * bpow radix2 (femax t))
(Hy :  Rabs (FT2R y)  < /4 * (bpow radix2 (femax t)))  :
let sl := TwoSumF_err xh y in
Binary.is_finite (fprec t) (femax t) (float_of_ftype sl) = true.
Proof.
rewrite /TwoSumF_sum/TwoSumF_err/TwoSumF/fst/snd => //.
have HA:  
Rabs (FT2R xh) <= / 2 * IZR (Z.pow_pos 2 1024) by  
  (apply TwoSumF_err_finite_bnd ; try nra).
have HFIN : Binary.is_finite (fprec t) (femax t) (float_of_ftype (BPLUS xh y)) = true.
apply TwoSumF_sum_finite => //.
(* *)
pose proof
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R (BPLUS xh y))
  (-FT2R y) ).

have Hov1: 
        (Rabs
           (round radix2 (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
              (Binary.B2R (fprec t) (femax t) (xh + y)%F64 - Binary.B2R (fprec t) (femax t) y))) <
        (bpow radix2 (femax t)).
{ destruct H as (d1 & Hd & B).  
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.  
rewrite -is_finite_Binary in HFIN.
destruct (BPLUS_accurate' _ _ _ HFIN) as (d6 & Hd6 & B).
rewrite B. clear B. 
move: Hd  Hd6. unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
match goal with |- Rabs ?a < _ =>
field_simplify a;
interval with (i_prec 128)
end. } 
have FIN1 : is_finite (xh + y - y)%F64 = true.
pose proof 
  (@Binary.Bminus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t)) 
  BinarySingleNaN.mode_NE ( xh + y)%F64 y
  HFIN HFINy) as Hp.
move: Hp.
rewrite Rlt_bool_true. move =>  [] A [] Hp _; auto.
auto. clear H.
(* *)
pose proof
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R (BPLUS xh y))
  (-FT2R (xh + y - y)%F64) ).

have Hov2: 
        (Rabs
           (round radix2 (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
              (Binary.B2R (fprec t) (femax t) (xh + y)%F64 - Binary.B2R (fprec t) (femax t) 
                (xh + y - y)%F64))) <
        (bpow radix2 (femax t)).
{ destruct H as (d1 & Hd & B).  
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.
destruct (BMINUS_accurate' _ _ _ FIN1) as (d2 & Hd2 & B).
rewrite B. clear B. 
rewrite -is_finite_Binary in HFIN.
destruct (BPLUS_accurate' _ _ _ HFIN) as (d3 & Hd3 & B).
rewrite B. clear B. 
move: Hd  Hd2 Hd3. unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
match goal with |- Rabs ?a < _ =>
field_simplify a;
interval with (i_prec 128)
end. } 

have FIN2 : is_finite (xh + y - (xh + y - y))%F64 = true.
rewrite is_finite_Binary in FIN1.
pose proof 
  (@Binary.Bminus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t)) 
  BinarySingleNaN.mode_NE ( xh + y)%F64 (xh + y - y)%F64
  HFIN FIN1 ) as Hp.
move: Hp.
rewrite Rlt_bool_true. move =>  [] A [] Hp _; auto.
auto.
clear H.
(* *)
pose proof
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R y)
  (-FT2R (xh + y - (xh + y - y))%F64) ).

have Hov3: 
        (Rabs
           (round radix2 (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
              (Binary.B2R (fprec t) (femax t) y - Binary.B2R (fprec t) (femax t) 
                (xh + y - (xh + y - y))%F64))) <
        (bpow radix2 (femax t)).
{ destruct H as (d1 & Hd & B).  
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.
destruct (BMINUS_accurate' _ _ _ FIN2) as (d2 & Hd2 & B).
rewrite B. clear B. 
destruct (BMINUS_accurate' _ _ _ FIN1) as (d4 & Hd4 & B).
rewrite B. clear B.
rewrite -is_finite_Binary in HFIN.
destruct (BPLUS_accurate' _ _ _ HFIN) as (d3 & Hd3 & B).
rewrite B. clear B.
move: Hd  Hd2 Hd3 Hd4. unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
match goal with |- Rabs ?a < _ =>
field_simplify a;
interval with (i_prec 128) 
end. } 

have FINR : is_finite (y - (xh + y - (xh + y - y)))%F64 = true.
rewrite is_finite_Binary in FIN2.
pose proof 
  (@Binary.Bminus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t)) 
  BinarySingleNaN.mode_NE y (xh + y - (xh + y - y))%F64
  HFINy FIN2 ) as Hp.
move: Hp.
rewrite Rlt_bool_true. move =>  [] A [] Hp _; auto.
auto.
clear H.
(* *)
pose proof
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R xh)
  (-FT2R (xh + y - y)%F64) ).

have Hov4: 
        (Rabs
           (round radix2 (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
              (Binary.B2R (fprec t) (femax t) xh - Binary.B2R (fprec t) (femax t) 
                (xh + y - y)%F64))) <
        (bpow radix2 (femax t)).
{ destruct H as (d1 & Hd & B).  
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.
destruct (BMINUS_accurate' _ _ _ FIN1) as (d2 & Hd2 & B).
rewrite B. clear B. 
rewrite -is_finite_Binary in HFIN.
destruct (BPLUS_accurate' _ _ _ HFIN) as (d3 & Hd3 & B).
rewrite B. clear B. 
move: Hd Hd2 Hd3. unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
match goal with |- Rabs ?a < _ =>
field_simplify a;
interval with (i_prec 128)
end. } 

have FINL : is_finite (xh - (xh + y - y))%F64 = true.
rewrite is_finite_Binary in FIN1.
pose proof 
  (@Binary.Bminus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
  BinarySingleNaN.mode_NE xh (xh + y - y)%F64
  HFINxh FIN1 ) as Hp.
move: Hp.
rewrite Rlt_bool_true. move =>  [] A [] Hp _; auto.
auto.
clear H.
(* *)


pose proof (Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R (xh - (xh + y - y))%F64)
  (FT2R (y - (xh + y - (xh + y - y)))%F64) ).


have HOV1: 
Rabs (round radix2 (SpecFloat.fexp (fprec t) (femax t)) 
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
(FT2R (xh - (xh + y - y))%F64 + FT2R (y - (xh + y - (xh + y - y)))%F64)) < bpow radix2 (femax t).

destruct H as (d1 & Hd & B).
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite B. clear B.  

pose proof (@BMINUS_accurate' _ _ _ y (xh + y - (xh + y - y))%F64).
destruct H as (d2 & Hd2 & B). auto.
rewrite B. clear B.

pose proof (@BMINUS_accurate' _ _ _ (xh + y)%F64 (xh + y - y)%F64).
destruct H as (d3 & Hd3 & B). auto.
rewrite B. clear B.

pose proof (@BMINUS_accurate' _ _ _ xh (xh + y - y)%F64).
destruct H as (d4 & Hd4 & B). auto.
rewrite B. clear B.

pose proof (@BMINUS_accurate' _ _ _ (xh + y)%F64 y).
destruct H as (d5 & Hd5 & B). auto.
rewrite B. clear B.

rewrite -is_finite_Binary in HFIN.
destruct (BPLUS_accurate' _ _ _ HFIN) as (d6 & Hd6 & B).
rewrite B. clear B. 

move: Hd Hd2 Hd3 Hd4 Hd5 Hd6. unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
match goal with |- Rabs ?a < _ =>
field_simplify a;
interval with (i_prec 128)
end.

pose proof 
  (@Binary.Bplus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
  BinarySingleNaN.mode_NE ( (xh - (xh + y - y))%F64) 
  (y - (xh + y - (xh + y - y)))%F64
  FINL FINR) as Hp.
move: Hp.
rewrite Rlt_bool_true. move =>  [] A [] Hp _; auto.
auto.
Qed.

Theorem is_finite_p_TwoSum 
(HFINxh: Binary.is_finite (fprec t) (femax t) (float_of_ftype xh) = true) 
(HFINy : Binary.is_finite (fprec t) (femax t) (float_of_ftype y) = true) 
(Hxh : Rabs (FT2R xh + FT2R xl) < /4 * (bpow radix2 (femax t)))
(Hy :  Rabs (FT2R y)  < /4 * (bpow radix2 (femax t)))  :
is_finite_p (TwoSumF xh y).
Proof. 
rewrite /is_finite_p; split.
apply TwoSumF_sum_finite => //.
apply TwoSumF_err_finite_bnd => //.
apply TwoSumF_err_finite => //.
Qed.

Let sh := TwoSumF_sum xh y.
Let sl := TwoSumF_err xh y.

Lemma xl_bnd 
(Hxh : Rabs (FT2R xh) <= /2 * (bpow radix2 (femax t))) :
Rabs (FT2R xl) <= / 2 * IZR (Z.pow_pos 2 971). 
Proof.
apply dw_ulp in DWx.
refine (Rle_trans _ _ _  DWx _).
set g:=
/ 2 * ulp radix2 (SpecFloat.fexp (fprec t) (femax t)) 
    ( bpow radix2 (femax t - 1)).
refine (Rle_trans _ g _  _ _).
rewrite /g.
apply Rmult_le_compat_l; try nra.
apply ulp_le. 
apply BinarySingleNaN.fexp_correct.
apply (fprec_gt_0 t).
apply FLT_exp_monotone.
refine (Rle_trans _ _  _  Hxh _).
rewrite Rabs_pos_eq; [simpl; try nra | apply bpow_ge_0].
subst g. rewrite ulp_bpow. simpl; nra.
Qed.

Theorem DWPlusFP_zh_finite
(HFINxh: Binary.is_finite (fprec t) (femax t) (float_of_ftype xh) = true) 
(HFINxl: Binary.is_finite (fprec t) (femax t) (float_of_ftype xl) = true) 
(HFINy : Binary.is_finite (fprec t) (femax t) (float_of_ftype y) = true) 
(Hxhl : Rabs (FT2R xh + FT2R xl) < /4 * (bpow radix2 (femax t)))
(Hy :  Rabs (FT2R y)  < /4 * (bpow radix2 (femax t))): 
let zh := Fast2Sum_sum sh (BPLUS xl sl) in
 Binary.is_finite (fprec t) (femax t) (float_of_ftype zh) = true.
Proof.
rewrite /Fast2Sum_err/fst/snd => //.
rewrite /Fast2Sum_sum/fst/Fast2Sum.

have Hxh:  
Rabs (FT2R xh) <= / 2 * IZR (Z.pow_pos 2 1024). by  
  (apply TwoSumF_err_finite_bnd ; try nra).

have HFIN : Binary.is_finite (fprec t) (femax t) (float_of_ftype (BPLUS xh y)) = true.
apply TwoSumF_sum_finite => //.

have Hxl :Rabs (FT2R xl) <= / 2 * IZR (Z.pow_pos 2 971) by
  apply xl_bnd => //.

have HFINsl :
Binary.is_finite (fprec t) (femax t) (float_of_ftype sl) = true by
apply TwoSumF_err_finite => //.

destruct (TwoSumF_error xh y 
  (is_finite_p_TwoSum HFINxh HFINy Hxhl Hy))  as (d1 & B1 & Hd1).
fold sl in B1. 

have HFINxsl : 
Binary.is_finite (fprec t) (femax t) (xl + sl)%F64 = true.
pose proof 
  (@Binary.Bplus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t))
  BinarySingleNaN.mode_NE xl sl HFINxl HFINsl
   ) as Hp.
 move: Hp.
rewrite Rlt_bool_true. move =>  A.
destruct A, H0 => //.

destruct
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R xl)
  (FT2R sl )) as 
(d & Hd & B).
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite -B2R_float_of_ftype in B. rewrite B. clear B.

rewrite B1 B2R_float_of_ftype .

move: Hd Hd1. rewrite /Relative.u_ro; simpl. move => Hd Hd1.
match goal with |- context [Rabs ?a ] =>
 field_simplify a;
 interval with (i_prec 128)
end.

pose proof 
  (@Binary.Bplus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t)) 
  BinarySingleNaN.mode_NE sh (xl + sl)%F64
   ) as Hp.
 move: Hp.
rewrite Rlt_bool_true. move =>  A.
destruct A => //. destruct H0 => //.

destruct
(Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R sh)
  (FT2R (xl + sl)%F64 )) as 
(d & Hd & B).
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite -B2R_float_of_ftype in B. rewrite B. clear B.

rewrite -is_finite_Binary in HFINxsl.
destruct (BPLUS_accurate' _ _ _ HFINxsl) as (d6 & Hd6 & B).
rewrite B. clear B. 

rewrite B1 B2R_float_of_ftype .

subst sh; rewrite /TwoSumF_sum/fst/TwoSumF.
rewrite -is_finite_Binary in HFIN.
destruct (BPLUS_accurate' _ _ _ HFIN) as (d5 & Hd5 & B).
rewrite B. clear B. 

interval with (i_prec 128). 
Qed.

Theorem DWPlusFP_zl_finite
(HFINxh: Binary.is_finite (fprec t) (femax t) (float_of_ftype xh) = true) 
(HFINxl: Binary.is_finite (fprec t) (femax t) (float_of_ftype xl) = true) 
(HFINy : Binary.is_finite (fprec t) (femax t) (float_of_ftype y) = true) 
(Hxhl : Rabs (FT2R xh + FT2R xl) < /4 * (bpow radix2 (femax t)))
(Hy :  Rabs (FT2R y)  < /4 * (bpow radix2 (femax t))) :
let zl := Fast2Sum_err sh (BPLUS xl sl) in
Binary.is_finite (fprec t) (femax t) (float_of_ftype zl) = true.
Proof.
have Hxh:  
Rabs (FT2R xh) <= / 2 * IZR (Z.pow_pos 2 1024). by  
  (apply TwoSumF_err_finite_bnd ; try nra).

set zh := Fast2Sum_sum sh (BPLUS xl sl).
have : Binary.is_finite (fprec t) (femax t) (float_of_ftype zh) = true . 
apply DWPlusFP_zh_finite => //.
rewrite /Fast2Sum_err/fst/snd => //.
rewrite /Fast2Sum_sum/fst/Fast2Sum.
move => FINzh.

have Hu :Rabs (FT2R xl) <= / 2 * IZR (Z.pow_pos 2 971)
 by apply xl_bnd => //.

have HFINxsl :
is_finite (xl + sl)%F64 = true.
rewrite -is_finite_Binary in FINzh.
apply BPLUS_finite_e in FINzh. 
destruct FINzh => //.

destruct (TwoSumF_error xh y 
  (is_finite_p_TwoSum HFINxh HFINy Hxhl Hy)) 
  as (d2s & Heq & Hd). fold sl in Heq.

have HFINsh: 
Binary.is_finite (fprec t) (femax t) sh = true.
apply TwoSumF_sum_finite => //.

have FINR : 
Binary.is_finite (fprec t) (femax t) (sh + (xl + sl) - sh)%F64 = true.
{ 
pose proof 
  (@Binary.Bminus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t)) 
  BinarySingleNaN.mode_NE (sh + (xl + sl))%F64 
  sh) as Hp.
move: Hp.
rewrite Rlt_bool_true.  move => Hp; auto.
destruct Hp => //. destruct H0. auto.

pose proof (Plus_error.FLT_plus_error_N_ex   
      Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R (sh + (xl + sl))%F64)
  (-FT2R sh) ).
destruct H as (d1 & Hd2 & B). 
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite -!B2R_float_of_ftype in B.
rewrite B. clear B.

rewrite -is_finite_Binary in FINzh.
destruct (BPLUS_accurate' _ _ _ FINzh) as (d6 & Hd6 & B).
rewrite B2R_float_of_ftype.
rewrite B. clear B. 

destruct (BPLUS_accurate' _ _ _ HFINxsl) as (d5 & Hd5 & B).
rewrite B. clear B. rewrite !B2R_float_of_ftype.

subst sh. move: HFINsh. rewrite /TwoSumF_sum/fst/TwoSumF.
  move => HFINsh.
rewrite -is_finite_Binary in HFINsh.
destruct (BPLUS_accurate' _ _ _ HFINsh) as (d4 & Hd4 & B).
rewrite B. clear B. 

rewrite Heq.

move: Hd5 Hd6 Hd2 Hd. unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.
match goal with |- Rabs ?a < _ =>
field_simplify a;
interval with (i_prec 128)
end. }  

pose proof 
  (@Binary.Bminus_correct (fprec t) (femax t)
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t)) 
  BinarySingleNaN.mode_NE (xl + sl)%F64) 
  (sh + (xl + sl) - sh)%F64 as Hp.
move: Hp.
rewrite Rlt_bool_true.  move => Hp; auto.
destruct Hp => //. 

destruct H0. auto.

pose proof (Plus_error.FLT_plus_error_N_ex   
      Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R (xl + sl)%F64)
  (-FT2R (sh + (xl + sl) - sh)%F64) ).
destruct H as (d1 & Hd1 & B). 
1,2:rewrite -B2R_float_of_ftype; try
  apply Generic_fmt.generic_format_opp; apply Binary.generic_format_B2R.
rewrite -!FT2R_ftype_of_float.
rewrite B. clear B.

rewrite -is_finite_Binary in FINR.
pose proof (@BMINUS_accurate' _ _ _ 
          (sh + (xl + sl))%F64 sh FINR).
destruct H as (d3 & Hd3 & B). 
rewrite B. clear B.

rewrite -is_finite_Binary in FINzh.
pose proof (@BPLUS_accurate' _ _ _ 
          sh (xl + sl)%F64 FINzh).
destruct H as (d4 & Hd4 & B). 
rewrite B. clear B.

pose proof (@BPLUS_accurate' _ _ _ xl sl HFINxsl).
destruct H as (d2 & Hd2 & B). 
rewrite B. clear B.

rewrite Heq.

subst sh. move: HFINsh. rewrite /TwoSumF_sum/fst/TwoSumF.
  move => HFINsh.
rewrite -is_finite_Binary in HFINsh.
destruct (BPLUS_accurate' _ _ _ HFINsh) as (d5 & Hd5 & B).
rewrite B. clear B. 

move: Hd5 Hd4 Hd2 Hd3 Hd1. unfold default_rel, Relative.u_ro. simpl.
intros. simpl in Hxh, Hy.

match goal with |-context[Rabs ?a] =>
field_simplify a;
interval with (i_prec 128)
end.
Qed.

Let zh := Fast2Sum_sum sh (BPLUS xl sl) .
Let zl := Fast2Sum_err sh (BPLUS xl sl) .

Theorem DWPlusFP_finite 
(HFINxh: Binary.is_finite (fprec t) (femax t) (float_of_ftype xh) = true) 
(HFINxl: Binary.is_finite (fprec t) (femax t) (float_of_ftype xl) = true) 
(HFINy : Binary.is_finite (fprec t) (femax t) (float_of_ftype y) = true) 
(Hxhl : Rabs (FT2R xh + FT2R xl) < /4 * (bpow radix2 (femax t)))
(Hy :  Rabs (FT2R y)  < /4 * (bpow radix2 (femax t))):
is_finite_p (DWPlusFP xh xl y).
Proof.
rewrite /is_finite_p/DWPlusFP.
replace (TwoSumF _ _) with (sh,sl) => //.
replace (Fast2Sum _ _) with (zh,zl) => //.
rewrite /fst/snd => //.
rewrite /Fast2Sum_sum/fst/Fast2Sum. split.
apply DWPlusFP_zh_finite => //.
apply DWPlusFP_zl_finite => //.
Qed.

End DWPlusFPFinite.

Section AccuracyDWPlusFP.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Variables (xh xl y : ftype t).
Let zh := (FT2R (fst (DWPlusFP xh xl y))).
Let zl := (FT2R (snd (DWPlusFP xh xl y))).
Let xr := (FT2R xh + FT2R xl).
Let yr := (FT2R y).
Let sl := snd (TwoSumF xh y).
Let v  := BPLUS xl sl.

(* start section hyps *)
Hypothesis  xE : double_word xh xl.
Hypothesis FIN : is_finite_p (DWPlusFP xh xl y). 
Hypothesis Hp3 : (3 <= fprec t)%Z.
(* end section hyps *)

Notation u   := (bpow Zaux.radix2 (- fprec t)).
Definition relative_error_DWPlusFP := Rabs (((zh + zl) - (xr  + yr)) / (xr  + yr)).
Definition errorDWFP := (FT2R xh + FT2R xl + FT2R y) - (zh + zl).
Local Notation p := (fprec t).
Definition rnd := 
  (round radix2 (SpecFloat.fexp (fprec t) (femax t)) (Generic_fmt.Znearest choice)). 

(* connect paper proofs to local defs *)
Fact rel_errorE: relative_error_DWPlusFP = Rabs errorDWFP * (Rabs (/( (FT2R xh + FT2R xl) + FT2R y))).
Proof.
rewrite /relative_error_DWPlusFP /errorDWFP /Rdiv !Rabs_mult -Ropp_minus_distr Rabs_Ropp //.
Qed.

Lemma DWPlusFP_0 : xr + yr = 0 -> zh + zl = 0.
Proof.
move => H0. 
pose proof DWPlusFP_eq xh xl y FIN.
rewrite /F2Rp in H. 
destruct (Req_dec xr 0).
{ have xh0: FT2R xh = 0.
move: xE; rewrite /double_word. 
fold xr; by rewrite H1 /rounded round_0.
(* cases on underflow *)
destruct (Rle_or_lt (bpow radix2 (@emin t + fprec t - 1)) (Rabs xr)).
{  have Hv2: 
Valid_rnd (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
  by apply BinarySingleNaN.valid_rnd_round_mode.
have Hxl: FT2R xl = 0.
move: H2 xE; subst xr; rewrite /double_word xh0; move => H2.
rewrite /rounded round_FLT_FLX Rplus_0_l => //. move => Hz. 
apply: (@eq_0_round_0_FLX radix2 (fprec t) _ 
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) Hv2) => //.
fold (@emin t); by rewrite Rplus_0_l in H2.
rewrite DWPlusFP0f in H => //; try lia. fold zl zh in H.
inversion H. move : H0; subst xr. rewrite H1; subst yr; nra.
rewrite /DWPlus.double_word; repeat split.
1,2 : rewrite -!B2R_float_of_ftype;
apply: generic_format_FLX_FLT;
  apply: Binary.generic_format_B2R.
by rewrite xh0 Hxl Rplus_0_l round_0.
rewrite -!B2R_float_of_ftype;
apply: generic_format_FLX_FLT;
  apply: Binary.generic_format_B2R. }  
have Hxl : FT2R xl = 0.
{  move: xE; subst xr; rewrite /double_word. 
rewrite /rounded round_generic. rewrite xh0 Rplus_0_l => //.
apply Plus_error.FLT_format_plus_small.
apply fprec_gt_0.
1,2 : rewrite -!B2R_float_of_ftype;
  apply: Binary.generic_format_B2R.
fold (@emin t). eapply Rle_trans. apply Rlt_le, H2.
apply bpow_le; lia. } 

rewrite DWPlusFP0f in H => //; try lia. fold zl zh in H.
inversion H. move : H0; subst xr. rewrite H1; subst yr; nra.
rewrite /DWPlus.double_word; repeat split.
1,2 : rewrite -!B2R_float_of_ftype;
apply: generic_format_FLX_FLT;
  apply: Binary.generic_format_B2R.
by rewrite xh0 Hxl Rplus_0_l round_0.
rewrite -!B2R_float_of_ftype;
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

Theorem relative_errorDWPlusFP_correct : relative_error_DWPlusFP <= 2 * u ^ 2.
Proof.
have Hf : generic_format radix2 (FLX_exp (fprec t)) (FT2R y).
{ apply (@generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t)).
  rewrite -!B2R_float_of_ftype. 
  apply (Binary.generic_format_B2R). }  
destruct (@DWPlusFP_correct (fprec t) (fprec_gt_one t) choice eq_refl 
  Hp3 (FT2R xh) (FT2R xl) (FT2R y) Hf) => // .
apply dw_word_DWdouble => //.
apply Rle_trans with (relative_errorDWFP (fprec t) choice (FT2R xh) (FT2R xl) (FT2R y)) => //.
apply Req_le.
rewrite /relative_error_DWPlusFP/relative_errorDWFP. 
pose proof DWPlusFP_eq xh  xl y FIN.
 rewrite /F2Rp/DWPlus.DWPlusFP in H1.
repeat f_equal.
all: by rewrite H1.
Qed.

Theorem relative_errorDWPlusFP_correct' : 
  exists del, (zh + zl) = (xr + yr) * (1 + del) /\
    Rabs del <= 2 * u ^ 2.
Proof.
have Hf : generic_format radix2 (FLX_exp (fprec t)) (FT2R y).
{ apply (@generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t)). 
  rewrite -!B2R_float_of_ftype. 
  apply (Binary.generic_format_B2R). }  
destruct (@DWPlusFP_correct (fprec t) (fprec_gt_one t) choice eq_refl 
  Hp3 (FT2R xh) (FT2R xl) (FT2R y) Hf) => // .
apply dw_word_DWdouble => //.
destruct (Req_dec (xr + yr) 0) as [Hx0|Hx0].
{ exists 0; rewrite Hx0; split; [field_simplify; 
  now rewrite DWPlusFP_0 | now rewrite Rabs_R0; nra]. } 
exists (((zh + zl) - (xr  + yr)) / (xr  + yr)); split. 
{ now field_simplify. } 
apply relative_errorDWPlusFP_correct.
Qed.

End AccuracyDWPlusFP.



