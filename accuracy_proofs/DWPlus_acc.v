Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common.
Require Import DWPlus DDModels Fast2Mult_acc TwoSum_acc.
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
                (bpow radix2 (@emin t + fprec t -1))).
{ have Hg: 
  generic_format radix2 (FLT_exp (@emin t) (fprec t)) (FT2R xh + FT2R xl).
  { apply Plus_error.FLT_format_plus_small.
  apply fprec_gt_0.
  1,2 : rewrite -B2R_float_of_ftype;
    apply: Binary.generic_format_B2R.
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

Fact FIN1 : is_finite_p (TwoSumF xh y).
Proof.
move : FIN.
rewrite /DWPlusFP.
replace ( TwoSumF xh y) with ( TwoSumF_sum xh y,  TwoSumF_err xh y) => //.
replace (Fast2Sum (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y))) with
  (Fast2Sum_sum (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y)), 
  Fast2Sum_err (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y))) => //.
intros.
destruct FIN0 as (FINm & _); clear FIN. 
unfold Fast2Mult_mul, Fast2Mult_err, fst, snd in *; simpl in *.
unfold Fast2Sum_sum, fst, Fast2Sum in FINm.
remember (TwoSumF_err xh y) as f1.
remember (TwoSumF_sum xh y) as f2;
split; simpl;  
rewrite is_finite_Binary;
remember (BPLUS xl f1) as f3;
rewrite !is_finite_Binary /BPLUS/BINOP !float_of_ftype_of_float
  in FINm.
destruct (float_of_ftype f2), (float_of_ftype f3), s, s0;
 auto; try contradiction. 
rewrite Heqf3 in FINm.
rewrite /BPLUS/BINOP !float_of_ftype_of_float
  in FINm.
destruct (float_of_ftype f1), (float_of_ftype f2),
   (float_of_ftype xl);
  destruct s, s0, s1; 
 auto; try contradiction. 
Qed.

Let sh := fst (TwoSumF xh y).
Let sl := snd (TwoSumF xh y).
Let v  := BPLUS xl sl.

Fact FIN2 : is_finite (BPLUS xl sl) = true.
Proof.
move: FIN. rewrite /DWPlusFP.
replace (TwoSumF xh y) with ( sh,sl) => //= H.
destruct H as (FINm & _). rewrite /fst in FINm.
remember (BPLUS xl sl) as f1.
remember sh as f2.
rewrite !is_finite_Binary /BPLUS/BINOP !float_of_ftype_of_float
  in FINm.
rewrite is_finite_Binary.
destruct (float_of_ftype f1), (float_of_ftype f2), s, s0; simpl; auto;
 try contradiction; auto. 
Qed.

Fact FIN3 : is_finite (BPLUS xh y) = true.
Proof.
move: FIN. rewrite /DWPlusFP.
replace (TwoSumF xh y) with ( sh,sl) => //=.
subst sh. rewrite /TwoSumF/fst/snd => H.
destruct H as (FINa & _). unfold fst in FINa. 
remember (BPLUS xh y) as f1.
remember (BPLUS xl sl) as f2.
rewrite !is_finite_Binary /BPLUS/BINOP !float_of_ftype_of_float
  in FINa.
rewrite is_finite_Binary.
destruct (float_of_ftype f1), (float_of_ftype f2), s, s0; simpl; auto;
 try contradiction; auto. 
Qed.

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

Let rnd_p {t} := 
round radix2 (FLX_exp (fprec t)) (Znearest choice).


(* the necessary ordering for Fast2Sum holds *)
Lemma Fast2Sum_CorrectDWPlusFP (xh y xl: ftype t)   (Hbn :  (3 <= fprec t)%Z): 
  is_finite (BPLUS xl (snd (TwoSumF xh y))) = true -> 
  is_finite_p (TwoSumF xh y) -> 
  FT2R xh + FT2R y <> 0 -> 
  double_word xh xl->
  Rabs (FT2R (BPLUS xl (snd (TwoSumF xh y)))) <= Rabs (FT2R (fst (TwoSumF xh y))).
Proof.
intros FIN1 FIN2 S0 DWx.

have Hv: Valid_exp fexp by apply FLT.FLT_exp_valid.
have Hexp: Exp_not_FTZ fexp by apply  fexp_not_FTZ.
have Hv2: 
Valid_rnd (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
  by apply BinarySingleNaN.valid_rnd_round_mode.
have Ha: generic_format radix2 fexp (FT2R xh) by
  rewrite -!B2R_float_of_ftype; apply Binary.generic_format_B2R. 
have Hb: generic_format radix2 fexp (FT2R y) by 
  rewrite -!B2R_float_of_ftype; apply Binary.generic_format_B2R. 
have Hc: generic_format radix2 fexp (FT2R xl) by 
  rewrite -!B2R_float_of_ftype; apply Binary.generic_format_B2R. 
have Hrnd: rounded t (FT2R xh + FT2R y) <> 0.
rewrite /rounded; apply Plus_error.round_plus_neq_0 => //.


case:(Req_dec (FT2R xh) 0)=> hxh0.
{ pose proof TwoSum0 xh y FIN2 hxh0 as H.
  BPLUS_correct t xl (snd (TwoSumF xh y)); clear H5.
  inversion H. rewrite /fst/snd/TwoSumF B2R_float_of_ftype;
  rewrite H1 H2 Rplus_0_r.
  have H0 : FT2R xl = 0.
  { move: DWx. rewrite /double_word hxh0 => DWx.
    rewrite -(Rplus_0_l (FT2R xl)). 
    symmetry in DWx; rewrite /rounded in DWx.
    apply: (Plus_error.round_plus_eq_0
        radix2 (SpecFloat.fexp (fprec t) (femax t))
        (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) );
    try apply:generic_format_0;
    try rewrite -!B2R_float_of_ftype;
    try apply Binary.generic_format_B2R;
    try rewrite -!B2R_float_of_ftype in DWx;
    try apply DWx. }
  rewrite H0 round_0 Rabs_R0. apply: Rabs_pos. }

(* facts *)
have FIN3: is_finite (BPLUS xh y) = true.
destruct FIN2. simpl in H => //.
have Hp0 : Prec_gt_0 (fprec t) by apply fprec_gt_0.
have Hvd : Valid_exp fexp by apply FLT_exp_valid.
have Hrn : Valid_rnd (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) by
  apply BinarySingleNaN.valid_rnd_round_mode.
have Hxhy : generic_format radix2 fexp
  (round radix2 fexp (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) 
      (FT2R xh + FT2R y)) by apply generic_format_round.
have Hxhy2 : generic_format radix2 fexp (FT2R (snd (TwoSumF xh y))) by
  rewrite -!B2R_float_of_ftype; apply Binary.generic_format_B2R.
have hf : (1 < fprec t)%Z by pose proof @fprec_lb t; lia.
(* end facts *)

(* cases on underflow, (xh + y) *)
(* case 1 *)
destruct (Rlt_or_le 
  (Rabs (FT2R xh + FT2R y))
  (bpow radix2 (@emin t + fprec t - 1))).
{ 
refine (Rle_trans _ _ _ _ _ ).
2: rewrite /fst/TwoSumF; BPLUS_correct t xh y.
2: apply roundN_plus_ulp_FLT => //.

set (g:= snd (TwoSumF xh y)) in *.
BPLUS_correct t xl g; subst g; clear H4.
fold (TwoSumF_err xh y) (TwoSumF_sum xh y) (@FT2R t).
rewrite TwoSumF_correct /TwoSumF_sum/fst/TwoSumF.
rewrite BPLUS_UF_exact => //=.

have xle:= (dw_ulp xh xl DWx).
rewrite !B2R_float_of_ftype.
rewrite round_generic. field_simplify_Rabs.
unfold Rmax.
fold ulp in xle.
destruct (Rle_dec (ulp (FT2R xh) /2) (ulp (FT2R y) / 2)).
refine (Rle_trans _ _ _ xle _ ) .
refine (Rle_trans _ (ulp (FT2R xh) / 2) _ _ _ ) => //.
apply Req_le; field_simplify => //.
refine (Rle_trans _ (/ 2 * ulp (FT2R xh)) _ _ _ ) => //.
apply Req_le; field_simplify => //.
match goal with |- context[generic_format _ _ ?a] => 
field_simplify a
end. 
rewrite -!B2R_float_of_ftype; apply Binary.generic_format_B2R.
simpl in FIN2 => //.
}

(* cases on underflow (xh + xl) *)
destruct (Rlt_or_le 
  (Rabs (FT2R xh + FT2R xl))
  (bpow radix2 (@emin t + fprec t - 1))).
(* case 1 *)
{ have hxl : FT2R xl = 0.
move : DWx. rewrite /double_word. 
rewrite /rounded round_generic. 
move => DWx; nra.
apply Plus_error.FLT_format_plus_small => //.
refine (Rle_trans _ _ _ (Rlt_le _ _ H0) _).
apply bpow_le. fold (@emin t); lia.
BPLUS_correct t xl (snd (TwoSumF xh y)).
rewrite B2R_float_of_ftype; rewrite hxl Rplus_0_l round_generic => //.
fold (TwoSumF_err xh y) (TwoSumF_sum xh y). 
  rewrite TwoSumF_correct /TwoSumF_sum/fst/TwoSumF => //.
rewrite Rabs_minus_sym.
BPLUS_correct t xh y.
 rewrite !B2R_float_of_ftype.  
refine (Rle_trans _ _ _ (error_le_ulp_round _ _ _ _ ) _).
refine (Rle_trans _ _ _ _ _) .
2: apply (ulp_le_abs radix2 fexp) => //.
nra. } 

(* cases on underflow, xl + 2sum_err xh y *)
(* case 1 *)
destruct (Rlt_or_le 
  (Rabs (FT2R xl + FT2R (snd (TwoSumF xh y))))
  (bpow radix2 (@emin t + fprec t - 1))).
{ BPLUS_correct t xl (snd (TwoSumF xh y)).
replace (fst (TwoSumF xh y)) with
  (BPLUS xh y ) => //. 
   rewrite !B2R_float_of_ftype.
BPLUS_correct t xh y.
rewrite -!round_NE_abs. apply round_le => //.
rewrite !B2R_float_of_ftype;  
eapply Rle_trans. apply Rlt_le, H1. assumption.  } 

have DWx2 : DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl).
{ move : DWx. rewrite /double_word/DWPlus.double_word.
rewrite /rounded round_FLT_FLX. move => DWx; repeat split => //;
  try apply (generic_format_FLX_FLT radix2 (@emin t)) => //.
  fold (@emin t); nra. } 

set (g:= (snd (TwoSumF xh y))) in *.
BPLUS_correct t xl g.
subst g.

pose proof @TwoSumEq_FLT NANS t _ _ _ FIN2 as H2;
unfold F2Rp in H2.

rewrite !B2R_float_of_ftype.
move : H1.
replace (FT2R (snd (TwoSumF xh y)))
  with (TwoSum_err (fprec t) choice (FT2R xh) (FT2R y)) by
  inversion H2 => //.
move => H1.
replace (FT2R (fst (TwoSumF xh y)))
  with (TwoSum_sum (fprec t) choice (FT2R xh) (FT2R y)) by
inversion H2 => //.

clear H5 H6 H7.

rewrite /rounded !round_FLT_FLX => //.

clear H2 DWx H H0 H1 FIN1 FIN2 FIN3 Hxhy Hxhy2.

wlog xhy : y xh S0 Ha Hb Hc Hrnd hxh0 DWx2
  /  Rabs (FT2R y) <= Rabs (FT2R xh).
  move=> Hwlog.
  case:(Rle_lt_dec (Rabs (FT2R y)) (Rabs (FT2R xh)))=> absyxh.
    by apply: ( Hwlog y xh)=>//.

(* we can use Hwlog as long as (xl + xh) and (xl + y) are DWs *) 

  have yn0: FT2R y <> 0.
    by move=>y0; move:  absyxh; rewrite y0 Rabs_R0; move:(Rabs_pos (FT2R xh)); lra. 

have xle:= (@DWPlus.dw_ulp _ hf choice (FT2R xh) (FT2R xl) DWx2).

have xluy: Ulp.ulp radix2 (FLX_exp (fprec t)) (FT2R xh) <=
              Ulp.ulp radix2 (FLX_exp (fprec t)) (FT2R y).
    apply ulp_le => //; try nra. 
    apply FLX_exp_valid.
    apply fprec_gt_0.
    apply FLX_exp_monotone.

(* facts *)
have HFy : 
generic_format radix2 (FLX_exp (fprec t)) (FT2R y) by
 apply: (generic_format_FLX_FLT _ (@emin t) _) => //. 
have HFxl : 
generic_format radix2 (FLX_exp (fprec t)) (FT2R xl) by
 apply: (generic_format_FLX_FLT _ (@emin t) _) => //. 
have HFxh : 
generic_format radix2 (FLX_exp (fprec t)) (FT2R xh) by
 apply: (generic_format_FLX_FLT _ (@emin t) _) => //. 
have Hch: choice = (fun n : Z => negb (Z.even n)).
apply functional_extensionality; rewrite /choice //=.
(* end facts *)

case:  xluy=> xluy.
    have yE: FT2R y = @rnd_p t (FT2R y + FT2R xl). rewrite /rnd_p. 
    symmetry.  
    apply: (@rulp2p' (fprec t) hf choice Hch (FT2R xh) (FT2R y) (FT2R xl)) => //.


move : DWx2. rewrite /DWPlus.double_word. 
  repeat move => []. move =>  A B DWx2.

case:  (Hwlog xh y)=>//; try lra. 
rewrite Rplus_comm => //.
rewrite /DWPlus.double_word; repeat split => //.

1,2,3: rewrite TwoSum_errC /TwoSum_sum/fst/TwoSum => //;
  replace (FT2R y + FT2R xh) with (FT2R xh + FT2R y) by nra; try nra.

case:(Rle_lt_or_eq_dec  _  _  xle)=> xel'.

have HB: ~ Bayleyaux.is_pow radix2 (FT2R y).
    move => [ey yE].
 move:  (absyxh)  (xluy).
    have-> :  Ulp.ulp radix2 (FLX_exp (fprec t)) (FT2R y) = 
            bpow radix2 (ey + 1 - fprec t) => //.
      move: yE; rewrite -(Rabs_pos_eq (bpow radix2 ey)); last by apply: bpow_ge_0.
      case/Rabs_eq_Rabs => // H. 
      rewrite H  ulp_bpow /FLX_exp //=.
      rewrite H ulp_opp  ulp_bpow /FLX_exp //=.
    rewrite yE ulp_neq_0 // /cexp /FLX_exp.
    move=> h1. move /bpow_inj => h2.
    have {} h2:  ((ey + 1 ) = mag radix2 (FT2R xh) )%Z by lia.
    have : bpow radix2 ey <= Rabs (FT2R xh).
      have ->: (ey = (mag radix2 (FT2R xh) - 1))%Z by lia.
      apply:(bpow_mag_le radix2 (FT2R xh)); lra.
    lra.

case:  (Hwlog xh y)=>//; try lra => //. 
rewrite Rplus_comm => //.
rewrite /DWPlus.double_word; repeat split => //.
symmetry.
apply rulp2p => //; last lra. 

1,2,3: rewrite TwoSum_errC /TwoSum_sum/fst/TwoSum => //;
  replace (FT2R y + FT2R xh) with (FT2R xh + FT2R y) by nra; try nra.

{  fold (@FT2R t).
apply (part_case_ulps
  (fprec_gt_one t) Hch Hbn DWx2 HFy) => //.
rewrite xel'; nra. } 

wlog xhpos: xl xh y S0 Ha Hb Hc Hrnd hxh0 DWx2 xhy / 0 <  FT2R xh.
  move=> Hwlog.
  case:(Rlt_le_dec 0 (FT2R xh)) => xhpos.
   by  apply: Hwlog. 
  case:xhpos=>xh0; first last.
    move:xhy; rewrite {1}xh0 Rabs_R0.
    move:(Rabs_pos (FT2R y)) => H1 H2.
    have : Rabs (FT2R y ) = 0 by lra.
    by move:(Rabs_no_R0 (FT2R y)) => *; lra.

    case:(Hwlog (BOPP xl) (BOPP xh)  (BOPP y)); 
  try apply:generic_format_opp =>//; try lra.
    { rewrite -!B2R_float_of_ftype/BOPP !float_of_ftype_of_float
      !Binary.B2R_Bopp -Ropp_plus_distr. 
      rewrite !B2R_float_of_ftype. nra. } 
    1,2,3: try (rewrite -!B2R_float_of_ftype/BOPP !float_of_ftype_of_float !Binary.B2R_Bopp; 
          apply generic_format_opp, Binary.generic_format_B2R => //). 
    { rewrite -!B2R_float_of_ftype/BOPP !float_of_ftype_of_float
 !Binary.B2R_Bopp -Ropp_plus_distr /rounded round_NE_opp. 
      move: Hrnd. rewrite /rounded 
        -!B2R_float_of_ftype => //=; nra. } 
    { rewrite -!B2R_float_of_ftype/BOPP !float_of_ftype_of_float
      !Binary.B2R_Bopp.  rewrite !B2R_float_of_ftype. nra. }
rewrite -!B2R_float_of_ftype/BOPP !float_of_ftype_of_float !Binary.B2R_Bopp.
apply DW_sym => //. 
by rewrite !B2R_float_of_ftype.
rewrite -!B2R_float_of_ftype/BOPP !float_of_ftype_of_float 
    !Binary.B2R_Bopp !Rabs_Ropp !B2R_float_of_ftype  => //.
rewrite -!B2R_float_of_ftype/BOPP float_of_ftype_of_float
   Binary.B2R_Bopp B2R_float_of_ftype. nra. 

1,2 : rewrite -!B2R_float_of_ftype/BOPP !float_of_ftype_of_float  !Binary.B2R_Bopp vAsym /choice 
  /TwoSum_sum //= -Ropp_plus_distr round_NE_opp !Rabs_Ropp; nra.

(* facts *)
have HFy : 
generic_format radix2 (FLX_exp (fprec t)) (FT2R y) by
 apply: (generic_format_FLX_FLT _ (@emin t) _) => //. 
have HFxl : 
generic_format radix2 (FLX_exp (fprec t)) (FT2R xl) by
 apply: (generic_format_FLX_FLT _ (@emin t) _) => //. 
have HFxh : 
generic_format radix2 (FLX_exp (fprec t)) (FT2R xh) by
 apply: (generic_format_FLX_FLT _ (@emin t) _) => //. 
have Hch: choice = (fun n : Z => negb (Z.even n)).
apply functional_extensionality; rewrite /choice //=.
(* end facts *)

case: (scale_generic_12 HFxh xhpos)=> exh Hxhs.
  have powgt0 := (bpow_gt_0 radix2 exh).

have : forall xlr xhr yr,
   xhr + yr <> 0 -> 
1 <=  xhr <= 2 - 2 * u -> 
DWPlus.double_word (fprec t) choice xhr xlr ->
Rabs yr <= Rabs xhr -> 
generic_format radix2 (FLX_exp (fprec t)) yr -> 
Rabs
  (round radix2 (FLX_exp (fprec t)) (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
      (xlr + TwoSum_err (fprec t) choice xhr yr)) <=
Rabs (TwoSum_sum (fprec t) choice xhr yr).
move => xlr xhr yr S1 [] xh1 xh2 DWx xhyr Fyr. 

(* c'est là que ça commence vraiment...*) 
have hpxh: bpow radix2 (1-1) <= Rabs xhr < bpow radix2 1.
   rewrite Rabs_pos_eq //; move:xh2; rewrite /u /=; last lra.
    rewrite IZR_Zpower_pos /=; move:(bpow_gt_0 radix2 (-fprec t)); 
    rewrite /u /= IZR_Zpower_pos /=;  try lra.
have xlu: Rabs xlr <= u.
  move:(DD.paper_proofs.DWPlus.dw_ulp (fprec_gt_one t) DWx).
  rewrite (Bayleyaux.u_ulp1 (fprec t)).
  rewrite !ulp_neq_0; try lra; rewrite /cexp /fexp.
  rewrite (mag_unique_pos radix2 xhr 1); try lra; rewrite /=.
    rewrite (mag_unique_pos radix2 1 1) /= ?IZR_Zpower_pos /=;lra.
  split=>//.
  rewrite /u /= in xh2.
   move:(bpow_gt_0 radix2 (-fprec t)); rewrite  IZR_Zpower_pos /=; lra.
have lnbxh:=(mag_unique radix2 xhr 1%Z  hpxh ).
rewrite (Rabs_pos_eq  xhr) in xhyr; try lra.
move/Rabs_le_inv: xhyr=>[hd hu].
case:(DWx)=> [[Fxh Fxl] xE].
case: (Rle_lt_dec yr (-xhr/2) )=> hyr.
  have sl0: TwoSum_err (fprec t) choice xhr yr = 0.
  rewrite DWPlus.TwoSum_correct //=. rewrite TwoSum_sumE  round_generic; first  ring.
  have->: xhr+yr = xhr - (-yr) by ring.
  apply: Bayleyaux.sterbenz'=>//. 
     by apply:generic_format_opp.
  by lra. 
  rewrite sl0 Rplus_0_r round_generic //.
refine (Rle_trans _ _ _ (DWPlus.dw_ulp _ DWx) _) => //. 
rewrite /TwoSum_sum/TwoSum/=.
refine (Rle_trans _ _ _ _ (roundN_plus_ulp _ _ _ _ _) ) => //.
refine (Rle_trans _ _ _ (Rmax_l _ 
  (Ulp.ulp radix2 (FLX_exp (fprec t)) yr / 2)) _).
apply Rcomplements.Rmax_le_compat; try nra. 

(* case 2 *)
have hled: 1/2 <= xhr/2 by lra.
have hltle: xhr/2 < xhr + yr <= 2* xhr by lra.
have shge: /2 <= TwoSum_sum (fprec t) choice xhr yr.
  have ->: /2 = @rnd_p t (/2).
    rewrite /rnd_p round_generic //.
    have -> : /2 = bpow radix2 (-1) by [].
    apply: generic_format_bpow'.
    rewrite /FLX_exp; lia.
  by apply: round_le; lra.
have shle3: Rabs (xlr + TwoSum_err (fprec t) choice xhr yr) <= 3*u.
  apply:(Rle_trans _ (Rabs xlr + Rabs (TwoSum_err (fprec t) choice xhr yr))).
    by apply: Rabs_triang .
  suff:  Rabs (TwoSum_err (fprec t) choice xhr yr)<= 2 * u by lra.
  case:(Rle_lt_dec (xhr + yr) 2)=> sh2.
    suff:  Rabs (TwoSum_err (fprec t) choice xhr yr) <= u .
        rewrite /u; move : (bpow_gt_0 radix2 (- fprec t)) => //=; try lra.
    rewrite  DWPlus.TwoSum_correct //=  /u.
    have ->:  (xhr + yr - @rnd_p t (xhr + yr)) =
         - (@rnd_p t (xhr + yr) - (xhr + yr)) by ring.
    rewrite Rabs_Ropp.
    have: bpow radix2 (- fprec t) =  
        / 2 * bpow radix2 (- fprec t) * bpow radix2 1. 
        rewrite /= IZR_Zpower_pos /= ; lra. 
  move => Hu. 
  refine (Rle_trans _ _ _ (Bayleyaux.error_le_half_ulp' _ _ _ 1 _ ) _ ) => //.
    rewrite /= Rabs_pos_eq ?IZR_Zpower_pos /=; lra.
    simpl; nra. 
  rewrite   DWPlus.TwoSum_correct //  /u /=.
  have ->:  (xhr + yr - @rnd_p t (xhr + yr)) = - (@rnd_p t (xhr + yr) - (xhr + yr)) by ring.
  rewrite Rabs_Ropp.
  have ->: 2 * bpow radix2 (- fprec t) =  /2 * bpow radix2 (- fprec t) * 
          bpow radix2 2 by rewrite /= IZR_Zpower_pos /= ; lra.
  apply: Bayleyaux.error_le_half_ulp' => //.
  rewrite /= Rabs_pos_eq; try lra.
    apply: (Rle_trans _ (4 - 4 * u)); try lra.
    rewrite /u IZR_Zpower_pos /=; move:(bpow_gt_0 radix2 (-fprec t)). 
    have : 0 < IZR (Z.pow_pos 2 (fprecp t)) by (apply IZR_lt, Zpower_pos_gt_0 => //).
    simpl; intros; field_simplify; try lra. apply Rdiv_le_left => //.
    have : IZR (Z.pow_pos 2 (fprecp t)) -1 <= IZR (Z.pow_pos 2 (fprecp t)); lra.

refine (Rle_trans _ (3*u)  _ _ _ ).
   apply: abs_round_le_generic=>//.
(*  format (3 * u). *)
  rewrite /u.
  pose fx := Float radix2 3 (-fprec t).
  have xfx: (3 * bpow radix2 (- fprec t)) =  F2R fx by [] => //=.
    
  apply: (FLX_format_Rabs_Fnum (fprec t) xfx ).
  rewrite Rabs_pos_eq; try lra.
  apply: (Rlt_le_trans _ (bpow radix2 2)).
    have ->: bpow radix2 2 = 4 by []. simpl.
      by lra.
    apply:bpow_le. lia. simpl. lra.

  apply:(Rle_trans _ (/2) )=>//.
  rewrite /u => //=.
    apply:(Rmult_le_reg_r 
          (bpow radix2 (fprec t))); first by exact:bpow_gt_0 => //=.
    replace (/ IZR (Z.pow_pos 2 (fprecp t))) with (bpow radix2 (-fprec t))
      by (simpl; lra).
    rewrite Rmult_assoc -bpow_plus Zplus_opp_l /= Rmult_1_r.
    apply:(Rle_trans _ (bpow radix2 2)).
      by change (3 <= 4); lra. 
    change( bpow radix2 2 <= bpow radix2 (-1) * bpow radix2 (fprec t)); 

          rewrite -bpow_plus;  apply: bpow_le. lia.
  rewrite  Rabs_pos_eq ; lra.

intros. specialize (H (FT2R xl * bpow radix2 exh)
      (FT2R xh * bpow radix2 exh) (FT2R y * bpow radix2 exh)) => //.

rewrite vS /TwoSum_sum/TwoSum //=  in H => //.
pose proof (@TwoSumS (fprec t) choice (FT2R xh) (FT2R y)
    exh HFxh HFy).
inversion H0. clear H3. rewrite H2 in H.
suff :     Rabs
      (round radix2 (FLX_exp (fprec t)) ZnearestE
         (FT2R xl + TwoSum_err (fprec t) (fun x : Z => negb (Z.even x)) (FT2R xh) (FT2R y)) * 
       bpow radix2 exh) <=
    Rabs (round radix2 (FLX_exp (fprec t)) (Znearest choice) (FT2R xh + FT2R y) * bpow radix2 exh).
rewrite Rabs_mult; rewrite Rabs_mult.
apply Rmult_le_reg_r. apply Rabs_pos_lt. apply not_eq_sym,  Rlt_not_eq => //.
apply H => //.

rewrite -Rmult_plus_distr_r.
apply Rmult_integral_contrapositive_currified => //.
apply Stdlib.Rlt_neq_sym. apply bpow_gt_0.

apply DW_S => //; try lia.
rewrite !Rabs_mult. 
apply Rmult_le_compat_r => //.
apply Rabs_pos.

apply formatS => //.
Qed.

Let emin :=  (@DDModels.emin t).


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
{ BPLUS_correct t xl (snd (TwoSumF xh y)).
rewrite (round_FLT_FLX radix2 (@DDModels.emin t)) => //.
by rewrite !B2R_float_of_ftype. } 
apply Fast2Sum_CorrectDWPlusFP => //. }

rewrite -FastTwoSumEq_FLT => //. f_equal.
rewrite BPLUS_UF_exact => //.
rewrite round_generic => //; f_equal.
apply: (generic_format_FLX_FLT _ emin).
apply: Plus_error.FLT_format_plus_small.
1,2 : rewrite -!B2R_float_of_ftype;
  apply: Binary.generic_format_B2R.
 
refine (Rle_trans _ _ _ (Rlt_le _ _ _) _ ). apply HUF.
apply bpow_le; lia.

apply Fast2Sum_CorrectDWPlusFP => //.
Qed.

End CorrectDWPlusFP'.


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
pose proof DWPlusFP_eq xh xl y xE FIN Hp3.
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
pose proof DWPlusFP_eq xh  xl y xE FIN.
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

Section FiniteDWPlusFP.

Context {NANS: Nans} {t : type} {STD: is_standard t}.
Variables (xh xl y : ftype Tdouble).

(* start section hyps *)
Hypothesis  xE : double_word xh xl.

Definition ov := Raux.bpow Zaux.radix2 (femax Tdouble).

Theorem is_finite_DWPlusFP_ex  
  (Hxy : is_finite (xh + xl + y)%F64 = true) 
  (Hxh : is_finite (xh)%F64 = true)
  (Hxl : is_finite (xl)%F64 = true)
  (Hy  : is_finite (y)%F64 = true):
  is_finite_p (DWPlusFP xh xl y).
Proof.
rewrite /DWPlusFP/is_finite_p. 
replace (TwoSumF xh y) with
  (TwoSumF_sum xh y, TwoSumF_err xh y) => //.
remember (xl + TwoSumF_err xh y)%F64 as f1.
replace (Fast2Sum (TwoSumF_sum xh y) f1) with
  (Fast2Sum_sum (TwoSumF_sum xh y) f1, 
      Fast2Sum_err (TwoSumF_sum xh y) f1) => //;
rewrite /fst/snd.
rewrite /Fast2Sum_sum/fst/Fast2Sum.
rewrite /TwoSumF_sum/fst/TwoSumF.
unfold double_word in xE.
have FIN1: (is_finite (xh + y)%F64 = true).
{  destruct xh, y, xl, s, s0, s1; simpl; auto; 
  try discriminate. 
Admitted. 

End FiniteDWPlusFP.

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
if Rlt_bool (Rabs (F2R (Operations.Fplus (FT2F xhi) (FT2F xlo)))) dd_ov then
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
all: by apply Rcompare_Eq. 
Defined.

Definition DD_compare_correct x y a b :
      DD2F x = Some a ->
      DD2F y = Some b ->
      DD_compare x y = Some (Rcompare (F2R a) (F2R b)).
rewrite /DD2F/DD_compare. 
remember (Rlt_bool _ dd_ov) as fb.
destruct fb => //=. 
move => H1.
match goal with |-context[Rlt_bool ?a ?b] => 
  remember (Rlt_bool a b) as fb0  end.
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

(** TODO *)
Definition DD_bounds x :
(-(bpow radix2 (femax Tdouble) - 
      bpow radix2 ((femax Tdouble) - Z.pos 106%positive)) <=
match DD2F x with Some f => F2R f | None => R0 end <=
bpow radix2 (femax Tdouble) - 
    bpow radix2 ((femax Tdouble) - Z.pos 106%positive)).
rewrite /DD2F. remember (is_finite (fst x)) as b.
destruct b => //=; try nra. apply Stdlib.Rabs_def2_le.
pose proof Binary.bounded_le_emax_minus_prec.
destruct x,f,f0 => //=; simpl in Heqb; try discriminate.
Admitted.

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

Notation ulp :=  (Ulp.ulp Zaux.radix2 
  (SpecFloat.fexp (fprec Tdouble) (femax Tdouble))).

Lemma Rlt_compat2 a b c d:
 0 < a -> 0 < b -> 0< c -> a <= b -> c < d -> a * c < b * d.
Proof.  intros. nra. Qed. 


Definition dd_pred (a: dd_rep) : Prop := 
  (0 <>  (FT2R (fst a)) ->  
  bpow radix2 (@emin Tdouble + fprec Tdouble - 1) <= 
          Rabs (FT2R (fst a)))
  /\
  (0 <> (FT2R (fst a) + FT2R (snd a)) ->  
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
rewrite /dd_pred/double_word; move =>  [] H1 [] H2 H3.
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
 apply Rmult_le_pos; try lra.
 apply ulp_ge_0.
 apply (exist _ _ H). 
Defined.

Definition dd_ov :=
(bpow radix2 (femax Tdouble) - 
      bpow radix2 ((femax Tdouble) - Z.pos 106%positive)).

Definition DD2F' (x : dd_rep1) 
  : option (float radix2):= let s:= (proj1_sig x) in
let xhi := fst s in let xlo := snd s in
if Rlt_bool (Rabs (F2R (Operations.Fplus (FT2F xhi) (FT2F xlo)))) dd_ov
  && 
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
Qed.


Definition double_double' : type. 
pose (NONSTD 106 (femax Tdouble) fprec_le_femax_DD nstd_prf2
  dd_rep1 DD_zero' DD2F' DD_compare' 
  DD_is_finite_compare' DD_compare_correct' 
  DD_nonstd_nonempty_finite' DD_bounds').
pose (GTYPE 106 (femax Tdouble) fprec_le_femax_DD nstd_prf2
  (Some n)).
assumption.
Defined.

Definition f_lb : ftype Tdouble :=
 ftype_of_float (Binary.B754_infinity _ _ true).

Definition f_ub : ftype Tdouble :=
 ftype_of_float (Binary.B754_infinity _ _ false).

Definition finite_bnds := 
    ((f_lb, true), (f_ub, true)).

Require Import Interval.Tactic.

Definition dd_lb : ftype double_double'.
rewrite /ftype/double_double' => //=.
rewrite /dd_rep1.
set y := (Zconst Tdouble (-Z.pow 2 (femax Tdouble -1))).
have Hy : FT2R y = IZR (- 2 ^ (femax Tdouble - 1)).
{ subst y . rewrite /Zconst. 
destruct (@IEEE754_extra.BofZ_representable
(fprec Tdouble)
  (femax Tdouble) (Pos2Z.is_pos (fprecp Tdouble)) (fprec_lt_femax Tdouble)
(- 2 ^ (femax Tdouble - 1))) as ( A & _).
apply IEEE754_extra.integer_representable_opp.
apply (@IEEE754_extra.integer_representable_2p (fprec Tdouble)
  (femax Tdouble) (fprec_gt_0 Tdouble) (fprec_lt_femax Tdouble) 
( (femax Tdouble - 1))); split; simpl; lia.
rewrite FT2R_ftype_of_float A Ropp_Ropp_IZR; simpl;
  nra. } 
pose y' := (/ 2 * ulp (FT2R y)).
unfold ulp in y'. 
remember (Req_bool (FT2R y) 0) as y0.
destruct y0. 
{ subst y. 
rewrite -B2R_float_of_ftype in Heqy0.
rewrite Req_bool_false in Heqy0 => //=.
apply F2R_neq_0 => //=. } 
set y1 := Zconst Tdouble (Z.pow 2 (-971)). 
have Hy1 : FT2R y1 = IZR (2 ^ (-971)).
{ subst y1 . rewrite /Zconst. 
destruct (@IEEE754_extra.BofZ_representable
(fprec Tdouble)
  (femax Tdouble) (Pos2Z.is_pos (fprecp Tdouble)) (fprec_lt_femax Tdouble)
(2 ^ (-971))) as ( A & _).
apply (@IEEE754_extra.integer_representable_n (fprec Tdouble)
  (femax Tdouble) (fprec_gt_0 Tdouble) (fprec_lt_femax Tdouble) 
( 2 ^ -971)); split; simpl; try lia.
rewrite FT2R_ftype_of_float A ; simpl;
  nra. } 
set Y:= (y,y1); assert (dd_pred Y).
rewrite /Y/dd_pred/fst/snd; repeat split; intros.
rewrite Hy;
rewrite Ropp_Ropp_IZR Rabs_Ropp Rabs_pos_eq; simpl; nra.
rewrite Hy Hy1. interval.
rewrite Hy1 Hy. rewrite Rabs_R0. apply Rmult_le_pos ; [nra|].
apply Ulp.ulp_ge_0.
 apply (exist _ _ H). 

(* set P := (fun (a: dd_rep) => Rabs (FT2R (snd a)) <= / 2 * ulp (FT2R (fst a))).
set y := (Zconst Tdouble (-Z.pow 2 (femax Tdouble -1))).
pose y' := (/ 2 * ulp (FT2R y)).
unfold ulp in y'. 
remember (Req_bool (FT2R y) 0) as y0.
destruct y0. *)
(* { subst y. 
rewrite -B2R_float_of_ftype in Heqy0.
rewrite Req_bool_false in Heqy0 => //=.
apply F2R_neq_0 => //=. } 
set y1 := Zconst Tdouble (Z.pow 2 (-971)). 
set Y:= (y,y1); assert (P Y); rewrite /Y/P/FT2R/Ulp.ulp => //=.
rewrite Req_bool_false; [|apply F2R_neq_0 => //=  ].
clear y'.
set y':= FT2R y. unfold FT2R in y'. simpl in y'.
fold y'. rewrite (cexp_fexp radix2
  (SpecFloat.fexp (fprec Tdouble) (femax Tdouble)) y' 1024) => //=;
try interval.
subst y'; rewrite /F2R => //=; split; try interval.
rewrite Rabs_mult.
try interval with (i_prec 128). 
 apply (exist _ _ H).  *)
(* Defined. *) 
Qed.


(* simpl in y'.
rewrite -B2R_float_of_ftype in y'.
rewrite (cexp_fexp radix2
  (SpecFloat.fexp (fprec Tdouble) (femax Tdouble)) (FT2R y) 11)  in y'.
simpl in y'. *)

Definition dd_ub : ftype double_double'.
rewrite /ftype/double_double' => //=.
rewrite /dd_rep1.
set y := (Zconst Tdouble (Z.pow 2 (femax Tdouble - 1))).
have Hy : FT2R y = IZR (2 ^ (femax Tdouble - 1)).
{ subst y . rewrite /Zconst. 
destruct (@IEEE754_extra.BofZ_representable
(fprec Tdouble)
  (femax Tdouble) (Pos2Z.is_pos (fprecp Tdouble)) (fprec_lt_femax Tdouble)
( 2 ^ (femax Tdouble - 1))) as ( A & _).
apply (@IEEE754_extra.integer_representable_2p (fprec Tdouble)
  (femax Tdouble) (fprec_gt_0 Tdouble) (fprec_lt_femax Tdouble) 
( (femax Tdouble - 1))); split; simpl; lia.
rewrite FT2R_ftype_of_float A; simpl;
  nra. } 
pose y' := (/ 4 * ulp (FT2R y)).
unfold ulp in y'. 
remember (Req_bool (FT2R y) 0) as y0.
destruct y0.
{ subst y. 
rewrite -B2R_float_of_ftype in Heqy0.
rewrite Req_bool_false in Heqy0 => //=.
apply F2R_neq_0 => //=. } 
set y1 := Zconst Tdouble (Z.pow 2 (969)). 
have Hy1 : FT2R y1 = IZR (2 ^ (969)).
{ subst y1 . rewrite /Zconst. 
destruct (@IEEE754_extra.BofZ_representable
(fprec Tdouble)
  (femax Tdouble) (Pos2Z.is_pos (fprecp Tdouble)) (fprec_lt_femax Tdouble)
(2 ^ (969))) as ( A & _).
apply (@IEEE754_extra.integer_representable_2p (fprec Tdouble)
  (femax Tdouble) (fprec_gt_0 Tdouble) (fprec_lt_femax Tdouble) 
( 969)); split; simpl; try lia.
rewrite FT2R_ftype_of_float A ; simpl;
  nra. } 
set Y:= (y,y1); assert (dd_pred Y).
rewrite /Y/dd_pred/fst/snd; repeat split; intros.
rewrite Hy;
rewrite  Rabs_pos_eq; simpl; nra.
rewrite Hy Hy1. interval.
rewrite Hy1 Hy. simpl.
simpl in y'.
rewrite /Ulp.ulp Req_bool_false.
simpl in Hy. rewrite -Hy.
pose proof (cexp_fexp radix2
  (SpecFloat.fexp (fprec Tdouble) (femax Tdouble)) (FT2R y) 1024).
rewrite H. rewrite Rabs_pos_eq. simpl. try interval with (i_prec 128). 
try interval with (i_prec 128).
rewrite Hy Rabs_pos_eq; [split; simpl | nra];
try interval with (i_prec 128). nra. 
 apply (exist _ _ H). 
Qed.

Definition finite_bnds2 := 
    ((dd_lb, true), (dd_ub, true)).

Definition DWplusFP_bnds' : klist bounds [double_double'; Tdouble]:=
   Kcons (finite_bnds2) (Kcons (finite_bnds) Knil).

Definition DWPlusFP' {NANS: Nans}
  (x : ftype double_double') (y : ftype Tdouble) :=
  let xs := proj1_sig x in 
  DWPlusFP (fst xs) (snd xs) y.


Definition DWPlusFP_ff {NANS: Nans} : floatfunc 
                  [double_double' ;Tdouble] double_double
    DWplusFP_bnds' (fun xhl y => xhl + y)%R.
apply (Build_floatfunc [double_double';Tdouble] 
                double_double _ _ 
          (DWPlusFP')
           1%N 1%N).
intros x ? y ?.
{ simpl in H, H0.
rewrite !andb_true_iff in H H0.
destruct H as [HA HB].
destruct H0 as [HC HD].
rewrite/DWPlusFP'.
repeat split; intros; try discriminate.
{ destruct x, x. rewrite /proj1_sig.
rewrite /rounded_finite/FT2R/nonstd_to_R in H. simpl in H.
remember (DD2F' (exist (fun a : dd_rep => dd_pred a) (f, f0) d)).
destruct o.
{ move : Heqo. rewrite /DD2F' => /=.
match goal with |- context [if ?a && ?b then _ else _] => 
remember (a && b)
end.
move => Heqbo. destruct b => //=.
inversion Heqbo. clear Heqbo. rewrite /DD2F.
match goal with |- context [Rlt_bool ?a ?b ] => 
remember (Rlt_bool a b)
end.
destruct b => //. 


admit. } 

 
rewrite Rlt_bool_true. Req_bool_false.
remember (  (if negb (Req_bool (FT2R f + FT2R f0) 0)
   then Rle_bool (/ IZR (Z.pow_pos 2 1022)) (Rabs (FT2R f + FT2R f0))
   else true)).
destruct b => //=.
remember (Rlt_bool (Rabs (F2R (Operations.Fplus (B2F f) (B2F f0)))) dd_ov).
destruct b => //=.


in Heqo.


admit.
destruct d. simpl in H.
move: H. rewrite /rounded_finite/FT2R/nonstd_to_R => //=.
rewrite /DD2F' => //=.
move : HA.
rewrite /compare/extend_comp/compare' => //=.
rewrite /proj1_sig/fst/snd => //=.

apply finite_bnds_e in HB, HC, HD.

remember (Req_bool (FT2R f + FT2R f0) 0).
destruct b => //=.
move => H.


destruct (
  relative_errorDWPlusFP_correct' f f0 y) 
as (del & A & B)=> //. admit. 
admit. admit. }
exists del, 0.
  repeat split; try nra.
simpl. rewrite /FPCore.default_rel.
move : B.
simpl;
cbv [fprec double_double] => //=.
move => B. 
refine (Rle_trans _ _ _ B _).
field_simplify; try lra. admit. admit.

simpl. rewrite /FT2R/nonstd_to_R => //=.

admit.
Admitted.


End VCFloat.


