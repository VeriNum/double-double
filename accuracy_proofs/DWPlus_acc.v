Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common.
Require Import DWPlus DDModels Fast2Mult_acc TwoSum_acc.
From Flocq Require Import Pff2Flocq Core.

Require Import mathcomp.ssreflect.ssreflect.

Context {NANS: Nans} {t : type}.

Section CorrectDWPlusFP.

Variables (xh xl y : ftype t).

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
set (f1 :=(TwoSumF_err xh y)) in *.
set (f2:= (TwoSumF_sum xh y)) in *.
split; simpl; auto.
set (f3:= (BPLUS xl f1)) in *.
destruct f2; destruct f3; destruct s; destruct s0;
 auto; try contradiction. 
destruct f2; destruct f1;   destruct xl; 
  destruct s; destruct s0; destruct s1; 
 auto; try contradiction. 
Qed.

Let sh := fst (TwoSumF xh y).
Let sl := snd (TwoSumF xh y).
Let v  := BPLUS xl sl.

Fact FIN2 : Binary.is_finite _ _ (BPLUS xl sl) = true.
Proof.
move: FIN. rewrite /DWPlusFP.
replace (TwoSumF xh y) with ( sh,sl) => //= H.
destruct H as (FINm & _). rewrite /fst in FINm.
destruct (BPLUS xl sl); simpl; auto;
destruct sh; destruct s0; destruct s; try contradiction; auto.
Qed.

Fact FIN3 : Binary.is_finite _ _ (BPLUS xh y) = true.
Proof.
move: FIN. rewrite /DWPlusFP.
replace (TwoSumF xh y) with ( sh,sl) => //=.
subst sh. rewrite /TwoSumF/fst/snd => H.
destruct H as (FINa & _). unfold fst in FINa. simpl; auto;
destruct (BPLUS xl sl); destruct (BPLUS xh y); destruct s; 
  destruct s0; try contradiction; auto.
Qed.

End CorrectDWPlusFP.

Section  CorrectDWPlusFP'.

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
  rewrite /FT2R; apply Binary.generic_format_B2R. 
have Hb: generic_format radix2 fexp (FT2R b) by 
  rewrite /FT2R; apply Binary.generic_format_B2R. 
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
Lemma Fast2Sum_CorrectDWPlusFP (xh y xl: ftype t): 
  Binary.is_finite _ _ (BPLUS xl (snd (TwoSumF xh y))) = true -> 
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
  rewrite /FT2R; apply Binary.generic_format_B2R. 
have Hb: generic_format radix2 fexp (FT2R y) by 
  rewrite /FT2R; apply Binary.generic_format_B2R. 
have Hc: generic_format radix2 fexp (FT2R xl) by 
  rewrite /FT2R; apply Binary.generic_format_B2R. 
have Hrnd: rounded t (FT2R xh + FT2R y) <> 0.
rewrite /rounded; apply Plus_error.round_plus_neq_0 => //.


case:(Req_dec (FT2R xh) 0)=> hxh0.
{ pose proof TwoSum0 xh y FIN2 hxh0 as H.
  BPLUS_correct t xl (snd (TwoSumF xh y)); clear H5.
  inversion H. rewrite /fst/snd/TwoSumF; 
  fold (@FT2R t); rewrite H1 H2 Rplus_0_r.
  have H0 : FT2R xl = 0.
  { move: DWx. rewrite /double_word hxh0 => DWx.
    rewrite -(Rplus_0_l (FT2R xl)). 
    symmetry in DWx; rewrite /rounded in DWx.
    apply: (Plus_error.round_plus_eq_0
        radix2 (SpecFloat.fexp (fprec t) (femax t))
        (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) );
    unfold FT2R ;
    try apply:generic_format_0;
    try apply Binary.generic_format_B2R;
    try apply DWx. }
  rewrite H0 round_0 Rabs_R0. apply: Rabs_pos. }

have FIN3: Binary.is_finite (fprec t) (femax t) (BPLUS xh y) = true. admit.

(* cases on underflow *)
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
  rewrite /FT2R; apply Binary.generic_format_B2R.
admit.
}

(* cases on underflow *)
destruct (Rlt_or_le 
  (Rabs (FT2R xh + FT2R xl))
  (bpow radix2 (@emin t + fprec t - 1))).
{ have hxl : FT2R xl = 0.
move : DWx. rewrite /double_word. 
rewrite /rounded round_generic. 
move => DWx; nra.
apply Plus_error.FLT_format_plus_small => //.
refine (Rle_trans _ _ _ (Rlt_le _ _ H0) _).
apply bpow_le. fold (@emin t); lia.
BPLUS_correct t xl (snd (TwoSumF xh y)).
fold (@FT2R t); rewrite hxl Rplus_0_l round_generic.
fold (TwoSumF_err xh y) (TwoSumF_sum xh y). 
  rewrite TwoSumF_correct /TwoSumF_sum/fst/TwoSumF => //.
rewrite Rabs_minus_sym.
BPLUS_correct t xh y; fold (@FT2R t).
refine (Rle_trans _ _ _ (error_le_ulp_round _ _ _ _ ) _).
refine (Rle_trans _ _ _ _ _) .
2: apply (ulp_le_abs radix2 fexp) => //.
nra. admit. admit. } 

(* cases on underflow *)
destruct (Rlt_or_le 
  (Rabs (FT2R xl + FT2R (snd (TwoSumF xh y))))
  (bpow radix2 (@emin t + fprec t - 1))).
admit.

have DWx2 : DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl).
{ move : DWx. rewrite /double_word/DWPlus.double_word.
rewrite /rounded round_FLT_FLX. move => DWx; repeat split => //;
  try apply (generic_format_FLX_FLT radix2 (@emin t)) => //.
  fold (@emin t); nra. } 

set (g:= (snd (TwoSumF xh y))) in *.
BPLUS_correct t xl g.
subst g.

pose proof @TwoSumEq_FLT NANS t _ _ FIN2 as H2;
unfold F2Rp in H2.
  
fold (@FT2R t).
replace (FT2R (snd (TwoSumF xh y)))
  with (TwoSum_err (fprec t) choice (FT2R xh) (FT2R y)) by
  inversion H2 => //.
replace (FT2R (fst (TwoSumF xh y)))
  with (TwoSum_sum (fprec t) choice (FT2R xh) (FT2R y)) by
inversion H2 => //.

clear H5 H6 H7.

rewrite /rounded !round_FLT_FLX => //.

clear H2 DWx H H0 H1 FIN1 FIN2 FIN3.

wlog xhy : y xh S0 Ha Hb Hc Hrnd hxh0 DWx2
  /  Rabs (FT2R y) <= Rabs (FT2R xh).
  move=> Hwlog.
  case:(Rle_lt_dec (Rabs (FT2R y)) (Rabs (FT2R xh)))=> absyxh.
    by apply: ( Hwlog y xh)=>//.

(* we can use Hwlog as long as (xl + xh) and (xl + y) are DWs *) 

  have yn0: FT2R y <> 0.
    by move=>y0; move:  absyxh; rewrite y0 Rabs_R0; move:(Rabs_pos (FT2R xh)); lra. 

have hf : (1 < fprec t)%Z by pose proof @fprec_lb t; lia.

have xle:= (@DWPlus.dw_ulp _ hf choice (FT2R xh) (FT2R xl) DWx2).

have xluy: Ulp.ulp radix2 (FLX_exp (fprec t)) (FT2R xh) <=
              Ulp.ulp radix2 (FLX_exp (fprec t)) (FT2R y).
    apply ulp_le => //; try nra. 
    apply FLX_exp_valid.
    apply fprec_gt_0.
    apply FLX_exp_monotone.

case:  xluy=> xluy.
    have yE: FT2R y = @rnd_p t (FT2R y + FT2R xl). rewrite /rnd_p. 
    have Hch: choice = (fun n : Z => negb (Z.even n)). admit.
    symmetry.  
    apply: (@rulp2p' (fprec t) hf choice Hch (FT2R xh) (FT2R y) (FT2R xl)) => //.
    admit.

 
move : DWx2. rewrite /DWPlus.double_word. 
  repeat move => []. move =>  A B DWx2.

case:  (Hwlog xh y)=>//; try lra. 
rewrite Rplus_comm => //.
rewrite /DWPlus.double_word; repeat split => //.

admit.  admit. admit.

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

case:  (Hwlog xh y)=>//; try lra. 
rewrite Rplus_comm => //.
rewrite /DWPlus.double_word; repeat split.
admit. admit. symmetry.
apply rulp2p => //; last lra. admit. admit. admit.

{ 

have Hch: choice = (fun n : Z => negb (Z.even n)).
admit.
have Hbn :  (3 <= fprec t)%Z.
admit.
have Hy: generic_format beta (FLX_exp (fprec t)) (FT2R y).
admit.

fold (@FT2R t).

pose proof (part_case_ulps
  (fprec_gt_one t) Hch Hbn DWx2 Hy).


refine (Rle_trans _ _ _ _ _).
apply H.

(FT2R xh) (FT2R xl).

Search ( _ <= fprec _)%Z.

 apply round_le. admit. admit.
fold (@FT2R t). Search Rplus round.
(*refine (Rle_trans _ _ _ _ (ulp_le_abs radix2 fexp _ _ _)).
refine (Rle_trans _ _ _ (Rabs_triang _ _) _).
refine (Rle_trans _ _ _ (Rplus_le_compat _ _ _ _ _ _) _).
apply xle.
rewrite /snd/TwoSum.
fold (TwoSumF_err xh y).
apply TwoSum_accuracy.




Search Rle Ulp.ulp Rabs. 

Search (~ Bayleyaux.is_pow _ _).

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


destruct (Bayleyaux.is_pow_dec radix2 (FT2R y)) as [Hi|Hi].
{ 
 have yE: FT2R y = @rnd_p t (FT2R y + FT2R xl). rewrite /rnd_p.
  symmetry. apply rulp2p => //; last lra. admit.
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

case:  (Hwlog xh y)=>//; try lra. admit. 
admit. admit. admit.

case:  (Hwlog xh y)=>//; try lra. admit. 
rewrite /DWPlus.double_word; repeat split.
admit. admit. symmetry.
apply rulp2p => //. admit. admit. admit. admit.

destruct (Bayleyaux.is_pow_dec radix2 (FT2R y)) as [Hi|Hi].
 
    have Hch: choice = (fun n : Z => negb (Z.even n)). admit.
    symmetry.  
    apply: (@rulp2p (fprec t) hf choice Hch ) => //.

Search (Bayleyaux.is_pow).
    admit.

Bayleyaux.rbpowpuW
rulp2p Bayleyaux.rbpowpu
case:  (Hwlog xh y)=>//; try lra. admit.  


admit. admit. admit. admit.  admit. admit.
case:  (Hwlog y xh)=>//; try lra. 
  
Search Ulp.ulp Rabs (_ = _).

admit.  admit. admit. admit. admit.  admit. admit.
  
   rewrite rulp2p //; last lra.
    move => [ey yE].
    move:  (absyxh)  (xluy).
    have->: ulp y = pow (ey + 1 -p).
      move: yE; rewrite -(Rabs_pos_eq (pow ey)); last by apply: bpow_ge_0.
      by case/Rabs_eq_Rabs => ->; rewrite 1?(ulp_opp) ulp_bpow /fexp.
    rewrite yE ulp_neq_0 // /cexp /fexp.
    move=>h /bpow_inj => h2.
    have {} h2:  ((ey + 1 ) = mag radix2 xh )%Z by lia.
    have : (pow ey) <= Rabs xh.
      have ->: (ey = (mag radix2 xh - 1))%Z by lia.
      apply:(bpow_mag_le two xh); lra.
    lra.
  case:(part_case_ulp  DWx Fy)=>//; first lra.
  move=> he f2sc.
  split.    suff ->: relative_errorDWFP xh xl y = 0 by apply:  boundDWFP_ge_0.
  rewrite rel_errorE he  Rabs_R0; ring.
  by apply:F2Sum_correct_DW'.




*) *)
Admitted.

Let emin :=  (@DDModels.emin t).


Variables (xh xl y : ftype t).
Hypothesis  xE : double_word xh xl.
Hypothesis FIN : is_finite_p (DWPlusFP xh xl y). 


Theorem DWPlusFP_eq :
  DWPlus.DWPlusFP (fprec t) choice (FT2R xh) (FT2R xl) (FT2R y) = F2Rp (DWPlusFP xh xl y).
Proof.
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
have FIN3: (is_finite_p (TwoSumF xh y)) by admit. 
have FIN4 : Binary.is_finite _ _ (BPLUS xl (snd (TwoSumF xh y))) = true by admit.
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
{ 
apply TwoSumF_eq in H => //.
inversion H.
rewrite Fast2Sum_2sum0' => //; 
rewrite /TwoSumF/fst/snd.
rewrite H2 H1 Rplus_0_r.
rewrite F2Sum.Fast2Sum0f round_generic => //. 
all: try apply (generic_format_FLX_FLT radix2 emin);
try apply Binary.generic_format_B2R.
now rewrite H2 H1. } 

destruct (Rle_or_lt 
(bpow radix2 (emin + fprec t - 1))  
(Rabs
  (Binary.B2R (fprec t) (femax t) xl +
   Binary.B2R (fprec t) (femax t) (snd (TwoSumF xh y))))) as [HUF|HUF].

{ 
rewrite -FastTwoSumEq_FLT => //; f_equal.
{ BPLUS_correct t xl (snd (TwoSumF xh y)).
rewrite (round_FLT_FLX radix2 (@DDModels.emin t)) => //. } 
 (*
bpow radix2 (emin + fprec t - 1) <=
      Rabs
        (Binary.B2R (fprec t) (femax t) xl +
         Binary.B2R (fprec t) (femax t) (snd (TwoSumF xh y))) -> 
Rabs (FT2R (BPLUS xl (snd (TwoSumF xh y)))) <= Rabs (FT2R (fst (TwoSumF xh y))) *)
admit. }


rewrite -FastTwoSumEq_FLT => //. f_equal.

rewrite BPLUS_UF_exact => //.
rewrite round_generic => //; f_equal.
apply: (generic_format_FLX_FLT _ emin).
apply: Plus_error.FLT_format_plus_small. 
admit. admit.
refine (Rle_trans _ _ _ (Rlt_le _ _ _) _ ). apply HUF.
apply bpow_le; lia.

rewrite BPLUS_UF_exact => //. 
(* Rabs
        (Binary.B2R (fprec t) (femax t) xl +
         Binary.B2R (fprec t) (femax t) (snd (TwoSumF xh y))) <
      bpow radix2 (emin + fprec t - 1) -> 
Rabs (FT2R xl + FT2R (snd (TwoSumF xh y))) <= Rabs (FT2R (fst (TwoSumF xh y))) *)

(* go by cases on RHS equals 0 *) admit. 

Admitted. 

End CorrectDWPlusFP'.


Section AccuracyDWPlusFP.

Variables (xh xl y : ftype t).
Hypothesis  xE : double_word xh xl.
Let zh := (FT2R (fst (DWPlusFP xh xl y))).
Let zl := (FT2R (snd (DWPlusFP xh xl y))).
Let xr := (FT2R xh + FT2R xl).
Let yr := (FT2R y).
Let sl := snd (TwoSumF xh y).
Let v  := BPLUS xl sl.

Hypothesis FIN : is_finite_p (DWPlusFP xh xl y). 

Notation u   := (bpow Zaux.radix2 (- fprec t)).

Definition relative_error_DWPlusFP := Rabs (((zh + zl) - (xr  + yr)) / (xr  + yr)).

Definition errorDWFP := (FT2R xh + FT2R xl + FT2R y) - (zh + zl).

Local Notation p := (fprec t).
Definition rnd := 
  (round radix2 (SpecFloat.fexp (fprec t) (femax t)) (Generic_fmt.Znearest choice)). 

Fact rel_errorE: relative_error_DWPlusFP = Rabs errorDWFP * (Rabs (/( (FT2R xh + FT2R xl) + FT2R y))).
Proof.
rewrite /relative_error_DWPlusFP /errorDWFP /Rdiv !Rabs_mult -Ropp_minus_distr Rabs_Ropp //.
Qed.

Fact null_sl 
  (sl0: FT2R sl = 0):  errorDWFP = 0.
Proof.
have Fsh:= Fsh;  have Fv:= Fv;  have Fx := Fxl.
pose proof FIN2 xh xl y FIN. 
pose proof FIN3 xh xl y FIN. 
have vE: FT2R v =  FT2R xl.
{ subst v. 
fold sl in H. unfold p in H.
BPLUS_correct t xl sl. unfold FT2R in sl0.
rewrite sl0 Rplus_0_r round_generic; auto.
apply Binary.generic_format_B2R. } 
have xhye : (FT2R xh + FT2R y) = rnd (FT2R xh + FT2R y).
{ move: (TwoSumF_correct xh y (FIN1 xh xl y FIN)); rewrite sl0. 
rewrite /TwoSumF_sum/fst/TwoSumF.
BPLUS_correct t xh y. rewrite /rnd; intros. 
symmetry in TwoSumF_correct. 
by apply Rminus_diag_uniq_sym in TwoSumF_correct. }  
case:(Req_dec (FT2R xl) 0)=> xl0.
  rewrite /errorDWFP  xl0. 
subst zh zl.
rewrite /fst/snd/DWPlusFP/Fast2Sum.

unfold DWPlusFP.
Fast2Sumf0 //= TwoSum_sumE -xhye; ring.
case:(Req_dec (xh + y) 0)=> xhy0.
  have sh0: sh = 0  by rewrite  TwoSum_sumE  xhy0 round_0.
  rewrite /errorDWFP sh0 Fast2Sum0f //= vE; lra.
  rewrite /errorDWFP F2Sum_correct_abs //= ?vE;
    try (apply/rnd_p_sym/choiceP).
  rewrite TwoSum_sumE -xhye; ring.
have he:=(roundN_plus_ulp Fxh Fy xhy0).
apply:(Rle_trans _ (ulp radix2 fexp xh / 2)).
  by move/dw_ulp:  xDW; lra.
rewrite TwoSum_sumE; 
apply:(Rle_trans _ (Rmax (ulp radix2 fexp xh / 2) (ulp radix2 fexp y / 2))); try lra.
by apply:Rmax_l.
Qed.

Fact null_sl_rel 
  (sl0: (TwoSum_err (fprec t) choice (FT2R xh) (FT2R y)) = 0):  relative_error_DWPlusFP = 0.
Proof.
by rewrite rel_errorE null_sl // Rabs_R0 Rmult_0_l.
Qed.

Fact null_xh_rel (xh0: FT2R xh = 0): relative_error_DWPlusFP = 0.
Proof.
  apply:null_sl_rel; case: xDW; case=> Fxh Fxl _.
  rewrite  TwoSum_correct //= TwoSum_sumE  xh0 Rplus_0_l round_generic //; ring.
Qed.


Theorem relative_errorDWPlusFP_correct : relative_error_DWPlusFP <= 2 * u^2.
Proof.
have rn_sym:= (round_opp radix2 (SpecFloat.fexp (fprec t) (femax t))
   (Generic_fmt.Znearest choice)).
have boundDWFP_ge_0 : 0 <= 2*u^2 by rewrite /u; move: (bpow_ge_0 radix2 (-p)); nra.
case:(Req_dec (FT2R xh) 0)=> hxh0.
{ rewrite /relative_error_DWPlusFP; subst xr zh zl. 
rewrite /DWPlusFP/fst/snd.
rewrite hxh0.
rewrite ?null_xh_rel.
  rewrite hxh0  DWPlusFP0f //=.
    split; [split |] =>//; try apply:generic_format_0.
    by rewrite Rplus_0_r round_generic.
  have xl0: xl = 0 by move:xE;  rewrite hxh0 Rplus_0_l round_generic.
  split; [split |] =>//; try apply:generic_format_0.
  by rewrite xl0 Rplus_0_r round_0.
case: (Req_dec  (xh + y) 0)=> xhy0.
  rewrite (null_case_rel  Fy DWx  xhy0).
  (* have ppow := bpow_gt_0 two (1 -2*p). *)
  (* have ppo1 :  pow (1 -  p) < 1. *)
  (*   have -> : (1 - p = -( p -1))%Z by lia. *)
  (*   apply:(bpow_lt_1  two). *)
  (*   lia. *)
  (* have ppo11 : 0 < (1 - pow (1 - p)) by lra. *)
  (* rewrite /Rdiv; split. *)
  (*   apply: Rmult_le_pos; try lra. *)
  (*   by apply: Rlt_le; apply: Rinv_0_lt_compat. *)
  split; first by apply:  boundDWFP_ge_0.
  rewrite /DWPlusFP TwoSum_sumE  xhy0 round_0  Fast2Sum0f /=; last apply:Fv.
  split; [split |] =>//; try apply:generic_format_0; try apply:Fv.
  by rewrite Rplus_0_r; rewrite [X in _ = X]round_generic //; apply:Fv.
clear Fxh xE.
wlog xhy : y xh Fy xhy0 DWx hxh0   /  Rabs y <= Rabs xh.
  move=> Hwlog.
  case:(Rle_lt_dec (Rabs y) (Rabs xh) )=> absyxh.
    by apply: ( Hwlog y xh)=>//. 
  have xel:= (dw_ulp  DWx).
  case: (DWx)=> [[Fxh _]]   hxh.
  have yn0: y <> 0.
    by move=>y0; move:  absyxh; rewrite y0 Rabs_R0; move:(Rabs_pos xh); lra.
  have xluy: ulp xh <=  ulp y.
    rewrite !ulp_neq_0 //.
    apply:bpow_le; rewrite /cexp /fexp.
    suff: (mag radix2 xh <=  (mag radix2 y))%Z by lia.
    apply: mag_le_abs=>//; lra.
  case:  xluy=> xluy.
    have yE: y = rnd_p (y + xl) by rewrite (@rulp2p' xh).
    rewrite relative_error_DWFPC //DWPlusFPC // ; split; case:  (Hwlog xh y)=>//; lra.
  case:(Rle_lt_or_eq_dec  _  _  xel)=> xel'.
    rewrite relative_error_DWFPC // DWPlusFPC // ;  case:  (Hwlog xh y)=>//; try lra.
    split=>//;  rewrite rulp2p //; last lra.
    move => [ey yE].
    move:  (absyxh)  (xluy).
    have->: ulp y = pow (ey + 1 -p).
      move: yE; rewrite -(Rabs_pos_eq (pow ey)); last by apply: bpow_ge_0.
      by case/Rabs_eq_Rabs => ->; rewrite 1?(ulp_opp) ulp_bpow /fexp.
    rewrite yE ulp_neq_0 // /cexp /fexp.
    move=>h /bpow_inj => h2.
    have {} h2:  ((ey + 1 ) = mag radix2 xh )%Z by lia.
    have : (pow ey) <= Rabs xh.
      have ->: (ey = (mag radix2 xh - 1))%Z by lia.
      apply:(bpow_mag_le two xh); lra.
    lra.
  case:(part_case_ulp  DWx Fy)=>//; first lra.
  move=> he f2sc.
  split.    suff ->: relative_errorDWFP xh xl y = 0 by apply:  boundDWFP_ge_0.
  rewrite rel_errorE he  Rabs_R0; ring.
  by apply:F2Sum_correct_DW'.
clear Fxl.
wlog xhpos: xl  y xh  Fy xhy0 xhy  DWx  hxh0 / 0 <  xh.
  move=> Hwlog.
  case:(Rlt_le_dec 0 xh) => xhpos.
   by  apply: Hwlog. 
  case:xhpos=>xh0; first last.
    move:xhy; rewrite {1}xh0 Rabs_R0.
    move:(Rabs_pos  y)=> H1 H2.
    have : Rabs y = 0 by lra.
    by move:(Rabs_no_R0 y) => *; lra.
  case: (DWx)=>[[Fxh Fxl] xE].

  suff -> :( relative_errorDWFP xh xl y) = (relative_errorDWFP  (-xh) (-xl) (-y)).
    have Fy' := generic_format_opp two fexp y Fy.
    have Fxl' := generic_format_opp two fexp xl Fxl.
    have Fxh' := generic_format_opp two fexp xh Fxh.
    case:(Hwlog (-xl) (-y) (-xh)); try apply:generic_format_opp =>//; try lra.
    + by rewrite !Rabs_Ropp.
    + split; first split;  try  apply:generic_format_opp =>//.
      have -> : - xh + - xl = -(xh + xl) by ring.
      by rewrite    ZNE round_NE_opp -ZNE {1}xE.
   split=>//.
    rewrite DWPlusFP_Asym in b.
    have fst_opp: forall x , fst (pair_opp x)= - fst x by [].
    have snd_opp: forall x , snd (pair_opp x)= - snd x by [].
    move:b ; rewrite fst_opp snd_opp.
    by move/DW_sym; rewrite !Ropp_involutive.
  rewrite /relative_errorDWFP.
  congr Rabs.
  have -> :  (- xh + - xl + - y)= -(xh + xl + y) by ring.
  rewrite /TwoSum_sum TwoSum_asym vAsym Fast2Sum_asym // /pair_opp /=.
 field.
  move => den0.
  apply : xhy0.
  have den00: xh + xl + y = 0 by lra.
  move: DWx; rewrite /double_word=>[[[_ _]]].
  have ->: xh + xl = -y by lra.
  rewrite  ZNE round_NE_opp => -> /=.
  by rewrite round_generic //; ring. 
wlog [xh1 xh2]: xl xh y   DWx Fy  xhy0 xhy  xhpos hxh0
             / 1 <= xh  <= 2-2*u.
  move=> Hwlog.
  case:(DWx)=>[[Fxh Fxl] xE].
  case: (scale_generic_12 Fxh xhpos)=> exh Hxhs.
  have powgt0 := (bpow_gt_0 two exh).
  rewrite -(relative_error_DWFPS exh Fy Fxh).
    case:(Hwlog (xl * pow exh) (xh * pow exh) (y * pow exh))=>//.
    + exact:DW_S.
    + exact: formatS.
    + rewrite -Rmult_plus_distr_r; clear - xhy0  powgt0; nra.
    + rewrite !Rabs_mult (Rabs_pos_eq (pow _)); try lra.
      by apply: Rmult_le_compat_r;lra.
    + clear -  Hxhs   powgt0; nra.
    + clear -  Hxhs   powgt0; nra.
    move=> h1 h2; split =>//.
    move/(DW_S (-exh)):h2.
    by rewrite DWPlusFPS //= 2!Rmult_assoc -bpow_plus; ring_simplify (exh + - exh)%Z;  
       rewrite !Rmult_1_r.
  case:DWx => [_] h  h1.
  apply : xhy0.
  have hy: y = - (xh + xl) by lra.
  have : rnd_p y = - rnd_p (xh + xl) by rewrite hy ZNE -round_NE_opp.
  by rewrite -h !round_generic //; lra.
(* c'est là que ça commence vraiment...*) 
have hpxh: pow (1-1) <= Rabs xh < pow 1.
   rewrite Rabs_pos_eq //; move:xh2; rewrite /u /=; last lra.
    rewrite IZR_Zpower_pos /=; move:(bpow_gt_0 two (-p));  try lra.
have xlu: Rabs xl <= u.
  move:(dw_ulp DWx).
  rewrite /u u_ulp1.
  rewrite !ulp_neq_0; try lra; rewrite /cexp /fexp.
  rewrite (mag_unique_pos two xh 1); try lra; rewrite /=.
    rewrite (mag_unique_pos two 1 1) /= ?IZR_Zpower_pos /=;lra.
  split=>//.
  rewrite /u in xh2.
  by move:(bpow_gt_0 two (-p)); rewrite  IZR_Zpower_pos /=; lra.
have lnbxh:=(mag_unique two xh 1%Z  hpxh ).
rewrite (Rabs_pos_eq  xh) in xhy; try lra.
move/Rabs_le_inv: xhy=>[hd hu].
case:(DWx)=> [[Fxh Fxl] xE].
case: (Rle_lt_dec y (-xh/2) )=> hy.
  have sl0: sl xh y = 0.
  rewrite  TwoSum_correct //= TwoSum_sumE   round_generic; first  ring.
  have->: xh+y = xh - (-y) by ring.
  apply: sterbenz'=>//.
    by apply:generic_format_opp.
  by lra.
  split; first by rewrite  null_sl_rel //; apply: bound_ge_0.
  rewrite /DWPlusFP.
  apply: F2Sum_correct_DW'.
rewrite /Fast2Sum_correct.
have ->: (v xh y xl) = xl.
  rewrite sl0 Rplus_0_r round_generic //.
  have shE: sh xh y = xh + y.
move: (TwoSum_correct Fxh Fy); rewrite sl0; lra.
rewrite shE /=.

apply: F2Sum_correct_abs=>//.
  rewrite -shE; apply:generic_format_round.
have rxhyn0: rnd_p (xh + y ) <> 0.
move:(shE); 
rewrite TwoSum_sumE; lra.

have he:=(roundN_plus_ulp Fxh Fy xhy0).
apply:(Rle_trans _ (ulp  xh / 2)).
  by move/dw_ulp:  DWx; lra.
apply:(Rle_trans _ (Rmax (ulp  xh / 2) (ulp  y / 2))); try lra.
by apply:Rmax_l.
rewrite -shE TwoSum_sumE; lra.

(* case 2 *)
have hled: 1/2 <= xh/2 by lra.
have hltle: xh/2 < xh + y <= 2* xh by lra.
have shge: /2 <= sh xh y.
  have ->: /2 = rnd_p (/2).
    rewrite round_generic //.
    have -> : /2 = pow (-1) by [].
    apply: generic_format_bpow'.
    by rewrite /fexp; lia.
  by apply: round_le; lra.
have shle3: Rabs (xl + sl xh y) <= 3*u.
  apply:(Rle_trans _ (Rabs xl + Rabs (sl xh y))).
    by apply: Rabs_triang .
  suff:  Rabs (sl xh y)<= 2 * u by lra.
  case:(Rle_lt_dec (xh + y) 2)=> sh2.
    suff:  Rabs (sl xh y) <= u by rewrite /u; move : (bpow_gt_0 two (-p)); lra.
    rewrite  TwoSum_correct //  /u.
    have ->:  (xh + y - rnd_p (xh + y)) = - (rnd_p (xh + y) - (xh + y)) by ring.
    rewrite Rabs_Ropp.
    have ->: pow (- p) =  / 2 * pow (- p) * pow 1 by rewrite /= IZR_Zpower_pos /= ; lra.
    apply: error_le_half_ulp'.
      exact:Hp.
    rewrite /= Rabs_pos_eq ?IZR_Zpower_pos /=; lra.
  rewrite   TwoSum_correct //  /u.
  have ->:  (xh + y - rnd_p (xh + y)) = - (rnd_p (xh + y) - (xh + y)) by ring.
  rewrite Rabs_Ropp.
  have ->: 2 * pow (- p) =  /2 * pow (- p) * pow 2 by rewrite /= IZR_Zpower_pos /= ; lra.
  apply: error_le_half_ulp'.
    exact:Hp.
  rewrite /= Rabs_pos_eq.
    apply: (Rle_trans _ (4 - 4 * u)); try lra.
    by rewrite /u IZR_Zpower_pos /=; move:(bpow_gt_0 two (-p)); lra.
  lra.
 pose vv := v y xh xl. 
have:Rabs vv <= 3*u.
   apply: abs_round_le_generic=>//.
(*  format (3 * u). *)
  rewrite /u.
  pose fx := Float two 3 (-p).
  have xfx: (3 * pow (- p)) =  F2R fx by [].
  apply:(FLX_format_Rabs_Fnum  xfx)=>/=.
  rewrite Rabs_pos_eq; try lra.
  apply: (Rlt_le_trans _ (pow 2)).
    have ->: pow 2 = 4 by [].
      by lra.
    by apply:bpow_le; lia.
  by move:shle3; rewrite  TwoSum_errC //.
rewrite /vv vC // => hv.
have hvsf: Rabs (v xh y xl) <= Rabs (sh xh y).
  apply:(Rle_trans _ (3 * u))=>//.
  apply:(Rle_trans _ (/2) )=>//.
  rewrite /u.
    apply:(Rmult_le_reg_r (pow p)); first by exact:bpow_gt_0.
    rewrite Rmult_assoc -bpow_plus Zplus_opp_l /= Rmult_1_r.
    apply:(Rle_trans _ (pow 2)).
      by change (3 <= 4); lra.
    change( pow 2 <= pow (-1) * pow p); rewrite -bpow_plus;  apply: bpow_le; lia.
  rewrite  Rabs_pos_eq ; lra.
have f2sc: (Fast2Sum_correct p choice (sh xh y) (v  xh y xl)).
  by apply: F2Sum_correct_abs=>//;apply:generic_format_round.
 rewrite rel_errorDWFPe_abs //.
split; last by apply: F2Sum_correct_DW'.
case:(Rle_lt_dec (xh + y) 2)=> sh2.
  have slu:  Rabs (sl xh y) <= u.
    rewrite  TwoSum_correct //  /u.
    have ->:  (xh + y - rnd_p (xh + y)) = - (rnd_p (xh + y) - (xh + y)) by ring.
    rewrite Rabs_Ropp.
    have ->: pow (- p) =  / 2 * pow (- p) * pow 1 by rewrite /= IZR_Zpower_pos /=; lra.
    apply: error_le_half_ulp'.
      exact:Hp.
    rewrite /= Rabs_pos_eq ?IZR_Zpower_pos /=; lra.
  have vu: Rabs (xl + (sl xh y)) <= 2 * u.
    apply:(Rle_trans _ (Rabs xl + Rabs (sl xh y))).
      by apply: Rabs_triang .
    by lra.
  set e := sl _ _ +xl - _.
  have he: Rabs e  <= u ^2.
    rewrite /e.
    have ->: (sl xh y  + xl - v xh y xl) = - (v xh y xl  - (xl + sl xh y)) by ring.
    apply:(Rle_trans _ (/ 2 * pow (- p) * pow (- p + 1) )).
      rewrite Rabs_Ropp; apply:  (error_le_half_ulp' Hp choice (xl+sl xh y) (-p +1)).
      move:vu; rewrite /u.
      have -> : 2 = pow 1 by [].
      by rewrite -bpow_plus Zplus_comm.
    by rewrite bpow_plus /u /= IZR_Zpower_pos /=; lra.
  pose x := xh + xl.
  have spos: 0< xh +xl +y by move/Rabs_le_inv: xlu;lra.
  rewrite Rabs_mult  Rabs_Rinv //; last lra.
  rewrite (Rabs_pos_eq (_ +_)); last lra.
  case: (Rlt_le_dec (xh + xl + y) (/2))=> s2; last first.
    clear - s2 spos he.
      have u2pos: 0 < u^2 by move:(bpow_gt_0 two (-p)); rewrite /u; nra.
    have: 0< / (xh + xl + y) <= 2.
    split.
apply:Rinv_0_lt_compat =>//.

      have ->: 2 = /(/2) by field.
apply: Rinv_le =>//; try lra.
nra.

have h1: xh + y < /2 +u by move/Rabs_le_inv: xlu;lra.
have h2: xh/2 < /2 +u by lra.
have xhe: xh = 1.
apply:Rle_antisym=> //.
suff  ->: 1 = (pred two fexp (1 + 2*u)).
  apply:pred_ge_gt => //; try lra.
  rewrite /u u_ulp1.
   have ->:2 * (/ 2 * ulp 1)= (ulp 1) by field.
   apply:generic_format_succ_aux1 ; try lra.

change (format (pow 0)).
apply:generic_format_bpow; rewrite /fexp; lia.

have ->: 1 + 2 * u= succ two fexp 1.



rewrite succ_FLX_1 /u bpow_plus.
have->: pow 1 = 2 by [].
ring.
rewrite pred_succ //.
change (format (pow 0)).
apply:generic_format_bpow; rewrite /fexp; lia.
case: (Rle_lt_dec (- (u/2) ) xl) => xlu2 ; last first.
have h : xh +xl < 1 - (u/2) by lra.


 have is_pow1: is_pow two 1 by exists 0%Z;rewrite Rabs_pos_eq //;lra. 
 have F1: format 1 by apply:is_pow_generic ; try lra. 

have : rnd_p (xh + xl) <= 1-u.
rewrite pred_1.
apply:round_N_le_midp.

apply: generic_format_pred => //.
rewrite  succ_pred //.
rewrite -pred_1; lra.
rewrite -xE; lra.
 have is_pow1: is_pow two 1 by exists 0%Z;rewrite Rabs_pos_eq //;lra. 
 have F1: format 1 by apply:is_pow_generic ; try lra. 
have: y < -/2 + u/2 by lra.
have : 1 - u < - (2 * y) by lra.

rewrite pred_1.
have F2y: format (- (2 * y)).
apply:generic_format_opp; rewrite Rmult_comm; change (format (y * (pow 1))).
by apply:formatS.
have Fpred: format (pred radix2 fexp 1 ).
apply:generic_format_pred =>//.



move/(succ_le_lt two fexp _ _ Fpred F2y).
rewrite succ_pred //.
lra.
(* cas 2.2 *)
have xhyup: xh + y <= 4 - 4 * u  by lra.
have xhyup4: xh + y <= 2 ^ 2 by  rewrite /u in xhyup; move: (bpow_ge_0 two (-p)); lra.
have sl2: Rabs (sl xh y) <= 2 * u.
  have -> : 2 * u = /2 * (pow (-p)) * (pow 2) by rewrite /u /= IZR_Zpower_pos /= ; field.
  rewrite   TwoSum_correct // .
  have ->: (xh + y - rnd_p (xh + y)) = - (rnd_p (xh + y) - (xh +y)) by ring.
  rewrite Rabs_Ropp.
  apply : error_le_half_ulp'.
    exact: Hp.
  by rewrite Rabs_pos_eq /= ?IZR_Zpower_pos /=; lra.
have vu3 : Rabs (xl + sl xh y) <= 3 *u.
  apply:(Rle_trans _ (Rabs xl + Rabs (sl xh y))).
    by apply: Rabs_triang .
  by lra.
have vu: Rabs (xl + sl xh y) <= pow (-p + 2).
  apply:(Rle_trans _ (3 * u))=>//.
    by rewrite /u bpow_plus /= IZR_Zpower_pos /=; move: (bpow_ge_0 two (-p)); lra.
 set e := sl xh y + xl - _.
have he: Rabs e <= 2 * u^2.
  rewrite /e.
  have ->: (sl xh y + xl - rnd_p (xl + sl xh y)) = - (rnd_p (xl + sl xh y) - (xl + sl xh y)) by ring.
  rewrite Rabs_Ropp.
  apply:(Rle_trans _ (/ 2 * pow (- p) * pow (- p + 2) )).
    by apply:(error_le_half_ulp' Hp choice (xl+sl _ _) (-p +2)).
  by rewrite bpow_plus /u /= IZR_Zpower_pos /=; lra.
pose x := xh + xl.
have den1p: 0 < 2 - u.
  suff  : u < 2 by lra.
  have->: 2 = pow 1 by [].
  by rewrite /u; apply:bpow_lt;lia.
apply:(Rle_trans _ (2 * u^2 / (2 - u))); last first.
rewrite /Rdiv.
rewrite -[X in _ <=X]Rmult_1_r.
apply:Rmult_le_compat_l.
lra.
 have ->: 1 = /1 by field.
apply:Rinv_le;  lra.


(* suff : 1 <= 2- u by nra. have *)
(*  ->: 1 = /1 by field. *)


(*   have denp: 0 < (1 - pow ( 1 -p )). *)
(*     suff  : (pow ( 1 - p)) < 1 by lra. *)
(*     have ->: ((1 - p ) = -( p -1))%Z by ring. *)
(*     by apply: bpow_lt_1;  lia. *)
(*   apply:(Rmult_le_reg_r (2 -u))=>//. *)
(*   have ->: ((2 * u ^ 2 / (2 - u))  * (2 - u)) =  2 * u ^ 2 by field ; lra. *)
(*   apply:(Rmult_le_reg_r (1 - pow (1 - p)) )=>//. *)
(*   have ->: pow (1 - 2 * p) / (1 - pow (1 - p)) * (2 - u) * (1 - pow (1 - p))=  pow (1 - 2 * p) * (2 - u). *)
(*     by field ; lra. *)
(*   rewrite !bpow_plus. *)
(*   have ->: pow 1 = 2 by []. *)
(*   have ->:( -( 2 * p ) = -p + -p)%Z by lia. *)
(*   rewrite bpow_plus -/u. *)
(*   have -> : u * u = u ^ 2 by ring. *)
(*   apply: Rmult_le_compat_l. *)
(*     by move:(pow2_ge_0 u); set uu := u ^ 2; lra. *)
(*   have : 0 <= u by rewrite /u; apply: bpow_ge_0. *)
(*   by lra. *)
rewrite Rabs_mult; apply: Rmult_le_compat => //; try apply: Rabs_pos.
have bdxy: 2 - u <= Rabs (xh + xl + y).
  apply: Rabs_ge.
  right.
  suff : - u <= xl by lra.
  by move/Rabs_le_inv:   xlu => [h _].
rewrite Rabs_Rinv.
apply: Rinv_le=>//.
case: (Req_dec   (xh + xl + y ) 0) =>// h0.
by rewrite h0  Rabs_R0 in   bdxy; lra.
Qed.




pose proof Fast2Sum_CorrectDWPlusFP.
set (sh := fst (TwoSumF xh y)) .
destruct (Rlt_or_le (Rabs (FT2R xh)) (Rabs (FT2R y))) as [Hxy|Hxy].
{

unfold relative_error_DWPlusFP.
subst zh zl. move : FIN.
rewrite /DWPlus.DWPlusFP/DWPlusFP.
replace ( TwoSumF xh y) with ( TwoSumF_sum xh y,  TwoSumF_err xh y) => //.
replace (Fast2Sum (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y))) with
  (Fast2Sum_sum (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y)), 
  Fast2Sum_err (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y))) => //.
rewrite /fst/snd. intros.
destruct FIN0 as (FINm & FINp). clear FIN. 
unfold Fast2Mult_mul, Fast2Mult_err, fst, snd in *; simpl in *.
assert (Binary.is_finite _ _ 
            (BPLUS xl (TwoSumF_err xh y)) = true) by admit.
assert (is_finite_p (TwoSumF xh y )) by admit.
replace (  FT2R
    (Fast2Sum_sum (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y))) +
  FT2R
    (Fast2Sum_err (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y)))) with 
(FT2R (TwoSumF_sum xh y) +  FT2R(BPLUS xl (TwoSumF_err xh y))).
destruct (BPLUS_accurate' xl (TwoSumF_err xh y) H) as (del & A & B).
rewrite B.
pose proof TwoSumF_correct xh y H0.
replace (FT2R (TwoSumF_sum xh y)) with 
(FT2R xh + FT2R y - FT2R (TwoSumF_err xh y)).
unfold xr, yr.
destruct (TwoSumF_error xh y H0) as (del' & C & D).
rewrite C.
field_simplify_Rabs.
set (s1 := (FT2R xh * del' * del + FT2R y * del' * del + FT2R xl * del)).
set (s2 := (FT2R xh + FT2R y  + FT2R xl) * del).
set (d:= (FT2R xh + FT2R y + FT2R xl)).
refine (Rle_trans _ (Rabs (s2/d)) _ _ _). 

have Hf : generic_format radix2 (FLX_exp (fprec t)) (FT2R y).
{ apply (@generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t)). unfold FT2R.
  apply (Binary.generic_format_B2R (fprec t) (femax t) y). }  
destruct (@DWPlusFP_correct (fprec t) (fprec_gt_one t) choice eq_refl 
  Hp3 (FT2R xh) (FT2R xl) (FT2R y) Hf) => // .
apply Rle_trans with (relative_errorDWFP (fprec t) choice (FT2R xh) (FT2R xl) (FT2R y)) => //.
apply Req_le.
rewrite /relative_error_DWPlusFP/relative_errorDWFP. 
pose proof DWPlusFP_eq_no_underflow. rewrite /F2Rp/DWPlus.DWPlusFP in H1.
repeat f_equal.
all: by rewrite H1.
Qed.


Lemma DWPlusFP_0 : xr + yr = 0 -> zh + zl = 0. Admitted.

Theorem relative_errorDWPlusFP_correct' : 
  exists del, (zh + zl) = (xr + yr) * (1 + del) /\
    Rabs del <= 2 * u ^ 2.
Proof.
have Hf : generic_format radix2 (FLX_exp (fprec t)) (FT2R y).
{ apply (@generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t)). unfold FT2R.
  apply (Binary.generic_format_B2R (fprec t) (femax t) y). }  
destruct (@DWPlusFP_correct (fprec t) (fprec_gt_one t) choice eq_refl 
  Hp3 (FT2R xh) (FT2R xl) (FT2R y) Hf) => // .
destruct (Req_dec (xr + yr) 0) as [Hx0|Hx0].
{ exists 0; rewrite Hx0; split; [field_simplify; 
  now rewrite DWPlusFP_0 | now rewrite Rabs_R0; nra]. } 
exists (((zh + zl) - (xr  + yr)) / (xr  + yr)); split. 
{ now field_simplify. } 
now apply  relative_errorDWPlusFP_correct.
Qed.

Theorem DW_plus_FP_error :
  exists del, 
   zh + zl = (xr + yr) * (1 + del) /\
   Rabs del <= /2 * bpow radix2 (-fprec t + 1). 
Proof.
subst zh zl. move : FIN.
rewrite /DWPlus.DWPlusFP/DWPlusFP.
replace ( TwoSumF xh y) with ( TwoSumF_sum xh y,  TwoSumF_err xh y) => //.
replace (Fast2Sum (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y))) with
  (Fast2Sum_sum (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y)), 
  Fast2Sum_err (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y))) => //.
rewrite /fst/snd. intros.
destruct FIN0 as (FINm & FINp). clear FIN. 
unfold Fast2Mult_mul, Fast2Mult_err, fst, snd in *; simpl in *.
assert (Binary.is_finite _ _ 
            (BPLUS xl (TwoSumF_err xh y)) = true) by admit.
assert (is_finite_p (TwoSumF xh y )) by admit.
replace (  FT2R
    (Fast2Sum_sum (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y))) +
  FT2R
    (Fast2Sum_err (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y)))) with 
(FT2R (TwoSumF_sum xh y) +  FT2R(BPLUS xl (TwoSumF_err xh y))).
destruct (BPLUS_accurate' xl (TwoSumF_err xh y) H) as (del & A & B).
rewrite B.
pose proof TwoSumF_correct xh y H0.
replace (FT2R (TwoSumF_sum xh y)) with 
(FT2R xh + FT2R y - FT2R (TwoSumF_err xh y)).
unfold xr, yr.
destruct (TwoSumF_error xh y H0) as (del' & C & D).
rewrite C.
exists (del*del'), del; split; [now field_simplify | split].
now refine (Rle_trans _ _ _ A _); apply Req_le; rewrite /default_rel.
rewrite Rmult_1_r Rabs_mult; apply Rmult_le_compat; now try apply Rabs_pos.
now rewrite H1; field_simplify.

Admitted.

Theorem DW_plus_FP_error :
  exists d1 d2, 
   zh + zl = (FT2R xh + yr) * (1 + d1) + FT2R xl * (1 + d2) /\
   Rabs d2 <= /2 * bpow radix2 (-fprec t + 1) /\
   Rabs d1 <= (/2 * bpow radix2 (-fprec t + 1))^2 .
Proof.
subst zh zl. move : FIN.
rewrite /DWPlus.DWPlusFP/DWPlusFP.
replace ( TwoSumF xh y) with ( TwoSumF_sum xh y,  TwoSumF_err xh y) => //.
replace (Fast2Sum (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y))) with
  (Fast2Sum_sum (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y)), 
  Fast2Sum_err (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y))) => //.
rewrite /fst/snd. intros.
destruct FIN0 as (FINm & FINp). clear FIN. 
unfold Fast2Mult_mul, Fast2Mult_err, fst, snd in *; simpl in *.
assert (Binary.is_finite _ _ 
            (BPLUS xl (TwoSumF_err xh y)) = true) by admit.
assert (is_finite_p (TwoSumF xh y )) by admit.
replace (  FT2R
    (Fast2Sum_sum (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y))) +
  FT2R
    (Fast2Sum_err (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y)))) with 
(FT2R (TwoSumF_sum xh y) +  FT2R(BPLUS xl (TwoSumF_err xh y))).
destruct (BPLUS_accurate' xl (TwoSumF_err xh y) H) as (del & A & B).
rewrite B.
pose proof TwoSumF_correct xh y H0.
replace (FT2R (TwoSumF_sum xh y)) with 
(FT2R xh + FT2R y - FT2R (TwoSumF_err xh y)).
unfold xr, yr.
destruct (TwoSumF_error xh y H0) as (del' & C & D).
rewrite C.
exists (del*del'), del; split; [now field_simplify | split].
now refine (Rle_trans _ _ _ A _); apply Req_le; rewrite /default_rel.
rewrite Rmult_1_r Rabs_mult; apply Rmult_le_compat; now try apply Rabs_pos.
now rewrite H1; field_simplify.

Admitted. *)

Hypothesis FINA : is_finite_p (TwoSumF xh y) (* should follow from FIN *).
Hypothesis FINB : Binary.is_finite _ _ (BPLUS xl (TwoSumF_err xh y)) = true (* should follow from FIN *).
Hypothesis Hp3 : (3 <= (fprec t))%Z.
Hypothesis DW  :   DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl).
Hypothesis HUF1 :   bpow radix2 ((@DDModels.emin t) + fprec t - 1) <=
  Rabs (FT2R (TwoSumF_sum xh y) + FT2R (BPLUS xl (TwoSumF_err xh y))).
Hypothesis HUF2 : bpow radix2 ((@DDModels.emin t) + fprec t - 1) <=
  Rabs (FT2R xl + FT2R (TwoSumF_err xh y)).
Hypothesis HUF3 : bpow radix2 ((@DDModels.emin t) + fprec t - 1) <= Rabs (FT2R xh + FT2R y).
Hypothesis Hle  : Rabs (FT2R (BPLUS xl (TwoSumF_err xh y))) <= Rabs (FT2R (TwoSumF_sum xh y)).


Theorem DWPlusFP_eq_no_underflow :
  DWPlus.DWPlusFP (fprec t) choice (FT2R xh) (FT2R xl) (FT2R y) = F2Rp (DWPlusFP xh xl y).
Proof.
move : FIN. move => []. 
pose proof round_FLT_FLX radix2 (@DDModels.emin t).
move => FIN1 FIN2. rewrite /DWPlus.DWPlusFP/DWPlusFP.
replace ( TwoSumF xh y) with ( TwoSumF_sum xh y,  TwoSumF_err xh y) => //.
replace (Fast2Sum (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y))) with
  (Fast2Sum_sum (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y)), 
  Fast2Sum_err (TwoSumF_sum xh y) (BPLUS xl (TwoSumF_err xh y))) => //.
rewrite -FastTwoSumEq_no_underflow => //.
{ rewrite /TwoSum_err/TwoSum_sum TwoSumEq_no_underflow/fst/snd => //. 
f_equal. 
BPLUS_correct t xl (TwoSumF_err xh y). 
replace ( TwoSumF xh y) with ( TwoSumF_sum xh y,  TwoSumF_err xh y) => //.
rewrite /F2Rp/FT2R/fst/snd -H => //=. }  
Qed. 

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 
Notation u   := (bpow Zaux.radix2 (- fprec t)).

Definition relative_error_DWPlusFP := Rabs (((zh + zl) - (xr  + yr)) / (xr  + yr)).

Theorem relative_errorDWPlusFP_correct : relative_error_DWPlusFP <= 2 * u ^ 2.
Proof.
have Hf : generic_format radix2 (FLX_exp (fprec t)) (FT2R y).
{ apply (@generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t)). unfold FT2R.
  apply (Binary.generic_format_B2R (fprec t) (femax t) y). }  
destruct (@DWPlusFP_correct (fprec t) (fprec_gt_one t) choice eq_refl 
  Hp3 (FT2R xh) (FT2R xl) (FT2R y) Hf) => // .
apply Rle_trans with (relative_errorDWFP (fprec t) choice (FT2R xh) (FT2R xl) (FT2R y)) => //.
apply Req_le.
rewrite /relative_error_DWPlusFP/relative_errorDWFP. 
pose proof DWPlusFP_eq_no_underflow. rewrite /F2Rp/DWPlus.DWPlusFP in H1.
repeat f_equal.
all: by rewrite H1.
Qed.


Lemma DWPlusFP_0 : xr + yr = 0 -> zh + zl = 0. Admitted.

Theorem relative_errorDWPlusFP_correct' : 
  exists del, (zh + zl) = (xr + yr) * (1 + del) /\
    Rabs del <= 2 * u ^ 2.
Proof.
have Hf : generic_format radix2 (FLX_exp (fprec t)) (FT2R y).
{ apply (@generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t)). unfold FT2R.
  apply (Binary.generic_format_B2R (fprec t) (femax t) y). }  
destruct (@DWPlusFP_correct (fprec t) (fprec_gt_one t) choice eq_refl 
  Hp3 (FT2R xh) (FT2R xl) (FT2R y) Hf) => // .
destruct (Req_dec (xr + yr) 0) as [Hx0|Hx0].
{ exists 0; rewrite Hx0; split; [field_simplify; 
  now rewrite DWPlusFP_0 | now rewrite Rabs_R0; nra]. } 
exists (((zh + zl) - (xr  + yr)) / (xr  + yr)); split. 
{ now field_simplify. } 
now apply  relative_errorDWPlusFP_correct.
Qed.


End AccuracyDWPlusFP.

