Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common.
Require Import DWPlusFLT DDModels Fast2Mult_acc TwoSum_acc.
Require Import F2SumFLT.
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
destruct FIN0 as (FINm & FINp); clear FIN. 
unfold Fast2Mult_mul, Fast2Mult_err, fst, snd in *; simpl in *.
split; simpl; auto.
{ move: FINm. rewrite /Fast2Sum_sum/fst/Fast2Sum .
  set (g:= (BPLUS xl (TwoSumF_err xh y))). move => Hg.
  destruct (TwoSumF_sum xh y); destruct g; auto.
  destruct s; destruct s0; auto. }  
 move: FINm. rewrite /Fast2Sum_sum/fst/Fast2Sum .
  set (g:= (TwoSumF_sum xh y)). move => Hg.
  destruct (TwoSumF_err xh y); destruct g; destruct xl; auto;
  destruct s; destruct s0; destruct s1; auto.   
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


(* check that the necessary ordering for Fast2Sum holds *)
Lemma Fast2Sum_CorrectDWPlusFP : 
  Rabs (FT2R v) <= Rabs (FT2R sh).
Proof.
have Hy:  Rabs (FT2R y) <=  Rabs (FT2R xh) \/ Rabs (FT2R xh) <=  Rabs (FT2R y). 
destruct (Rle_or_lt (Rabs (FT2R y)) (Rabs (FT2R xh))). { by left. } right. nra.  
destruct Hy as [Hy | Hy].
apply Rabs_le_inv in Hy.
destruct (Rlt_or_le (FT2R xh) 0) as [Hx|Hx].
apply Rabs_left in Hx; rewrite Hx Ropp_involutive in Hy.
destruct (Rle_or_lt (FT2R y) (- Rabs (FT2R xh) /2)) as [Hy2|Hy2].
{ assert (FT2R sh = FT2R xh + FT2R y).
  {  pose proof Sterbenz.sterbenz radix2 (SpecFloat.fexp (fprec t) (femax t))
 (FT2R y) (- (FT2R xh)).
  subst sh; rewrite /TwoSumF/fst.
  pose proof FIN1.
  destruct H0 as (FIN1 &  FIN2).
  simpl in FIN1; BPLUS_correct t xh y.
assert (FT2R sl = 0). 
Admitted.

End CorrectDWPlusFP.

Section AccuracyDWPlusFP_aux.

Variables (xh xl y : ftype t).
Hypothesis  xE : double_word xh xl.
Let zh := (FT2R (fst (DWPlusFP xh xl y))).
Let zl := (FT2R (snd (DWPlusFP xh xl y))).
Let xr := (FT2R xh + FT2R xl).
Let yr := (FT2R y).
Let sl := snd (TwoSumF xh y).
Let sh := fst (TwoSumF xh y).
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

Fact null_sl_aux
  (sl0: FT2R sl = 0):  FT2R v =  FT2R xl.
Proof.
subst v. 
pose proof FIN2 xh xl y FIN as H1. 
fold sl in H1. unfold p in *. 
BPLUS_correct t xl sl. unfold FT2R in sl0.
rewrite sl0 Rplus_0_r round_generic; auto.
apply Binary.generic_format_B2R. 
Qed.

Fact null_sl 
  (sl0: FT2R sl = 0):  errorDWFP = 0.
Proof.
pose proof FIN1 xh xl y FIN as H. 
pose proof FIN2 xh xl y FIN as H1. 
pose proof FIN3 xh xl y FIN as H2.
fold sl in H1. unfold p in *. 
have vE: FT2R v =  FT2R xl; [by apply: null_sl_aux | ].
have xhye : (FT2R xh + FT2R y) = rnd (FT2R xh + FT2R y).
{ move: (TwoSumF_correct xh y (FIN1 xh xl y FIN)); rewrite sl0. 
rewrite /TwoSumF_sum/fst/TwoSumF.
BPLUS_correct t xh y. rewrite /rnd; intros. 
symmetry in TwoSumF_correct. 
by apply Rminus_diag_uniq_sym in TwoSumF_correct. }  
case:(Req_dec (FT2R xl) 0)=> xl0.
{ have Hv: (FT2R v = 0). 
  { subst v. BPLUS_correct t xl sl.
  unfold FT2R in xl0, sl0; rewrite xl0 sl0 => //=.
  by rewrite Rplus_0_l round_0. }  

 
rewrite /errorDWFP xl0.
subst zh.
rewrite /DWPlusFP/fst.
move: FIN. 
rewrite /is_finite_p/DWPlusFP.
replace (TwoSumF xh y) with 
  (TwoSumF_sum xh y, sl) => //= FIN1.
destruct FIN1 as (FIN1 & FIN2).
subst v. move: Hv. 
set (s:= (BPLUS xl sl)) in *.
BPLUS_correct t (TwoSumF_sum xh y) s.
subst s.
BPLUS_correct t xl sl => H0.
rewrite H0. clear H10 H7.

have Hzl : (zl = 0).
{ subst zl. rewrite /snd/DWPlusFP.
replace (TwoSumF xh y) with 
  (TwoSumF_sum xh y, sl) => //=.
set (b:=(BMINUS (BPLUS (TwoSumF_sum xh y) (BPLUS xl sl)) 
  (TwoSumF_sum xh y))) in *.
BMINUS_correct t (BPLUS xl sl) b.
unfold FT2R in vE, xl0. rewrite vE xl0.
rewrite <- (round_0 radix2
  (SpecFloat.fexp p (femax t)) 
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)).
f_equal.
rewrite !round_0 Rminus_0_l -Ropp_0; f_equal. 
subst b.
set (b:= (BPLUS (TwoSumF_sum xh y) (BPLUS xl sl))) in *.
BMINUS_correct t b (TwoSumF_sum xh y).
move : H0.
rewrite <- (round_0 radix2
  (SpecFloat.fexp p (femax t)) 
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)) => H0.
f_equal. subst b.
set (k :=(BPLUS xl sl)) in *.
BPLUS_correct t (TwoSumF_sum xh y) k.
clear H18 H15 H12.
apply Rminus_diag_eq.
replace (Binary.B2R _ _ (TwoSumF_sum xh y)) with
  (rnd (FT2R xh + FT2R y)).
unfold rnd at 2.
f_equal. set (x:= rnd (FT2R xh + FT2R y)).
rewrite xhye. subst x.
match goal with |- context [_ + ?a = _] => 
replace a with 0; try nra end.
move : (TwoSum_exact xh y H xhye).
move => He. 
move: (TwoSumF_correct xh y H). rewrite He.
move => He2.
rewrite xhye in He2.
unfold FT2R in He2. 
symmetry in He2.
by apply Rminus_diag_uniq. } 
rewrite Hzl.
field_simplify_round.
field_simplify.
admit. } 

case:(Req_dec (FT2R xh + FT2R y) 0)=> xhy0.
{ have sh0: FT2R (fst (TwoSumF xh y)) = 0.
  { rewrite /TwoSumF/fst. BPLUS_correct t xh y.
    unfold FT2R in xhy0. by rewrite xhy0 round_0. }  

rewrite /errorDWFP. subst zh zl. 
rewrite /fst/snd/DWPlusFP.
move : sh0.
move: (TwoSum0 xh y H xhy0).
replace (TwoSumF xh y) with 
  ((fst (TwoSumF xh y)), sl) => //= sh0 s0.

admit. } 

rewrite /errorDWFP. subst zh zl. rewrite /DWPlusFP.
replace (TwoSumF xh y) with 
  (TwoSumF_sum xh y, sl).
set (a:= (TwoSumF_sum xh y)).
set (b:=  (BPLUS xl sl)).  
replace (Fast2Sum a b) with 
  (Fast2Sum_sum a b, Fast2Sum_err a b) => //=.
replace (FT2R (Fast2Sum_sum a b) + FT2R (Fast2Sum_err a b))
  with (FT2R a + FT2R b). subst a b. 
rewrite TwoSum_exact' => //. 
fold v; rewrite vE; nra.
rewrite (FastTwoSum_correct a b) => //; 
  field_simplify; try nra. 

apply Fast2Sum_CorrectDWPlusFP => //.
subst sl => //.
Admitted.

Fact null_sl_rel 
  (sl0: FT2R sl = 0):  relative_error_DWPlusFP = 0.
Proof.
rewrite rel_errorE null_sl //. by rewrite Rabs_R0 Rmult_0_l.
Qed.

Fact null_xh_rel (xh0: FT2R xh = 0): relative_error_DWPlusFP = 0.
Proof.
apply: null_sl_rel.
pose proof FIN1 xh xl y FIN. 
rewrite TwoSumF_correct //= /TwoSumF_sum/TwoSumF/fst.
pose proof FIN3 xh xl y FIN. 
BPLUS_correct t xh y. 
unfold FT2R in xh0; rewrite xh0 Rplus_0_l round_generic //; [ring | ].
apply Binary.generic_format_B2R. 
Qed.


Fact null_xhy_rel : FT2R xh + FT2R y = 0 -> relative_error_DWPlusFP = 0.
Proof. 
pose proof FIN1 xh xl y FIN as H1. 
move => H. apply TwoSum0 in H => //. move: H. 
rewrite /F2Rp. fold sl sh => H.
apply null_sl_rel; by inversion H. 
Qed.

Let fexp :=(SpecFloat.fexp p (femax t)).
Let ulp  := ulp radix2 fexp.

Lemma dw_ulp: double_word xh xl -> 
  Rabs (FT2R xl) <= /2 * ulp (FT2R xh).
Proof.
rewrite /double_word/rounded => xhe.
have -> : FT2R xl = - (rnd xr - xr).
unfold xr; rewrite /rnd -xhe; ring. 
rewrite Rabs_Ropp. refine (Rle_trans _ (/ 2 * ulp (rnd xr)) _ _ _).
  by apply: error_le_half_ulp_round.
unfold xr; rewrite /rnd -xhe; lra.
Qed.

Theorem FLT_ulp_pos : forall x, (x <> 0%R) ->(0 < ulp x)%R.
Proof.
intros x xneq0; rewrite /ulp ulp_neq_0; trivial; apply bpow_gt_0.
Qed.

Hypothesis ZNE : choice = fun n => negb (Z.even n).

Lemma rxpu2pow (x z : ftype t) :   
  (Bayleyaux.is_pow radix2 (FT2R x))-> 
  Rabs (FT2R z) <=  /4 * (ulp (FT2R x)) -> rnd (FT2R x + FT2R z) = FT2R x.
Proof.
move=> xpow  zb.
wlog xpos: x xpow z zb / 0 <= FT2R x.
  move=> Hwlog.
  case:(Rle_lt_dec 0 (FT2R x)) => x0.
    apply:Hwlog=>//.
  suff:  -rnd (FT2R x + FT2R z) = - FT2R x by lra.
  rewrite  -round_NE_opp  Ropp_plus_distr !FT2R_opp.
  apply: Hwlog; try lra.
    case: xpow => e xe; exists e; by rewrite -FT2R_opp Rabs_Ropp.
    by rewrite -!FT2R_opp Rabs_Ropp /ulp ulp_opp.
    rewrite -!FT2R_opp; nra.
  have xer: FT2R x = rnd (FT2R x).
    rewrite /FT2R; symmetry; apply round_generic. admit.
   by apply Binary.generic_format_B2R.
case: xpos => x0; last first.
case:xpow => e xe.
move:xe; rewrite -x0 Rabs_R0; move:(bpow_gt_0 radix2 e); lra.
case:(Rle_lt_dec 0 (FT2R z))=> xl0.
apply:Rle_antisym.
  apply:round_N_le_midp =>//.
   by apply Binary.generic_format_B2R.
  rewrite /succ  Rle_bool_true; try lra.
  case/Rabs_le_inv : zb=> h1 h2. 
  fold fexp (ulp (FT2R x)).
  suff : 0 < ulp (FT2R x) by lra.
  apply: FLT_ulp_pos; lra.
rewrite {1} xer; apply/round_le; lra.
rewrite -Rabs_Ropp Rabs_pos_eq // in zb; last by lra.
 have: FT2R x - / 4 * ulp (FT2R x)  <= FT2R x + FT2R z  by lra.
move/(round_le radix2 fexp (Znearest choice)).
have ->:  round radix2 fexp (Znearest choice) 
  (FT2R x - / 4 * ulp(FT2R x)) = FT2R x.
case:(xpow)=> e xe.
destruct (Rle_or_lt
  (bpow radix2 (((SpecFloat.emin p (femax t)) + p) - 1)) 
  ( FT2R x)).
destruct (Rle_or_lt
  (bpow radix2 (((SpecFloat.emin p (femax t)) + p) - 1)) 
  (Rabs ((FT2R x) - ((/ 4) * (ulp (FT2R x)))))).
{ rewrite round_FLT_FLX => //.
  rewrite Rabs_pos_eq // in xe; try lra.
  rewrite /ulp xe ulp_neq_0. rewrite cexp_FLT_FLX.
  rewrite  (cexp_fexp_pos radix2 (FLX_exp p) (bpow radix2 e) (e + 1)).
  have ->: (FLX_exp p (e + 1) = e +1  -p)%Z by rewrite /fexp.
  have ->: (bpow radix2 e) - / 4 * bpow radix2 (e + 1 - p) = 
      (1 - /4 * bpow radix2 (1 - p)) * bpow radix2 e.
    rewrite !bpow_plus; field.
  rewrite Bayleyaux.round_bpow  !bpow_plus /= IZR_Zpower_pos /=.
  have ->:  / 4 * (2 * 1 * bpow radix2 (- p)) =  bpow radix2 (- p) / 2 by field.
  rewrite Bayleyaux.r1mu2 => //; try ring. 
  apply fprec_gt_one. 
  split. apply bpow_le; lia. 
  apply bpow_lt; lia.
  refine (Rle_trans _ _ _ H _). 
  rewrite xe; apply RRle_abs. nra. }
{      Search   (round _ _ _ _ = round _ _ (FIX_exp _) _).
  rewrite round_FLT_FLX => //.
  rewrite Rabs_pos_eq // in xe; try lra.
  rewrite /ulp xe ulp_neq_0. rewrite cexp_FLT_FLX.
  rewrite  (cexp_fexp_pos radix2 (FLX_exp p) (bpow radix2 e) (e + 1)).
  have ->: (FLX_exp p (e + 1) = e +1  -p)%Z by rewrite /fexp.
  have ->: (bpow radix2 e) - / 4 * bpow radix2 (e + 1 - p) = 
      (1 - /4 * bpow radix2 (1 - p)) * bpow radix2 e.
    rewrite !bpow_plus; field.
  rewrite Bayleyaux.round_bpow  !bpow_plus /= IZR_Zpower_pos /=.
  have ->:  / 4 * (2 * 1 * bpow radix2 (- p)) =  bpow radix2 (- p) / 2 by field.
  rewrite Bayleyaux.r1mu2 => //; try ring. 
  apply fprec_gt_one. 
  split. apply bpow_le; lia. 
  apply bpow_lt; lia.
  refine (Rle_trans _ _ _ H _). 
  rewrite xe; apply RRle_abs. nra. }
{ 
  rewrite xe /ulp ulp_bpow. rewrite /fexp/SpecFloat.fexp//=.
Admitted.


Lemma  rulp2p' (x w z : ftype t) : 
  Rabs (FT2R z) <= /2  * ulp (FT2R x) -> ulp (FT2R x) < ulp (FT2R w) ->  
  FT2R x <> 0 -> FT2R w <> 0 ->
  rnd (FT2R w + FT2R z) = FT2R w.
Proof.
move=> rxlu uxuy xn0 yn0 .
have h: Rabs (FT2R z) <= / 4 * ulp (FT2R w).
  apply:(Rle_trans _ (/ 2 * ulp (FT2R x)))=>//.
  suff: ulp (FT2R x) <= / 2 * ulp (FT2R w) by lra.
  move: uxuy.  rewrite /ulp !ulp_neq_0 => //.
  move/lt_bpow/Zlt_le_succ; rewrite -Z.add_1_r.
  move/(bpow_le radix2); rewrite bpow_plus.
  have ->: (bpow radix2 1 = 2) by [].
  lra.
case:(Bayleyaux.is_pow_dec radix2 (FT2R w))=> hw.
  rewrite  rxpu2pow => //.
 rewrite rulp2p //; lra.
Qed.

End AccuracyDWPlusFP_aux.

Section AccuracyDWPlusFP.

Notation p := (fprec t).
Notation u := (bpow Zaux.radix2 (- p)).
Let fexp :=(SpecFloat.fexp p (femax t)).
Let ulp  := ulp radix2 fexp.

Theorem relative_errorDWPlusFP_correct xh xl y: 
  forall (DW : double_word xh xl)
         (FIN: is_finite_p (DWPlusFP xh xl y)),
  relative_error_DWPlusFP xh xl y <= 2 * u^2.
Proof.
have rn_sym:= (round_opp radix2 (SpecFloat.fexp (fprec t) (femax t))
   (Generic_fmt.Znearest choice)).
move => DW FIN. 
have boundDWFP_ge_0 : 0 <= 2*u^2 by rewrite /u; move: (bpow_ge_0 radix2 (-p)); nra.
case:(Req_dec (FT2R xh) 0)=> hxh0.
{ rewrite /relative_error_DWPlusFP; 
pose proof null_xh_rel xh xl y DW FIN hxh0. 
unfold relative_error_DWPlusFP in H.
by rewrite H. } 

case: (Req_dec  (FT2R xh +  FT2R y) 0)=> xhy0.
  apply (null_xhy_rel xh xl y) in xhy0 => //; by rewrite xhy0.

clear hxh0.
wlog xhy : y xh xhy0 DW FIN /  Rabs (FT2R y) <= Rabs (FT2R xh).
  move=> Hwlog.
  case:(Rle_lt_dec (Rabs (FT2R y)) (Rabs (FT2R xh) )) => absyxh.
    by apply: ( Hwlog y xh)=>//. 
  have xel:= (dw_ulp  xh xl DW).
  have yn0: FT2R y <> 0.
    by move=>y0; move:  absyxh; rewrite y0 Rabs_R0; move:(Rabs_pos (FT2R xh)); lra.
  have xluy: ulp (FT2R xh) <=  ulp (FT2R y). apply ulp_le; try nra. admit. admit.
  case:  xluy=> xluy.
    have yE: FT2R y = rnd (FT2R y + FT2R xl)
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

