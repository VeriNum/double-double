Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common.
Require Import Fast2Mult_acc TwoSum_acc DWPlus_acc.
Require Import DWPlus DDModels.
From Flocq Require Import Pff2Flocq Core.

Require Import mathcomp.ssreflect.ssreflect.

(* for choice functions : choice = fun x0 : Z => negb (Z.even x0) *)
Require Import Logic.FunctionalExtensionality.

Section AccuracyDWPlusDW.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Let ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 
Notation u   := (bpow Zaux.radix2 (- fprec t)).



Lemma Fast2Sum_CorrectDWPlusDW1 
  (xh xl yh yl: ftype t) 
         (DWx: double_word xh xl)(DWy: double_word yh yl) :
  is_finite (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl)) = true -> 
  is_finite_p (TwoSumF xh yh) -> 
  FT2R xh + FT2R yh <> 0 -> 
  Rabs (FT2R (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl))) 
              <= Rabs (FT2R (TwoSumF_sum xh yh)).
Proof.
intros.
case:(Rle_lt_dec (Rabs (FT2R yh)) (Rabs (FT2R xh)) )=> absyxh.
{ case:(Req_dec (FT2R xh) 0)=> x0. 
BPLUS_correct t (TwoSumF_err xh yh) (TwoSumF_sum xl yl);
  rewrite !B2R_float_of_ftype.  
replace (FT2R (TwoSumF_err xh yh)) with 0. rewrite Rplus_0_l.
have xl0: FT2R xl = 0.
move : DWx. rewrite /double_word x0. move => DWx.
rewrite DWx Rplus_0_l /rounded round_generic. 
reflexivity. admit.
rewrite /TwoSumF_sum/TwoSumF/fst.
have HF : is_finite (BPLUS xl yl) = true by admit.
rewrite round_generic.
BPLUS_correct t xl yl;
  rewrite !B2R_float_of_ftype xl0.  
have HF1 : is_finite (BPLUS xh yh) = true by admit.
BPLUS_correct t xh yh;
  rewrite !B2R_float_of_ftype x0. 
rewrite !Rplus_0_l !round_generic.
apply DWord_defs.dw_le => //.
move: H1; rewrite x0; nra. admit. admit. admit.
pose proof TwoSum0 xh yh H0 x0. 
move: H2. rewrite /F2Rp. move => H2.
inversion H2. rewrite /TwoSumF_err/TwoSumF/snd.
rewrite H8 => //.

BPLUS_correct t (TwoSumF_err xh yh) (TwoSumF_sum xl yl).
pose proof @TwoSumEq_FLT NANS t _ _ _ H0 as H2;
unfold F2Rp in H2.
have FIN2: is_finite_p (TwoSumF xl yl) by admit.
pose proof @TwoSumEq_FLT NANS t _ _ _ FIN2 as H3;
unfold F2Rp in H3.
rewrite !B2R_float_of_ftype.
replace (FT2R (TwoSumF_err xh yh))
  with (TwoSum_err (fprec t) choice (FT2R xh) (FT2R yh)) by
  inversion H2 => //.
replace (FT2R (TwoSumF_sum xh yh))
  with (TwoSum_sum (fprec t) choice (FT2R xh) (FT2R yh)) by
inversion H2 => //.
replace (FT2R (TwoSumF_sum xl yl))
  with (TwoSum_sum (fprec t) choice (FT2R xl) (FT2R yl)) by
inversion H3 => //.
clear H3 H2 H5 H6 H7.

wlog xhy : xh xl yh yl  DWx DWy H H0 H1 absyxh x0 FIN2  / 0 <  FT2R xh.
  move=> Hwlog.
  case: (Rle_lt_dec 0 (FT2R xh))=> xh0.
    apply:Hwlog => //; lra.

specialize (Hwlog (BOPP xh) (BOPP xl) (BOPP yh) (BOPP yl)).
move: Hwlog.  
rewrite /BOPP !FT2R_ftype_of_float !Binary.B2R_Bopp 
  !B2R_float_of_ftype !TwoSum_sum_asym.
rewrite !TwoSum_err_asym. rewrite -!Ropp_plus_distr.
rewrite !round_NE_opp  !Rabs_Ropp. move => Hwlog.
apply Hwlog => //; clear Hwlog; try nra. 
admit. admit. admit. admit. admit.
1-3: admit.

wlog [xh1 xh2]:  xh xl yh yl DWx DWy H H0 H1 absyxh x0 FIN2 xhy
             / 1 <= FT2R xh  <= 2-2*u.
  move=> Hwlog.
apply dw_word_DWdouble in DWx.
pose proof Fxh DWx as Fxh.
  case: (scale_generic_12 Fxh xhy)=> exh Hxhs.
have powgt0 := (bpow_gt_0 radix2 exh).
  rewrite -(relative_errorDWDWS exh) //; try lra.
  apply:Hwlog; try lra.
    + split ; first by split;apply:formatS.
      rewrite -Rmult_plus_distr_r round_bpow.
      by case:DWx=> _ {1}->.
    + split ; first by split;apply:formatS.
      rewrite -Rmult_plus_distr_r round_bpow.
      by case:DWy=> _ {1}->.
    + rewrite !Rabs_mult  (Rabs_pos_eq (pow _)); try lra.
      by apply: Rmult_le_compat_r ; lra.
  rewrite -!Rmult_plus_distr_r.
  by apply: Rmult_integral_contrapositive_currified; lra.




Search (- _ + - _).
Search (TwoSum_err _ _ (-_)).

  apply: Hwlog => //; try lra; try apply: DW_asym => //.
  apply DWx. apply DWy. apply H. apply H0. apply FIN2.
  rewrite -rel_errorDWDW_Sym =>//.

    case:(Hwlog (BOPP xh) (BOPP xl) (BOPP yh) (BOPP yl)); 
  try apply:generic_format_opp =>//; try lra.
admit. admit.

  case:(DWx)=>[[Fxh Fxl] hx].
  case:(DWy)=>[[Fyh Fyl] hy].
  rewrite -rel_errorDWDW_Sym =>//.
  apply: Hwlog; try lra; try apply: DW_asym => //.
  by rewrite !Rabs_Ropp.
(*AEK pos hyp sat*)
destruct (Req_dec (xh + xl + (yh + yl)) 0); [exfalso|nra].
apply Rplus_opp_r_uniq in H.
have Hr: (rnd_p (yh + yl) = rnd_p (-(xh + xl))) by f_equal.
apply s0. rewrite hx hy. rewrite Hr.
rewrite (rnd_p_sym _ _ choiceP). nra.
(* end AEK *)
wlog [xh1 xh2]:  xh xl yh yl DWx DWy (* xyn0 *) xhy s0 x0 xhpos
             / 1 <= xh  <= 2-2*u.
  move=> Hwlog.
  case:(DWx)=>[[Fxh Fxl] hx].  
  case:(DWy)=>[[Fyh Fyl] hy].
  case: (scale_generic_12 Fxh xhpos)=> exh Hxhs.
  have powgt0 := (bpow_gt_0 two exh).
  rewrite -(relative_errorDWDWS exh) //; try lra.
  apply:Hwlog; try lra.
    + split ; first by split;apply:formatS.
      rewrite -Rmult_plus_distr_r round_bpow.
      by case:DWx=> _ {1}->.
    + split ; first by split;apply:formatS.
      rewrite -Rmult_plus_distr_r round_bpow.
      by case:DWy=> _ {1}->.
    + rewrite !Rabs_mult  (Rabs_pos_eq (pow _)); try lra.
      by apply: Rmult_le_compat_r ; lra.
  rewrite -!Rmult_plus_distr_r.
  by apply: Rmult_integral_contrapositive_currified; lra.
(*AEK pos hyp sat*)
destruct (Req_dec (xh + xl + (yh + yl)) 0); [exfalso|nra].
apply Rplus_opp_r_uniq in H.
have Hr: (rnd_p (yh + yl) = rnd_p (-(xh + xl))) by f_equal.
apply s0. rewrite hx hy. rewrite Hr.
rewrite (rnd_p_sym _ _ choiceP). nra.
(* *)
by  case:( DWPlusDW_relerr_bound_pre Hp3 DWx DWy).

Qed.
Variables (xh xl yh yl : ftype t).


Let emin :=  (@DDModels.emin t).

Hypothesis  xE : double_word xh xl.
Hypothesis  yE : double_word yh yl.
Hypothesis Hp3 : (3 <= fprec t)%Z.

(* Let xhr := (FT2R xh).
Let xlr := (FT2R xl).
Let yhr := (FT2R yh).
Let ylr := (FT2R yl). *)

(* Let zh := (FT2R (fst (AccurateDWPlusDW xh xl yh yl))).
Let zl := (FT2R (snd (AccurateDWPlusDW xh xl yh yl))). *)

(* Definition relative_error_DWPlusDW := 
  Rabs ((zh + zl - (xhr + xlr + yhr + ylr)) / (xhr + xlr + yhr + ylr)).
Definition errorDWDW := ((xhr + xlr + yhr + ylr) - (zh + zl)).
*)
Local Notation p := (fprec t).
Definition rnd := 
  (round radix2 (SpecFloat.fexp (fprec t) (femax t)) (Generic_fmt.Znearest choice)). 

(* connect paper proofs to local defs *)
(* Fact rel_errorE: relative_error_DWPlusDW = 
    Rabs errorDWDW * (Rabs (/( xhr + xlr + yhr + ylr))).
Proof.
rewrite /relative_error_DWPlusDW  
  /Rdiv !Rabs_mult -Ropp_minus_distr Rabs_Ropp //.
Qed.
 *)
Fact FIN1 : 
is_finite_p (TwoSumF xl yl). Admitted.

Fact FIN2 : 
is_finite_p (TwoSumF xh yh). Admitted.

Fact FIN3 :
is_finite_p 
  (Fast2Sum (TwoSumF_sum xh yh) 
    (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl))). Admitted. 

Lemma Fast2Sum_CorrectDWPlusDW1 : 
  is_finite (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl)) = true -> 
  is_finite_p (TwoSumF xh yh) -> 
  FT2R xh + FT2R yh <> 0 -> 
  Rabs (FT2R (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl))) 
              <= Rabs (FT2R (TwoSumF_sum xh yh)).
Proof.
intros. clear H H0 H1 xE yE.
wlog xhy : xh xl yh yl
 xE yE H H0 H1  /  Rabs (FT2R yh) <= Rabs (FT2R xh).
  move=> Hwlog.



intros FIN1 FINp H0. 

have Hv: Valid_exp fexp by apply FLT.FLT_exp_valid.
have Hexp: Exp_not_FTZ fexp by apply  fexp_not_FTZ.
have Hv2: 
Valid_rnd (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
  by apply BinarySingleNaN.valid_rnd_round_mode.
have Ha: generic_format radix2 fexp (FT2R xh) by
  rewrite -!B2R_float_of_ftype; apply Binary.generic_format_B2R. 
have Hb: generic_format radix2 fexp (FT2R yh) by 
  rewrite -!B2R_float_of_ftype; apply Binary.generic_format_B2R. 
have Hc: generic_format radix2 fexp (FT2R xl) by 
  rewrite -!B2R_float_of_ftype; apply Binary.generic_format_B2R. 
have Hd: generic_format radix2 fexp (FT2R yl) by 
  rewrite -!B2R_float_of_ftype; apply Binary.generic_format_B2R. 
have Hrnd: rounded t (FT2R xh + FT2R yh) <> 0.
rewrite /rounded; apply Plus_error.round_plus_neq_0 => //.


(* cases on the higher order term*)
case:(Req_dec (FT2R xh) 0)=> hxh0.
{ pose proof TwoSum0 xh yh FINp hxh0 as H.
  BPLUS_correct t (TwoSumF_err xh yh) (TwoSumF_sum xl yl); clear H5.
  inversion H. rewrite /fst/snd/TwoSumF B2R_float_of_ftype.
  rewrite H3 Rplus_0_l.
  have H0l : FT2R xl = 0.
  { move: xE. rewrite /double_word hxh0 => DWx.
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
  rewrite /TwoSumF_sum/fst/TwoSumF. 
  have FIN2: is_finite (BPLUS xl yl) = true. admit.  
  BPLUS_correct t xl yl.
  rewrite !B2R_float_of_ftype H2 H0l Rplus_0_l.
  rewrite !round_generic. apply DWord_defs.dw_le => //.
  by rewrite hxh0 Rplus_0_l in H0.
  all: rewrite -B2R_float_of_ftype;
   apply Binary.generic_format_B2R. } 

(* facts *)
have FIN3: is_finite (BPLUS xh yh) = true.
destruct FIN2. simpl in H => //.
have Hp0 : Prec_gt_0 (fprec t) by apply fprec_gt_0.
have Hvd : Valid_exp fexp by apply FLT_exp_valid.
have Hrn : Valid_rnd (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) by
  apply BinarySingleNaN.valid_rnd_round_mode.
have Hxhy : generic_format radix2 fexp
  (round radix2 fexp (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) 
      (FT2R xh + FT2R yh)) by apply generic_format_round.
have Hxhy2 : generic_format radix2 fexp (FT2R (snd (TwoSumF xh yh))) by
  rewrite -!B2R_float_of_ftype; apply Binary.generic_format_B2R.
have Hxly : generic_format radix2 fexp (FT2R (fst (TwoSumF xl yl))) by
  rewrite -!B2R_float_of_ftype; apply Binary.generic_format_B2R.
have hf : (1 < fprec t)%Z by pose proof @fprec_lb t; lia.
(* end facts *)

(* cases on underflow, (xh + y) *)
(* case 1 *)
 destruct (Rlt_or_le 
  (Rabs (FT2R xh + FT2R yh))
  (bpow radix2 (emin + fprec t - 1))).
{  BPLUS_correct t (TwoSumF_err xh yh) (TwoSumF_sum xl yl). 
rewrite TwoSumF_correct /TwoSumF_sum/fst/TwoSumF.
rewrite BPLUS_UF_exact => //=. 
field_simplify_round.
rewrite round_generic. 
  have FIN2: is_finite (BPLUS xl yl) = true. admit.  
BPLUS_correct t xl yl. rewrite !B2R_float_of_ftype.
Search (Ulp.ulp _ _ ( _ + _)).
Search TwoSum_sum.
BPLUS_correct t xh yh; rewrite !B2R_float_of_ftype.

destruct (Rle_or_lt (Rabs ( (FT2R xl + FT2R yl)))
   (Rabs ( (FT2R xh + FT2R yh)))) => //. admit.

exfalso.
have: Rabs (FT2R xh + FT2R yh) < Rabs (FT2R xl + FT2R yl)


rewrite -!round_NE_abs.
apply round_le. admit. admit.
eapply Rle_trans; [apply Rabs_triang|].
eapply Rle_trans; [apply Rplus_le_compat|].

rewrite BPLUS_UF_exact => //=. 
have Hr : rounded t (Rabs (FT2R xl + FT2R xh)) <= 
    rounded t (Rabs (FT2R xl) + Rabs (FT2R xh)).
apply round_le. admit. admit. apply Rabs_triang.


ulp_FLT_le

rewrite round_generic.
suff: Rabs (FT2R xl + FT2R yl) <= Rabs (FT2R xh + FT2R yh). admit.
destruct (Rle_or_lt (Rabs ( (FT2R xl + FT2R yl)))
   (Rabs ( (FT2R xh + FT2R yh)))) => //.
exfalso.
have: Rabs (FT2R xh) + FT2R yh) < Rabs (FT2R xl + FT2R yl)

 
destruct (Rle_or_lt (Rabs (rounded t (FT2R xl + FT2R yl)))
   (Rabs (rounded t (FT2R xh + FT2R yh)))) => //.
exfalso.
destruct (Rle_or_lt (ulp (FT2R xh) /2) 
    (ulp (FT2R yh)/ 2)).
suff: ulp (FT2R yh) < ulp (FT2R yh). admit.

eapply Rle_lt_trans.
replace (ulp (FT2R yh)/2) with 
  (Rmax (ulp (FT2R yh)/2) (ulp (FT2R xh)/2)).
apply roundN_plus_ulp_FLT. admit. admit.
eapply Rlt_le_trans.
rewrite Rplus_comm. apply H1.
eapply Rle_trans with (rounded t (Rabs (FT2R xl + FT2R yl))). admit.
eapply Rle_trans. apply round_le. admit. admit.
apply Rabs_triang.
eapply Rle_trans. apply round_le. admit. admit.
eapply Rplus_le_compat.
apply DWord_defs.dw_ulp; apply xE.
apply DWord_defs.dw_ulp; apply yE.
eapply Rle_trans. apply round_le. admit. admit.
apply Rplus_le_compat_r.
replace (/ 2 * Ulp.ulp radix2 fexp (FT2R xh)) with 
   (ulp (FT2R xh) / 2) by admit.
apply H2. 
replace ((ulp (FT2R yh) / 2 + / 2 * Ulp.ulp radix2 fexp (FT2R yh)))
  with (ulp (FT2R yh)). 
rewrite round_generic.

Search Ulp.ulp generic_format.
Search ( _ + _ <= _).
DWord_defs.dw_le
rewrite -!round_NE_abs. apply round_le. admit. admit.
destruct (Rle_or_lt (Rabs (FT2R xl + FT2R yl))
   (Rabs (FT2R xh + FT2R yh))) => //.
exfalso. 
Search double_word.
Search (round _ _ _ (Rabs _ )).
{ rewrite {2}/TwoSumF_sum/fst/TwoSumF; BPLUS_correct t xh yh.
rewrite -round_NE_abs.
apply round_ge_generic. admit. admit.
apply generic_format_abs.
apply Binary.generic_format_B2R.
Search (round _ _ _ (Rabs _)).
refine (Rle_trans _ _ _ _ _ ).
apply round_ge_generic. admit. admit.


2: { rewrite /TwoSumF_sum/fst/TwoSumF; BPLUS_correct t xh yh.
Search (_ <= round _ _ _ _).
eapply round_ge_generic.
 apply roundN_plus_ulp_FLT => //. } 

BPLUS_correct t (TwoSumF_err xh yh) (TwoSumF_sum xl yl). 
rewrite TwoSumF_correct /TwoSumF_sum/fst/TwoSumF.
rewrite BPLUS_UF_exact => //=.

have xle:= (dw_ulp  xh xl DWx).
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


(*  OLD *)
rewrite /TwoSumF_sum/TwoSumF/fst/snd.
have HFIN: is_finite (BPLUS (TwoSumF_err xh yh) (BPLUS xl yl)) = true. admit.
remember (BPLUS xl yl) as f1.
remember (TwoSumF_err xh yh) as f2.
BPLUS_correct t f2 f1. clear H4.
rewrite Heqf2 Heqf1.
move: FIN; rewrite /AccurateDWPlusDW/is_finite_p; move=> [] FIN1 FIN2.
simpl in FIN1. move: FIN1.
subexpr_finite.
rewrite TwoSumF_correct => //.
rewrite /TwoSumF_sum/TwoSumF/fst.
rewrite B2R_float_of_ftype.
eapply Rle_trans.
2: BPLUS_correct t xh yh.
apply Rle_refl.
rewrite -!round_NE_abs.
apply round_le. admit. admit. (* include in auto *)
Search (_ + Ulp.ulp _ _ _).
Search DWPlus.double_word.
Search (round _ _ _ ( _ + _) = _).
Search (generic_format _ _ ( _ + _)).
Search (Ulp.ulp _ _ ( _ + _)).
generic_format_ulp
Search double_word Ulp.ulp.

Admitted.

Lemma ORD2 : 
let f  := fst (Fast2Sum (TwoSumF_sum xh yh) (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl))) in
let f0 := snd (Fast2Sum (TwoSumF_sum xh yh) (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl))) in
Rabs (FT2R (BPLUS (TwoSumF_err xl yl) f0)) <= Rabs (FT2R f).
Proof.
intros.

Qed.


Hypothesis FIN : is_finite_p (AccurateDWPlusDW xh xl yh yl). 

Lemma relative_errorDWDW_eq :
relative_errorDWDW p choice xhr xlr yhr ylr = relative_error_DWPlusDW.
Proof.
rewrite /relative_errorDWDW/relative_error_DWPlusDW.
f_equal. f_equal; try nra. f_equal; try nra.
unfold zh, zl. 
move : FIN. rewrite /AccurateDWPlusDW.
remember (TwoSum_sum _ _ xlr ylr) as f1.
remember (TwoSum_sum _ _ xhr yhr) as f2.
remember (TwoSum_err _ _ xhr yhr) as f3.
remember (TwoSum_err _ _ xlr ylr) as f4.
pose proof TwoSumEq_FLT xl yl FIN1 as H. move: H.
pose proof TwoSumEq_FLT xh yh FIN2 as H1. move: H1.
replace (TwoSumF xh yh) with (TwoSumF_sum xh yh, TwoSumF_err xh yh) => //.
replace (TwoSumF xl yl) with (TwoSumF_sum xl yl, TwoSumF_err xl yl) => //.
replace (TwoSum p choice (FT2R xl) (FT2R yl)) with
  (TwoSum_sum p choice xlr ylr, TwoSum_err p choice xlr ylr) => //.
replace (TwoSum p choice (FT2R xh) (FT2R yh)) with
  (TwoSum_sum p choice xhr yhr, TwoSum_err p choice xhr yhr) => //.
rewrite/F2Rp. move => HA HB FIN1. rewrite /fst/snd in HA, HB. 
  inversion HA; clear HA. inversion HB; clear HB.
rewrite H0 in Heqf2; clear H0.
rewrite H1 in Heqf3; clear H1.
rewrite H2 in Heqf1; clear H2.
rewrite H3 in Heqf4; clear H3.
remember (F2Sum.Fast2Sum _ _ f2 _) as f5.

pose proof FastTwoSumEq_FLT (TwoSumF_sum xh yh)
  (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl)) FIN3 Fast2Sum_CorrectDWPlusDW1. 
rewrite -Heqf2 in H.
move : Heqf5.
replace (round _ _ _ (f3 + f1))
  with (FT2R (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl))).
rewrite H /F2Rp. clear H.
move => Heqf5.
(* pose proof Fast2Sum_CorrectDWPlusFP xh yh (TwoSumF_sum xl yl). *)
remember (Fast2Sum _ (BPLUS _ _)) as Hb.
destruct Hb.
replace (round _ _ _ (f4 + snd f5)) 
  with (FT2R (BPLUS (TwoSumF_err xl yl) f0)).
simpl in Heqf5; rewrite Heqf5. destruct f5; subst.
rewrite FastTwoSumEq_FLT /F2Rp => //.

apply Fast2Sum_CorrectDWPlusDW1.

(* fold (TwoSumF_sum xh yh) in H0.
fold (TwoSumF_err xh yh) in H0. *)
set (sh:= (TwoSumF_sum xh yh)) in *.
set (sl:= (TwoSumF_err xh yh)) in *.
set (th:= (TwoSumF_sum xl yl)) in *.
set (tl:= (TwoSumF_err xl yl)) in *.
Search double_word.

Search Fast2Sum.

have: double_word xh (TwoSumF_sum xl yl).
pose proof DWPlusFP_double_word. xh (TwoSumF_sum xl yl).

move: FIN.
replace (Fast2Sum f (BPLUS (TwoSumF_err xl yl) f0))
  with (Fast2Sum_sum f (BPLUS (TwoSumF_err xl yl) f0),
  Fast2Sum_err f (BPLUS (TwoSumF_err xl yl) f0)) => //.
clear FIN; move => [] FIN1 FIN2.
apply BPLUS_finite_e in FIN1; destruct FIN1 as (FIN0 & FIN1).
BPLUS_correct t (TwoSumF_err xl yl) f0;
  rewrite B2R_float_of_ftype.

move: FIN0.
replace f with 
  (Fast2Sum_sum (TwoSumF_sum xh yh) (BPLUS (TwoSumF_err xh yh) 
  (TwoSumF_sum xl yl))).
rewrite /Fast2Sum_sum/fst/Fast2Sum.
set (x1:= (TwoSumF_sum xh yh)).
set (x2:= (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl))).
move => FIN0.
replace f0 with 
  (Fast2Sum_err (TwoSumF_sum xh yh) (BPLUS (TwoSumF_err xh yh) 
  (TwoSumF_sum xl yl))).
BPLUS_correct t x1 x2;
  rewrite !B2R_float_of_ftype.
subst x1 x2.
set (y:= (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl))).
set (hxy := (TwoSumF_sum xh yh)).
rewrite -!round_NE_abs. apply round_le.
  admit. admit.


pose proof Fast2Sum_CorrectDWPlusFP.  
rewrite /Fast2Sum_err/snd/Fast2Sum.
remember (snd (TwoSumF (TwoSumF_sum xl yl) (TwoSumF_sum xh yh))) as s.
rewrite /TwoSumF/snd in Heqs.
rewrite /hxy/y.
(TwoSumF_err xh yh).

eapply Rle_trans.
apply Rabs_triang.
have Hle:
Rabs (FT2R (TwoSumF_err xl yl)) <= Rabs (FT2R (Fast2Sum_err hxy y)).
have Hle:
Rabs (FT2R (TwoSumF_err xl yl)) <= Rabs (FT2R (TwoSumF_err xh yh)). admit.
eapply Rle_trans. apply Hle.
rewrite FastTwoSum_correct.
eapply Rle_trans.
2: apply Rabs_triang_inv.
rewrite /hxy.

Search ( _ <= Rabs ( _ - _)).
rewrite /TwoSumF_err/snd/TwoSumF.
rewrite /Fast2Sum_err/snd/Fast2Sum/hxy/y.
replace (
fold (Fast2Sum_err hxy y).
remember (Fast2Sum_err hxy y) as Hy.
rewrite /Fast2Sum_err/snd/Fast2Sum in HeqHy.
rewrit
rewrite Heqf4 Heqf5 /snd. admit.
rewrite Heqf3 Heqf1 /fst. admit.


pose proof Fast2Sum_CorrectDWPlusDW1.
move: HeqHb.
replace (Fast2Sum _ _) with
  (Fast2Sum_sum (TwoSumF_sum xh yh) (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl)), 
   Fast2Sum_err (TwoSumF_sum xh yh) (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl))) => //.
move => HeqHb.
inversion HeqHb. subst. clear HeqHb.
rewrite .Fast2Sum_sum
rewrite /Fast2Sum_sum/fst/Fast2Sum.


apply FIN.
destruct x1. 
rewrite /fst/snd in Heqf5.
rewrite Heqf5. 
set (x2:= (F2Sum.Fast2Sum _ _ (fst _) _)) in *.
simpl in x2.
f_equal.

replace (fst f5) 
with
(FT2R (fst (Fast2Sum (TwoSumF_sum xh yh) 
          (BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl))))).

  
in Heqf5. rewrite Heqf5 /F2Rp{2}/fst{2}/snd.
rewrite {2}/fst{2}/snd.
move : H. rewrite /F2Rp.
replace F2Sum.Fast2Sum with (F2Sum_sum
 rewrite H.
Admitted.

Theorem relative_errorDWPlusDW_correct :
relative_error_DWPlusDW <= (3 * u^2) / (1 - 4 * u).
Proof.
have HDWx: DWPlus.double_word p choice xhr xlr by 
  (unfold xhr, xlr; apply @dw_word_DWdouble => //).
have HDWy: DWPlus.double_word p choice yhr ylr by 
  (unfold yhr, ylr; apply @dw_word_DWdouble => //).
pose proof @DWPlusDW_relerr_bound (fprec t) 
  (fprec_gt_one t) choice eq_refl Hp3 xhr xlr yhr ylr
  HDWx HDWy.
move: H. by rewrite relative_errorDWDW_eq.
Qed.

End AccuracyDWPlusDW.


