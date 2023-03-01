(* Copyright (c)  Inria. All rights reserved. *)

Require Import Psatz ZArith Reals.

From Flocq Require Import Core Relative Sterbenz Operations Plus_error Mult_error.

Require Import mathcomp.ssreflect.ssreflect.
Require Import Bayleyaux.
Require Import DWPlus.
Require Import DWTimesFP.
Require Import F2Sum.


Set Implicit Arguments.

Local Open Scope Z_scope.
Local Open Scope R_scope.

Local Notation two := radix2 (only parsing).
Local Notation pow e := (bpow two e).

Section Times.

Variables p : Z.


Variable choice : Z -> bool.
Hypothesis ZNE : choice = fun n => negb (Z.even n).

Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format two fexp).
Local Notation ce := (cexp two fexp).
Local Notation mant := (scaled_mantissa two fexp).
Local Notation rnd_p := (round two fexp (Znearest choice)).
Let u := pow (-p).



Section Algo10.

Hypothesis Hp4 : Z.le 4 p.

Local Instance p_gt_0_4_10 : Prec_gt_0 p.
exact: (Z.lt_le_trans _ 4 _ _ Hp4).
Qed.


Fact  Hp1_4_10 : (1 < p)%Z.
Proof. lia. 
Qed.

Notation Hp1 := Hp1_4_10.

Notation Fast2Mult := (Fast2Mult p choice).
Notation Fast2Sum := (Fast2Sum p choice).


Notation F2P_prod a b  :=  (fst (Fast2Mult a b)).
Notation F2P_error a b  :=  (snd (Fast2Mult a b)).

Hypothesis Fast2Mult_correct: 
  forall a b, a * b =  F2P_prod a b +  F2P_error a b.

Notation F2P_errorE := (F2P_errorE Fast2Mult_correct).


Hypothesis TwoProdE : TwoProd = Fast2Mult. (* or Dekker's algorithm *)



Definition DWTimesDW (xh xl yh yl : R) :=
  let (ch, cl1) := (TwoProd xh yh) in
  let tl1 := rnd_p (xh * yl) in
  let tl2 := rnd_p (xl * yh) in
  let cl2 := rnd_p (tl1 + tl2) in 
  let cl3 := rnd_p (cl1 + cl2) in  Fast2Sum ch cl3.

Lemma  DWTimesDWC (xh xl yh yl : R):  DWTimesDW xh xl yh yl = DWTimesDW  yh yl  xh xl.
Proof.
rewrite /DWTimesDW TwoProdE Fast2MultC.
suff ->: (rnd_p (xh * yl) + rnd_p (xl * yh)) = (rnd_p (yh * xl) + rnd_p (yl * xh)) by [].
rewrite (Rmult_comm xh) (Rmult_comm yh); ring.
Qed.



Definition errorDWTDW xh xl yh yl  := let (zh, zl) := DWTimesDW xh xl yh yl in
  let xy := ((xh + xl) * (yh  + yl))%R in ((zh + zl) - xy).

Definition relative_errorDWTFP xh xl yh yl  := let (zh, zl) := DWTimesDW xh xl yh yl  in
  let xy :=  ((xh + xl) * (yh  + yl))%R  in (Rabs (((zh + zl) - xy)/ xy)).


Lemma  boundDWTDW_ge_0: 0 < 7 * (u * u).
Proof.
have upos:= upos p.
have u2pos: 0 < u * u by apply:Rmult_lt_0_compat.
 lra.
Qed.

Fact h7u2:  7 * (u * u) / ((1 + u)* (1+ u)) < 7 * (u * u).
Proof.
have upos:= upos p; rewrite -/u in upos.
have ult1 : u < 1 by rewrite /u ; apply:bpow_lt_1; lia.
apply: (Rmult_lt_reg_r (((1 + u) * (1 + u)))); first nra.
rewrite /Rdiv Rmult_assoc Rinv_l; try nra; apply:Rmult_lt_compat_l; nra.
Qed.

Notation double_word := (double_word  p choice).

Lemma l5_2 a b : 1 <= a  <= 2 -> 1 <= b <= 2 ->  a * b  <=2 ->  (a + b) <= 3.
Proof. move=> [a1 a2] [b1 b2] ab2; nra. Qed.

Lemma l5_20  a b:  1 <= a  <= 2 ->  1 <= b <= 2->  a * b  <=2 ->  (a + b) = 3 ->
      ((a = 1 /\ b = 2)) \/ ((a = 2 ) /\ (b = 1)).
Proof. nra. Qed.


Lemma l5_2F a b  : format a -> format b ->1 <= a  <= 2 - 2*u -> 1 <= b <= 2 - 2*u ->  
                   a * b  <= 2 ->  (a + b) <= 3 - 2*u.
Proof.
move=> Fa Fb [a1 a2] [b1 b2]  ab2.
have upos := (upos p); rewrite -/u in upos.
have:(a + b) <= 3 by apply:  l5_2;lra.
case =>ab3; last first.
  have:  ((a = 1 /\ b = 2)) \/ ((a = 2 ) /\ (b = 1)) 
    by apply: l5_20; lra.
  lra.
have pow0: pow 0 = 1 by [].
case:(ex_mul 0 _ Fa).
  rewrite Rabs_pos_eq /= ; lra.
rewrite pow0 Rmult_1_r -/u; move=> ma ae.
case:(ex_mul 0 _ Fb).
  rewrite Rabs_pos_eq /= ; lra.
rewrite pow0  Rmult_1_r -/u;  move=> mb be.
have te:  3 = IZR (3 *  (2^(p- 1)))%Z * (2*u).
  rewrite mult_IZR (IZR_Zpower two); last lia.
  have ->: 2 = pow 1 by [].
  rewrite /u Rmult_assoc  -!bpow_plus.
  ring_simplify  (p - 1 + (1 + - p))%Z; by rewrite Rmult_1_r. 
have uupos: 0 < 2 * u by lra.
move: ab3.
have ->: a+b = (IZR ma + IZR mb) * (2 * u) by rewrite ae be ;ring.
rewrite {1}te; move/(Rmult_lt_reg_r _ _ _ uupos).
rewrite -plus_IZR; move/lt_IZR/Zlt_left => h.
have : ((ma + mb) <=  3 * 2 ^ (p - 1) -1)%Z by lia.
move/IZR_le/(Rmult_le_compat_r (2 *u) _ _  (Rlt_le _ _ uupos)).
rewrite minus_IZR te;lra.
Qed.

Lemma l5_2F' a b  : format a -> format b ->1 <= a  <= 2 - 2*u -> 1 <= b <= 2 - 2*u ->  
                   a * b  <= 2 ->  (a + b) <= 3 - 2*u.
Proof.
move=> Fa Fb [a1 a2] [b1 b2]  ab2.
have upos := (upos p); rewrite -/u in upos.

 have:(a + b) <= 3 by apply:  l5_2;lra.
case =>ab3; last first.
  have:  ((a = 1 /\ b = 2)) \/ ((a = 2 ) /\ (b = 1)) by apply: l5_20; lra.
  lra.
case:(ex_mul 0 _ Fa).
  rewrite Rabs_pos_eq /= ; lra.
move=> ma ae.
case:(ex_mul 0 _ Fb).
  rewrite Rabs_pos_eq /= ; lra.
move=> mb be.
case : (@ex_mul p 3 1).
    have->: pow 1 = 2 by [].
    rewrite Rabs_pos_eq /= ; lra.
  have h3F: 3 = F2R (Float two 3 0) by rewrite /F2R/=; ring.
  apply:(FLX_format_Rabs_Fnum  p  h3F). 
  rewrite /F2R/= Rabs_pos_eq; last lra.
  apply:(Rlt_le_trans _ (pow 2)); last by apply : bpow_le; lia.
  have ->: pow 2 = 4 by [].
  lra.
move=> m3 e3.
move: ab3.
rewrite ae be  e3 [pow 0] /= Rmult_1_r -/u.
have ->:  IZR ma * (2 * u) + IZR mb * (2 * u) = (IZR ma + IZR mb)* (2 * u) by ring.
have ->: pow 1 = 2 by [].
have->:  IZR m3 * (2 * u * 2) = IZR m3 * 2 * (2 * u) by ring.
have u2pos : 0 < 2 * u by lra.
move/(Rmult_lt_reg_r _ _ _ u2pos).
rewrite -plus_IZR.
have->: IZR m3 * 2 = IZR (m3 * 2)%Z by rewrite mult_IZR.
move/lt_IZR/Pff.Zle_Zpred; rewrite -Z.sub_1_r => /IZR_le.
have u2ge0 : 0 <= 2*u by lra.
move/(@Rmult_le_compat_r _ _ _  u2ge0).
by rewrite minus_IZR; lra.
Qed.


Fact  DWTimesDW_Asym_r xh xl yh yl :
  (DWTimesDW xh xl (-yh ) (- yl)) =
       pair_opp  (DWTimesDW xh xl yh yl).
Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
rewrite /DWTimesDW TwoProdE /=.
(* case=> <- <-. *)
rewrite ZNE !(=^~Ropp_mult_distr_r, round_NE_opp,  Fast2Sum_asym) -ZNE //.
have->: (- (xh * yh) - - rnd_p (xh * yh)) = -((xh * yh) - rnd_p (xh * yh)) by ring.
by rewrite ZNE !(=^~Ropp_plus_distr, round_NE_opp,  Fast2Sum_asym) ?Ropp_involutive  -ZNE.
Qed.

Fact  DWTimesDW_Asym_l xh xl yh yl   : 
  (DWTimesDW (-xh) (-xl)  yh yl ) =  pair_opp  (DWTimesDW xh xl yh yl).
  Proof.
    by rewrite !(DWTimesDWC _ _ yh _) DWTimesDW_Asym_r.
Qed.

  Fact  DWTimesDWSx xh xl yh yl  e:
    (DWTimesDW (xh * pow e) (xl * pow e)  yh yl ) =
    map_pair (fun x => x * (pow e))  (DWTimesDW xh xl   yh yl ).
Proof.
rewrite /DWTimesDW TwoProdE /=.
by rewrite !(Rmult_comm _ yh) !(Rmult_comm _ yl)!(=^~Rmult_assoc, round_bpow, =^~Rmult_plus_distr_r,Fast2SumS,=^~Rmult_minus_distr_r ) 
  !(Rmult_comm yh)//; apply:generic_format_round.
Qed.

Fact  DWTimesDWSy xh xl yh yl e:
  (DWTimesDW xh xl   (yh * pow e) (yl * pow e)) =
  map_pair (fun x => x * (pow e))  (DWTimesDW xh xl   yh yl ). 
Proof.
 rewrite /DWTimesDW TwoProdE /=.
by rewrite  !(=^~Rmult_assoc, round_bpow, =^~Rmult_plus_distr_r,Fast2SumS,=^~Rmult_minus_distr_r ) //; 
   apply:generic_format_round.
Qed.


Lemma double_lpart_u ah al (DWa:double_word ah al):  1 <= ah < 2 -> Rabs al <= u.
Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
move=> ahb.
have [[Fah Fal] Eah] := DWa.
have:= (dw_ulp Hp1 DWa).
suff ->:  / 2 * ulp radix2 fexp ah = u by [].
have ah0 : ah <> 0 by lra.
rewrite ulp_neq_0 // /cexp /fexp bpow_plus -/u -Rmult_assoc.
  suff -> : / 2 * (pow (mag radix2 ah)) = 1 by ring.
  suff ->:  ((mag radix2 ah)  = 1%Z :>Z).
    rewrite /= IZR_Zpower_pos /=; field.
  apply:mag_unique_pos; rewrite /= IZR_Zpower_pos /=; split;lra.
Qed.


(* Theorem 5.1 *)
Lemma DWTimesDW_correct xh xl yh yl  (DWx:double_word xh xl) (DWy:double_word yh yl):
  let (zh, zl) := DWTimesDW xh xl yh yl in
  let xy := ((xh + xl) * (yh + yl))%R in
  Rabs ((zh + zl - xy) / xy) < 7 * (u * u).
Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
have [[Fxh Fxl] Exh] := DWx.
have [[Fyh Fyl] Eyh] := DWy.
case E1: DWTimesDW => [zh zl].
have Hp1:= Hp1.
case:(Req_dec yh 0)=> yh0.
  have yl0: yl = 0.
    by move:Eyh; rewrite  yh0 Rplus_0_l round_generic.
  move:E1; rewrite /DWTimesDW yh0 yl0 Rmult_0_r TwoProdE round_0 Fast2MultC Rmult_0_r Fast2Mult0f. 
  rewrite /Fast2Sum /F2SumFLX.Fast2Sum !(Rplus_0_r, Rminus_0_r, Rplus_0_l, round_0).
  case=> <- <-; rewrite Rplus_0_r Rmult_0_r Rminus_0_l /Rdiv Ropp_0 Rmult_0_l Rabs_R0.
  exact: boundDWTDW_ge_0.
case:(Req_dec xh 0)=> xh0.
  have xl0: xl = 0.
    by move:Exh; rewrite  xh0 Rplus_0_l round_generic.
  move:E1; rewrite /DWTimesDW xh0 xl0 Rmult_0_l TwoProdE  round_0 Fast2Mult0f.
  rewrite /Fast2Sum /F2SumFLX.Fast2Sum !(Rplus_0_r, Rminus_0_r, Rplus_0_l, round_0, Rmult_0_l).
  case=> <- <-; rewrite Rplus_0_r  /Rdiv   Rmult_0_l Rabs_R0.
  exact: boundDWTDW_ge_0.
have x0: xh + xl <> 0 by move=> x0; apply:xh0; rewrite Exh x0 round_0.
have y0: yh + yl <> 0 by move=> y0; apply:yh0; rewrite Eyh y0 round_0.
rewrite /=.
clear Fxh Fxl Exh Fyh Fyl Eyh.
wlog xhpos: yh yl  xh xl zh zl DWx DWy  E1 xh0 yh0 x0 y0 / 0 <= xh.
  move=> Hwlog.
  case:(Rle_lt_dec 0 xh) => xhle0; first by apply:Hwlog.
  have ->: (zh + zl - (xh + xl) * (yh + yl)) / ((xh + xl) * (yh +yl))= 
   ((- zh + - zl - (- xh + - xl) * (yh + yl)) / ((- xh + - xl) * (yh + yl)))
    by field; lra.
  apply:(Hwlog yh yl  (-xh) (-xl) (-zh) (-zl))=>//; try lra; last  by rewrite DWTimesDW_Asym_l E1.
  have [[Fxh Fxl] Exh] := DWx.
  split; [split|]; try apply:generic_format_opp=>//.
  have ->:- xh + - xl = -(xh +  xl) by ring.
  by rewrite ZNE round_NE_opp -ZNE {1}Exh.

wlog yhpos: yh yl  xh xl zh zl DWx DWy  E1 xh0 yh0 x0 y0 xhpos / 0 <= yh.
  move=> Hwlog.
  case:(Rle_lt_dec 0 yh) => yhle0; first by apply:Hwlog.
  have ->: (zh + zl - (xh + xl) * (yh + yl)) / ((xh + xl) * (yh +yl))= 
   ((- zh + - zl - ( xh +  xl) * (- yh + - yl)) / (( xh + xl) * (- yh + - yl)))
    by field; lra.
  apply:(Hwlog (-yh) (-yl)  (xh) (xl) (-zh) (-zl))=>//; try lra; last by rewrite DWTimesDW_Asym_r E1.
  have [[Fyh Fyl] Eyh] := DWy.
  split; [split|]; try apply:generic_format_opp=>//.
  have ->:- yh + - yl = -(yh +  yl) by ring.
  by rewrite ZNE round_NE_opp -ZNE {1}Eyh.
have {} xhpos: 0 < xh by lra.
have {} yhpos: 0 < yh by lra.

wlog [xh1 xh2]: xl xh  zh zl DWx   xh0 x0 xhpos E1/ 1 <= xh  <= 2 - 2*u.
  move=> Hwlog.
  have [[Fxh Fxl] Exh] := DWx.
  case: (scale_generic_12 Fxh xhpos)=> exh Hxhs.
  have xhp0: 0 <  xh * pow exh by lra.
  have ->: (zh + zl - (xh + xl) * (yh + yl)) / ((xh + xl) * (yh + yl)) = 
         (zh * pow exh  + zl * pow exh  - 
         (xh * pow exh + xl * pow exh) * (yh + yl)) / ((xh * pow exh + xl * pow exh) * (yh + yl)).
    field.
    split; try lra; split; nra.
  apply:Hwlog=>//; try lra.
      split;[split|]; try apply:formatS=>//.
      by rewrite -Rmult_plus_distr_r round_bpow -Exh.
    nra.
  by rewrite DWTimesDWSx E1.
wlog [y1 y2]: yh yl  zh zl  DWy yh0 y0 yhpos E1/ 1 <= yh <= 2-2*u.
  move=> Hwlog.
  have [[Fyh Fyl] Eyh] := DWy.
  case: (scale_generic_12 Fyh yhpos)=> eyh Hyhs.
  have ->: (zh + zl - (xh + xl) * (yh + yl)) / ((xh + xl) * (yh + yl)) = 
         (zh * pow eyh  + zl * pow eyh - 
        (xh  + xl) * (yh  * pow eyh + yl * pow eyh)) 
           / ((xh + xl ) * (yh * pow eyh + yl * pow eyh)).
  field;  move:(bpow_gt_0 two eyh); nra.
  apply:Hwlog=>//; try lra.
    split;[split|]; try apply:formatS=>//.
      by rewrite -Rmult_plus_distr_r round_bpow -Eyh.
    nra.  
  by rewrite DWTimesDWSy E1.
have upos:= upos p.
rewrite -/u in upos.
have ult1 : u < 1 by rewrite /u ; apply:bpow_lt_1; lia.
have u2pos: 0 < u * u by apply:Rmult_lt_0_compat.
have xh2': xh <= 2 by lra.
have yh2': yh <= 2 by lra.
have h0 : xh * yh <= 4 by nra.
have ylu:Rabs yl <= u by apply: (double_lpart_u DWy); lra.
have xlu:Rabs xl <= u by apply: (double_lpart_u DWx); lra.
have [[Fxh Fxl] Exh] := DWx.
have [[Fyh Fyl] Eyh] := DWy.
move:E1; rewrite /DWTimesDW.
rewrite TwoProdE /=.
set ch := rnd_p (xh * yh).
set cl1 :=   xh * yh -  ch.
have chcl1E: ch + cl1 = xh * yh by  rewrite /cl1 /ch; lra.
have cl1ub: Rabs cl1 <= 2 * u.
  rewrite /cl1 -Ropp_minus_distr Rabs_Ropp /ch.
  have ->: 2 * u = / 2 * u * pow 2.
    rewrite /= IZR_Zpower_pos /=; field.
  rewrite /u; apply: error_le_half_ulp'; first lia.
  rewrite Rabs_pos_eq  /= ?IZR_Zpower_pos /=; nra.
set tl1 := rnd_p (xh * yl).
pose e1 := tl1 - xh*yl.
have tl1E: tl1 = xh*yl + e1 by rewrite  /e1 /tl1; ring.
have xhylub: Rabs (xh*yl) <= 2*u - 2*(u*u).
  rewrite Rabs_mult Rabs_pos_eq; last lra.
have->: 2 * u - 2 * (u * u) = (2 - 2 * u) * u by ring.
apply:Rmult_le_compat; try apply: Rabs_pos; lra.
have tl1ub: Rabs tl1 <= 2*u -2* (u *u).
  rewrite /tl1  ZNE -round_NE_abs -ZNE.
  suff -> : 2 * u - 2 * (u * u) = rnd_p (2 * u - 2 * (u * u))  by apply:round_le.
  rewrite round_generic //.
  have ->:  (2 * u - 2 * (u * u)) = (pow (-p) * ( pow p - 1) * (pow (1 -p))).
    rewrite /u !bpow_plus /= IZR_Zpower_pos /= Rmult_minus_distr_l.
    rewrite !Rmult_1_r.
    have ->:  pow (-p) * (pow p ) = 1 by rewrite -bpow_plus; ring_simplify (-p + p)%Z.
    ring.
  have->: pow (- p) * (pow p - 1) * pow (1 - p) =  (pow p - 1) * ( pow (1 - p)*(pow (- p))) by ring.
  rewrite -bpow_plus.
  apply:(formatS Hp1).
  have ->: (pow p - 1)= F2R  (Float two ((2 ^ p)  -1)%Z 0).
    rewrite /F2R /= minus_IZR (IZR_Zpower two) ; try lia; ring.
  apply: FLX_format_Rabs_Fnumf =>//.
  rewrite /F2R/=  minus_IZR (IZR_Zpower two) ?Rabs_pos_eq; try lia; try lra.
  suff: pow 0 <= pow p by rewrite /=; lra.
  apply bpow_le; lia.
have e1ub: Rabs e1 <= u*u.
  rewrite /e1.
  have->: u * u = /2 * u * (pow (1 -p)) by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  rewrite bpow_plus  /= IZR_Zpower_pos /= -/u; apply:(Rle_trans _  (2 * u - 2 * (u * u))) =>//.
  lra.
(* tl2 *)
set tl2 := rnd_p (xl * yh).
pose e2 := tl2 - xl*yh.
have tl2E: tl2 = xl*yh + e2 by rewrite  /e2 /tl2; ring.
have xlyhub: Rabs (xl*yh) <= 2*u - 2*(u*u).
  rewrite Rabs_mult (Rabs_pos_eq yh); try lra.
  have->: 2 * u - 2 * (u * u) = u * (2 - 2 * u) by ring.
  apply:Rmult_le_compat; try apply: Rabs_pos; lra.
have tl2ub: Rabs tl2 <= 2*u -2* (u *u).
  rewrite /tl2  ZNE -round_NE_abs -ZNE.
  suff -> : 2 * u - 2 * (u * u) = rnd_p (2 * u - 2 * (u * u))  by apply:round_le.
  rewrite round_generic //.
  have ->:  (2 * u - 2 * (u * u)) = (pow (-p) * ( pow p - 1) * (pow (1 -p))).
    rewrite /u !bpow_plus /= IZR_Zpower_pos /= Rmult_minus_distr_l.
    have ->:  pow (-p) * (pow p ) = 1. 
      by rewrite -bpow_plus; ring_simplify (-p + p)%Z.
    ring.
  have->: pow (- p) * (pow p - 1) * pow (1 - p) =  (pow p - 1) * ( pow (1 - p)*(pow (- p))) by ring.
  rewrite -bpow_plus.
  apply:(formatS Hp1).
  have ->: (pow p - 1)= F2R  (Float two ((2 ^ p)  -1)%Z 0).
    rewrite /F2R /= minus_IZR (IZR_Zpower two) ; try lia; ring.
  apply: FLX_format_Rabs_Fnumf =>//.
  rewrite /F2R/=  minus_IZR (IZR_Zpower two) ?Rabs_pos_eq; try lia; try lra.
  suff: pow 0 <= pow p by rewrite /=; lra.
  apply bpow_le; lia.  
have e2ub: Rabs e2 <= u*u.
  rewrite /e2.
  have->: u * u = /2 * u * (pow (1 -p)) by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  rewrite bpow_plus  /= IZR_Zpower_pos /= -/u. 
  apply:(Rle_trans _ ( 2 * u - 2 * (u * u))) =>//; lra.
set cl2 := rnd_p (tl1 + tl2).
pose e3 := cl2 - (tl1 + tl2).
have tl1tl2: Rabs (tl1 + tl2) <= 4*u - 4*(u * u).
apply:(Rle_trans _ _ _ (Rabs_triang _ _)); lra.
have cleub: Rabs cl2 <= 4*u - 4*(u * u).
  rewrite /cl2.
  suff->:  4*u - 4*(u * u) = rnd_p  (4*u - 4*(u * u)) 
    by rewrite ZNE -round_NE_abs -ZNE; apply:round_le.
  rewrite round_generic //.
  have ->:(4 * u - 4 * (u * u)) = (1 -u)* pow (2 -p).
    rewrite bpow_plus -/u /= IZR_Zpower_pos /=; field.
  apply:(formatS Hp1).
  have fle : 1 - u = F2R (Float two ((2 ^ p) -1) (-p)).
    rewrite /F2R  minus_IZR (IZR_Zpower two); try lia. 
  have->: (Fexp {| Fnum := 2 ^ p - 1; Fexp := - p |}) = (-p)%Z by [].
    ring_simplify; rewrite -bpow_plus Z.add_opp_diag_r /= /u; ring.
  apply: (FLX_format_Rabs_Fnum p fle); rewrite /=  minus_IZR (IZR_Zpower two); last  lia.
  rewrite Rabs_pos_eq; first lra.
  suff: pow 0 <= pow p by rewrite /=; lra.
  apply bpow_le; lia.
have e3ub: Rabs e3 <= 2 * u * u.
  rewrite /e3.
  have->: 2 * u * u = /2 * u * (pow (2 -p)) by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  rewrite bpow_plus  /= IZR_Zpower_pos /= -/u; lra.
set cl3 := rnd_p (cl1 + cl2).
pose e4 := cl3 - (cl1 + cl2).
have cl1cl2: Rabs (cl1 + cl2) <= 6*u - 4*(u * u).
  apply:(Rle_trans _ _ _ (Rabs_triang _ _)); lra.
have cl3ub: Rabs cl3 <= 6*u.
  rewrite /cl3 ZNE -round_NE_abs -ZNE.
  suff ->: 6*u = rnd_p (6 * u) by apply:round_le; lra.
  rewrite round_generic //.
  rewrite /u; apply:formatS=>//.
  have fle : 6 = F2R (Float two 6 0) by rewrite /F2R /=; ring.
  apply: (FLX_format_Rabs_Fnum p fle);  rewrite /= Rabs_pos_eq; last lra.
  apply:(Rlt_le_trans _ 8); first lra.
  have->:8 = pow 3 by [].
  apply:bpow_le; lia.
have Fcl1: format cl1.    
  by rewrite /cl1 -Ropp_minus_distr; apply/generic_format_opp/ mult_error_FLX.
have e4ub: Rabs e4 <= 4 * u * u.
 rewrite /e4.
  have->: 4 * u * u = /2 * u * (pow (3 -p)) by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  rewrite bpow_plus  /= IZR_Zpower_pos /= -/u; nra.
have hf2Sc: Rabs cl3 <= Rabs ch.
  apply:(Rle_trans _ (6 * u))=>//.
  apply: (Rle_trans _ 1).
   apply: (Rle_trans _ (8 * u)); try lra.
  suff : pow (3 - p) <= pow 0 .
   rewrite bpow_plus  /= IZR_Zpower_pos /= -/u; lra.
   apply:bpow_le; lia.
  have ->:  1 = pow 0 by [].
  rewrite -(round_generic two fexp (Znearest choice) (pow 0)).
  rewrite /ch ZNE -round_NE_abs -ZNE; apply/round_le; rewrite /= Rabs_pos_eq; nra.
  apply:generic_format_bpow; rewrite /fexp; lia.
   rewrite (surjective_pairing (Fast2Sum  _ _)).
rewrite F2Sum_correct_abs=>//; try apply: generic_format_round; last by rewrite (round_generic _ _ _ cl1)//.
rewrite (round_generic _ _ _ cl1)//.
case=> zhe  zle.
pose eta := -(xl* yl) + e1 + e2 + e3 + e4.
have ->: zh + zl =  (xh + xl) * (yh + yl) + eta.
  rewrite -zhe -zle.
  ring_simplify; rewrite -/cl3.
  have-> : ch = xh*yh -cl1 by rewrite /cl1;   ring.
  have->: cl3 = cl1 + cl2 + e4 by rewrite /e4; ring.
  have->: cl2 = tl1 + tl2 + e3 by rewrite /e3; ring.
  have->: tl2 = xl * yh + e2 by rewrite /e2; ring.
  have->: tl1 = xh * yl + e1 by rewrite /e1; ring.
  rewrite /eta ; ring.
have etaub: Rabs eta <= 9 *(u * u).
  rewrite /eta.
  apply:(Rle_trans _ (Rabs (- (xl * yl))  + Rabs e1 + Rabs e2 + Rabs e3 + Rabs e4)).
    repeat (apply: (Rle_trans _ _ _ (Rabs_triang _ _)); 
      apply:Rplus_le_compat_r); lra.
  suff : Rabs (- (xl * yl)) <= u * u by lra.
  rewrite Rabs_Ropp Rabs_mult; apply:Rmult_le_compat; try apply:Rabs_pos ; lra.

case:(Rlt_le_dec 2 (xh * yh))=>xhyh2.
  apply:(Rle_lt_trans _ ((9 * (u * u)) / (2 * (1 - u) * (1 - u)))); last first.
    apply: (Rle_lt_trans _ (7*  (u * u) / ((1 + u) * (1 + u)))); last first.
      have h: 1 < ((1 + u) * (1 + u)).
       clear - upos ; nra.
      rewrite -[X in _ < X]Rmult_1_r.
      rewrite /Rdiv; apply:Rmult_lt_compat_l; try lra.
      rewrite -[X in _< X]Rinv_1.
      apply:Rinv_lt; lra.
    set d1 := (2 * (1 - u) * (1 - u)).
    set d2 :=((1 + u) * (1 + u)).
    set u2 := u * u.
    rewrite /Rdiv (Rmult_comm 9) (Rmult_comm 7) 2!Rmult_assoc.
    apply:Rmult_le_compat_l; rewrite /u2; try lra.
    suff : 0 < d1.
      suff: 0 < d2.
        move=> *.
        suff: 9 * d2 < 7 * d1.
          move=> *.
          apply: (Rmult_le_reg_r d1); try lra.
          rewrite Rmult_assoc Rinv_l; try lra.
          rewrite Rmult_1_r; apply: (Rmult_le_reg_r d2); try lra.
          have->: 7 * / d2 * d1 * d2 = 7 * d1 by field; lra.
          lra.
        rewrite /d2 /d1.
        ring_simplify.
        set ue2:= u^2.
        apply: (Rplus_lt_reg_r (-( 9 * ue2 + 18 * u +  9))).
        ring_simplify.
        have ue2pos:= (pow2_ge_0  u).
        clear - upos ue2pos  ult1 Hp4.
        suff : 46 * u < 5 by rewrite /ue2 ; lra.
        apply:(Rlt_le_trans _ (64 * u)); try lra.
        apply:(Rle_trans _ 4); try lra.
        have ->: 64 = 2 * (2 * 16) by [].
        rewrite -Rmult_assoc -[X in _ <= X]Rmult_1_r.
        have->:  2 * 2 * 16 * u = 4 * (16 * u) by ring.
        apply: Rmult_le_compat; try lra.
        have ->: 1 = pow 0 by [].
        have ->: 16 * u = pow (4 - p) by rewrite bpow_plus -/u.
        apply:bpow_le; lia.
        have->: d2 = 1 + 2*u + u * u by rewrite /d2 ; ring.
      lra.
  rewrite /d1.
  clear - upos ult1; nra.
  rewrite /Rdiv Rabs_mult.
  apply:Rmult_le_compat; try apply:Rabs_pos.
    by ring_simplify((xh + xl) * (yh + yl) + eta - (xh + xl) * (yh + yl)).
  have xpos: 0 < xh + xl.
    clear - xh1 xh2 xlu  upos ult1.
    move/Rabs_le_inv: xlu;lra.
  have :(xh + xl ) >= xh * (1 - u).
    clear - xh1 xh2 xlu  upos ult1.
    move/Rabs_le_inv: xlu;nra.
  have :(yh + yl ) >= yh * (1 - u).
    clear - y1  ylu  upos ult1.
    move/Rabs_le_inv: ylu;nra.
  move =>  hy hx.    
  have hypos : 0 < (yh + yl).
    clear -  y1   ult1 ylu.
    move/Rabs_le_inv: ylu; lra.
  rewrite Rabs_pos_eq.
    suff h: 0 < (2 * (1 - u) * (1 - u)) <= ((xh + xl) * (yh + yl)) by apply:Rinv_le; lra.
    split;  first lra.
    apply:(Rle_trans _ (xh * (1 -u) * (yh * (1 -u)))).
      clear - xpos hypos upos ult1 xhyh2 xh1   y1.
      have -> : xh * (1 - u) * (yh * (1 - u)) = (xh * yh) * (1-u) *(1 -u) by ring.
      apply:Rmult_le_compat_r;  nra.
    apply:Rmult_le_compat; nra.
  clear - xpos hypos; apply/Rlt_le/Rinv_0_lt_compat; nra.
have  cl1u: Rabs cl1 <= u.
  rewrite /cl1 -Ropp_minus_distr Rabs_Ropp /ch.
  have ->: u = / 2 * u * (pow 1)  by rewrite /= IZR_Zpower_pos /=; field.
  rewrite /u; apply: error_le_half_ulp'; first lia.
  rewrite Rabs_pos_eq  /= ?IZR_Zpower_pos /= ?Rmult_1_r //.
  clear - xh1 y1;  nra.
 have hsxhyh: xh + yh <= 3 by apply:l5_2; nra. 

(* have hsxhyh: xh + yh <= 3- 2*u by apply:l5_2F. *)
(* (* have hsxhyh: xh + yh <= 3 by apply:l5_2; nra. *) *)
have tl1u: Rabs tl1 <= xh * u.
  rewrite /tl1  ZNE -round_NE_abs -ZNE.
 suff -> : xh * u = rnd_p (xh * u).
 apply:round_le.
  rewrite Rabs_mult Rabs_pos_eq; try lra.
  apply:Rmult_le_compat_l; try lra.
  by rewrite /u round_bpow round_generic.
have tl2u: Rabs tl2 <= yh * u.
  rewrite /tl2  ZNE -round_NE_abs -ZNE.
  suff -> : yh * u = rnd_p (yh * u).
    apply:round_le.
    rewrite Rabs_mult Rmult_comm Rabs_pos_eq; try lra.
    apply:Rmult_le_compat_l; try lra.
  by rewrite /u round_bpow round_generic.
have stl12u: Rabs (tl1 + tl2)  <= 3 * u.
  apply: (Rle_trans _ _ _ (Rabs_triang _ _)).
  apply:(Rle_trans _ ((xh  + yh)* u)); try lra.

  apply :Rmult_le_compat_r; lra.

have cl2u: Rabs cl2 <= 3 * u.
  have->: 3 * u= rnd_p (3*u).
    rewrite round_generic //.
    apply:formatS; try lia.
    apply:(@FLX_format_Rabs_Fnum _ _(Float two 3 0)).
      rewrite /F2R //=; ring.
    rewrite /=; apply:(Rlt_le_trans _ (pow 2)).
      have->: pow 2 = 4 by [].
      rewrite Rabs_pos_eq; lra.
    by apply: bpow_le; lia.
  rewrite /cl2.
rewrite ZNE -round_NE_abs -ZNE.
by apply:round_le.

have scl12u: Rabs (cl1 + cl2) <= 4*u.
  apply: (Rle_trans _ _ _ (Rabs_triang _ _)); lra.
have e4u: Rabs e4 <= 2 * u *u.
  rewrite /e4 /cl3.
  have-> :  2 * u * u = / 2 * pow (- p) * pow (2 - p).
    rewrite bpow_plus -/u /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'; first lia.
  rewrite !bpow_plus -/u /= IZR_Zpower_pos /=; lra.
have etaub7: Rabs eta <= 7 *(u * u).
  rewrite /eta.
  apply:(Rle_trans _ (Rabs (- (xl * yl))  + Rabs e1 + Rabs e2 + Rabs e3 + Rabs e4)).
    repeat (apply: (Rle_trans _ _ _ (Rabs_triang _ _)); 
      apply:Rplus_le_compat_r); lra.
  suff : Rabs (- (xl * yl)) <= u * u by lra.
  rewrite Rabs_Ropp Rabs_mult; apply:Rmult_le_compat; try apply:Rabs_pos ; lra.
ring_simplify (((xh + xl) * (yh + yl) + eta - (xh + xl) * (yh + yl))).
have xpos: 0 < xh + xl by  move/Rabs_le_inv: xlu; lra.
have ypos: 0 < yh + yl by move/Rabs_le_inv: ylu; lra.
have xypos: 0 < (xh + xl) * (yh + yl) by apply/Rmult_lt_0_compat; lra.

rewrite Rabs_mult Rabs_Rinv; try lra.
rewrite [X in _ * / X  ] Rabs_pos_eq; try lra.
apply:(Rmult_lt_reg_r ((xh + xl) * (yh + yl))) =>//.
rewrite Rmult_assoc Rinv_l ?Rmult_1_r; try lra.
have hcl1: cl1 = 0 -> Rabs eta < 7 * (u * u) * ((xh + xl) * (yh + yl)).
  move=> cl1_0.
  have abseta : Rabs eta <= Rabs (xl * yl) + Rabs e1 + Rabs e2 + Rabs e3 + Rabs e4.
  rewrite /eta.
   repeat (apply: (Rle_trans _ _ _ (Rabs_triang _ _)); 
     first apply : Rplus_le_compat_r).
   rewrite Rabs_Ropp ; lra.

  apply:(Rle_lt_trans _ ( Rabs (xl * yl) +  Rabs e1 + Rabs e2 + Rabs e3 + Rabs e4))=>//.
  have->: e4 = 0.
    rewrite /e4 /cl3 cl1_0 Rplus_0_l round_generic; first ring.
    by rewrite /cl2; apply: generic_format_round.
  rewrite Rabs_R0 Rplus_0_r.
  apply: (Rle_lt_trans _ (5 * (u *u))).
    suff : Rabs (xl * yl) <= u * u by lra.
    clear -   ylu xlu upos; 
    have rxl:= (Rabs_pos  xl); have ryl:= (Rabs_pos  yl);  rewrite Rabs_mult; nra.
  apply:(Rlt_le_trans _ (7 * (u * u) * ((1 -u ) * (1  - u)))); last first.
    apply:Rmult_le_compat; first by clear -upos; nra.
    + clear -ult1; nra.
    + clear -upos; nra.
    clear - ylu xlu   xh1  y1 ult1.
    move/Rabs_le_inv:  ylu; move/Rabs_le_inv :xlu=> ylu xlu.
    apply:Rmult_le_compat; lra.
  clear - upos u2pos ult1 Hp4.
(* suff : 21 * u < 4 by nra. *)
  suff :  u < / 8  by nra.
  have -> : /8 = pow (-3) by [].
   rewrite /u; apply: bpow_lt;  lia.
case: xh1 => xh1; last first.
  apply:hcl1; rewrite /cl1 /ch -xh1 Rmult_1_l round_generic //; ring.
case: y1 => yh1; last first.
 apply:hcl1; rewrite /cl1 /ch -yh1 Rmult_1_r round_generic //; ring.
apply: (Rle_lt_trans _ (7 * (u* u))) =>//.
rewrite -[X in X < _]Rmult_1_r.
apply:Rmult_lt_compat_l; try lra.
rewrite -(Rmult_1_r 1).
apply:Rmult_lt_compat; try lra.
  case:(Rlt_le_dec 1 (xh + xl))=>//.
  move/(round_le two fexp (Znearest choice)); rewrite -Exh round_generic; first lra.
  have ->: 1 = pow 0 by [].
  apply:generic_format_bpow; rewrite /fexp; lia.
case:(Rlt_le_dec 1 (yh + yl))=>//.
move/(round_le two fexp (Znearest choice)); rewrite -Eyh round_generic; first lra.
have ->: 1 = pow 0 by [].
apply:generic_format_bpow; rewrite /fexp; lia.
Qed.
End Algo10.

Section Algo11.

Hypothesis Hp5 : Z.le 5 p.

Local Instance p_gt_0_5_10 : Prec_gt_0 p.
exact: (Z.lt_le_trans _ 5 _ _ Hp5).
Qed.


Fact  Hp1_5_10 : (1 < p)%Z.
Proof. lia. 
Qed.

Notation Hp1 := Hp1_5_10.

Notation Fast2Mult := (Fast2Mult p choice).
(* Notation F2S_err a b  :=  (F2Sum_err  p choice a b). *)


Notation Fast2Sum   := (Fast2Sum  p choice).



Notation F2P_prod a b  :=  (fst (Fast2Mult a b)).
Notation F2P_error a b  :=  (snd (Fast2Mult a b)).

Hypothesis Fast2Mult_correct: 
  forall a b, a * b =  F2P_prod a b +  F2P_error a b.

Notation F2P_errorE := (F2P_errorE Fast2Mult_correct).


Hypothesis TwoProdE : TwoProd = Fast2Mult. (* or Dekker's algorithm *)




Definition DWTimesDW11 (xh xl yh yl : R) :=
  let (ch, cl1) := (TwoProd xh yh) in
  let tl := rnd_p (xh * yl) in
  let cl2 := rnd_p (tl + xl* yh) in 
  let cl3 := rnd_p (cl1 + cl2) in Fast2Sum ch cl3.

Lemma  DWTimesDW11C (xh xl yh yl : R):  DWTimesDW11 xh xl yh yl = DWTimesDW11  yh yl  xh xl.
Proof.
rewrite /DWTimesDW11 TwoProdE Fast2MultC /=.
suff ->: rnd_p(rnd_p (xh * yl) + xl * yh) =  rnd_p (rnd_p (yh * xl) + yl * xh) by [].
(* rewrite (Rmult_comm xh) (Rmult_comm yh); ring. *)
(* Qed. *)
Abort.



Definition errorDWTDW11 xh xl yh yl  := let (zh, zl) := DWTimesDW11 xh xl yh yl in
  let xy := ((xh + xl) * (yh  + yl))%R in ((zh + zl) - xy).

Definition relative_errorDW11TFP xh xl yh yl  := let (zh, zl) := DWTimesDW11 xh xl yh yl  in
  let xy :=  ((xh + xl) * (yh  + yl))%R  in (Rabs (((zh + zl) - xy)/ xy)).


Lemma  boundDWTDW11_ge_0: 0 < 6 * (u * u).
Proof.
have upos:= upos p.
have u2pos: 0 < u * u by apply:Rmult_lt_0_compat.
 lra.
Qed.

Notation double_word := (double_word  p choice).

Fact  DWTimesDW11_Asym_r xh xl yh yl: 
  (DWTimesDW11 xh xl (-yh ) (- yl)) =
     pair_opp   (DWTimesDW11 xh xl yh yl).
Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
 rewrite /DWTimesDW11 TwoProdE /=.
(* case=> <- <-. *)
rewrite ZNE !(=^~Ropp_mult_distr_r, round_NE_opp,  Fast2Sum_asym) -ZNE //.
have->: (- (xh * yh) - - rnd_p (xh * yh)) = -((xh * yh) - rnd_p (xh * yh)) by ring.
by rewrite ZNE !(=^~Ropp_plus_distr, round_NE_opp,  Fast2Sum_asym) ?Ropp_involutive -ZNE .
Qed.

Fact  DWTimesDW11_Asym_l xh xl yh yl:
  (DWTimesDW11 (-xh) (-xl)  yh yl ) =  pair_opp   (DWTimesDW11 xh xl yh yl).
  Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
 rewrite /DWTimesDW11 TwoProdE /=.
rewrite ZNE !(=^~Ropp_mult_distr_l, round_NE_opp,  Fast2Sum_asym) -ZNE //.
have->: (- (xh * yh) - - rnd_p (xh * yh)) = -((xh * yh) - rnd_p (xh * yh)) by ring.
by rewrite ZNE !(=^~Ropp_plus_distr, round_NE_opp,  Fast2Sum_asym) -ZNE ?Ropp_involutive. 
Qed.

Fact  DWTimesDW11Sx xh xl yh yl  e: 
  (DWTimesDW11 (xh * pow e) (xl * pow e)  yh yl ) =
  map_pair (fun x => x * (pow e))  (DWTimesDW11 xh xl  yh yl ).
Proof.
rewrite /DWTimesDW11 TwoProdE /=.
by rewrite !(Rmult_comm _ yh) !(Rmult_comm _ yl)!(=^~Rmult_assoc, round_bpow, =^~Rmult_plus_distr_r,Fast2SumS,=^~Rmult_minus_distr_r ) 
  !(Rmult_comm yh)//; apply:generic_format_round.
Qed.

Fact  DWTimesDW11Sy xh xl yh yl e:
  (DWTimesDW11 xh xl   (yh * pow e) (yl * pow e)) =
    map_pair (fun x => x * (pow e))  (DWTimesDW11 xh xl  yh yl ).
Proof.
 rewrite /DWTimesDW11 TwoProdE /=.
by rewrite  !(=^~Rmult_assoc, round_bpow, =^~Rmult_plus_distr_r,Fast2SumS,=^~Rmult_minus_distr_r ) //; 
   apply:generic_format_round.
Qed.


(* Theorem 5.3 *)
Lemma DWTimesDW11_correct xh xl yh yl  (DWx:double_word xh xl) (DWy:double_word yh yl):
  let (zh, zl) := DWTimesDW11 xh xl yh yl in
  let xy := ((xh + xl) * (yh + yl))%R in
  Rabs ((zh + zl - xy) / xy) < 6 * (u * u).
Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
have [[Fxh Fxl] Exh] := DWx.
have [[Fyh Fyl] Eyh] := DWy.
case E1: DWTimesDW11 => [zh zl].
have Hp1:= Hp1.
case:(Req_dec yh 0)=> yh0.
  have yl0: yl = 0.
    by move:Eyh; rewrite  yh0 Rplus_0_l round_generic.
  move:E1; rewrite /DWTimesDW11 yh0 yl0  Rmult_0_r  TwoProdE  round_0 Fast2MultC Rmult_0_r  Fast2Mult0f. 
  rewrite  !(Rplus_0_r, Rminus_0_r, Rplus_0_l, round_0). 
  case=> <- <-. rewrite /Rdiv !(Rplus_0_r, Rmult_0_r, Rminus_0_l,  Ropp_0, Rmult_0_l, Rabs_R0, round_0).
  exact: boundDWTDW11_ge_0.
case:(Req_dec xh 0)=> xh0.
  have xl0: xl = 0.
    by move:Exh; rewrite  xh0 Rplus_0_l round_generic.
  move:E1; rewrite /DWTimesDW11 xh0 xl0 Rmult_0_l TwoProdE  round_0 Fast2Mult0f.
  rewrite  !(Rplus_0_r, Rminus_0_r, Rplus_0_l, round_0, Rmult_0_l).
  case=> <- <-; rewrite /Rdiv  !(Rplus_0_r, Rmult_0_l, Rabs_R0, round_0, Rminus_0_r).
  exact: boundDWTDW11_ge_0.
have x0: xh + xl <> 0.
  by move=> x0; apply:xh0; rewrite Exh x0 round_0.
have y0: yh + yl <> 0.
  by move=> y0; apply:yh0; rewrite Eyh y0 round_0.
rewrite /=.
clear Fxh Fxl Exh Fyh Fyl Eyh.
wlog xhpos: yh yl  xh xl zh zl DWx DWy  E1 xh0 yh0 x0 y0 / 0 <= xh.
  move=> Hwlog.
  case:(Rle_lt_dec 0 xh) => xhle0.
    by apply:Hwlog.
  have ->: (zh + zl - (xh + xl) * (yh + yl)) / ((xh + xl) * (yh +yl))= 
   ((- zh + - zl - (- xh + - xl) * (yh + yl)) / ((- xh + - xl) * (yh + yl))).
  by field; lra.
 apply:(Hwlog yh yl  (-xh) (-xl) (-zh) (-zl))=>//; try lra; last  by rewrite DWTimesDW11_Asym_l E1.
  have [[Fxh Fxl] Exh] := DWx.
  split; [split|]; try apply:generic_format_opp=>//.
  have ->:- xh + - xl = -(xh +  xl) by ring.
  by rewrite ZNE round_NE_opp -ZNE {1}Exh.

wlog yhpos: yh yl  xh xl zh zl DWx DWy  E1 xh0 yh0 x0 y0 xhpos / 0 <= yh.
  move=> Hwlog.
  case:(Rle_lt_dec 0 yh) => yhle0.
    by apply:Hwlog.
  have ->: (zh + zl - (xh + xl) * (yh + yl)) / ((xh + xl) * (yh +yl))= 
   ((- zh + - zl - ( xh +  xl) * (- yh + - yl)) / (( xh + xl) * (- yh + - yl))).
  by field; lra.
 apply:(Hwlog (-yh) (-yl)  (xh) (xl) (-zh) (-zl))=>//; try lra; last by rewrite DWTimesDW11_Asym_r E1.
  have [[Fyh Fyl] Eyh] := DWy.
  split; [split|]; try apply:generic_format_opp=>//.
  have ->:- yh + - yl = -(yh +  yl) by ring.
  by rewrite ZNE round_NE_opp -ZNE {1}Eyh.
have {} xhpos: 0 < xh by lra.
have {} yhpos: 0 < yh by lra.

wlog [xh1 xh2]: xl xh  zh zl DWx   xh0 x0 xhpos E1/ 1 <= xh  <= 2-2*u.
  move=> Hwlog.
  have [[Fxh Fxl] Exh] := DWx.
  case: (scale_generic_12 Fxh xhpos)=> exh Hxhs.
  have xhp0: 0 <  xh * pow exh by lra.
  have ->: (zh + zl - (xh + xl) * (yh + yl)) / ((xh + xl) * (yh + yl)) = 
         (zh * pow exh  + zl * pow exh  - 
         (xh * pow exh + xl * pow exh) * (yh + yl)) / ((xh * pow exh + xl * pow exh) * (yh + yl)).
    field.
    split; try lra; split; nra.
  apply:Hwlog=>//; try lra.
      split;[split|]; try apply:formatS=>//.
      by rewrite -Rmult_plus_distr_r round_bpow -Exh.
    nra.
  by rewrite DWTimesDW11Sx E1.
wlog [y1 y2]: yh yl  zh zl  DWy yh0 y0 yhpos E1/ 1 <= yh <= 2-2*u.
  move=> Hwlog.
  have [[Fyh Fyl] Eyh] := DWy.
  case: (scale_generic_12 Fyh yhpos)=> eyh Hyhs.
  have ->: (zh + zl - (xh + xl) * (yh + yl)) / ((xh + xl) * (yh + yl)) = 
         (zh * pow eyh  + zl * pow eyh - 
        (xh  + xl) * (yh  * pow eyh + yl * pow eyh)) / ((xh + xl ) * (yh * pow eyh + yl * pow eyh)).
  field;  move:(bpow_gt_0 two eyh); nra.
  apply:Hwlog=>//; try lra.
    split;[split|]; try apply:formatS=>//.
      by rewrite -Rmult_plus_distr_r round_bpow -Eyh.
    nra.  
  by rewrite DWTimesDW11Sy E1.
have upos:= upos p.
rewrite -/u in upos.
have ult1 : u < 1 by rewrite /u ; apply:bpow_lt_1; lia.
have u2pos: 0 < u * u by apply:Rmult_lt_0_compat.
have xh2': xh <= 2 by lra.
have yh2': yh <= 2 by lra.
have h0 : xh * yh <= 4 by nra.
have ylu:Rabs yl <= u by apply: (double_lpart_u _ DWy); try lia; lra.
have xlu:Rabs xl <= u by apply: (double_lpart_u _ DWx); try lia;  lra.
have [[Fxh Fxl] Exh] := DWx.
have [[Fyh Fyl] Eyh] := DWy.
move:E1; rewrite /DWTimesDW11.
rewrite TwoProdE /=.
set ch := rnd_p (xh * yh).
set cl1 :=   xh * yh -  ch.
have chcl1E: ch + cl1 = xh * yh by  rewrite /cl1 /ch; lra.
have cl1ub: Rabs cl1 <= 2 * u.
  rewrite /cl1 -Ropp_minus_distr Rabs_Ropp /ch.
  have ->: 2 * u = / 2 * u * pow 2.
    rewrite /= IZR_Zpower_pos /=; field.
  rewrite /u; apply: error_le_half_ulp'; first lia.
  rewrite Rabs_pos_eq  /= ?IZR_Zpower_pos /=; nra.
set tl := rnd_p (xh * yl).
pose e1 := tl - xh*yl.
have tlE: tl = xh*yl + e1 by rewrite  /e1 /tl; ring.
have xhylub: Rabs (xh*yl) <= 2*u - 2*(u*u).
  rewrite Rabs_mult Rabs_pos_eq; last lra.
  have->: 2 * u - 2 * (u * u) = (2 - 2 * u) * u by ring.
  apply:Rmult_le_compat; try apply: Rabs_pos; lra.

have tlub: Rabs tl <= 2*u -2* (u *u).
  rewrite /tl  ZNE -round_NE_abs -ZNE.
  suff -> : 2 * u - 2 * (u * u) = rnd_p (2 * u - 2 * (u * u))  by apply:round_le.
  rewrite round_generic //.
  have ->:  (2 * u - 2 * (u * u)) = (pow (-p) * ( pow p - 1) * (pow (1 -p))).
    rewrite /u !bpow_plus /= IZR_Zpower_pos /= Rmult_minus_distr_l.
    rewrite !Rmult_1_r.
    have ->:  pow (-p) * (pow p ) = 1 by rewrite -bpow_plus; ring_simplify (-p + p)%Z.
    ring.
  have->: pow (- p) * (pow p - 1) * pow (1 - p) =  (pow p - 1) * ( pow (1 - p)*(pow (- p))) by ring.
  rewrite -bpow_plus.
  apply:(formatS Hp1).
  have ->: (pow p - 1)= F2R  (Float two ((2 ^ p)  -1)%Z 0).
    rewrite /F2R /= minus_IZR (IZR_Zpower two) ; try lia; ring.
  apply: FLX_format_Rabs_Fnumf =>//.
  rewrite /F2R/=  minus_IZR (IZR_Zpower two) ?Rabs_pos_eq; try lia; try lra.
  suff: pow 0 <= pow p by rewrite /=; lra.
  apply bpow_le; lia.
have e1ub: Rabs e1 <= u*u.
  rewrite /e1.
  have->: u * u = /2 * u * (pow (1 -p)) by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  rewrite bpow_plus  /= IZR_Zpower_pos /= -/u; apply:(Rle_trans _  (2 * u - 2 * (u * u))) =>//.
  lra.
have xlyhub: Rabs (xl*yh) <= 2*u - 2*(u*u).
  rewrite Rabs_mult (Rabs_pos_eq yh); try lra.
  have->: 2 * u - 2 * (u * u) = u * (2 - 2 * u) by ring.
  apply:Rmult_le_compat; try apply: Rabs_pos; lra.
set cl2 := rnd_p (tl + xl * yh).
pose e3 := cl2 - (tl + xl * yh).
have tlxlyh: Rabs (tl + xl * yh ) <= 4*u - 4*(u * u).
  apply:(Rle_trans _ _ _ (Rabs_triang _ _)); lra.
have cleub: Rabs cl2 <= 4*u - 4*(u * u).
  rewrite /cl2.
  suff->:  4*u - 4*(u * u) = rnd_p  (4*u - 4*(u * u)) 
    by rewrite ZNE -round_NE_abs -ZNE; apply:round_le.
  rewrite round_generic //.
  have ->:(4 * u - 4 * (u * u)) = (1 -u)* pow (2 -p).
    rewrite bpow_plus -/u /= IZR_Zpower_pos /=; field.
  apply:(formatS Hp1).
  have fle : 1 - u = F2R (Float two ((2 ^ p) -1) (-p)).
    rewrite /F2R  minus_IZR (IZR_Zpower two); try lia. 
  have->: (Fexp {| Fnum := 2 ^ p - 1; Fexp := - p |}) = (-p)%Z by [].
    ring_simplify; rewrite -bpow_plus Z.add_opp_diag_r /= /u; ring.
  apply: (FLX_format_Rabs_Fnum p fle); rewrite /=  minus_IZR (IZR_Zpower two); last  lia.
  rewrite Rabs_pos_eq; first lra.
  suff: pow 0 <= pow p by rewrite /=; lra.
  apply bpow_le; lia.
have e3ub: Rabs e3 <= 2 * u * u.
  rewrite /e3.
  have->: 2 * u * u = /2 * u * (pow (2 -p)) by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  rewrite bpow_plus  /= IZR_Zpower_pos /= -/u; lra.
set cl3 := rnd_p (cl1 + cl2).
pose e4 := cl3 - (cl1 + cl2).
have cl1cl2: Rabs (cl1 + cl2) <= 6*u - 4*(u * u).
  apply:(Rle_trans _ _ _ (Rabs_triang _ _)); lra.
have cl3ub: Rabs cl3 <= 6*u.
  rewrite /cl3 ZNE -round_NE_abs -ZNE.
  suff ->: 6*u = rnd_p (6 * u) by apply:round_le; lra.
  rewrite round_generic //.
  rewrite /u; apply:formatS=>//.
  have fle : 6 = F2R (Float two 6 0) by rewrite /F2R /=; ring.
  apply: (FLX_format_Rabs_Fnum p fle);  rewrite /= Rabs_pos_eq; last lra.
  apply:(Rlt_le_trans _ 8); first lra.
  have->:8 = pow 3 by [].
  apply:bpow_le; lia.
have Fcl1: format cl1.    
  by rewrite /cl1 -Ropp_minus_distr; apply/generic_format_opp/ mult_error_FLX.
have e4ub: Rabs e4 <= 4 * u * u.
 rewrite /e4.
  have->: 4 * u * u = /2 * u * (pow (3 -p)) by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  rewrite bpow_plus  /= IZR_Zpower_pos /= -/u; nra.
have hf2Sc: Rabs cl3 <= Rabs ch.
  apply:(Rle_trans _ (6 * u))=>//.
  apply: (Rle_trans _ 1).
   apply: (Rle_trans _ (8 * u)); try lra.
  suff : pow (3 - p) <= pow 0 .
   rewrite bpow_plus  /= IZR_Zpower_pos /= -/u; lra.
   apply:bpow_le; lia.
  have ->:  1 = pow 0 by [].
  rewrite -(round_generic two fexp (Znearest choice) (pow 0)).
  rewrite /ch ZNE -round_NE_abs -ZNE; apply/round_le; rewrite /= Rabs_pos_eq.
  + nra.
  + apply: Rmult_le_pos; lra.
    apply:generic_format_bpow; rewrite /fexp; lia.
rewrite (surjective_pairing (Fast2Sum _ _)).    
rewrite F2Sum_correct_abs=>//; try apply: generic_format_round; 
  last by rewrite (round_generic _ _ _ cl1)//.
rewrite (round_generic _ _ _ cl1)//.
case=> zhe  zle.
pose eta := -(xl* yl) + e1  + e3 + e4.
have ->: zh + zl =  (xh + xl) * (yh + yl) + eta.
  rewrite -zhe -zle.
  ring_simplify; rewrite -/cl3.
  have-> : ch = xh*yh -cl1 by rewrite /cl1;   ring.
  have->: cl3 = cl1 + cl2 + e4 by rewrite /e4; ring.
  have->: cl2 = tl + xl * yh  + e3 by rewrite /e3; ring.
  (* have->: tl2 = xl * yh + e2 by rewrite /e2; ring. *)
  have->: tl = xh * yl + e1 by rewrite /e1; ring.
  rewrite /eta ; ring.
have etaub: Rabs eta <= 8 *(u * u).
  rewrite /eta.
  apply:(Rle_trans _ (Rabs (- (xl * yl))  + Rabs e1  + Rabs e3 + Rabs e4)).
    repeat (apply: (Rle_trans _ _ _ (Rabs_triang _ _)); 
      apply:Rplus_le_compat_r); lra.
  suff : Rabs (- (xl * yl)) <= u * u by lra.
  rewrite Rabs_Ropp Rabs_mult; apply:Rmult_le_compat; try apply:Rabs_pos ; lra.
case:(Rlt_le_dec 2 (xh * yh))=>xhyh2.
  apply:(Rle_lt_trans _ ((8 * (u * u)) / (2 * (1 - u) * (1 - u)))); last first.
    apply: (Rle_lt_trans _ (6*  (u * u) / ((1 + u) * (1 + u)))); last first.
      have h: 1 < ((1 + u) * (1 + u)).
        rewrite -{1}[1]Rmult_1_l; apply:Rmult_lt_compat; lra.
      rewrite -[X in _ < X]Rmult_1_r.
      rewrite /Rdiv; apply:Rmult_lt_compat_l; try lra.
      rewrite -[X in _< X]Rinv_1.
      apply:Rinv_lt; lra.
    set d1 := (2 * (1 - u) * (1 - u)).
    set d2 :=((1 + u) * (1 + u)).
    set u2 := u * u.
    rewrite /Rdiv (Rmult_comm 8) (Rmult_comm 6) 2!Rmult_assoc.
    apply:Rmult_le_compat_l; rewrite /u2; try lra.
    suff : 0 < d1.
      suff: 0 < d2.
        move=> *.
        suff: 8 * d2 < 6 * d1.
          move=> *.
          apply: (Rmult_le_reg_r d1); try lra.
          rewrite Rmult_assoc Rinv_l; try lra.
          rewrite Rmult_1_r; apply: (Rmult_le_reg_r d2); try lra.
          have->: 6 * / d2 * d1 * d2 = 6 * d1 by field; lra.
          lra.
        rewrite /d2 /d1.
        ring_simplify.
        set ue2:= u^2.
        apply: (Rplus_lt_reg_r (-( 8 * ue2 + 16 * u +  8))).
        ring_simplify.
        have ue2pos:= (pow2_ge_0  u).
        clear - upos ue2pos  ult1 Hp5.
        suff : 40 * u < 4 by rewrite /ue2 ; lra.
        apply:(Rlt_le_trans _ (64 * u)); try lra.
        apply:(Rle_trans _ 4); try lra.
        have ->: 64 = 2 * (2 * 16) by [].
        rewrite -Rmult_assoc -[X in _ <= X]Rmult_1_r.
        have->:  2 * 2 * 16 * u = 4 * (16 * u) by ring.
        apply: Rmult_le_compat; try lra.
        have ->: 1 = pow 0 by [].
        have ->: 16 * u = pow (4 - p) by rewrite bpow_plus -/u.
        apply:bpow_le; lia.
        have->: d2 = 1 + 2*u + u * u by rewrite /d2 ; ring.
      lra.
    have ->: d1 = 2 - 4 * u + 2* u * u by rewrite /d1; ring.
    suff: 2 * u < 1   by lra.
    have ->: 1 = pow 0 by [].
    have->: 2 * u = pow (1 -p) by rewrite bpow_plus -/u.
    apply:bpow_lt; lia.
  rewrite /Rdiv Rabs_mult.
  apply:Rmult_le_compat; try apply:Rabs_pos.
    by ring_simplify((xh + xl) * (yh + yl) + eta - (xh + xl) * (yh + yl)).
  have xpos: 0 < xh + xl.
    clear - xh1 xh2 xlu  upos ult1.
    suff: 1 -u <= xh + xl by nra.
    move/Rabs_le_inv: xlu; lra.
  have :(xh + xl ) >= xh * (1 - u).
    move/Rabs_le_inv: xlu=>[xlul xluu].
    apply/Rle_ge.
    suff : -u * xh <= xl by lra.
    apply: (Rle_trans _ (-u)); try lra.
    suff : u * 1 <= u * xh by lra.
    by apply: Rmult_le_compat_l; lra.
  have :(yh + yl ) >= yh * (1 - u).
    clear -  y1    upos ult1 ylu.
    move/Rabs_le_inv: ylu=>[ylul yluu].
    apply/Rle_ge.
    suff : -u * yh <= yl by lra.
    apply: (Rle_trans _ (-u)); try lra.
    suff : u * 1 <= u * yh by lra.
    by apply: Rmult_le_compat_l; lra.
  move =>*.    
  have hypos : 0 < (yh + yl).
    clear -  y1   ult1 ylu.
    move/Rabs_le_inv: ylu=>[ylul yluu]; by lra.
  rewrite Rabs_pos_eq.
    suff h: 0 < (2 * (1 - u) * (1 - u)) <= ((xh + xl) * (yh + yl)).
      apply:Rinv_le; lra.
    split;  first lra.
    apply:(Rle_trans _ (xh * (1 -u) * (yh * (1 -u)))).
      have -> : xh * (1 - u) * (yh * (1 - u)) = (xh * yh) * (1-u) *(1 -u) by ring.
      apply:Rmult_le_compat_r; try lra.
      apply:Rmult_le_compat_r; lra.
    apply:Rmult_le_compat; nra.
  apply/Rlt_le/Rinv_0_lt_compat.
  by apply: Rmult_lt_0_compat.
have  cl1u: Rabs cl1 <= u.
  rewrite /cl1 -Ropp_minus_distr Rabs_Ropp /ch.
  have ->: u = / 2 * u * (pow 1)  by rewrite /= IZR_Zpower_pos /=; field.
  rewrite /u; apply: error_le_half_ulp'; first lia.
  rewrite Rabs_pos_eq  /= ?IZR_Zpower_pos /= ?Rmult_1_r //.
  clear - xh1 y1;  nra.
have hsxhyh: xh + yh <= 3.
  apply:l5_2; nra.
have tl1u: Rabs tl <= xh * u.
  rewrite /tl  ZNE -round_NE_abs -ZNE.
 suff -> : xh * u = rnd_p (xh * u).
 apply:round_le.
  rewrite Rabs_mult Rabs_pos_eq; try lra.
  apply:Rmult_le_compat_l; try lra.
  by rewrite /u round_bpow round_generic.
have stl12u: Rabs (tl + xl * yh)  <= 3 * u.
  apply: (Rle_trans _ _ _ (Rabs_triang _ _)).
  apply:(Rle_trans _ ((xh  + yh)* u)); last by  apply :Rmult_le_compat_r; lra.
  have tl2u : Rabs (xl * yh) <= yh * u. 
    rewrite Rabs_mult Rmult_comm Rabs_pos_eq; last lra.
    apply:Rmult_le_compat_l =>//; lra.
  apply:(Rle_trans _ ( xh * u + yh * u)); lra.
have cl2u: Rabs cl2 <= 3 * u  + 2 * u * u.
  have ->: cl2 = (tl + xl * yh) + e3 by rewrite /e3; ring.
  apply: (Rle_trans _ _ _ (Rabs_triang _ _)); lra.
have scl12u: Rabs (cl1 + cl2) <= 4*u + 2* u *u.
  apply: (Rle_trans _ _ _ (Rabs_triang _ _)); lra.
have e4u: Rabs e4 <= 2 * u *u.
  rewrite /e4 /cl3.
  have-> :  2 * u * u = / 2 * pow (- p) * pow (2 - p).
    rewrite bpow_plus -/u /= IZR_Zpower_pos /=; field.
  have cS:= (choiceP ZNE).
  apply:(@error_le_half_ulp_W _ Hp1 choice cS ZNE _ _ ( 2 * u * u)) =>//.
    rewrite !bpow_plus -/u /= IZR_Zpower_pos /=; lra.
  rewrite !bpow_plus -/u /= IZR_Zpower_pos /=; lra.
have etaub7: Rabs eta <= 6 *(u * u).
  rewrite /eta.
  apply:(Rle_trans _ (Rabs (- (xl * yl))  + Rabs e1  + Rabs e3 + Rabs e4)).
    repeat (apply: (Rle_trans _ _ _ (Rabs_triang _ _)); 
      apply:Rplus_le_compat_r); lra.
  suff : Rabs (- (xl * yl)) <= u * u by lra.
  rewrite Rabs_Ropp Rabs_mult; apply:Rmult_le_compat; try apply:Rabs_pos ; lra.
ring_simplify (((xh + xl) * (yh + yl) + eta - (xh + xl) * (yh + yl))).
case: xh1 => xh1; last first.
  have che: ch = yh by rewrite /ch -xh1 Rmult_1_l round_generic.
  have cl1e : cl1 = 0 by rewrite /cl1 -xh1  Rmult_1_l che ; ring.
  have tle: tl = yl  by rewrite /tl  -xh1 Rmult_1_l round_generic.
  have e10: e1= 0 by rewrite /e1 tle -xh1;  ring.
  have cl3e: cl3 = cl2.
    rewrite /cl3 cl1e Rplus_0_l /cl2 round_generic //;  apply: generic_format_round.
  have e40: e4 = 0 by  rewrite /e4  cl1e cl3e; ring.
  rewrite /eta e10 e40 !Rplus_0_r.
  have xpos: 0 < xh + xl by  move/Rabs_le_inv: xlu; lra.
  have ypos: 0 < yh + yl by move/Rabs_le_inv: ylu; lra.
  have xyous: 0 < (xh + xl) * (yh + yl) by apply/Rmult_lt_0_compat; lra .
  rewrite Rabs_mult Rabs_Rinv; try lra.
  apply:(Rmult_lt_reg_r (Rabs ((xh + xl) * (yh + yl)))).
    rewrite Rabs_pos_eq; lra.
  rewrite Rmult_assoc Rinv_l ?Rmult_1_r; last by  rewrite Rabs_pos_eq; lra.
  apply: (Rle_lt_trans _ (Rabs (- (xl * yl))   + Rabs e3)).
    apply: (Rle_trans  _ _ _ (Rabs_triang _ _)).
    apply:Rplus_le_compat_r; lra.
  (* apply: (Rle_trans  _ _ _ (Rabs_triang _ _)); apply:Rplus_le_compat_r; lra. *)
  rewrite Rabs_Ropp Rabs_mult.
  apply:(Rle_lt_trans _ (3 * (u * u))); try lra.
    clear - ylu xlu e3ub upos.
    have: Rabs xl * Rabs yl <= u *u .  
      by apply:Rmult_le_compat; (try apply: Rabs_pos).
    lra.
  suff:  3 * (u * u) < (6 * Rabs ((xh + xl) * (yh + yl))) * (u * u) by lra.
  apply:Rmult_lt_compat_r; first lra.
  rewrite Rabs_pos_eq; last lra.
  apply: (Rlt_le_trans _ (6 *(( 1- u) *(1-u)))); last first.
    apply:Rmult_le_compat_l; try lra.
    apply:Rmult_le_compat; try lra.
      move/Rabs_le_inv: xlu => [xll xlu];  lra.
    move/Rabs_le_inv: ylu => [yll ylu];  lra.
  suff: 4 * u < 1 by lra.
  have -> : 4 = pow (2) by [].
  rewrite /u  -bpow_plus.
  have -> : (2 + -p = - (p - 2))%Z  by  ring.
  apply : bpow_lt_1; lia.
case: y1 => yh1; last first.
 have che: ch = xh by rewrite /ch -yh1 Rmult_1_r round_generic.
  have cl1e : cl1 = 0 by rewrite /cl1 -yh1  Rmult_1_r che ; ring.
  (* have tl2e: tl2 = xl  by rewrite /tl2  -yh1 Rmult_1_r round_generic. *)
  (* have e20: e2= 0 by rewrite /e2 tl2e -yh1;  ring. *)
  have cl3e: cl3 = cl2.
    rewrite /cl3 cl1e Rplus_0_l /cl2 round_generic //;  apply: generic_format_round.
  have e40: e4 = 0 by  rewrite /e4  cl1e cl3e; ring.
  rewrite /eta  e40 !Rplus_0_r.
  have xpos: 0 < xh + xl by  move/Rabs_le_inv: xlu; lra.
  have ypos: 0 < yh + yl by move/Rabs_le_inv: ylu; lra.
  have xyous: 0 < (xh + xl) * (yh + yl) by apply/Rmult_lt_0_compat; lra .
  rewrite Rabs_mult Rabs_Rinv; try lra.
  apply:(Rmult_lt_reg_r (Rabs ((xh + xl) * (yh + yl)))).
    rewrite Rabs_pos_eq; lra.
  rewrite Rmult_assoc Rinv_l ?Rmult_1_r; last by  rewrite Rabs_pos_eq; lra.
  apply: (Rle_lt_trans _ (Rabs (- (xl * yl))  + Rabs e1 + Rabs e3)).
  apply: (Rle_trans  _ _ _ (Rabs_triang _ _)).
  apply:Rplus_le_compat_r.
  apply: (Rle_trans  _ _ _ (Rabs_triang _ _)); apply:Rplus_le_compat_r; lra.
  rewrite Rabs_Ropp Rabs_mult.
  apply:(Rle_lt_trans _ (4 * (u * u))); try lra.
    have: Rabs xl * Rabs yl <= u *u .  
      by apply:Rmult_le_compat; (try apply: Rabs_pos).
    lra.  
  suff:  4 * (u * u) < (6 * Rabs ((xh + xl) * (yh + yl))) * (u * u) by lra.
  apply:Rmult_lt_compat_r; first lra.
  rewrite Rabs_pos_eq; last lra.
  apply: (Rlt_le_trans _ (6 *(( 1- u) *(1-u)))); last first.
    apply:Rmult_le_compat_l; try lra.
    apply:Rmult_le_compat; try lra.
      move/Rabs_le_inv: xlu => [xll xlu];  lra.
    move/Rabs_le_inv: ylu => [yll ylu];  lra.
  suff: 6 * u < 1 by lra.
  apply:(Rlt_trans _ (8 * u)); try lra.
  have -> : 8 = pow (3) by [].
  rewrite /u  -bpow_plus.
  have -> : (3 + -p = - (p - 3))%Z  by  ring.
  apply : bpow_lt_1; lia.
have xpos: 0 < xh + xl by  move/Rabs_le_inv: xlu; lra.
have ypos: 0 < yh + yl by move/Rabs_le_inv: ylu; lra.
have xypos: 0 < (xh + xl) * (yh + yl) by apply/Rmult_lt_0_compat; lra.
rewrite Rabs_mult Rabs_Rinv; try lra.
rewrite [X in _ * / X  ] Rabs_pos_eq; try lra.
apply:(Rmult_lt_reg_r ((xh + xl) * (yh + yl))) =>//.
rewrite Rmult_assoc Rinv_l ?Rmult_1_r; try lra.
apply: (Rle_lt_trans _ (6 * (u* u))) =>//.
rewrite -[X in X < _]Rmult_1_r.
apply:Rmult_lt_compat_l; try lra.
rewrite -(Rmult_1_r 1).
apply:Rmult_lt_compat; try lra.
  case:(Rlt_le_dec 1 (xh + xl))=>//.
  move/(round_le two fexp (Znearest choice)); rewrite -Exh round_generic; first lra.
  have ->: 1 = pow 0 by [].
  apply:generic_format_bpow; rewrite /fexp; lia.
case:(Rlt_le_dec 1 (yh + yl))=>//.
move/(round_le two fexp (Znearest choice)); rewrite -Eyh round_generic; first lra.
have ->: 1 = pow 0 by [].
apply:generic_format_bpow; rewrite /fexp; lia.
Qed.

End Algo11.


Section Algo12.

Hypothesis Hp4 : Z.le 4 p.

Local Instance p_gt_0_4_12 : Prec_gt_0 p.
exact: (Z.lt_le_trans _ 4 _ _ Hp4).
Qed.



Notation Hp1_4_10 := (Hp1_4_10 Hp4).

Notation Hp1 := Hp1_4_10.

Notation Fast2Mult := (Fast2Mult p choice).
Notation Fast2MultC := (Fast2MultC p choice).


Notation Fast2Sum := (Fast2Sum p choice).

Notation F2P_prod a b  :=  (fst (Fast2Mult a b)).
Notation F2P_error a b  :=  (snd (Fast2Mult a b)).

Hypothesis Fast2Mult_correct: 
  forall a b, a * b =  F2P_prod a b +  F2P_error a b.

Notation F2P_errorE := (F2P_errorE Fast2Mult_correct).


Hypothesis TwoProdE : TwoProd = Fast2Mult. (* or Dekker's algorithm *)



Definition DWTimesDW12 (xh xl yh yl : R) :=
  let (ch, cl1) := (TwoProd xh yh) in
  let tl0 :=  rnd_p (xl * yl) in
  let tl1 := rnd_p (xh * yl + tl0) in
  let cl2 := rnd_p (tl1 + xl * yh) in 
  let cl3 := rnd_p (cl1 + cl2) in  Fast2Sum ch cl3.

Definition errorDWTDW12 xh xl yh yl  := let (zh, zl) := DWTimesDW12 xh xl yh yl in
  let xy := ((xh + xl) * (yh  + yl))%R in ((zh + zl) - xy).


Definition relative_errorDWTFP12 xh xl yh yl  := let (zh, zl) := DWTimesDW12 xh xl yh yl  in
  let xy :=  ((xh + xl) * (yh  + yl))%R  in (Rabs (((zh + zl) - xy)/ xy)).


Lemma  boundDWTDW12_ge_0: 0 < 5 * (u * u).
Proof.
have upos:= upos p.
have u2pos: 0 < u * u by apply:Rmult_lt_0_compat.
 lra.
Qed.


Notation double_word := (double_word  p choice).


Fact  DWTimesDW12_Asym_r xh xl yh yl  : 
  (DWTimesDW12 xh xl (-yh ) (- yl)) =
     pair_opp (DWTimesDW12 xh xl yh yl). 
Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
 rewrite /DWTimesDW12 TwoProdE /=.
rewrite ZNE !(=^~Ropp_mult_distr_r, round_NE_opp,  Fast2Sum_asym) -ZNE //.
have->: (- (xh * yh) - - rnd_p (xh * yh)) = -((xh * yh) - rnd_p (xh * yh)) by ring.
by rewrite ZNE !(=^~Ropp_plus_distr, round_NE_opp,  Fast2Sum_asym) ?Ropp_involutive -ZNE .
Qed.

Fact  DWTimesDW12_Asym_l xh xl yh yl: 
  (DWTimesDW12 (-xh) (-xl)  yh yl ) =
       pair_opp (DWTimesDW12 xh xl yh yl). 
Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
 rewrite /DWTimesDW12 TwoProdE /=.
rewrite ZNE !(=^~Ropp_mult_distr_l, round_NE_opp,  Fast2Sum_asym) -ZNE //.
have->: (- (xh * yh) - - rnd_p (xh * yh)) = -((xh * yh) - rnd_p (xh * yh)) by ring.
by rewrite ZNE !(=^~Ropp_plus_distr, round_NE_opp,  Fast2Sum_asym) ?Ropp_involutive -ZNE .
Qed.

Fact  DWTimesDW12Sx xh xl yh yl e: 
  (DWTimesDW12 (xh * pow e) (xl * pow e)  yh yl ) =
      map_pair (fun x => x * (pow e))   (DWTimesDW12 xh xl yh yl).
Proof.
rewrite /DWTimesDW12 TwoProdE /=.
by rewrite !(Rmult_comm _ yh) !(Rmult_comm _ yl)!(=^~Rmult_assoc, round_bpow, =^~Rmult_plus_distr_r,Fast2SumS,=^~Rmult_minus_distr_r ) 
  !(Rmult_comm yh)//; apply:generic_format_round.
Qed.

Fact  DWTimesDW12Sy xh xl yh yl e:
  (DWTimesDW12 xh xl   (yh * pow e) (yl * pow e)) =
   map_pair (fun x => x * (pow e))   (DWTimesDW12 xh xl yh yl).
Proof.
 rewrite /DWTimesDW12 TwoProdE /=.
by rewrite  !(=^~Rmult_assoc, round_bpow, =^~Rmult_plus_distr_r,Fast2SumS,=^~Rmult_minus_distr_r ) //; 
   apply:generic_format_round.
Qed.

Notation double_lpart_u := (double_lpart_u Hp4).

Fact DWTimesDW12f0 xh xl :   (DWTimesDW12 xh xl   0 0) =(0 , 0).
Proof.
 rewrite /DWTimesDW12 TwoProdE /=.
rewrite !(Rmult_0_r, round_0, Rminus_0_r, Rplus_0_r).
 rewrite Fast2Sumf0 //; apply:generic_format_0.
Qed.
Fact DWTimesDW120f yh yl  :   (DWTimesDW12    0 0 yh yl ) =(0 , 0).
Proof.
 rewrite /DWTimesDW12 TwoProdE /=.
rewrite !(Rmult_0_l, round_0, Rminus_0_r, Rplus_0_r).
 rewrite Fast2Sumf0 //; apply:generic_format_0.
Qed.

Fact DWTimesDW12n0 xh xl yh yl (DWx: double_word xh xl) (DWy:double_word yh yl) :  
     DWTimesDW12 xh xl yh yl <> (0,0) -> xh + xl <> 0 /\ yh + yl <> 0.
Proof.
move=> h.
case:DWx =>[[Fxh Fxl] xE].
case:DWy =>[[Fyh Fyl] yE].
split=> [x0|y0]; apply: h.
  have xh0: xh = 0 by  move:xE; rewrite x0 round_0.
  have xl0: xl = 0 by move: x0 xh0 ;lra.
  by rewrite xh0 xl0 DWTimesDW120f.
have yh0: yh = 0 by  move:yE; rewrite y0 round_0.
  have yl0: yl = 0 by move: y0 yh0 ;lra.
  by rewrite yh0 yl0 DWTimesDW12f0.
Qed.


Fact DWTimesDW12n0' xh xl yh yl (DWx: double_word xh xl) (DWy:double_word yh yl) :  
     DWTimesDW12 xh xl yh yl <> (0,0) -> xh + xl <> 0 ->  yh + yl <> 0.
Proof.
move=> h x0.
case:DWx =>[[Fxh Fxl] xE].
case:DWy =>[[Fyh Fyl] yE].
move=> y0; apply: h.
have yh0: yh = 0 by  move:yE; rewrite y0 round_0.
  have yl0: yl = 0 by move: y0 yh0 ;lra.
  by rewrite yh0 yl0 DWTimesDW12f0.
Qed.



(* Theorem 5.1 *)
Lemma DWTimesDW12_correct xh xl yh yl  (DWx:double_word xh xl) (DWy:double_word yh yl):
  let (zh, zl) := DWTimesDW12 xh xl yh yl in
  let xy := ((xh + xl) * (yh + yl))%R in
  Rabs ((zh + zl - xy) / xy) < 5 * (u * u).
Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
have [[Fxh Fxl] Exh] := DWx.
have [[Fyh Fyl] Eyh] := DWy.
case E1: DWTimesDW12 => [zh zl].
have Hp1:= Hp1.
case:(Req_dec yh 0)=> yh0.
  have yl0: yl = 0.
    by move:Eyh; rewrite  yh0 Rplus_0_l round_generic. 
  move:E1; rewrite /DWTimesDW12 /= yh0 yl0 Rplus_0_r Rmult_0_r TwoProdE 
   Fast2MultC Fast2Mult0f !(Rmult_0_r,Rplus_0_l,Rplus_0_r,Rminus_0_r,round_0)
    Fast2Sumf0; last by apply:generic_format_0.
  case=> <- <-; rewrite Rplus_0_r   /Rdiv  Rmult_0_l Rabs_R0.
  exact: boundDWTDW12_ge_0.
case:(Req_dec xh 0)=> xh0.
  have xl0: xl = 0.
    by move:Exh; rewrite  xh0 Rplus_0_l round_generic.
  move:E1;rewrite /DWTimesDW12 xh0 xl0 Rmult_0_l TwoProdE round_0 Fast2Mult0f.
  rewrite /Fast2Sum /F2SumFLX.Fast2Sum  !(Rplus_0_r, Rminus_0_r, Rplus_0_l, 
  round_0, Rmult_0_l).
  case=> <- <-; rewrite Rplus_0_r  /Rdiv   Rmult_0_l Rabs_R0.
  exact: boundDWTDW12_ge_0.
have x0: xh + xl <> 0.
  by move=> x0; apply:xh0; rewrite Exh x0 round_0.
have y0: yh + yl <> 0.
  by move=> y0; apply:yh0; rewrite Eyh y0 round_0.
rewrite /=.
clear Fxh Fxl Exh Fyh Fyl Eyh.
wlog xhpos: yh yl  xh xl zh zl DWx DWy  E1 xh0 yh0 x0 y0 / 0 <= xh.
  move=> Hwlog.
  case:(Rle_lt_dec 0 xh) => xhle0.
    by apply:Hwlog.
  have ->: (zh + zl - (xh + xl) * (yh + yl)) / ((xh + xl) * (yh +yl))= 
   ((- zh + - zl - (- xh + - xl) * (yh + yl)) / ((- xh + - xl) * (yh + yl))).
  by field; lra.
  apply:(Hwlog yh yl  (-xh) (-xl) (-zh) (-zl))=>//; try lra; 
    last  by rewrite DWTimesDW12_Asym_l E1.
  have [[Fxh Fxl] Exh] := DWx.
  split; [split|]; try apply:generic_format_opp=>//.
  have ->:- xh + - xl = -(xh +  xl) by ring.
  by rewrite ZNE round_NE_opp -ZNE {1}Exh.
wlog yhpos: yh yl  xh xl zh zl DWx DWy  E1 xh0 yh0 x0 y0 xhpos / 0 <= yh.
  move=> Hwlog.
  case:(Rle_lt_dec 0 yh) => yhle0.
    by apply:Hwlog.
  have ->: (zh + zl - (xh + xl) * (yh + yl)) / ((xh + xl) * (yh +yl))= 
   ((- zh + - zl - ( xh +  xl) * (- yh + - yl)) / 
   (( xh + xl) * (- yh + - yl))).
    by field; lra.
  apply:(Hwlog (-yh) (-yl)  (xh) (xl) (-zh) (-zl))=>//; try lra; 
    last by rewrite DWTimesDW12_Asym_r E1.
  have [[Fyh Fyl] Eyh] := DWy.
  split; [split|]; try apply:generic_format_opp=>//.
  have ->:- yh + - yl = -(yh +  yl) by ring.
  by rewrite ZNE round_NE_opp -ZNE {1}Eyh.
have {} xhpos: 0 < xh by lra.
have {} yhpos: 0 < yh by lra.
wlog [xh1 xh2]: xl xh  zh zl DWx   xh0 x0 xhpos E1/ 1 <= xh  <= 2-2*u.
  move=> Hwlog.
  have [[Fxh Fxl] Exh] := DWx.
  case: (scale_generic_12 Fxh xhpos)=> exh Hxhs.
    have xhp0: 0 <  xh * pow exh by lra.
    have ->: (zh + zl - (xh + xl) * (yh + yl)) / ((xh + xl) * (yh + yl)) = 
         (zh * pow exh  + zl * pow exh  - 
         (xh * pow exh + xl * pow exh) * (yh + yl)) / 
           ((xh * pow exh + xl * pow exh) * (yh + yl)).
      field.
    split; try lra; split; nra.
  apply:Hwlog=>//; try lra.
  + split;[split|]; try apply:formatS=>//.
    by rewrite -Rmult_plus_distr_r round_bpow -Exh.
  + nra.
  by rewrite DWTimesDW12Sx E1.
wlog [y1 y2]: yh yl  zh zl  DWy yh0 y0 yhpos E1/ 1 <= yh <= 2-2*u.
  move=> Hwlog.
  have [[Fyh Fyl] Eyh] := DWy.
  case: (scale_generic_12 Fyh yhpos)=> eyh Hyhs.
  have ->: (zh + zl - (xh + xl) * (yh + yl)) / ((xh + xl) * (yh + yl)) = 
         (zh * pow eyh  + zl * pow eyh - 
        (xh  + xl) * (yh  * pow eyh + yl * pow eyh)) / 
        ((xh + xl ) * (yh * pow  eyh + yl * pow eyh)). 
    field;  move:(bpow_gt_0 two eyh); nra.
  apply:Hwlog=>//; try lra.
  + split;[split|]; try apply:formatS=>//.
      by rewrite -Rmult_plus_distr_r round_bpow -Eyh.
  + nra.  
  by rewrite DWTimesDW12Sy E1.
have upos:= upos p.
rewrite -/u in upos.
have ult1 : u < 1 by rewrite /u ; apply:bpow_lt_1; lia.
have u2pos: 0 < u * u by apply:Rmult_lt_0_compat.
have xh2': xh <= 2 by lra.
have yh2': yh <= 2 by lra.
have h0 : xh * yh < 4 by nra.
have ylu:Rabs yl <= u by apply: (double_lpart_u DWy); lra.
have xlu:Rabs xl <= u by apply: (double_lpart_u DWx); lra.
have [[Fxh Fxl] Exh] := DWx.
have [[Fyh Fyl] Eyh] := DWy.
move:E1; rewrite /DWTimesDW12.
rewrite TwoProdE /=.
set ch := rnd_p (xh * yh).
set cl1 :=   xh * yh -  ch.
have chcl1E: ch + cl1 = xh * yh by  rewrite /cl1 /ch; lra.
have cl1ub: Rabs cl1 <= 2 * u.
  rewrite /cl1 -Ropp_minus_distr Rabs_Ropp /ch.
  have ->: 2 * u = / 2 * u * pow 2.
    have->: pow 2 = 4 by [].
    field.
  rewrite /u; apply: error_le_half_ulp'; first lia.
  have->: pow 2 = 4 by [].
  rewrite Rabs_pos_eq;nra.
have xhylub: Rabs (xh*yl) <= 2*u - 2*(u*u).
  rewrite Rabs_mult Rabs_pos_eq; last lra.
  have->: 2 * u - 2 * (u * u) = (2 - 2 * u) * u by ring.
  apply:Rmult_le_compat; try apply: Rabs_pos; lra.

set tl0 := rnd_p (xl * yl).
have tl0ub: Rabs tl0 <= (u *u).
  rewrite /tl0 ZNE -round_NE_abs -ZNE.
  suff -> : (u * u) = rnd_p (u * u).
    apply:round_le; rewrite Rabs_mult; apply:Rmult_le_compat=>//; 
     apply : Rabs_pos.
  rewrite round_generic //.  
  have->: u * u = pow (-p -p) by rewrite bpow_plus /u.
  apply: generic_format_bpow; rewrite /fexp; lia.
pose e0 := tl0 - xl*yl.
have tl0E: tl0 = xl*yl + e0 by rewrite  /e0 /tl0; ring.
have e0ub: Rabs e0 <= /2 *(u*u*u).
  rewrite /e0.
  have->:  /2 *(u*u*u) = /2 * u * (pow (-p -p)).
    by rewrite /u !bpow_plus /=; ring.
  apply: error_le_half_ulp'=>//.
  by rewrite Rabs_mult bpow_plus -/u; apply/Rmult_le_compat; 
      try apply:Rabs_pos.
set tl1 := rnd_p (xh * yl + tl0).

pose e1 := tl1 - (xh*yl + tl0).
have tl1E: tl1 = xh*yl + tl0 + e1 by rewrite  /e1 /tl1; ring.
have tl1ub': Rabs (xh * yl + tl0) <= 2 * u  -  (u * u) 
   by apply:(Rle_trans _ _ _ (Rabs_triang _ _));lra.
have  tl1ub'': Rabs (xh * yl + tl0) <= 2 * u by lra.
have tl1ub: Rabs tl1 <= 2*u.
  rewrite /tl1  ZNE -round_NE_abs -ZNE.
  suff -> : 2 * u   = rnd_p (2 * u ) by apply:round_le.
  rewrite round_generic //.
  have ->: 2 * u = pow (1 -p) by rewrite bpow_plus /u.
  by apply: generic_format_bpow; rewrite /fexp; lia.
have e1ub: Rabs e1 <= u*u.
  rewrite /e1 /tl1.
  have->:  u * u = /2 * u * (pow (1-p)).
     rewrite /u bpow_plus /=  IZR_Zpower_pos /= /u ; field.
  rewrite /u; apply: error_le_half_ulp'=>//.
  rewrite bpow_plus -/u -/tl1 /= IZR_Zpower_pos /= Rmult_1_r; lra.

have xlyhub: Rabs (xl*yh) <= 2*u - 2*(u*u).
  rewrite (Rmult_comm xl)  Rabs_mult Rabs_pos_eq; last  lra.
  have->: 2 * u - 2 * (u * u) = (2 - 2 * u) * u by ring.
  apply:Rmult_le_compat; try apply: Rabs_pos; lra.
set cl2 := rnd_p (tl1 + xl * yh).
have cl2ub': Rabs (tl1 + xl * yh ) <= 4 * u.
by apply:(Rle_trans _ _ _ (Rabs_triang _ _));lra.
have cl2ub: Rabs cl2 <= 4*u.
  rewrite /cl2 ZNE -round_NE_abs -ZNE. 
  suff -> : 4 * u  = rnd_p (4 * u ) by apply:round_le.
  have ->: (4 * u) =  pow (2 -p) 
    by rewrite /u bpow_plus /= IZR_Zpower_pos /= .
  rewrite round_generic //; apply:generic_format_bpow; rewrite /fexp;lia.
pose e2 := cl2 - (xl*yh + tl1).
have cl2E: cl2 = xl*yh + tl1 + e2 by rewrite  /e2 /cl2; ring.
have e2ub: Rabs e2 <= 2* (u*u).
  rewrite /e2 /cl2.
  have->:  2 * (u * u)  = /2 * u * (pow (2-p)).
     rewrite /u !bpow_plus /=  IZR_Zpower_pos /= /u ; field.
     rewrite /u Rplus_comm; apply: error_le_half_ulp'=>//.
     by rewrite  Rplus_comm  bpow_plus -/u -/cl2 /= IZR_Zpower_pos /= 
     Rmult_1_r.
set cl3 := rnd_p (cl1 + cl2).
have cl3ub': Rabs (cl1 +cl2 ) <= 6 * u.
  by apply:(Rle_trans _ _ _ (Rabs_triang _ _));lra.
have cl3ub: Rabs cl3 <= 6*u.
  rewrite /cl3 ZNE -round_NE_abs -ZNE. 
   suff -> : 6 * u  = rnd_p (6 * u ) by apply:round_le.
  rewrite round_generic //.
  rewrite /u; apply:formatS=>//.
  have fle : 6 = F2R (Float two 6 0) by rewrite /F2R /=; ring.
  apply: (FLX_format_Rabs_Fnum p fle);  rewrite /= Rabs_pos_eq; last lra.
  apply:(Rlt_le_trans _ 8); first lra.
  have->:8 = pow 3 by [].
  apply:bpow_le; lia.
have Fcl1: format cl1.    
  by rewrite /cl1 -Ropp_minus_distr; apply/generic_format_opp/ mult_error_FLX.
pose e3 := cl3 - (cl1 + cl2).
have e3ub: Rabs e3 <= 4 * u * u.
 rewrite /e3.
  have->: 4 * u * u = /2 * u * (pow (3 -p)) by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  rewrite bpow_plus  /= IZR_Zpower_pos /= -/u; lra. 
have hf2Sc: Rabs cl3 <= Rabs ch.
  apply:(Rle_trans _ (6 * u))=>//.
  apply: (Rle_trans _ 1).
   apply: (Rle_trans _ (8 * u)); try lra.
  suff : pow (3 - p) <= pow 0 .
   rewrite bpow_plus  /= IZR_Zpower_pos /= -/u; lra.
   apply:bpow_le; lia.
  have ->:  1 = pow 0 by [].
  rewrite -(round_generic two fexp (Znearest choice) (pow 0)).
  rewrite /ch ZNE -round_NE_abs -ZNE; apply/round_le; rewrite /= Rabs_pos_eq; nra.
  apply:generic_format_bpow; rewrite /fexp; lia.
rewrite (surjective_pairing (Fast2Sum _ _)).    
rewrite F2Sum_correct_abs=>//; try apply: generic_format_round; last by rewrite (round_generic _ _ _ cl1)//.
rewrite (round_generic _ _ _ cl1)//.
case=> zhe  zle.
pose eta := e0 + e1 + e2 + e3 .
have ->: zh + zl =  (xh + xl) * (yh + yl) + eta.
  rewrite -zhe -zle.
  ring_simplify; rewrite -/cl3.
  have-> : ch = xh*yh -cl1 by rewrite /cl1;   ring.
  have->: cl3 = cl1 + cl2 + e3 by rewrite /e3; ring.
  rewrite cl2E tl1E tl0E.
  rewrite /eta; ring.
have etaub: Rabs eta <= 7 *(u * u) + /2* (u * u * u).
  have ->: 7 *(u * u) + /2* (u * u * u) =  
             / 2 * (u * u * u) + u * u +  2 * (u * u) +  4 * u * u by ring.
  rewrite /eta.
  repeat (apply: (Rle_trans _ _ _ (Rabs_triang _ _));  apply:Rplus_le_compat =>//).
ring_simplify((xh + xl) * (yh + yl) + eta - (xh + xl) * (yh + yl)).

have xpos: 0 < xh + xl.
  clear - xh1 xh2 xlu  upos ult1.
  suff: 1 -u <= xh + xl by nra.
  move/Rabs_le_inv: xlu; lra.
have x1mu:(xh + xl ) >= xh * (1 - u).
  move/Rabs_le_inv: xlu=>[xlul xluu].
  apply/Rle_ge.
  suff : -u * xh <= xl by lra.
  apply: (Rle_trans _ (-u)); try lra.
  suff : u * 1 <= u * xh by lra.
  by apply: Rmult_le_compat_l; lra.
 have y1mu:(yh + yl ) >= yh * (1 - u).
  clear -  y1    upos ult1 ylu.
  move/Rabs_le_inv: ylu=>[ylul yluu].
  apply/Rle_ge.
  suff : -u * yh <= yl by lra.
  apply: (Rle_trans _ (-u)); try lra.
  suff : u * 1 <= u * yh by lra.
  by apply: Rmult_le_compat_l; lra.
have hypos : 0 < (yh + yl).
  clear -  y1   ult1 ylu.
  move/Rabs_le_inv: ylu=>[ylul yluu]; by lra.
case:(Rlt_le_dec 2 (xh * yh))=>xhyh2.
   apply:(Rle_lt_trans _ ((7 * (u * u) + / 2 * (u * u * u)) / (2 * (1 - u) * (1 - u)))); 
    last first.
    apply:(Rmult_lt_reg_r ( (2 * (1 - u) * (1 - u)))).
      clear -ult1 ; nra.
    rewrite /Rdiv Rmult_assoc Rinv_l; last by clear -ult1 ; nra.
    suff : (u <=/16) by clear - upos u2pos ult1 ; nra.
    change (pow (-p) <= pow (-4)); apply:bpow_le ; lia.
  rewrite /Rdiv Rabs_mult.
  apply:Rmult_le_compat =>//; try apply:Rabs_pos.

  rewrite Rabs_pos_eq.
    suff h: 0 < (2 * (1 - u) * (1 - u)) <= ((xh + xl) * (yh + yl)).
      apply:Rinv_le; lra.
    split;  first lra.
    apply:(Rle_trans _ (xh * (1 -u) * (yh * (1 -u)))).
      have -> : xh * (1 - u) * (yh * (1 - u)) = (xh * yh) * (1-u) *(1 -u) by ring.
      apply:Rmult_le_compat_r; try lra.
      apply:Rmult_le_compat_r; lra.
    apply:Rmult_le_compat; nra.
  apply/Rlt_le/Rinv_0_lt_compat.
  by apply: Rmult_lt_0_compat.
(* a revoir et factoriser ...*)
case: xh1=> xh1; last first.
  have cl10:  cl1 = 0.
    by rewrite /cl1 /ch -xh1 Rmult_1_l round_generic //; ring.
  have cle: cl3 = cl2.
    by rewrite /cl3 cl10 Rplus_0_l  round_generic // /cl2 ;
       apply:generic_format_round.
  have e30: e3 = 0.
    rewrite /e3 cle cl10; ring.
  ring_simplify   ((xh + xl) * (yh + yl) + eta - (xh + xl) * (yh + yl)).
  have  etaub' : Rabs eta <= 3 * (u * u) + / 2 * (u * u * u).
rewrite /eta e30 Rplus_0_r.
  have ->: 3 *(u * u) + /2* (u * u * u) =  
             / 2 * (u * u * u) + u * u +  2 * (u * u)  by ring.
  repeat (apply: (Rle_trans _ _ _ (Rabs_triang _ _));  apply:Rplus_le_compat =>//).
   apply:(Rle_lt_trans _ ((3 * (u * u) + / 2 * (u * u * u)) / ( (1 - u) * (1 - u)))); 
    last first.
    apply:(Rmult_lt_reg_r ( ( (1 - u) * (1 - u)))).
      clear -ult1 ; nra.
    rewrite /Rdiv Rmult_assoc Rinv_l; last by clear -ult1 ; nra.
    suff : (u <=/8) by clear - upos u2pos ult1 ; nra.
    change (pow (-p) <= pow (-3)); apply:bpow_le ; lia.
  rewrite /Rdiv Rabs_mult.
  apply:Rmult_le_compat =>//; try apply:Rabs_pos.
  rewrite Rabs_pos_eq.
    suff h: 0 < (1 - u) * (1 - u) <= ((xh + xl) * (yh + yl)).
      apply:Rinv_le; lra.
    split;  first lra.
    apply:(Rle_trans _ (xh * (1 -u) * (yh * (1 -u)))).
      rewrite -xh1 Rmult_1_l.
      apply:Rmult_le_compat_l; try lra.
      clear -upos ult1 y1; nra.
    apply:Rmult_le_compat; try lra.
      rewrite -xh1; lra.
    clear - ult1 y1; nra.
  apply/Rlt_le/Rinv_0_lt_compat.
  by apply: Rmult_lt_0_compat.

case: y1=> yh1; last first.
  have cl10:  cl1 = 0.
    by rewrite /cl1 /ch -yh1 Rmult_1_r round_generic //; ring.
  have cle: cl3 = cl2.
    by rewrite /cl3 cl10 Rplus_0_l  round_generic // /cl2 ;
       apply:generic_format_round.
  have e30: e3 = 0.
    rewrite /e3 cle cl10; ring.
  have  etaub' : Rabs eta <= 3 * (u * u) + / 2 * (u * u * u).
rewrite /eta e30 Rplus_0_r.
  have ->: 3 *(u * u) + /2* (u * u * u) =  
             / 2 * (u * u * u) + u * u +  2 * (u * u)  by ring.
  repeat (apply: (Rle_trans _ _ _ (Rabs_triang _ _));  apply:Rplus_le_compat =>//).
   apply:(Rle_lt_trans _ ((3 * (u * u) + / 2 * (u * u * u)) / ( (1 - u) * (1 - u)))); 
    last first.
    apply:(Rmult_lt_reg_r ( ( (1 - u) * (1 - u)))).
      clear -ult1 ; nra.
    rewrite /Rdiv Rmult_assoc Rinv_l; last by clear -ult1 ; nra.
    suff : (u <=/8) by clear - upos u2pos ult1 ; nra.
    change (pow (-p) <= pow (-3)); apply:bpow_le ; lia.
  rewrite /Rdiv Rabs_mult.
  apply:Rmult_le_compat =>//; try apply:Rabs_pos.
  rewrite Rabs_pos_eq.
    suff h: 0 < (1 - u) * (1 - u) <= ((xh + xl) * (yh + yl)).
      apply:Rinv_le; lra.
    split;  first lra.
    apply:(Rle_trans _ (xh * (1 -u) * (yh * (1 -u)))).
      rewrite -yh1 Rmult_1_l.
      apply:Rmult_le_compat_r; try lra.
      clear -upos ult1 xh1; nra.
    apply:Rmult_le_compat; try lra;     clear - ult1 yh1 xh1; nra.
  apply/Rlt_le/Rinv_0_lt_compat.
  by apply: Rmult_lt_0_compat.
have  cl1u: Rabs cl1 <= u.
  rewrite /cl1 -Ropp_minus_distr Rabs_Ropp /ch.
  have ->: u = / 2 * u * (pow 1)  by rewrite /= IZR_Zpower_pos /=; field.
  rewrite /u; apply: error_le_half_ulp'; first lia.
  rewrite Rabs_pos_eq  /= ?IZR_Zpower_pos /= ?Rmult_1_r //.
  clear - xh1 yh1;  nra.
have hsxhyh: xh + yh <= 3 - 2*u by apply: l5_2F=>//; lra.
have h: Rabs (xh*yl + yh*xl) <= 3*u - 2* (u * u).
  have->: 3 * u - 2 * (u * u) = (3 - 2*u) *u by ring.
  apply: (Rle_trans _ _ _ (Rabs_triang _ _)).
  apply: (Rle_trans _ (xh * u + yh * u)); last first.
    have -> :   xh * u + yh * u  = (xh + yh) *u by ring.
    apply:(Rmult_le_compat_r); lra.
  by apply:Rplus_le_compat; rewrite Rabs_mult;
       apply:Rmult_le_compat=>//; try apply/Rabs_pos; 
       rewrite Rabs_pos_eq //;lra.
have h2: Rabs (xh*yl + yh*xl + xl*yl) <= 3*u - u^2.
  apply: (Rle_trans _ _ _ (Rabs_triang _ _)).
  have->:  3 * u - u ^ 2 = 3*u -2*(u*u) + u*u by ring.
  apply: Rplus_le_compat=>//.
  by rewrite Rabs_mult; apply: Rmult_le_compat=>//; apply/Rabs_pos.
have h3: Rabs (xh*yl + yh*xl + tl0) <= 3*u - u^2 + /2* u^3.
  rewrite tl0E  -Rplus_assoc.
  apply: (Rle_trans _ _ _ (Rabs_triang _ _)); lra.
have h4: Rabs (yh * xl + tl1 ) <= 3*u + /2*u^3.
  rewrite tl1E.
  have->:  yh * xl + (xh * yl + tl0 + e1) = 
            (xh * yl + yh * xl + tl0) + e1 by ring.

  apply: (Rle_trans _ _ _ (Rabs_triang _ _)); lra.

have : Rabs cl2 <= rnd_p ( 3 * u + / 2 * u ^ 3).
  rewrite /cl2.
  have->:  (tl1 + xl * yh) = (yh * xl + tl1) by ring.
  rewrite ZNE -round_NE_abs -ZNE.
  by apply: round_le.
have ->: rnd_p (3 * u + / 2 * u ^ 3) = 3*u.
  have ->: (3 * u + / 2 * u ^ 3)= (3 + /2* u^2) *u by ring.
  rewrite /u round_bpow.
  congr Rmult.
  apply:rulp2p=>//.
  +  apply:(@FLX_format_Rabs_Fnum _ _(Float two 3 0)).
       rewrite /F2R //=; ring.
     rewrite /=; apply:(Rlt_le_trans _ (pow 2)).
       have->: pow 2 = 4 by [].
       rewrite Rabs_pos_eq; lra.
    by apply: bpow_le; lia.
  + case => et.
    rewrite Rabs_pos_eq ; try lra; move=> teq.
    have : 2 < 3 < 4 by lra.
    rewrite teq;have->: 2 = pow 1 by [].
    have ->: 4 = pow 2 by [].
    case; move/lt_bpow=> hh;  move/lt_bpow=>gg.
    lia.
  rewrite Rabs_pos_eq; last first.
    rewrite -/u; clear -upos; nra.
  rewrite ulp_neq_0  /cexp /fexp; last lra.
  have -> : / 2 * pow (- p) ^ 2 = pow ( -1 + -p + -p).
    rewrite !bpow_plus; have->: /2 = pow (-1) by [].
    ring.
  have->: /2 = pow (-1) by [].
  rewrite -bpow_plus.
  apply:bpow_lt.
  rewrite (mag_unique_pos two 3 2); try lia.
  have->: pow 2 = 4 by [].
  have ->: pow (2 -1) = pow 1 by congr bpow ; ring.
  change (2 <= 3 < 4); lra.
move=> h5.
have hcl3 : Rabs (cl1 + cl2 ) <= 4*u.
  apply: (Rle_trans _ _ _ (Rabs_triang _ _)); lra.
clear cl3ub.
have cl3ub: Rabs cl3  <= 4*u.
  rewrite /cl3 ZNE -round_NE_abs -ZNE.
  suff ->: 4 * u = rnd_p (4*u ) by apply:round_le.
  rewrite round_generic //.
  have ->: 4* u = pow (2 -p) .
    rewrite bpow_plus /u //.
  apply: generic_format_bpow; rewrite /fexp; lia.
have {} e3ub: Rabs e3 <= 2 * u * u.
  have ->:  2 * u * u = / 2 * pow (- p) * pow (2 + (-p)).
  rewrite bpow_plus -/u /= IZR_Zpower_pos /=; field.
  have  he: 0 <= 2 * u * u <= / 2 * pow (- p) * pow (2 + (- p)).
  rewrite bpow_plus -/u.
  have -> : pow 2 = 4 by [].
  clear - upos; nra.
  rewrite /e3 /cl3.
  apply:(error_le_half_ulp_W Hp1 (choiceP ZNE) ZNE (cl1 + cl2 ) (2 + - p)   he).
  apply: (Rle_trans _ _ _ (Rabs_triang _ _)).
  rewrite bpow_plus -/u.
  have -> : pow 2 = 4 by [].
  lra.

have rabs_eta : Rabs eta <= Rabs e0 + Rabs e1 + Rabs e2 + Rabs e3.
  rewrite /eta.
  apply:(Rle_trans _ ( Rabs e0 + Rabs e1 + Rabs e2 + Rabs e3)).
   repeat (apply: (Rle_trans _ _ _ (Rabs_triang _ _)); 
     first apply : Rplus_le_compat_r); lra.
  lra.
have etaub': Rabs eta <= 5 * (u * u) + / 2 * (u * u * u) by lra.
have xhlb: 1+ 2*u <= xh.
  rewrite /u u_ulp1 -Rmult_assoc Rinv_r  ?Rmult_1_l; try lra.
  rewrite - succ_eq_pos; try lra.
  apply:succ_le_lt=>//.
  change (format (pow 0)); apply:generic_format_bpow; rewrite /fexp;lia.
have yhlb: 1+ 2*u <= yh.
  rewrite /u u_ulp1 -Rmult_assoc Rinv_r  ?Rmult_1_l; try lra.
  rewrite - succ_eq_pos; try lra.
  apply:succ_le_lt=>//.
  by change (format (pow 0)); apply:generic_format_bpow; rewrite /fexp;lia.
set x := xh + xl.
have xlb:  1+ u <= x by rewrite /x; move/Rabs_le_inv: xlu; lra.
set y := yh + yl.
have ylb:  1+ u <= y by rewrite /y; move/Rabs_le_inv: ylu; lra.
have xylb: (1+u) ^2 <= x * y by clear - ult1 upos xlb ylb; nra.
have xyipos : 0 < /(x * y) by apply/Rinv_0_lt_compat; lra.
rewrite Rabs_mult (Rabs_pos_eq (/ (x * y))); last lra.
apply/(Rmult_lt_reg_r (x*y)); try  lra.
rewrite Rmult_assoc Rinv_l; last lra.
rewrite Rmult_1_r.
apply:(Rle_lt_trans _  (5 * (u * u) + / 2 * (u * u * u))) =>//.
apply:(Rlt_le_trans _  (5 * (u * u) *  ((1 + u) ^ 2))); last first.
  apply: Rmult_le_compat_l=>//.
  clear -upos; nra.
have ->:  (1 + u) ^ 2 = 1 + 2*u + u^2 by ring.
suff: / 2 * (u * u * u) <  10  * u^3 + 5* u ^ 4.
  lra.
suff : 0< 19 * u^3 + 10 * u^4 by lra.
clear -upos u2pos; nra.
Qed.


Lemma DWTimesDW12_correct_bis xh xl yh yl  (DWx:double_word xh xl) (DWy:double_word yh yl):
(5 <= p)%Z -> 
  let (zh, zl) := DWTimesDW12 xh xl yh yl in
  let xy := ((xh + xl) * (yh + yl))%R in
  Rabs ((zh + zl - xy) / xy) < 4 * (u * u).
Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
move=>Hp5.
have [[Fxh Fxl] Exh] := DWx.
have [[Fyh Fyl] Eyh] := DWy.
case E1: DWTimesDW12 => [zh zl].
have Hp1:= Hp1.
have upos: 0 < u by rewrite /u ; exact: upos.
case:(Req_dec yh 0)=> yh0.
  have yl0: yl = 0 by move:Eyh; rewrite  yh0 Rplus_0_l round_generic. 
  move:E1; rewrite /DWTimesDW12 /= yh0 yl0 Rplus_0_r Rmult_0_r TwoProdE 
    Fast2MultC Fast2Mult0f 
    !(Rmult_0_r,Rplus_0_l,Rplus_0_r,Rminus_0_r, round_0) Fast2Sumf0; 
    last by apply:generic_format_0.
  case=> <- <-; rewrite Rplus_0_r   /Rdiv  Rmult_0_l Rabs_R0;  nra.
case:(Req_dec xh 0)=> xh0.
  have xl0: xl = 0 by move:Exh; rewrite  xh0 Rplus_0_l round_generic.
  move:E1;rewrite /DWTimesDW12 xh0 xl0 Rmult_0_l TwoProdE round_0 Fast2Mult0f.
  rewrite /Fast2Sum /F2SumFLX.Fast2Sum  
    !(Rplus_0_r, Rminus_0_r, Rplus_0_l, round_0, Rmult_0_l).
  case=> <- <-; rewrite Rplus_0_r  /Rdiv   Rmult_0_l Rabs_R0.
  rewrite /u; move:(bpow_gt_0 two (-p));  nra.
have x0: xh + xl <> 0 by move=> x0; apply:xh0; rewrite Exh x0 round_0.
have y0: yh + yl <> 0 by move=> y0; apply:yh0; rewrite Eyh y0 round_0.
rewrite /=; clear Fxh Fxl Exh Fyh Fyl Eyh.
wlog xhpos: yh yl  xh xl zh zl DWx DWy  E1 xh0 yh0 x0 y0 / 0 <= xh.
  move=> Hwlog.
  case:(Rle_lt_dec 0 xh) => xhle0  ; first by apply:Hwlog.
  have ->: (zh + zl - (xh + xl) * (yh + yl)) / ((xh + xl) * (yh +yl))= 
   ((- zh + - zl - (- xh + - xl) * (yh + yl)) / ((- xh + - xl) * (yh + yl))).
    by field; lra.
  apply:(Hwlog yh yl  (-xh) (-xl) (-zh) (-zl))=>//; try lra; 
    last  by rewrite DWTimesDW12_Asym_l E1.
  have [[Fxh Fxl] Exh] := DWx.
  split; [split|]; try apply:generic_format_opp=>//.
  have ->:- xh + - xl = -(xh +  xl) by ring.
  by rewrite ZNE round_NE_opp -ZNE {1}Exh.
wlog yhpos: yh yl  xh xl zh zl DWx DWy  E1 xh0 yh0 x0 y0 xhpos / 0 <= yh.
  move=> Hwlog.
  case:(Rle_lt_dec 0 yh) => yhle0 ; first by apply:Hwlog.
  have ->: (zh + zl - (xh + xl) * (yh + yl)) / ((xh + xl) * (yh +yl))= 
   ((- zh + - zl - ( xh +  xl) * (- yh + - yl)) / 
   (( xh + xl) * (- yh + - yl)))  by field; lra.
  apply:(Hwlog (-yh) (-yl)  (xh) (xl) (-zh) (-zl))=>//; try lra; 
    last by rewrite DWTimesDW12_Asym_r E1.
  have [[Fyh Fyl] Eyh] := DWy.
  split; [split|]; try apply:generic_format_opp=>//.
  have ->:- yh + - yl = -(yh +  yl) by ring.
  by rewrite ZNE round_NE_opp -ZNE {1}Eyh.
have {} xhpos: 0 < xh by lra.
have {} yhpos: 0 < yh by lra.
wlog [xh1 xh2]: xl xh  zh zl DWx   xh0 x0 xhpos E1/ 1 <= xh  <= 2-2*u.
  move=> Hwlog.
  have [[Fxh Fxl] Exh] := DWx.
  case: (scale_generic_12 Fxh xhpos)=> exh Hxhs.
  have xhp0: 0 <  xh * pow exh by lra.
  have ->: (zh + zl - (xh + xl) * (yh + yl)) / ((xh + xl) * (yh + yl)) = 
         (zh * pow exh  + zl * pow exh  - 
         (xh * pow exh + xl * pow exh) * (yh + yl)) / 
            ((xh * pow exh + xl * pow exh) * (yh + yl)).
    field.
    split; try lra; split; nra.
  apply:Hwlog=>//; try lra.
  + split;[split|]; try apply:formatS=>//.
    by rewrite -Rmult_plus_distr_r round_bpow -Exh.
  + nra.
  by rewrite DWTimesDW12Sx E1.
wlog [y1 y2]: yh yl  zh zl  DWy yh0 y0 yhpos E1/ 1 <= yh <= 2-2*u.
  move=> Hwlog.
  have [[Fyh Fyl] Eyh] := DWy.
  case: (scale_generic_12 Fyh yhpos)=> eyh Hyhs.
  have ->: (zh + zl - (xh + xl) * (yh + yl)) / ((xh + xl) * (yh + yl)) = 
         (zh * pow eyh  + zl * pow eyh - 
        (xh  + xl) * (yh  * pow eyh + yl * pow eyh)) / 
         ((xh + xl ) * (yh * pow eyh + yl * pow eyh)).
    field;  move:(bpow_gt_0 two eyh); nra.
  apply:Hwlog=>//; try lra.
  + split;[split|]; try apply:formatS=>//.
      by rewrite -Rmult_plus_distr_r round_bpow -Eyh.
  + nra.  
  by rewrite DWTimesDW12Sy E1.
have ult1 : u < 1 by rewrite /u ; apply:bpow_lt_1; lia.
have u2pos: 0 < u * u by apply:Rmult_lt_0_compat.
have xh2': xh <= 2 by lra.
have yh2': yh <= 2 by lra.
have h0 : xh * yh < 4 by nra.
have ylu:Rabs yl <= u by apply: (double_lpart_u DWy); lra.
have xlu:Rabs xl <= u by apply: (double_lpart_u DWx); lra.
have [[Fxh Fxl] Exh] := DWx.
have [[Fyh Fyl] Eyh] := DWy.
move:E1; rewrite /DWTimesDW12.
rewrite TwoProdE /=.
set ch := rnd_p (xh * yh).
set cl1 :=   xh * yh -  ch.
have chcl1E: ch + cl1 = xh * yh by  rewrite /cl1 /ch; lra.
have cl1ub: Rabs cl1 <= 2 * u.
  rewrite /cl1 -Ropp_minus_distr Rabs_Ropp /ch.
  have ->: 2 * u = / 2 * u * pow 2  by change (2*u=/2*u*4);field.
  rewrite /u; apply: error_le_half_ulp'; first lia.
  have->: pow 2 = 4 by []; rewrite Rabs_pos_eq;nra.
set tl0 := rnd_p (xl * yl).
have tl0ub: Rabs tl0 <= (u *u).
  rewrite /tl0 ZNE -round_NE_abs -ZNE.
  suff -> : (u * u) = rnd_p (u * u).
    by apply:round_le; rewrite Rabs_mult; apply:Rmult_le_compat=>//; 
      apply : Rabs_pos.
  rewrite round_generic //.  
  have->: u * u = pow (-p -p) by rewrite bpow_plus /u.
  apply: generic_format_bpow; rewrite /fexp; lia.
pose e0 := tl0 - xl*yl.
have tl0E: tl0 = xl*yl + e0 by rewrite  /e0 /tl0; ring.
have e0ub: Rabs e0 <= /2 *(u*u*u).
  rewrite /e0.
  have->:  /2 *(u*u*u) = /2 * u * (pow (-p -p)).
    by rewrite /u !bpow_plus /=; ring.
  apply: error_le_half_ulp'=>//.
  by rewrite Rabs_mult bpow_plus -/u; apply/Rmult_le_compat; 
      try apply:Rabs_pos.
set tl1 := rnd_p (xh * yl + tl0).
pose e1 := tl1 - (xh*yl + tl0).
have tl1E: tl1 = xh*yl + tl0 + e1 by rewrite  /e1 /tl1; ring.
have xhylub: Rabs (xh*yl) <= 2*u - 2*(u*u).
  rewrite Rabs_mult Rabs_pos_eq; last lra.
  have->: 2 * u - 2 * (u * u) = (2 - 2 * u) * u by ring.
  apply:Rmult_le_compat; try apply: Rabs_pos; lra.
have tl1ub': Rabs (xh * yl + tl0) <= 2 * u  -  (u * u) 
   by apply:(Rle_trans _ _ _ (Rabs_triang _ _));lra.
have  tl1ub'': Rabs (xh * yl + tl0) <= 2 * u by lra.
have tl1ub: Rabs tl1 <= 2*u.
  rewrite /tl1  ZNE -round_NE_abs -ZNE.
  suff -> : 2 * u   = rnd_p (2 * u ) by apply:round_le.
  rewrite round_generic //.
  have ->: 2 * u = pow (1 -p) by rewrite bpow_plus /u.
  by apply: generic_format_bpow; rewrite /fexp; lia.
have e1ub: Rabs e1 <= u*u.
  rewrite /e1 /tl1.
  have->:  u * u = /2 * u * (pow (1-p)).
     rewrite /u bpow_plus /=  IZR_Zpower_pos /= /u ; field.
  rewrite /u; apply: error_le_half_ulp'=>//.
  rewrite bpow_plus -/u -/tl1 /= IZR_Zpower_pos /= Rmult_1_r; lra.
have xlyhub: Rabs (xl*yh) <= 2*u - 2*(u*u).
  rewrite (Rmult_comm xl)  Rabs_mult Rabs_pos_eq; last  lra.
  have->: 2 * u - 2 * (u * u) = (2 - 2 * u) * u by ring.
  apply:Rmult_le_compat; try apply: Rabs_pos; lra.
set cl2 := rnd_p (tl1 + xl * yh).
have cl2ub': Rabs (tl1 + xl * yh ) <= 4 * u.
  by apply:(Rle_trans _ _ _ (Rabs_triang _ _));lra.
have cl2ub: Rabs cl2 <= 4*u.
  rewrite /cl2 ZNE -round_NE_abs -ZNE. 
  suff -> : 4 * u  = rnd_p (4 * u ) by apply:round_le.
  have ->: (4 * u) =  pow (2 -p) 
    by rewrite /u bpow_plus /= IZR_Zpower_pos /= .
  by rewrite round_generic //; apply:generic_format_bpow; rewrite /fexp;lia.
pose e2 := cl2 - (xl*yh + tl1).
have cl2E: cl2 = xl*yh + tl1 + e2 by rewrite  /e2 /cl2; ring.
have e2ub: Rabs e2 <= 2* (u*u).
  rewrite /e2 /cl2.
  have->:  2 * (u * u)  = /2 * u * (pow (2-p)).
    by rewrite /u !bpow_plus /=  IZR_Zpower_pos /= /u ; field.
  rewrite /u Rplus_comm; apply: error_le_half_ulp'; rewrite //  Rplus_comm.
     by rewrite  bpow_plus -/u -/cl2 /= IZR_Zpower_pos /= Rmult_1_r.

set cl3 := rnd_p (cl1 + cl2).
have cl3ub': Rabs (cl1 +cl2 ) <= 6 * u.
  by apply:(Rle_trans _ _ _ (Rabs_triang _ _));lra.
have cl3ub: Rabs cl3 <= 6*u.
  rewrite /cl3 ZNE -round_NE_abs -ZNE. 
   suff -> : 6 * u  = rnd_p (6 * u ) by apply:round_le.
  rewrite round_generic //.
  rewrite /u; apply:formatS=>//.
  have fle : 6 = F2R (Float two 6 0) by rewrite /F2R /=; ring.
  apply: (FLX_format_Rabs_Fnum p fle);  rewrite /= Rabs_pos_eq; last lra.
  apply:(Rlt_le_trans _ 8); first lra.
  have->:8 = pow 3 by [].
  apply:bpow_le; lia.
have Fcl1: format cl1.    
  by rewrite /cl1 -Ropp_minus_distr; apply/generic_format_opp/ mult_error_FLX.
pose e3 := cl3 - (cl1 + cl2).
have e3ub: Rabs e3 <= 4 * u * u.
 rewrite /e3.
  have->: 4 * u * u = /2 * u * (pow (3 -p)) 
    by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  rewrite bpow_plus  /= IZR_Zpower_pos /= -/u; lra. 
have hf2Sc: Rabs cl3 <= Rabs ch.
  apply:(Rle_trans _ (6 * u))=>//.
  apply: (Rle_trans _ 1).
    apply: (Rle_trans _ (8 * u)); try lra.
    change((pow 3) * (pow (-p)) <= pow 0); rewrite -bpow_plus; apply/bpow_le;       lia.
  have ->:  1 = pow 0 by [].
  rewrite -(round_generic two fexp (Znearest choice) (pow 0)).
    rewrite /ch ZNE -round_NE_abs -ZNE; apply/round_le;rewrite /= Rabs_pos_eq;      nra.
  apply:generic_format_bpow; rewrite /fexp; lia.
rewrite (surjective_pairing (Fast2Sum _ _)).    
rewrite F2Sum_correct_abs=>//; try apply: generic_format_round; last by rewrite (round_generic _ _ _ cl1)//.
rewrite (round_generic _ _ _ cl1)//.
case=> zhe  zle.
pose eta := e0 + e1 + e2 + e3 .
have ->: zh + zl =  (xh + xl) * (yh + yl) + eta.
  rewrite -zhe -zle.
  ring_simplify; rewrite -/cl3.
  have-> : ch = xh*yh -cl1 by rewrite /cl1;   ring.
  have->: cl3 = cl1 + cl2 + e3 by rewrite /e3; ring.
  rewrite cl2E tl1E tl0E.
  rewrite /eta; ring.
have etaub: Rabs eta <= 7 *(u * u) + /2* (u * u * u).
  have ->: 7 *(u * u) + /2* (u * u * u) =  
             / 2 * (u * u * u) + u * u +  2 * (u * u) +  4 * u * u by ring.
  rewrite /eta.
  repeat (apply: (Rle_trans _ _ _ (Rabs_triang _ _));  apply:Rplus_le_compat =>//).
ring_simplify((xh + xl) * (yh + yl) + eta - (xh + xl) * (yh + yl)).
have xpos: 0 < xh + xl.
  clear - xh1 xh2 xlu  upos ult1.
  suff: 1 -u <= xh + xl by nra.
  move/Rabs_le_inv: xlu; lra.
have x1mu:(xh + xl ) >= xh * (1 - u).
  move/Rabs_le_inv: xlu=>[xlul xluu].
  apply/Rle_ge.
  clear - xh1 xlul upos ; nra.
have y1mu:(yh + yl ) >= yh * (1 - u).
  clear -  y1    upos ult1 ylu.
  move/Rabs_le_inv: ylu=>[ylul yluu].
  apply/Rle_ge; nra.
have hypos : 0 < (yh + yl).
  clear -  y1   ult1 ylu.
  move/Rabs_le_inv: ylu=>[ylul yluu]; by lra.
case:(Rlt_le_dec 2 (xh * yh))=>xhyh2.
  apply:(Rle_lt_trans _ 
            ((7 * (u * u) + / 2 * (u * u * u)) / (2 * (1 - u) * (1 - u)))); 
     last first.
  apply:(Rmult_lt_reg_r ( (2 * (1 - u) * (1 - u)))).
      clear -ult1 ; nra.
    rewrite /Rdiv Rmult_assoc Rinv_l; last by clear -ult1 ; nra.
    suff : (u <=/32) by clear - upos u2pos ult1 ; nra.
    change (pow (-p) <= pow (-5)); apply:bpow_le ; lia.
  rewrite /Rdiv Rabs_mult.
  apply:Rmult_le_compat =>//; try apply:Rabs_pos.
  rewrite Rabs_pos_eq.
    suff h: 0 < (2 * (1 - u) * (1 - u)) <= ((xh + xl) * (yh + yl)).
      apply:Rinv_le; lra.
    split;  first lra.
    apply:(Rle_trans _ (xh * (1 -u) * (yh * (1 -u)))).
      have -> : xh * (1 - u) * (yh * (1 - u)) = (xh * yh) * (1-u) *(1 -u) 
       by ring.
      apply:Rmult_le_compat_r; try lra.
      apply:Rmult_le_compat_r; lra.
    apply:Rmult_le_compat; nra.
  apply/Rlt_le/Rinv_0_lt_compat.
  by apply: Rmult_lt_0_compat.
have xypos : 0 < (xh+xl)*(yh+yl) by clear -xpos hypos; nra.
move/Rinv_0_lt_compat: (xypos)  => xyipos.

rewrite Rabs_mult (Rabs_pos_eq _ (Rlt_le _ _  xyipos)).
apply:(Rmult_lt_reg_r ((xh + xl) * (yh + yl))) =>//.
rewrite Rmult_assoc Rinv_l ?Rmult_1_r; last lra.
have rabs_eta : Rabs eta <= Rabs e0 + Rabs e1 + Rabs e2 + Rabs e3.
  rewrite /eta.
  apply:(Rle_trans _ ( Rabs e0 + Rabs e1 + Rabs e2 + Rabs e3)).
   repeat (apply: (Rle_trans _ _ _ (Rabs_triang _ _)); 
     first apply : Rplus_le_compat_r); lra.
  lra.

have eta_ub1: (xh = 1)\/ (yh = 1)-> 
   Rabs eta <= 3 * (u * u) + / 2 * (u * u * u).
  move=> xhyh1.
  have cl10: cl1 = 0.
    rewrite /cl1 /ch; case : xhyh1 =>->; rewrite ?Rmult_1_l ?Rmult_1_r 
     round_generic //=; ring.
  have cl32e: cl3=cl2.
    by rewrite /cl3 cl10 Rplus_0_l  round_generic // /cl2 ;
       apply:generic_format_round.
  have e30: e3 = 0.
    rewrite /e3 cl32e cl10; ring.
  apply:(Rle_trans _ _ _ rabs_eta).
  by rewrite e30 Rabs_R0;lra.
have hxylb: (1 -u) ^ 2 <= ((xh + xl) * (yh + yl)).
  apply:Rmult_le_compat; try lra; clear - xh1 y1 x1mu y1mu  ult1 ; nra.
(* apply:(Rlt_le_trans _ (4 * (u * u) *(1 - u) ^ 2)); last first.
  by apply:Rmult_le_compat_l => //;  clear -upos;  nra. *)
have h2: xh = 1 \/ yh = 1 ->  Rabs eta < 4 * (u * u) * (1 - u) ^ 2.
  move/  eta_ub1=>h1;apply/ (Rle_lt_trans _ _ _ h1).
  have->: (1 - u) ^ 2 = 1 -2*u + u*u by ring.
  suff:   u < /16 by clear -upos u2pos; nra.
  by change ((pow (-p))< pow (-4)); apply:bpow_lt; lia.
case: xh1=> xh1; last first.
  apply:(Rlt_le_trans _ (4 * (u * u) *(1 - u) ^ 2)); last first.
    by apply:Rmult_le_compat_l => //;  clear -upos;  nra.
  by apply: h2; left; lra.
case: y1=> yh1; last first. 
  apply:(Rlt_le_trans _ (4 * (u * u) *(1 - u) ^ 2)); last first.
    by apply:Rmult_le_compat_l => //;  clear -upos;  nra.
  by apply: h2; right; lra.
have  cl1u: Rabs cl1 <= u.
  rewrite /cl1 -Ropp_minus_distr Rabs_Ropp /ch.
  have ->: u = / 2 * u * (pow 1)  by rewrite /= IZR_Zpower_pos /=; field.
  rewrite /u; apply: error_le_half_ulp'; first lia.
  rewrite Rabs_pos_eq  /= ?IZR_Zpower_pos /= ?Rmult_1_r //.
  clear - xh1 yh1;  nra.
have hsxhyh: xh + yh <= 3 - 2*u by apply: l5_2F=>//; lra.
have h: Rabs (xh*yl + yh*xl) <= 3*u - 2* (u * u).
  have->: 3 * u - 2 * (u * u) = (3 - 2*u) *u by ring.
  apply: (Rle_trans _ _ _ (Rabs_triang _ _)).
  apply: (Rle_trans _ (xh * u + yh * u)); last first.
    have -> :   xh * u + yh * u  = (xh + yh) *u by ring.
    apply:(Rmult_le_compat_r); lra.
  by apply:Rplus_le_compat; rewrite Rabs_mult;
       apply:Rmult_le_compat=>//; try apply/Rabs_pos; 
       rewrite Rabs_pos_eq //;lra.
have {} h2: Rabs (xh*yl + yh*xl + xl*yl) <= 3*u - u^2.
  apply: (Rle_trans _ _ _ (Rabs_triang _ _)).
  have->:  3 * u - u ^ 2 = 3*u -2*(u*u) + u*u by ring.
  apply: Rplus_le_compat=>//.
  by rewrite Rabs_mult; apply: Rmult_le_compat=>//; apply/Rabs_pos.
have h3: Rabs (xh*yl + yh*xl + tl0) <= 3*u - u^2 + /2* u^3.
  rewrite tl0E  -Rplus_assoc.
  apply: (Rle_trans _ _ _ (Rabs_triang _ _)); lra.
have h4: Rabs (yh * xl + tl1 ) <= 3*u + /2*u^3.
  rewrite tl1E.
  have->:  yh * xl + (xh * yl + tl0 + e1) = 
            (xh * yl + yh * xl + tl0) + e1 by ring.
  by apply: (Rle_trans _ _ _ (Rabs_triang _ _)); lra.

have : Rabs cl2 <= rnd_p ( 3 * u + / 2 * u ^ 3).
  rewrite /cl2.
  have->:  (tl1 + xl * yh) = (yh * xl + tl1) by ring.
  rewrite ZNE -round_NE_abs -ZNE.
  apply: round_le=>//.
have F3u: format (3 * u).
    change (format (3 * pow (-p))); apply:formatS; first lia.
  apply:(@FLX_format_Rabs_Fnum _ _(Float two 3 0)).
    rewrite /F2R //=; ring.
    rewrite /=; apply:(Rlt_le_trans _ (pow 2)).
    have->: pow 2 = 4 by [].
    rewrite Rabs_pos_eq; lra.
  by apply: bpow_le; lia. 
rewrite rbpowpuW' // ; try lia ;try lra; first last.
  rewrite ulp_neq_0  /cexp /fexp; last lra.
  rewrite (mag_unique_pos two (3*u) (2-p)) ?bpow_plus ; try lia.
    change( 0 <= / 2 * u ^ 3 < / 2 * ( 4 * u * u));
      clear -upos u2pos ult1 ; nra.
  change(4 * u * /2 <= 3 * u < 4* u);  clear -upos u2pos ult1 ; nra.
move=> {} cl2ub.
have hcl3 : Rabs (cl1 + cl2 ) <= 4*u.
  apply: (Rle_trans _ _ _ (Rabs_triang _ _)); lra.
have {} cl3ub: Rabs cl3  <= 4*u.
  rewrite /cl3 ZNE -round_NE_abs -ZNE.
  suff ->: 4 * u = rnd_p (4*u ) by apply:round_le.
  rewrite round_generic //.
  change (format (pow 2 * pow (-p))).
  rewrite -bpow_plus; apply: generic_format_bpow; rewrite /fexp; lia.
have {} e3ub: Rabs e3 <= 2 * u * u.
  have ->:  2 * u * u = / 2 * pow (- p) * pow (2 + (-p)).
    rewrite bpow_plus /u; have -> : pow 2 = 4 by []; field.
  rewrite /e3 /cl3.
  apply:(error_le_half_ulp'); first lia.
  rewrite bpow_plus -/u.
  have -> : pow 2 = 4 by [].
  lra.
have etaub': Rabs eta <= 5 * (u * u) + / 2 * (u * u * u) by lra.
have xhlb: 1+ 2*u <= xh.
  rewrite /u u_ulp1 -Rmult_assoc Rinv_r  ?Rmult_1_l; try lra.
  rewrite - succ_eq_pos; try lra.
  apply:succ_le_lt=>//.
    change (format (pow 0)); apply:generic_format_bpow; rewrite /fexp;lia.
have yhlb: 1+ 2*u <= yh.
  rewrite /u u_ulp1 -Rmult_assoc Rinv_r  ?Rmult_1_l; try lra.
  rewrite - succ_eq_pos; try lra.
  apply:succ_le_lt=>//.
  change (format (pow 0)); apply:generic_format_bpow; rewrite /fexp;lia.
set x := xh + xl.
have xlb:  1+ u <= x.
  rewrite /x; move/Rabs_le_inv: xlu; lra.
set y := yh + yl.
have ylb:  1+ u <= y.
  rewrite /y; move/Rabs_le_inv: ylu; lra.
have xylb: (1+u) ^2 <= x * y by clear - ult1 upos xlb ylb; nra.
case:(@ex_mul p xh 0)=>//.
  change (1 <= Rabs xh); rewrite Rabs_pos_eq; lra.
  move=> mxh; rewrite Rmult_1_r -/u => xhE.
case:(@ex_mul p yh 0)=>//.
  change (1 <= Rabs yh); rewrite Rabs_pos_eq; lra.
  move=> myh; rewrite Rmult_1_r -/u => yhE.
have xhyhm4u2: xh*yh = IZR (mxh * myh) * (4* u^2).
  rewrite xhE yhE mult_IZR; ring.
case: (@ex_mul p ch 0)=>//.
    rewrite /ch; rewrite ZNE -round_NE_abs -ZNE.
    have ->: pow 0 = rnd_p 1.
    rewrite round_generic //.
      change (format (pow 0)); apply: generic_format_bpow; rewrite /fexp; lia.
    apply: round_le.
    rewrite Rabs_pos_eq; clear - xh1 yh1; nra.
  rewrite /ch; apply:generic_format_round.
move=> mch; rewrite Rmult_1_r -/u => chE.
have chm4u2: ch = (IZR ( mch * 2^(p -1)))* (4 * u^2).
  rewrite chE.
  have ->: 2*u = 4*u^2 * pow (p -1).
    have ->:  4 * u ^ 2 = pow (2 -p -p).
      have->: 4 = pow 2 by [].
      rewrite !bpow_plus /u; ring.
    rewrite -bpow_plus.
    have -> : 2 * u = pow (1 -p) by rewrite /u bpow_plus .
    congr bpow; ring.
  have->:  IZR mch * (4 * u ^ 2 * pow (p - 1)) =       
           (IZR mch *  pow (p - 1)) * (4 * u ^ 2 ) by ring.
  congr Rmult.
  rewrite mult_IZR (IZR_Zpower two) //.
  lia.

pose m:=   (mxh*myh - (mch * 2 ^ (p - 1)))%Z.
have cl1m4u2: cl1 = (IZR m)* (4*u^2).
  rewrite /cl1  xhyhm4u2   chm4u2 /m -Rmult_minus_distr_r .
  apply:Rmult_eq_compat_r.
  by rewrite minus_IZR.
case: (Rlt_le_dec (Rabs cl2) (2*u))=> hcl2.
  case (Rle_lt_dec (2*u)  (Rabs (tl1 + xl * yh))).
    move/(round_le two fexp (Znearest choice)).
    rewrite ZNE round_NE_abs -ZNE -/cl2 round_generic; first lra.
    have ->: 2* u = pow (1 -p) by rewrite bpow_plus /u.
    apply:generic_format_bpow; rewrite /fexp; lia.
  move=> ih1.
  have e2ub': Rabs e2 <= u^2.
    rewrite /e2 /cl2.
    have->:  u^2  = /2 * u * (pow (1-p)).
      rewrite /u !bpow_plus /=  IZR_Zpower_pos /= /u ; field.
    rewrite /u Rplus_comm; apply: error_le_half_ulp'=>//.
    rewrite  Rplus_comm  bpow_plus -/u.
    have->: pow 1 = 2 by [];lra. 
  apply:(Rlt_le_trans _  (4 * (u * u) *  ((1 + u) ^ 2))); last first.
    apply: Rmult_le_compat_l=>//; clear -upos; nra.
  have ->:  (1 + u) ^ 2 = 1 + 2*u + u^2 by ring.
  suff: / 2 * (u * u * u) <  8 * u^3 + 4* u ^ 4 by lra.
  suff : 0< 15 * u^3 + 8 * u^4 by lra.
  clear -upos u2pos; nra.
case:(@ex_mul p cl2 (1-p))=>//.
    rewrite bpow_plus -/u ; have ->: pow 1 = 2 by [].
    by [].
  by rewrite /cl2; apply: generic_format_round.
move=> mcl2; rewrite -/u  bpow_plus. 
have ->: (2 * u * (pow 1 * pow (- p))) = 4*u^2.
  rewrite /u; have->: pow 1 = 2 by []; ring.
move=>cl2m4u2.
pose m' := (m + mcl2)%Z.
have cl1cl2m4u2: cl1+cl2 = (IZR m') * (4 * u^2).
  rewrite cl1m4u2 cl2m4u2 /m' plus_IZR; ring.
move:  hcl3.
rewrite   cl1cl2m4u2 .
rewrite Rabs_mult (Rabs_pos_eq  (4 * u ^ 2)); last by clear -upos ; nra.
move=>hi1.
have : Rabs (IZR m') <= pow p.
  apply/(Rmult_le_reg_r (4 * u ^ 2)).
    clear -upos; nra.
  have -> //: pow p * (4 * u ^ 2)= 4*u.
  have->: 4* u^2 = pow (2 -p -p) .
    rewrite  !bpow_plus /u; have-> : pow 2 = 4 by []; ring.
  rewrite -bpow_plus.
  have->: 4*u = pow(2 -p) by rewrite  !bpow_plus /u.
  congr bpow; ring.
move=> hi2.
have Fcl12: format (cl1 + cl2).
  case: hi2=> hi2.
    have hh: cl1+cl2 = (F2R (Float two m' (2  -p -p))).
      rewrite  cl1cl2m4u2 /F2R; set exp := (2 - p -p)%Z.
      rewrite /=.
      congr Rmult.
      rewrite /exp !bpow_plus /u.
      have->:pow 2 = 4 by [].
      ring.
    by apply:(FLX_format_Rabs_Fnum p hh).
  rewrite  cl1cl2m4u2.
  move: hi2.
  rewrite -(Rabs_pos_eq (pow p)); last by apply:bpow_ge_0.
  case/Rabs_eq_Rabs => ->.
    have->: pow p * (4 * u ^ 2) = pow (2 -p ).
      have ->: (4 * u ^ 2) = pow (2 -p -p).
        rewrite !bpow_plus /u; have ->: 4 = pow 2 by [].
        ring.
      rewrite -bpow_plus.
      congr bpow; ring.
    apply:generic_format_bpow; rewrite /fexp;lia.
  have ->: 
   (- pow p * (4 * u ^ 2))= - (pow p * (4 * u ^ 2)) by ring.
  apply/generic_format_opp.
  have->: pow p * (4 * u ^ 2) = pow (2 -p ).
    have ->: (4 * u ^ 2) = pow (2 -p -p).
      rewrite !bpow_plus /u; have ->: 4 = pow 2 by [].
      ring.
    rewrite -bpow_plus; congr bpow; ring.
  apply:generic_format_bpow; rewrite /fexp;lia.
have e30: e3 = 0.
  rewrite /e3 /cl3 round_generic //; ring.
apply:(Rle_lt_trans _  (4* (u * u) + / 2 * (u * u * u))) =>//.
  have e3': Rabs e3 = 0 by rewrite e30 Rabs_0.
  lra.
apply:(Rlt_le_trans _  (4 * (u * u) *  ((1 + u) ^ 2))); last first.
  apply: Rmult_le_compat_l=>//; clear -upos; nra.
have ->:  (1 + u) ^ 2 = 1 + 2*u + u^2 by ring.
suff: / 2 * (u * u * u) <  8 * u^3 + 4* u ^ 4.
  lra.
suff : 0< 15 * u^3 + 8 * u^4 by lra.
clear -upos u2pos; nra.
Qed.
 

End Algo12.



End Times.

