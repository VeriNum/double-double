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
Hypothesis hp1 : (1 < p)%Z.

Local Instance p_gt_0 : Prec_gt_0 p.
exact: (Z.lt_trans _ 1 _ _ hp1).
Qed.

Variable choice : Z -> bool.
(* Hypothesis ZNE : choice = fun n => negb (Z.even n). *)
Hypothesis choice_sym: forall x, choice x  = negb (choice (- (x + 1))).

Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format two fexp).
Local Notation ce := (cexp two fexp).
Local Notation mant := (scaled_mantissa two fexp).
Local Notation rnd_p := (round two fexp (Znearest choice)).
Let u := pow (-p).

Fact  upos: 0 < u . Proof. by apply:(upos p). Qed.
Fact  u2pos: 0 < u * u. by move: upos ; nra. Qed.

Definition middle_point x:= (~ (format x)) /\
 x - round two  fexp Zfloor x = round two  fexp Zceil x - x.

Lemma round_mant_even  x (ZNE:  choice = fun n => negb (Z.even n)): 
 middle_point x ->
Zeven (Znearest choice (mant x)).
Proof.
move=>  [nFx hmid].
have pn0: pow (ce x) <> 0 by move:(bpow_gt_0 two (ce x)); lra.
move/(round_N_middle two fexp  choice x) :(hmid).
rewrite ZNE.
case e: (Z.even (Zfloor (mant x))); rewrite /= -ZNE /round /F2R /=;
  move/Rmult_eq_reg_r /(_ pn0)/eq_IZR=> ->.
  by move/Zeven_bool_iff: e => e.
rewrite Zceil_floor_neq. 
  apply/Zeven_bool_iff.
  by rewrite Z.add_1_r  Z.even_succ Zodd_even_bool e.
move=> h.
apply:nFx.
suff->: x = round two fexp Zfloor x by apply/generic_format_round.
rewrite /round /F2R /= h /scaled_mantissa Rmult_assoc -bpow_plus.
ring_simplify(- ce x + ce x)%Z.
by rewrite Rmult_1_r.
Qed.

Lemma rnd_p_sym x: rnd_p (-x) = - (rnd_p  (x)).
Proof.
suff : - rnd_p (- x) =  rnd_p x by lra.
by rewrite round_N_opp Ropp_involutive /round  /Znearest -choice_sym.
Qed.

Lemma rnd_p_abs x: rnd_p (Rabs x) = Rabs (rnd_p x).
Proof.
case:(Rlt_le_dec x 0)=> x0.
  have: rnd_p x <= 0.
    have -> : 0 = rnd_p 0 by rewrite round_0.
    apply:round_le; first lra.
  by rewrite Rabs_left // => h ; rewrite Rabs_left1 // rnd_p_sym.
move/(round_le radix2 fexp (Znearest choice)):(x0); rewrite round_0=> h.
by rewrite !Rabs_pos_eq.
Qed.

Section DWTimesDW1.

Hypothesis Hp6 : (6 <= p)%Z.


Local Instance p_gt_0_6 : Prec_gt_0 p.
exact: (Z.lt_le_trans _ _  _ _ Hp6).
Qed.


Fact  Hp1_6 : (1 < p)%Z.
Proof. lia. 
Qed.

Notation Hp1 := Hp1_6.

Notation Fast2Mult := (Fast2Mult p choice).
Notation Fast2Sum := (Fast2Sum p choice).


Notation F2P_prod a b  :=  (fst (Fast2Mult a b)).
Notation F2P_error a b  :=  (snd (Fast2Mult a b)).

Hypothesis Fast2Mult_correct: 
  forall a b, a * b =  F2P_prod a b +  F2P_error a b.

Notation F2P_errorE := (F2P_errorE Fast2Mult_correct).


Hypothesis TwoProdE : TwoProd = Fast2Mult. (* or Dekker's algorithm *)



Definition DWTimesDW1 (xh xl yh yl : R) :=
  let (ch, cl1) := (TwoProd xh yh) in
  let tl1 := rnd_p (xh * yl) in
  let tl2 := rnd_p (xl * yh) in
  let cl2 := rnd_p (tl1 + tl2) in 
  let cl3 := rnd_p (cl1 + cl2) in  Fast2Sum ch cl3.

Lemma  DWTimesDW1C (xh xl yh yl : R):  DWTimesDW1 xh xl yh yl = DWTimesDW1  yh yl  xh xl.
Proof.
rewrite /DWTimesDW1 TwoProdE Fast2MultC.
suff ->: (rnd_p (xh * yl) + rnd_p (xl * yh)) = (rnd_p (yh * xl) + rnd_p (yl * xh)) by [].
rewrite (Rmult_comm xh) (Rmult_comm yh); ring.
Qed.



Definition errorDWTDW1 xh xl yh yl  := let (zh, zl) := DWTimesDW1 xh xl yh yl in
  let xy := ((xh + xl) * (yh  + yl))%R in ((zh + zl) - xy).

Definition relative_errorDWTDW1 xh xl yh yl  := let (zh, zl) := DWTimesDW1 xh xl yh yl  in
  let xy :=  ((xh + xl) * (yh  + yl))%R  in (Rabs (((zh + zl) - xy)/ xy)).


Lemma  boundDWTDW_ge_0: 0 < 5 * (u * u).
Proof.
have upos:= upos.
have u2pos:= u2pos.
 lra.
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
have upos:= upos.
have u2pos:= u2pos.
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


Fact  DWTimesDW1_Asym_r xh xl yh yl :
  (DWTimesDW1 xh xl (-yh ) (- yl)) =
       pair_opp  (DWTimesDW1 xh xl yh yl).
Proof.
have rnd_p_sym := rnd_p_sym.
rewrite /DWTimesDW1 TwoProdE /=.
(* case=> <- <-. *)
rewrite !(=^~Ropp_mult_distr_r, rnd_p_sym,  Fast2Sum_asym)//.
have->: (- (xh * yh) - - rnd_p (xh * yh)) = -((xh * yh) - rnd_p (xh * yh)) by ring.

by rewrite !(=^~Ropp_plus_distr, rnd_p_sym ,  Fast2Sum_asym) ?Ropp_involutive .
Qed.

Fact  DWTimesDW1_Asym_l xh xl yh yl   : 
  (DWTimesDW1 (-xh) (-xl)  yh yl ) =  pair_opp  (DWTimesDW1 xh xl yh yl).
  Proof.
    by rewrite !(DWTimesDW1C _ _ yh _) DWTimesDW1_Asym_r.
Qed.

  Fact  DWTimesDW1Sx xh xl yh yl  e:
    (DWTimesDW1 (xh * pow e) (xl * pow e)  yh yl ) =
    map_pair (fun x => x * (pow e))  (DWTimesDW1 xh xl   yh yl ).
Proof.
rewrite /DWTimesDW1 TwoProdE /=.
by rewrite !(Rmult_comm _ yh) !(Rmult_comm _ yl)!(=^~Rmult_assoc, round_bpow, =^~Rmult_plus_distr_r,Fast2SumS,=^~Rmult_minus_distr_r ) 
  !(Rmult_comm yh)//; apply:generic_format_round.
Qed.

Fact  DWTimesDW1Sy xh xl yh yl e:
  (DWTimesDW1 xh xl   (yh * pow e) (yl * pow e)) =
  map_pair (fun x => x * (pow e))  (DWTimesDW1 xh xl   yh yl ). 
Proof.
 rewrite /DWTimesDW1 TwoProdE /=.
by rewrite  !(=^~Rmult_assoc, round_bpow, =^~Rmult_plus_distr_r,Fast2SumS,=^~Rmult_minus_distr_r ) //; 
   apply:generic_format_round.
Qed.


Lemma double_lpart_u ah al (DWa:double_word ah al):  1 <= ah < 2 -> Rabs al <= u.
Proof.
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

Section DWTimesDW1_kernel.

Variables xh xl yh yl :R.
Notation ch :=  (rnd_p (xh * yh)).
Notation cl1 :=  (xh * yh -  ch).
Notation tl1 := (rnd_p (xh * yl)).
Notation e1 := (tl1 - xh*yl).
Notation tl2 := (rnd_p (xl * yh)).
Notation e2 := (tl2 - xl*yh).
Notation cl2 := ( rnd_p (tl1 + tl2)).
Notation e3 := (cl2 - (tl1 + tl2)).
Notation cl3 := (rnd_p (cl1 + cl2)).
Notation e4 := (cl3 - (cl1 + cl2)).
Notation zh := (fst (Fast2Sum ch cl3)).
Notation zl := (snd (Fast2Sum ch cl3)).

Hypothesis DWx:double_word xh xl.
Hypothesis DWy:double_word yh yl.
Notation x := (xh + xl).
Notation y := (yh + yl).
Notation xy := (x * y).

Hypothesis  x0 : xh + xl <> 0.
Hypothesis  xh12 : 1 <= xh <= 2 - 2 * u.
Hypothesis  y0 : yh + yl <> 0.
Hypothesis  yh12 : 1 <= yh <= 2 - 2 * u.

Lemma Fcl1:  cl1 = rnd_p (xh * yh -  ch).
Proof.
rewrite [RHS] round_generic //.
case:DWx =>[[Fxh Fxl] _].
case:DWy =>[[Fyh Fyl] _].
have ->: cl1 = - (ch - xh * yh) by ring.
by apply/generic_format_opp/mult_error_FLX.
Qed.

Fact  cl1ub: Rabs cl1 <= 2 * u.
Proof.
have upos:= upos.
rewrite -Ropp_minus_distr Rabs_Ropp.
have ->: 2 * u = / 2 * u * pow 2.
  have->: pow 2 = 4 by [].
  field.
rewrite /u; apply: error_le_half_ulp'; first lia.
rewrite Rabs_pos_eq; last nra.
change (xh*yh <= 4); nra.
Qed.

Fact  cl1m4u2: exists Mcl1 , cl1 = (IZR Mcl1)* (4*u^2).
Proof.
case:DWx =>[[Fxh Fxl] _].
case:DWy =>[[Fyh Fyl] _].
case:(@ex_mul p xh 0)=>//.
  change (1 <= Rabs xh); rewrite Rabs_pos_eq; lra.
  move=> mxh; rewrite Rmult_1_r -/u => xhE.
case:(@ex_mul p yh 0)=>//.
  change (1 <= Rabs yh); rewrite Rabs_pos_eq; lra.
  move=> myh; rewrite Rmult_1_r -/u => yhE.
have xhyhm4u2: xh*yh = IZR (mxh * myh) * (4* u^2).
  rewrite xhE yhE mult_IZR; ring.
case: (@ex_mul p ch 0)=>//.
    rewrite  -rnd_p_abs.
    have ->: pow 0 = rnd_p 1.
    rewrite round_generic //.
      change (format (pow 0)); apply:format_bpow =>//.
    apply: round_le.
    rewrite Rabs_pos_eq; nra.
  rewrite /ch; apply:generic_format_round.
move=> mch; rewrite Rmult_1_r -/u => chmu2.
have chm4u2: ch = (IZR ( mch * 2^(p -1)))* (4 * u^2).
  rewrite chmu2.
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
by exists m; rewrite /m chm4u2 xhyhm4u2 plus_IZR opp_IZR ; ring.
Qed.


Fact  ylu:Rabs yl <= u.
Proof.
have upos:=upos.
by apply: (double_lpart_u DWy); lra.
Qed.

Fact  xlu:Rabs xl <= u.
Proof.
have upos:=upos.
by apply: (double_lpart_u DWx); lra.
Qed.

Fact xhylub: Rabs (xh*yl) <= 2*u - 2*(u*u).
Proof.
have upos:= upos.
rewrite Rabs_mult Rabs_pos_eq; last lra.
have->: 2 * u - 2 * (u * u) = (2 - 2 * u) * u by ring.
have ylu:=ylu.
apply:Rmult_le_compat; try apply: Rabs_pos; lra.
Qed.

Fact tl1ub: Rabs tl1 <= 2*u -2* (u *u).
Proof.
have upos:=upos.
have ylu:=ylu.
rewrite -rnd_p_abs.
have xhylub: Rabs (xh*yl) <= 2*u - 2*(u*u).
  rewrite Rabs_mult Rabs_pos_eq; last lra.
have->: 2 * u - 2 * (u * u) = (2 - 2 * u) * u by ring.
apply:Rmult_le_compat; try apply: Rabs_pos; lra.
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
Qed.

 Fact e1ub: Rabs e1 <= u*u.
Proof.
have upos:=upos.
have u2pos:=u2pos.
have xhylub:= xhylub.
have tl1ub:= tl1ub.
have->: u * u = /2 * u * (pow (1 -p)) by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
apply: error_le_half_ulp'=>//.
rewrite bpow_plus  /= IZR_Zpower_pos /= -/u; apply:(Rle_trans _  (2 * u - 2 * (u * u))) =>//.
lra.
Qed.


Fact xlyhub: Rabs (xl*yh) <= 2*u - 2*(u*u).
Proof.
have upos:=upos.
  rewrite Rabs_mult (Rabs_pos_eq yh); try lra.
  have->: 2 * u - 2 * (u * u) = u * (2 - 2 * u) by ring.
have xlu:= xlu.
  apply:Rmult_le_compat; try apply: Rabs_pos; lra.
Qed.


Fact tl2ub: Rabs tl2 <= 2*u -2* (u *u).
Proof.
have upos:= upos.
have xlu:=xlu.
rewrite -rnd_p_abs.
have xlyhub: Rabs (xl*yh) <= 2*u - 2*(u*u).
  rewrite Rabs_mult (Rabs_pos_eq yh); last lra.
  have->: 2 * u - 2 * (u * u) = u * (2 - 2 * u) by ring.
  apply:Rmult_le_compat; try apply: Rabs_pos; lra.
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
Qed.

 Fact e2ub: Rabs e2 <= u*u.
Proof.
have upos:= upos.
have u2pos:= u2pos.
have xlyhub:= xlyhub.
have tl2ub:= tl2ub.
have->: u * u = /2 * u * (pow (1 -p)) by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
apply: error_le_half_ulp'=>//.
rewrite bpow_plus  /= IZR_Zpower_pos /= -/u; apply:(Rle_trans _  (2 * u - 2 * (u * u))) =>//.
lra.
Qed.

Fact tl1tl2: Rabs (tl1 + tl2) <= 4*u - 4*(u * u).
Proof.
have tl1ub:=tl1ub.
have tl2ub:=tl2ub.
  by apply:(Rle_trans _ _ _ (Rabs_triang _ _)); lra.
Qed.

Fact cl2ub: Rabs cl2 <= 4*u - 4*(u * u).
Proof.
have tl1tl2:= tl1tl2.
suff->:  4*u - 4*(u * u) = rnd_p  (4*u - 4*(u * u)) 
  by rewrite -rnd_p_abs; apply:round_le.
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
Qed.

Fact e3ub: Rabs e3 <= 2 * (u * u).
Proof.
have upos:=upos.
have u2pos:= u2pos.
have tl1tl2:= tl1tl2.
have cl2ub:=cl2ub.
  have->: 2 * (u * u )= /2 * u * (pow (2 -p)) by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  rewrite bpow_plus  /= IZR_Zpower_pos /= -/u.
 lra.
Qed.


Fact cl1cl2: Rabs (cl1 + cl2) <= 6*u - 4*(u * u).
Proof.
have cl1ub:=cl1ub.
have cl2ub:=cl2ub.
apply:(Rle_trans _ _ _ (Rabs_triang _ _)); lra.
Qed.

Fact cl3ub: Rabs cl3 <= 6*u.
Proof.
have upos:= upos.
have u2pos:= u2pos.
have  cl1cl2:= cl1cl2.
rewrite -rnd_p_abs.
suff ->: 6*u = rnd_p (6 * u) by apply:round_le; lra.
rewrite round_generic //.
rewrite /u; apply:formatS=>//.
have fle : 6 = F2R (Float two 6 0) by rewrite /F2R /=; ring.
apply: (FLX_format_Rabs_Fnum p fle);  rewrite /= Rabs_pos_eq; last lra.
apply:(Rlt_le_trans _ 8); first lra.
have->:8 = pow 3 by [].
apply:bpow_le; lia.
Qed.

Fact e4ub: Rabs e4 <= 4 * (u * u).
Proof.
have upos:=  upos. 
have u2pos:= u2pos.
have cl1cl2 := cl1cl2.
have->: 4 * (u * u )= /2 * u * (pow (3 -p)) 
  by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
apply: error_le_half_ulp'=>//.
rewrite bpow_plus  /= IZR_Zpower_pos /= -/u. 
by apply:(Rle_trans _ (6 * u)); lra.
Qed.

Fact cl3lech: Rabs cl3 <= Rabs ch.
Proof.
have upos:= upos.
have cl3ub:=cl3ub.
apply:(Rle_trans _ (6 * u))=>//.
apply: (Rle_trans _ 1).
  apply: (Rle_trans _ (8 * u)); try lra.
  suff : pow (3 - p) <= pow 0 .
  rewrite bpow_plus  /= IZR_Zpower_pos /= -/u; lra.
  apply:bpow_le; lia.
  have ->:  1 = pow 0 by [].
  rewrite -(round_generic two fexp (Znearest choice) (pow 0)).
  rewrite /ch  -rnd_p_abs; apply/round_le; rewrite /= Rabs_pos_eq; nra.
  by apply:generic_format_bpow; rewrite /fexp; lia.
Qed.

Notation eta := (-(xl* yl) + e1 + e2 + e3 + e4).

Fact xlylub: Rabs (xl * yl) <= u*u.
Proof.
have upos:= upos.
have xlu :=xlu.
have ylu := ylu.
rewrite Rabs_mult;
  move : (Rabs_pos xl) (Rabs_pos yl); nra.
Qed.

Fact rabs_eta : Rabs eta <=  
                Rabs(xl * yl)  + Rabs e1 + Rabs e2 + Rabs e3 + Rabs e4.
Proof.
  apply:(Rle_trans _ ( (Rabs (xl*yl))+ Rabs e1 + Rabs e2 + Rabs e3 + Rabs e4)); last lra.

   repeat (apply: (Rle_trans _ _ _ (Rabs_triang _ _)); 
     first apply : Rplus_le_compat_r); try lra.
  rewrite Rabs_Ropp ; lra.
Qed.


Fact F2Schcl3: (Fast2Sum_correct p choice  ch cl3).
Proof.
have rnd_p_sym:= rnd_p_sym.
have cl3lech:= cl3lech.
apply/F2Sum_correct_abs=>//; apply/generic_format_round.
Qed.

Fact zhpzlE: zh + zl =  (xh + xl) * (yh + yl) + eta.
Proof. by rewrite  F2Schcl3; ring. Qed.

Fact etaub: Rabs eta <= 9 *(u * u).
Proof. by move:rabs_eta xlylub e1ub e2ub e3ub e4ub; lra. Qed.

Fact case_xhyhge2:  2 <= xh*yh -> (Rabs ((zh + zl - xy) / xy) < 5 * (u * u)).
Proof.
move=> xhyhge2.
have upos:= upos.
have u2pos:= u2pos.
have ult1 : u < 1 by rewrite /u ; apply:bpow_lt_1; lia.
apply:(Rle_lt_trans _ ((9 * (u * u)) / (2 * (1 - u) * (1 - u)))); last first.
  apply:(Rmult_lt_reg_r (2 * (1 - u) * (1 - u))).
    nra.
  rewrite /Rdiv Rmult_assoc Rinv_l; last  nra.
  have ->: (2 * (1 - u) * (1 - u)) = 2 - 4 * u + 2* (u*u) by ring.
  suff: 0 < u*u -20* u^3 + 10* (u*u) * (u * u)  by lra.
  suff : u <= /32 by clear -upos u2pos Hp6; nra.
  change (pow (-p) <= pow (- 5)); apply/bpow_le;lia.
rewrite /Rdiv Rabs_mult.
apply:Rmult_le_compat; try apply:Rabs_pos.
  rewrite zhpzlE; have ->: xy +eta -xy = eta by ring.
  exact etaub.
  have xpos: 0 < xh + xl.
    move/Rabs_le_inv: xlu;lra.
  have :(xh + xl ) >= xh * (1 - u).
    move/Rabs_le_inv: xlu; nra.
  have :(yh + yl ) >= yh * (1 - u).
    move/Rabs_le_inv: ylu;nra.
  move =>  hy hx.    
  have hypos : 0 < (yh + yl).
    move/Rabs_le_inv: ylu; lra.
 have xypos: 0 < xy by apply/ Rmult_lt_0_compat; lra.
rewrite Rabs_pos_eq ; last by apply/Rlt_le/Rinv_0_lt_compat.
clear -ult1 upos  xhyhge2 hx hy xh12 yh12.
apply/Rinv_le   ; first  nra.
apply:(Rle_trans _ ( xh * (1 - u) * (yh * (1 - u))));
last by apply/Rmult_le_compat ; nra.
rewrite Rmult_assoc.
have->:  xh * (1 - u) * (yh * (1 - u)) = xh *yh * ((1 - u) * (1 - u)) by ring.
apply/Rmult_le_compat_r;nra.
Qed.


Fact tlMu2 tl (Ftl: format tl) :u/2 <= Rabs tl -> exists Mtl, tl = IZR Mtl * (u*u).
Proof.
move=>u2letl.
case:(@ex_mul  p tl (-1 -p))=>// .
  suff->:   pow (-1 - p) =  u / 2 by [].
  by rewrite bpow_plus  /u; rewrite Rmult_comm.
move =>Mtl tlE ; exists Mtl.
rewrite tlE bpow_plus -/u.
have ->: (2 * u * (pow (-1) * u)) = u*u.
  have -> : pow (-1) = /2 by [];field.
done.
Qed.

Fact Ftl12_e30(Ftl12:  format (tl1+tl2)): e3=0.
Proof. by rewrite round_generic //; ring. Qed.

Section case_xhyhlt2.

Hypothesis xhyhlt2: xh * yh < 2.

Fact cl1ub': Rabs cl1 <= u.
Proof.
rewrite -Ropp_minus_distr Rabs_Ropp.
have ->: u = / 2 * u * (pow 1)  by rewrite /= IZR_Zpower_pos /=; field.
rewrite /u; apply: error_le_half_ulp'; first lia.
rewrite Rabs_pos_eq  /= ?IZR_Zpower_pos /= ?Rmult_1_r; try lra.
nra.
Qed.

Fact tl1u: Rabs tl1 <= xh * u.
Proof.
have ylu:=ylu.
have Fxh: format xh by case: DWx;  case.
rewrite -rnd_p_abs.
have -> : xh * u = rnd_p (xh * u).
  by rewrite /u round_bpow round_generic.
apply:round_le; rewrite Rabs_mult Rabs_pos_eq; last  lra.
  by apply:Rmult_le_compat_l ; lra.
Qed.

Fact tl2u: Rabs tl2 <= yh * u.
Proof.
have xlu:=xlu.
have Fyh: format yh by case: DWy; case.
rewrite -rnd_p_abs.
suff -> : yh * u = rnd_p (yh * u).
  apply:round_le.
  rewrite Rabs_mult Rmult_comm Rabs_pos_eq; try lra.
    apply:Rmult_le_compat_l; lra.
by rewrite /u round_bpow round_generic.
Qed.

Fact hsxhyh: xh + yh <= 3 -2*u .
Proof.
have Fxh: format xh  by case:DWx; case.
have Fyh: format yh  by case:DWy; case.
by apply:l5_2F=>//; lra.
Qed.

Fact  stl12u: Rabs (tl1 + tl2)  <= (3 -2*u) *u.
Proof.
have upos:= upos.
have tl1u := tl1u.
have tl2u := tl2u.
have  hsxhyh :=  hsxhyh.
apply: (Rle_trans _ _ _ (Rabs_triang _ _)).
apply:(Rle_trans _ ((xh  + yh)* u)); first lra.
by apply :Rmult_le_compat_r; lra.
Qed.



Fact  cl2ub': Rabs cl2 <= 3 * u.
Proof.
have upos:= upos.
have u2pos:= u2pos.
have  hsxhyh := hsxhyh.
have stl12u := stl12u.
have->: 3 * u= rnd_p (3*u).
  rewrite round_generic //;apply/formatS =>//.
  apply:(@FLX_format_Rabs_Fnum _ _(Float two 3 0)).
    rewrite /F2R //=; ring.
  rewrite /=; apply:(Rlt_le_trans _ (pow 2)).
    have->: pow 2 = 4 by [].
    rewrite Rabs_pos_eq; lra.
  by apply: bpow_le; lia.
by rewrite -rnd_p_abs;apply:round_le; lra.
Qed.

Fact  scl12u: Rabs (cl1 + cl2) <= 4*u.
Proof.
have cl1ub := cl1ub'.
have cl2ub := cl2ub'.
apply: (Rle_trans _ _ _ (Rabs_triang _ _)); lra.
Qed.

Fact  e4ub': Rabs e4 <= 2 * u *u.
Proof.
have scl12u :=scl12u.
have-> :  2 * u * u = / 2 * pow (- p) * pow (2 - p).
    rewrite bpow_plus -/u /= IZR_Zpower_pos /=; field.
apply: error_le_half_ulp'; first lia.
rewrite !bpow_plus -/u /= IZR_Zpower_pos /=; lra.
Qed.

Fact  etaub7: Rabs eta <= 7 *(u * u).
Proof.
have rabs_eta:= rabs_eta.
have e4ub:=e4ub'.
have e3ub := e3ub.
have e2ub := e2ub.
have e1ub := e1ub.
have xlylub := xlylub.
lra.
Qed.

Fact case_cl2ge2u: 2*u <= Rabs cl2 -> Rabs eta <= 5* (u * u).
Proof.
move => hcl2.
have upos:= upos.
have u2pos:= u2pos.
case : cl1m4u2=> Mcl1 cl1E.
case:(@ex_mul p cl2 (1-p)).
  + by rewrite bpow_plus -/u.
  + by  apply:generic_format_round.
move=> Mcl2. 
have ->:  (2 * pow (- p) * pow (1 - p)) = 4*(u * u).
  rewrite bpow_plus -/u; ring_simplify.
  by have ->: pow 1 = 2 by []; ring.
move=> cl2E.
have cl1p2E: cl1 + cl2 =  (IZR (Mcl1 + Mcl2))* ( 4 * (u *u)).
  rewrite plus_IZR cl2E cl1E;  ring.
have e40: e4 = 0.
  rewrite round_generic ; first ring.
  pose fx := Float two  (Mcl1 + Mcl2)%Z  (2* (1 -p)) %Z.
  case: scl12u=>h; last first.
    apply/generic_format_abs_inv; rewrite h.
    change (format ((pow 2) * pow (-p))).
    by rewrite -bpow_plus; apply/format_bpow.
  have hf : cl1 + cl2 = F2R fx.
    rewrite cl1p2E /fx /F2R.
    set e :=( 2 * (1 - p))%Z.
    rewrite /= /e.
    have ->: (2 * (1 - p) = 2 -p -p )%Z by ring.
    by rewrite !bpow_plus /u; have ->: 4 = pow 2 by []; ring.
  apply:(@FLX_format_Rabs_Fnum p _ fx)=>//.
  move: h; rewrite cl1p2E /fx /= Rabs_mult (Rabs_pos_eq (4 * (u * u))); try lra.
  move=>h.
  have {} h:  Rabs (IZR (Mcl1 + Mcl2)) * u < 1. nra.
  move/(Rmult_lt_compat_r (pow p)):h. 
  rewrite Rmult_assoc.
  have ->: u * pow p = 1.
    by rewrite /u -bpow_plus; have->: (-p +p = 0)%Z by ring.
  by rewrite Rmult_1_r Rmult_1_l; apply; apply:bpow_gt_0.
have e3ub := e3ub.
have e2ub := e2ub.
have e1ub := e1ub.
have xlylub := xlylub.
 move:rabs_eta; rewrite e40 Rabs_R0; lra.
Qed.

Section case_cl2lt2u.

Hypothesis cl2lt2u : Rabs cl2 < 2*u.

Fact e3ub': Rabs e3 <= (u * u).
Proof.
have->:(u * u )= /2 * u * (pow (1 -p)) by rewrite /u 
    bpow_plus /= IZR_Zpower_pos /=; field.
apply: error_le_half_ulp'=>//.
have ->: pow (1 -p) = 2 * u by rewrite bpow_plus /u.
case:(Rle_lt_dec  (Rabs (tl1 + tl2))  (2 * u))=>//.
move/Rlt_le/(round_le two fexp (Znearest choice)).
rewrite rnd_p_abs (round_generic _ _ _ (2 *u)); first lra.
change (format ((pow 1)* (pow (-p)))).
by  rewrite -bpow_plus; apply/format_bpow; lia.
Qed.

Fact case_tl1ltui2: Rabs tl1 < u/2 -> Rabs eta <= 475/100 * (u*u).
Proof.
move=> tl1ub.
have upos:= upos.
have u2pos:= u2pos.
have xlu:= xlu.
have ylub: Rabs yl < /2 * u.
  case:(Rlt_le_dec (Rabs yl) (/2*u)) =>//  h.
  have :  / 2 * u  *1 <= Rabs yl * xh.
    apply: Rmult_le_compat; lra.
  rewrite Rmult_1_r -(Rabs_pos_eq xh); last lra.
  rewrite -Rabs_mult.
  move/(round_le two fexp (Znearest choice)); rewrite rnd_p_abs 
      (Rmult_comm  yl) round_generic; try lra.
  change (format ((pow (-1)) * ( pow (-p)))).
  by  rewrite -bpow_plus; apply/format_bpow; lia.
have  e1ub: Rabs e1 <= /4 * (u * u).
  have ->:  / 4 * (u * u) =  /2 * u * (pow (-1  -p)).
    by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  rewrite bpow_plus  /= IZR_Zpower_pos /= -/u Rmult_1_r.
  case:(Rle_lt_dec   (Rabs (xh * yl)) (/2 *u))=>//.
  move/Rlt_le/(round_le two fexp (Znearest choice)).
  rewrite rnd_p_abs -/tl1 round_generic; first lra.
  by change (format ((pow (-1)) * (pow (-p)))); 
       rewrite -bpow_plus; apply/format_bpow.
have xlylub: Rabs (xl *yl) < /2 * (u * u).
  rewrite Rabs_mult.
  by clear - ylub xlu; move :(Rabs_pos xl) (Rabs_pos yl);  nra.
by move: rabs_eta e2ub e3ub' e4ub'; lra.
Qed.

Fact case_tl2ltui2:  Rabs tl2 < u/2 -> Rabs eta <= 475/100 * (u*u).
Proof.
move=> tl2ub.
have upos:= upos.
have u2pos:= u2pos.
have ylu:= ylu.
have xlub: Rabs xl < /2 * u.
  case:(Rlt_le_dec (Rabs xl) (/2*u)) =>//  h.
  have :  / 2 * u  *1 <= Rabs xl * yh.
    apply: Rmult_le_compat; lra.
  rewrite Rmult_1_r -(Rabs_pos_eq yh);last lra.
  rewrite -Rabs_mult.
  move/(round_le two fexp (Znearest choice)); rewrite rnd_p_abs 
        round_generic; first lra.
  change (format ((pow (-1)) * ( pow (-p)))).
  by  rewrite -bpow_plus; apply/format_bpow; lia.
have  e2ub: Rabs e2 <= /4 * (u * u).
  have ->:  / 4 * (u * u) =  /2 * u * (pow (-1  -p)).
    by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  rewrite bpow_plus  /= IZR_Zpower_pos /= -/u Rmult_1_r.
  case:(Rle_lt_dec   (Rabs (xl * yh)) (/2 *u))=>//.
  move/Rlt_le/(round_le two fexp (Znearest choice)).
  rewrite rnd_p_abs round_generic; first lra.
  by change (format ((pow (-1)) * (pow (-p)))); 
       rewrite -bpow_plus; apply/format_bpow.
have xlylub: Rabs (xl *yl) < /2 * (u * u).
  rewrite Rabs_mult.
  by clear - ylu xlub; move :(Rabs_pos xl) (Rabs_pos yl);  nra.
by move: rabs_eta e1ub e3ub' e4ub';lra.
Qed.

Fact tl12ub: Rabs(tl1 + tl2) <= 2*u.
Proof.
case:(Rle_lt_dec   (Rabs (tl1 + tl2)) (2*u))=>//.
move/Rlt_le/(round_le two fexp (Znearest choice));
     rewrite rnd_p_abs -/cl2 round_generic; first lra.
  change (format (pow 1 * (pow (-p)))).
  by rewrite -bpow_plus; apply/format_bpow; lia.
Qed.


(*ici*)

Fact tl12ltu_F Mtl ( tl12Mu2: tl1 + tl2 = IZR (Mtl) * (u *u)): 
   (Rabs (tl1 + tl2)) <=u  ->  format (tl1 + tl2).
Proof.
have upos:=upos.
case; last first.
  have ->: u = Rabs (pow (-p)) by rewrite /u Rabs_pos_eq //; exact: bpow_ge_0.
  by case/Rabs_eq_Rabs => ->; (try apply/generic_format_opp); apply/format_bpow.
  rewrite tl12Mu2 !Rabs_mult !(Rabs_pos_eq u); try lra.
  rewrite -Rmult_assoc -[X in _ < X]Rmult_1_l.
  move/(Rmult_lt_reg_r _ _ _ upos).
  move/(Rmult_lt_compat_r (pow p) _ _ (bpow_gt_0 two p)).
  rewrite /u Rmult_1_l Rmult_assoc -bpow_plus.
  have ->:  pow (- p + p) = 1 by ring_simplify (-p+p)%Z.
  rewrite Rmult_1_r =>h.
  rewrite -bpow_plus.
  pose f := (Float two  (Mtl)  (- p + - p)).
  apply/(@FLX_format_Rabs_Fnum p _  f).
    by rewrite /f /F2R.
  by rewrite /f .
Qed.

Fact  hFtl12 Mtl ( tl12Mu2: tl1 + tl2 = IZR (Mtl) * (u *u)): Zeven (Mtl) 
      -> format (tl1+tl2).
Proof.
have upos:= upos.
  move=> heven.
  move/Zeven_div2 :(heven).
  case: tl12ub; last first.
have ->: 2*u =  pow (1  -p)  by  rewrite bpow_plus.
rewrite -(Rabs_pos_eq (pow (1 -p))); last  apply:bpow_ge_0.
case/Rabs_eq_Rabs=> -> _; (try apply/generic_format_opp); apply/format_bpow; lia.
  move=>h; rewrite  tl12Mu2 => ->.
  rewrite mult_IZR.
  pose f := (Float two  ( Z.div2 (Mtl) )  (1 - p + - p)).
  apply/(@FLX_format_Rabs_Fnum p _  f).
    rewrite  -mult_IZR -Zeven_div2 /f /F2R //.
    set M:= Z.div2 (Mtl); set e := (1 - p + - p )%Z.
    rewrite /= /M /e !bpow_plus -!Rmult_assoc.
    have -> : pow 1 = 2 by [].
    by rewrite -mult_IZR Zmult_comm -Zeven_div2.
  rewrite /f /F2R /=.
  apply/(Rmult_lt_reg_r 2); first lra.
  rewrite -(Rabs_pos_eq 2); last lra.
  rewrite -Rabs_mult -mult_IZR Zmult_comm -Zeven_div2 //.

move:h; 
 rewrite  tl12Mu2 !Rabs_mult (Rabs_pos_eq u); try lra.
  rewrite -Rmult_assoc; move/(Rmult_lt_reg_r _ _ _ upos).
  move/(Rmult_lt_compat_r (pow p) _ _ (bpow_gt_0 two p)).
  rewrite Rmult_assoc /u -bpow_plus ; ring_simplify (-p + p)%Z.
  rewrite Rmult_1_r (Rabs_pos_eq 2);lra.
Qed.


Fact tl12leu: (u <= Rabs tl1) -> (u <= Rabs tl2) -> Rabs eta <= 5* (u * u).
Proof.
move=> htl1 htl2.
have tl12ub:= tl12ub.
have u2pos:= u2pos.
have  upos:= upos.

case:(@ex_mul  p tl1 ( -p)); try  apply/generic_format_round.
  by rewrite -/u.
move=> Mtl1.
rewrite -/u=> tl1M2u2.
case:(@ex_mul  p tl2 (-p)); try  apply/generic_format_round.
  by rewrite -/u.
move=> Mtl2; rewrite -/u=> tl2M2u2.
have tl12M2u2: tl1 + tl2 = IZR (Mtl1 + Mtl2) *( 2 * (u *u)).
 by rewrite tl1M2u2 tl2M2u2 plus_IZR; ring.
have Ftl12: format (tl1+tl2).
  case:  tl12ub; rewrite tl12M2u2 Rabs_mult=>  tl12ub.
    pose f := (Float two  (Mtl1 + Mtl2)  (1- p + - p)).
    apply/(@FLX_format_Rabs_Fnum p _  f).
    rewrite /f /F2R.

    suff ->:  (2 * (u * u)) = pow (1 - p + - p ) by [].
     by rewrite !bpow_plus  -/u -Rmult_assoc.
  rewrite /f /=.
apply/(Rmult_lt_reg_r (Rabs (2 * (u * u)))); first by rewrite Rabs_pos_eq;lra.
suff ->: pow p * (Rabs (2 * (u * u))) = 2 * u by [].
have ->:2 = pow 1 by [].
rewrite Rabs_pos_eq  /u -?bpow_plus; (try apply:bpow_ge_0); congr bpow; ring.
move: tl12ub; rewrite -Rabs_mult -(Rabs_pos_eq (2 *u)); try lra.
have ->: 2*u = pow (1 + -p) by rewrite bpow_plus.
  case/Rabs_eq_Rabs => ->; (try apply/generic_format_opp); apply/format_bpow; lia.
by move : rabs_eta  xlylub  e1ub e2ub e4ub'; rewrite  Ftl12_e30 // Rabs_R0; lra.
Qed.

End case_cl2lt2u.


Fact xh1yh1_eta_ub : xh = 1 \/ yh = 1 -> Rabs (eta ) <= 4*(u*u).
Proof.
move=> xhyhe1.
case:DWx =>[[Fxh Fxl] _].
case:DWy =>[[Fyh Fyl] _].
(* have upos:= upos. *)
have u2pos:= u2pos.
(* have ult1 : u < 1 by rewrite /u ; apply:bpow_lt_1; lia. *)
have cl10: cl1 = 0 by case : xhyhe1 => ->; rewrite ?Rmult_1_l ? Rmult_1_r round_generic //; ring.
have e40: e4 = 0.
  rewrite cl10 Rplus_0_l round_generic; first ring.
  by apply:generic_format_round.
have e1e20: e1 = 0 \/ e2 = 0.
  by case: xhyhe1 => ->; rewrite ?Rmult_1_l ?Rmult_1_r;[left|right]; rewrite round_generic //; 
    ring.
by move : rabs_eta xlylub  e2ub e3ub e1ub;case:   e1e20 => ->;  rewrite e40  !Rabs_R0; lra.
Qed.


Fact  e3Eu2  Mtl   (tllb : u < Rabs (tl1+tl2)) (tlub : Rabs (tl1+tl2) < 2 * u ) (hodd : Zodd (Mtl)) 
             (hmant : pow p <= Rabs (IZR (Mtl)) < pow (1 + p) ) ( tl12Mu2: tl1 + tl2 = IZR (Mtl) * (u *u)):
       Rabs e3 = u*u.
Proof.
have u2pos:= u2pos.


 move/Zodd_bool_iff  :hodd => Hodd.
  case: (Zeven_ex (Mtl))=>M  Me.
  have {Me} ME : (Mtl)%Z = (2 * M + 1)%Z.
   by rewrite Me; rewrite Zeven.Zeven_odd_bool Hodd.
  (* rewrite tl12Mu2  ME => tl12lb. *)
  have hub: IZR (2*M) < IZR (2 * M + 1) <IZR (2*M+2) by split; apply/IZR_lt; lia.
  have nFs: ~ format (IZR (2 * M + 1)).
    apply: (generic_format_discrete _ _ _ M).
    rewrite /F2R /cexp -ME (mag_unique _ _ (1+p)).
      set e := fexp (1+p).
      rewrite /= /e /fexp.
      ring_simplify (1 + p -p)%Z.
      have->: pow 1 = 2 by [].
      rewrite -!mult_IZR ME !(Zmult_comm _ 2).
      have->: ((2 * (M + 1)) =  (2 * M + 2))%Z by ring.
      by [].
    by ring_simplify(1 + p - 1)%Z.


  have cexpf :  (ce (IZR (2 * M + 1)) = 1)%Z.
    rewrite /cexp /fexp (mag_unique _ _  (1 +p)); first ring.
      have->:  (1 + p - 1 = p)%Z by ring.
      by rewrite -ME.

  have rDN: round two  fexp Zfloor (IZR (2 * M + 1))  =  IZR (2 * M).
    rewrite /round /scaled_mantissa .
    rewrite cexpf (Zfloor_imp M) /F2R.
      set f := Float _ _ _.
      by rewrite Rmult_comm mult_IZR ; congr Rmult.
    move: hub.
    have -> : (2 * M + 2 = 2 * (M + 1))%Z by ring.
    rewrite !mult_IZR.
    have ->: pow(-1) = /2 by [].
    lra.
  have rUP :  round two  fexp Zceil (IZR (2 * M + 1))  =  IZR (2 * (M+ 1)).
    rewrite round_UP_DN_ulp // rDN ulp_neq_0 ?cexpf.
      by rewrite Zmult_plus_distr_r  Zmult_1_r plus_IZR.
    by apply/not_0_IZR; lia.


rewrite tl12Mu2 ME.
 rewrite /u -bpow_plus round_bpow!bpow_plus -/u.
  case:(round_DN_or_UP two fexp (Znearest choice) (IZR (2 * M + 1)));


     rewrite ?rDN ?rUP => ->; rewrite plus_IZR.
 ring_simplify (IZR (2 * M) * (u * u) - (IZR (2 * M) + 1) * (u * u)).
rewrite Rabs_Ropp Rabs_pos_eq; lra.
 rewrite !mult_IZR !plus_IZR.
ring_simplify(2 * (IZR M + 1) * (u * u) - (2 * IZR M + 1) * (u * u)).
by rewrite Rabs_pos_eq; lra.
Qed.

Fact case_xhyhlt2: Rabs ((zh + zl - xy) / xy) < 
(if (Z.odd(Ztrunc (scaled_mantissa two fexp cl2))) then 55/10 else 5) * (u * u) .
Proof.
set bound := if _ then _ else  _.

have upos:= upos.
have u2pos:= u2pos.
have ult1 : u < 1 by rewrite /u ; apply:bpow_lt_1; lia.
have minb: 5  <= bound.
rewrite /bound ; case:  (Z.odd (Ztrunc (mant cl2 ))); lra.

case:DWx =>[[Fxh Fxl] _].
case:DWy =>[[Fyh Fyl] _].
have xpos: 0 < xh + xl.
  move/Rabs_le_inv: xlu;lra.  
have ypos : 0 < (yh + yl).
    move/Rabs_le_inv: ylu; lra.
apply:(Rmult_lt_reg_r xy); first nra.
have xyipos: 0 < /xy by apply: Rinv_0_lt_compat; nra.
rewrite Rabs_mult (Rabs_pos_eq (/xy)); last lra.
rewrite Rmult_assoc Rinv_l; last nra.
have hx:(xh + xl ) >= xh * (1 - u).
  move/Rabs_le_inv: xlu=> xlu; clear - xlu upos xh12; nra.
have hy:(yh + yl ) >= yh * (1 - u).
  move/Rabs_le_inv: ylu=>ylu ; clear - ylu upos yh12; nra.   
rewrite Rmult_1_r zhpzlE; have ->: xy +eta -xy = eta by ring.
have  minb':  5 * (u * u) <= bound * (u * u) .
  by apply/Rmult_le_compat_r;  lra.
have minb'':  5 * (u * u) * xy <= bound * (u * u) * xy.
  apply/Rmult_le_compat_r =>//;  by clear -xpos ypos;  nra. 
case :(Req_dec xh 1)=> xh1.
  apply:(Rle_lt_trans _ ( 4 * (u * u))).
    by apply: xh1yh1_eta_ub; left.
  apply: (Rlt_le_trans _ ( bound* (u * u)* ((1-u)*(1-u)))); last first.
    apply:Rmult_le_compat_l. 
      clear -u2pos minb.  suff : 0 <= bound by nra.
      lra.
    by apply : Rmult_le_compat; try lra; nra.
  apply:(Rlt_le_trans _  (5* (u * u) * ((1 - u) * (1 - u)))); last first.
     apply/Rmult_le_compat_r; try lra.
  have ->: ((1 - u) * (1 - u)) = 1  - 2 * u +  (u*u) by ring.
  suff : u <= /16 by clear -upos u2pos Hp6; nra.
  change (pow (-p) <= pow (- 4)); apply/bpow_le;lia.
case :(Req_dec yh 1)=> yh1.
  apply:(Rle_lt_trans _ ( 4 * (u * u))).
    by apply: xh1yh1_eta_ub; right.
  apply: (Rlt_le_trans _ ( bound* (u * u)* ((1-u)*(1-u)))); last first.
    apply:Rmult_le_compat_l.
    apply/Rmult_le_pos; lra.
    by apply : Rmult_le_compat; try lra; nra.
  apply: (Rlt_le_trans _ ( 5* (u * u) * ((1-u)*(1-u)))); last first.
    apply:Rmult_le_compat_r; try lra.
  have ->: ((1 - u) * (1 - u)) = 1  - 2 * u +  (u*u) by ring.
  suff : u <= /16 by clear -upos u2pos Hp6; nra.
  change (pow (-p) <= pow (- 4)); apply/bpow_le;lia.
have {} xh1 : 1 < xh by lra.
have {} yh1 : 1 < yh by lra.
have xh1pu2: 1 + 2* u <= xh.
  have : succ radix2 fexp 1 <= xh .
    apply/succ_le_lt =>//.
    by change (format (pow 0)); apply/format_bpow.
  rewrite succ_eq_pos; try lra.
  suff->: 2*u = ulp radix2 fexp 1 by [].
  rewrite /u u_ulp1; field.
have x1pu: 1+ u <= x by move/Rabs_le_inv: xlu; lra.
  have yh1pu2: 1 + 2* u <= yh.
    have : succ radix2 fexp 1 <= yh .
    apply/succ_le_lt =>//.
    by change (format (pow 0)); apply/format_bpow.
  rewrite succ_eq_pos; try lra.
  suff->: 2*u = ulp radix2 fexp 1 by [].
  rewrite /u u_ulp1; field.
have y1pu: 1+ u <= y by move/Rabs_le_inv: ylu; lra.
suff h: Rabs eta <= bound * (u * u).
  apply:(Rle_lt_trans _ ( bound * (u * u))) =>//.
  rewrite -[X in X < _]Rmult_1_r.
  apply:Rmult_lt_compat_l; last by clear -upos u2pos ult1    y1pu   x1pu  ; nra.
apply/Rmult_lt_0_compat; lra.
case: (Rle_lt_dec (2*u) (Rabs cl2)) => hcl2.
  by apply/(Rle_trans _ (5*(u*u)))=> //; apply /case_cl2ge2u.
case :(Rlt_le_dec (Rabs tl1) (u/2)) => htl1.
   apply/(Rle_trans _ (5*(u*u)))=> //;
  apply: (Rle_trans _  (475 / 100 * (u * u))); try lra.
  apply/case_tl1ltui2; try lra.
case :(Rlt_le_dec (Rabs tl2) (u/2)) => htl2.
   apply/(Rle_trans _ (5*(u*u)))=> //;
  apply: (Rle_trans _  (475 / 100 * (u * u))); try lra.
  apply/case_tl2ltui2; lra.

case:(@tlMu2 tl1) =>//; (try  apply/generic_format_round) => Mtl1 tl1Mu2.
case:(@tlMu2 tl2) =>//;( try  apply/generic_format_round) => Mtl2 tl2Mu2.
have tl12Mu2: tl1 + tl2 = IZR (Mtl1 + Mtl2) * (u *u).
 by rewrite tl1Mu2 tl2Mu2 plus_IZR; ring.


(* case:(tl12ub hcl2)=>tl12ub; last first. *)
(* have Ftl12: format (tl1+tl2). *)
(* move: tl12ub; rewrite -(Rabs_pos_eq (2 * u)); last lra. *)
(* have ->: 2*u = (pow (1 -p)) by rewrite bpow_plus. *)
(* case/Rabs_eq_Rabs =>->; (try apply/generic_format_opp); apply/format_bpow; lia. *)
(* by move : rabs_eta xlylub   e4ub' e2ub; rewrite Ftl12_e30  // Rabs_R0; lra. *)


case:(Rle_lt_dec (u) (Rabs tl1)) => tl1u.
  case:(Rle_lt_dec (u) (Rabs tl2)) => tl2u.
    apply/(Rle_trans _ (5*(u*u)))=> //;
    by apply/tl12leu.

(*   case:(Zeven_odd_dec   (Mtl1 + Mtl2)). *)
(*      move/hFtl12=> Ftl12. *)
(*     move : rabs_eta xlylub   e4ub' e1ub; rewrite Ftl12_e30  // ?Rabs_R0; try  lra. *)
(*     by apply:Ftl12. *)
(*   move => hodd. *)
(* move/Zodd_bool_iff : hodd  => Hodd. *)

(* rewrite /bound. *)
(* case e:(Z.odd (Ztrunc (mant cl2))). *)
(*   move : rabs_eta xlylub   e4ub' e1ub ; rewrite (e3Eu2 (Mtl1 + Mtl2));  try lra. *)
(* by apply/Zodd_bool_iff. *)

  have  e2ub: Rabs e2 <= /2 * u * u.
    have ->:  / 2 * u * u =  /2 * u * (pow ( -p)).
      rewrite /u ; ring.
    apply: error_le_half_ulp'=>//.
    rewrite -/u .
    case:(Rle_lt_dec  (Rabs (xl * yh)) u) =>// h.
    have : rnd_p u <= rnd_p (Rabs (xl * yh)).
      apply/round_le; lra.
    rewrite rnd_p_abs round_generic; try lra.
    change (format (pow (-p))); apply/format_bpow; lia.
  case: (Rle_lt_dec (Rabs (tl1 + tl2)) u)=> h.
    have Ftl12: format (tl1+tl2).
      apply:(tl12ltu_F (Mtl1 + Mtl2))=>//.
   apply/(Rle_trans _ (5*(u*u)))=> //;
    by move : rabs_eta xlylub   e4ub' e1ub; rewrite Ftl12_e30  // Rabs_R0; lra.
  case:(tl12ub hcl2)=>tl12ub; last first.
    have Ftl12: format (tl1+tl2).
    move: tl12ub; rewrite -(Rabs_pos_eq (2 * u)); last lra.
    have ->: 2*u = (pow (1 -p)) by rewrite bpow_plus.
    case/Rabs_eq_Rabs =>->; (try apply/generic_format_opp); apply/format_bpow; lia.
   apply/(Rle_trans _ (5*(u*u)))=> //;
    move : rabs_eta xlylub   e4ub' e1ub ;rewrite  Ftl12_e30 // Rabs_R0; lra.

 have hmant :  pow p <= Rabs (IZR (Mtl1 + Mtl2)) < pow (1 + p).
    move: h  tl12ub .
    rewrite  tl12Mu2.
    rewrite -/u; split=>//.
    apply/(Rmult_le_reg_r (u * u)) =>//. 
      suff ->:   pow p * (u * u) = u .
        rewrite -(Rabs_pos_eq (u * u)); try lra.
        by rewrite -Rabs_mult; lra.

      by rewrite /u -!bpow_plus; ring_simplify(p +( -p + -p))%Z.
    apply/(Rmult_lt_reg_r (u*u)); first lra.
    suff->: pow (1 + p) * (u * u) = 2*u.
      move: tl12ub0 ;  rewrite Rabs_mult (Rabs_pos_eq (u*u));  lra.
    rewrite /u -!bpow_plus; ring_simplify  (1 + p + (- p + - p))%Z.
    by rewrite bpow_plus Rmult_comm.
  case:(Zeven_odd_dec   (Mtl1 + Mtl2)).
     move/hFtl12=> Ftl12.
    move : rabs_eta xlylub   e4ub' e1ub; rewrite Ftl12_e30  // ?Rabs_R0; try  lra.
    by apply:Ftl12.
  move => hodd.
move/Zodd_bool_iff : hodd  => Hodd.

rewrite /bound.
case e:(Z.odd (Ztrunc (mant cl2))).
  move : rabs_eta xlylub   e4ub' e1ub ; rewrite (e3Eu2 (Mtl1 + Mtl2));  try lra.
by apply/Zodd_bool_iff.


have e40: e4= 0.
  rewrite round_generic ; first ring.
    case: scl12u=>h'; last first.
      apply/generic_format_abs_inv; rewrite h'.
      change (format ((pow 2) * pow (-p))).
      by rewrite -bpow_plus; apply/format_bpow.

    have: Zeven (Ztrunc (mant cl2)).
      by apply/Zeven_bool_iff; rewrite Zeven.Zeven_odd_bool e.
    case/Zeven.Zeven_ex => N NE.
    have Fcl2: format cl2 by apply/generic_format_round.
    case: cl1m4u2=>  M cl1E.

have cecl2E: (ce cl2 =  1 - p - p)%Z.
rewrite (cexp_fexp _ _ _ (1 - p)).
rewrite /fexp; ring.
ring_simplify(1 - p - 1)%Z.
rewrite bpow_plus -/u; split.
rewrite  -rnd_p_abs.
suff ->: u = rnd_p u.
apply/round_le; lra.
rewrite round_generic //; change (format (pow (-p))); apply format_bpow; lia.
by have->: pow 1 = 2 by [].
move:(h').
rewrite cl1E.
have cl2E: cl2 = IZR N * (4 * u ^ 2).
rewrite  Fcl2.


set fnum := Ztrunc _.
set fce := ce _.
rewrite /F2R /=  /fnum NE /fce cecl2E mult_IZR (Rmult_comm 2) !bpow_plus /u.
have ->: pow 1 = 2 by [].
ring.
rewrite cl2E -Rmult_plus_distr_r -plus_IZR.
have->:  4 * u ^ 2= pow (2 -p -p).
rewrite !bpow_plus /u; have ->: 4 = pow 2 by [].
ring.




    pose fx := Float two  (M + N)%Z  (2* (1 -p)) %Z.
    have hf : IZR (M + N) * pow (2 - p - p) = F2R fx.

      rewrite /fx /F2R.
      set e' :=( 2 * (1 - p))%Z.
set e'' := (2 - p - p)%Z.
      rewrite /= /e' /e''.
      by have ->: (2 * (1 - p) = 2 -p -p )%Z by ring.
rewrite Rabs_mult (Rabs_pos_eq ( pow (2 - p - p))); last apply/bpow_ge_0.
move=> h2. 
    apply:(@FLX_format_Rabs_Fnum p _ fx)=>//.
rewrite /fx /=.

apply/(Rmult_lt_reg_r ( pow (2 - p - p))); first exact:bpow_gt_0.
rewrite -bpow_plus.

suff->: pow (p + (2 - p - p)) = 4 * u by [].
have ->:  (p + (2 - p - p) = 2 -p)%Z by ring.
by rewrite bpow_plus.
  move : rabs_eta xlylub  e1ub ; rewrite e40 ?Rabs_R0 (e3Eu2 (Mtl1 + Mtl2));  try lra.
by apply/Zodd_bool_iff.

have  e1ub: Rabs e1 <= /2 * u * u.
  have ->:  / 2 * u * u =  /2 * u * (pow ( -p)).
    rewrite /u ; ring.
  apply: error_le_half_ulp'=>//.
  rewrite -/u .
  case:(Rle_lt_dec  (Rabs (xh * yl)) u) =>// h.
  have : rnd_p u <= rnd_p (Rabs (xh * yl)).
    apply/round_le; lra.
  rewrite rnd_p_abs round_generic; try lra.
  change (format (pow (-p))); apply/format_bpow; lia.
  case: (Rle_lt_dec (Rabs (tl1 + tl2)) u)=> h.
    have Ftl12: format (tl1+tl2).
      apply:(tl12ltu_F (Mtl1 + Mtl2))=>//.
   apply/(Rle_trans _ (5*(u*u)))=> //;
    by move : rabs_eta xlylub   e4ub' e2ub; rewrite Ftl12_e30  // Rabs_R0; lra.
  case:(tl12ub hcl2)=>tl12ub; last first.
    have Ftl12: format (tl1+tl2).
    move: tl12ub; rewrite -(Rabs_pos_eq (2 * u)); last lra.
    have ->: 2*u = (pow (1 -p)) by rewrite bpow_plus.
    case/Rabs_eq_Rabs =>->; (try apply/generic_format_opp); apply/format_bpow; lia.
   apply/(Rle_trans _ (5*(u*u)))=> //;
    move : rabs_eta xlylub   e4ub' e2ub ;rewrite  Ftl12_e30 // Rabs_R0; lra.

 have hmant :  pow p <= Rabs (IZR (Mtl1 + Mtl2)) < pow (1 + p).
    move: h  tl12ub .
    rewrite  tl12Mu2.
    rewrite -/u; split=>//.
    apply/(Rmult_le_reg_r (u * u)) =>//. 
      suff ->:   pow p * (u * u) = u .
        rewrite -(Rabs_pos_eq (u * u)); try lra.
        by rewrite -Rabs_mult; lra.

      by rewrite /u -!bpow_plus; ring_simplify(p +( -p + -p))%Z.
    apply/(Rmult_lt_reg_r (u*u)); first lra.
    suff->: pow (1 + p) * (u * u) = 2*u.
      move: tl12ub0 ;  rewrite Rabs_mult (Rabs_pos_eq (u*u));  lra.
    rewrite /u -!bpow_plus; ring_simplify  (1 + p + (- p + - p))%Z.
    by rewrite bpow_plus Rmult_comm.
  case:(Zeven_odd_dec   (Mtl1 + Mtl2)).
     move/hFtl12=> Ftl12.
    move : rabs_eta xlylub   e4ub' e2ub; rewrite Ftl12_e30  // ?Rabs_R0; try  lra.
    by apply:Ftl12.
  move => hodd.
move/Zodd_bool_iff : hodd  => Hodd.

rewrite /bound.
case e:(Z.odd (Ztrunc (mant cl2))).
  move : rabs_eta xlylub   e4ub' e2ub ; rewrite (e3Eu2 (Mtl1 + Mtl2));  try lra.
by apply/Zodd_bool_iff.


have e40: e4= 0.
  rewrite round_generic ; first ring.
    case: scl12u=>h'; last first.
      apply/generic_format_abs_inv; rewrite h'.
      change (format ((pow 2) * pow (-p))).
      by rewrite -bpow_plus; apply/format_bpow.

    have: Zeven (Ztrunc (mant cl2)).
      by apply/Zeven_bool_iff; rewrite Zeven.Zeven_odd_bool e.
    case/Zeven.Zeven_ex => N NE.
    have Fcl2: format cl2 by apply/generic_format_round.
    case: cl1m4u2=>  M cl1E.

have cecl2E: (ce cl2 =  1 - p - p)%Z.
rewrite (cexp_fexp _ _ _ (1 - p)).
rewrite /fexp; ring.
ring_simplify(1 - p - 1)%Z.
rewrite bpow_plus -/u; split.
rewrite  -rnd_p_abs.
suff ->: u = rnd_p u.
apply/round_le; lra.
rewrite round_generic //; change (format (pow (-p))); apply format_bpow; lia.
by have->: pow 1 = 2 by [].
move:(h').
rewrite cl1E.
have cl2E: cl2 = IZR N * (4 * u ^ 2).
rewrite  Fcl2.


set fnum := Ztrunc _.
set fce := ce _.
rewrite /F2R /=  /fnum NE /fce cecl2E mult_IZR (Rmult_comm 2) !bpow_plus /u.
have ->: pow 1 = 2 by [].
ring.
rewrite cl2E -Rmult_plus_distr_r -plus_IZR.
have->:  4 * u ^ 2= pow (2 -p -p).
rewrite !bpow_plus /u; have ->: 4 = pow 2 by [].
ring.




    pose fx := Float two  (M + N)%Z  (2* (1 -p)) %Z.
    have hf : IZR (M + N) * pow (2 - p - p) = F2R fx.

      rewrite /fx /F2R.
      set e' :=( 2 * (1 - p))%Z.
set e'' := (2 - p - p)%Z.
      rewrite /= /e' /e''.
      by have ->: (2 * (1 - p) = 2 -p -p )%Z by ring.
rewrite Rabs_mult (Rabs_pos_eq ( pow (2 - p - p))); last apply/bpow_ge_0.
move=> h2. 
    apply:(@FLX_format_Rabs_Fnum p _ fx)=>//.
rewrite /fx /=.

apply/(Rmult_lt_reg_r ( pow (2 - p - p))); first exact:bpow_gt_0.
rewrite -bpow_plus.

suff->: pow (p + (2 - p - p)) = 4 * u by [].
have ->:  (p + (2 - p - p) = 2 -p)%Z by ring.
by rewrite bpow_plus.
  move : rabs_eta xlylub  e2ub ; rewrite e40 ?Rabs_R0 (e3Eu2 (Mtl1 + Mtl2));  try lra.
by apply/Zodd_bool_iff.
Qed.

End case_xhyhlt2.

(* DWTimesDW1 general case after wlogs *)

Lemma DWTimesDW1_correct_part_high : (Rabs ((zh + zl - xy) / xy) < 55/10 * (u * u)).
Proof.
have upos:= upos.
have ult1 : u < 1 by rewrite /u ; apply:bpow_lt_1; lia.
have u2pos: 0 < u * u by nra.
case:(Rle_lt_dec 2 (xh * yh))=>h.
  apply:(Rlt_trans _ (5 *(u * u))); last nra.
  by apply/ case_xhyhge2.
move: h => /case_xhyhlt2.

case e:  (Z.odd (Ztrunc (mant cl2)))=>//.
by move=> h; apply: (Rlt_trans _ (5 *(u * u))); last nra.
Qed.



End DWTimesDW1_kernel.

Variable b : R.
Hypothesis b5or5_5 : b =  5 \/ b = 55/10.



(* DWTimesDW1 with ties_to_even *) 
Lemma DWTimesDW1_correct_even xh xl yh yl  
                         (DWx:double_word xh xl) (DWy:double_word yh yl) 
                         (ZNE : choice = fun n => negb (Z.even n)):
  let (zh, zl) := DWTimesDW1 xh xl yh yl in
  let xy := ((xh + xl) * (yh + yl))%R in
             (Rabs ((zh + zl - xy) / xy) < 5 * (u * u)).
Proof.
have rnd_p_sym := rnd_p_sym.
have upos:= upos.

have ult1 : u < 1 by rewrite /u ; apply:bpow_lt_1; lia.
have u2pos: 0 < u * u by apply:Rmult_lt_0_compat.
(* have b1ltb2:  5 * (u * u)  < 55 / 10 * (u * u) by lra. *)

have [[Fxh Fxl] Exh] := DWx.
have [[Fyh Fyl] Eyh] := DWy.
case E1: DWTimesDW1 => [zh zl].
have Hp1:= Hp1.
case:(Req_dec yh 0)=> yh0.
  have yl0: yl = 0.
    by move:Eyh; rewrite  yh0 Rplus_0_l round_generic.
  move:E1; rewrite /DWTimesDW1 yh0 yl0 Rmult_0_r TwoProdE round_0 Fast2MultC Rmult_0_r Fast2Mult0f. 
  rewrite /Fast2Sum /F2SumFLX.Fast2Sum !(Rplus_0_r, Rminus_0_r, Rplus_0_l, round_0).
  case=> <- <-; rewrite Rplus_0_r Rmult_0_r Rminus_0_l /Rdiv Ropp_0 Rmult_0_l Rabs_R0.
  clear -upos; nra.

case:(Req_dec xh 0)=> xh0.
  have xl0: xl = 0.
    by move:Exh; rewrite  xh0 Rplus_0_l round_generic.
  move:E1; rewrite /DWTimesDW1 xh0 xl0 Rmult_0_l TwoProdE  round_0 Fast2Mult0f.
  rewrite /Fast2Sum /F2SumFLX.Fast2Sum !(Rplus_0_r, Rminus_0_r, Rplus_0_l, round_0, Rmult_0_l).
  case=> <- <-; rewrite Rplus_0_r  /Rdiv   Rmult_0_l Rabs_R0.
  by clear -upos; nra.
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
  apply:(Hwlog yh yl  (-xh) (-xl) (-zh) (-zl))=>//; try lra; last  by rewrite DWTimesDW1_Asym_l E1.
  have [[Fxh Fxl] Exh] := DWx.
  split; [split|]; try apply:generic_format_opp=>//.
  have ->:- xh + - xl = -(xh +  xl) by ring.
  by rewrite rnd_p_sym {1}Exh.

wlog yhpos: yh yl  xh xl zh zl DWx DWy  E1 xh0 yh0 x0 y0 xhpos / 0 <= yh.
  move=> Hwlog.
  case:(Rle_lt_dec 0 yh) => yhle0; first by apply:Hwlog.
  have ->: (zh + zl - (xh + xl) * (yh + yl)) / ((xh + xl) * (yh +yl))= 
   ((- zh + - zl - ( xh +  xl) * (- yh + - yl)) / (( xh + xl) * (- yh + - yl)))
    by field; lra.
  apply:(Hwlog (-yh) (-yl)  (xh) (xl) (-zh) (-zl))=>//; try lra; last by rewrite DWTimesDW1_Asym_r E1.
  have [[Fyh Fyl] Eyh] := DWy.
  split; [split|]; try apply:generic_format_opp=>//.
  have ->:- yh + - yl = -(yh +  yl) by ring.
  by rewrite rnd_p_sym  {1}Eyh.
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
  by rewrite DWTimesDW1Sx E1.
wlog [yh1 yh2]: yh yl  zh zl  DWy yh0 y0 yhpos E1/ 1 <= yh <= 2-2*u.
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
  by rewrite DWTimesDW1Sy E1.
have xh2': xh < 2 by lra.
have yh2': yh < 2 by lra.
have h0 : 1 <= xh * yh < 4 by nra.

have ylu:Rabs yl <= u by apply: (double_lpart_u DWy); lra.
have xlu:Rabs xl <= u by apply: (double_lpart_u DWx); lra.
have [[Fxh Fxl] Exh] := DWx.
have [[Fyh Fyl] Eyh] := DWy.
move:E1; rewrite /DWTimesDW1.
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
case:(@ex_mul p xh 0)=>//.
  change (1 <= Rabs xh); rewrite Rabs_pos_eq; lra.
  move=> mxh; rewrite Rmult_1_r -/u => xhE.
case:(@ex_mul p yh 0)=>//.
  change (1 <= Rabs yh); rewrite Rabs_pos_eq; lra.
  move=> myh; rewrite Rmult_1_r -/u => yhE.
have xhyhm4u2: xh*yh = IZR (mxh * myh) * (4* u^2).
  rewrite xhE yhE mult_IZR; ring.
case: (@ex_mul p ch 0)=>//.
    rewrite /ch; rewrite  -rnd_p_abs.
    have ->: pow 0 = rnd_p 1.
    rewrite round_generic //.
      change (format (pow 0)); apply:format_bpow =>//.
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

set tl1 := rnd_p (xh * yl).
pose e1 := tl1 - xh*yl.
have tl1E: tl1 = xh*yl + e1 by rewrite  /e1 /tl1; ring.
have xhylub: Rabs (xh*yl) <= 2*u - 2*(u*u).
  rewrite Rabs_mult Rabs_pos_eq; last lra.
have->: 2 * u - 2 * (u * u) = (2 - 2 * u) * u by ring.
apply:Rmult_le_compat; try apply: Rabs_pos; lra.
have tl1ub: Rabs tl1 <= 2*u -2* (u *u).
  rewrite /tl1   -rnd_p_abs.
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
  rewrite /tl2   -rnd_p_abs.
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
  by apply:(Rle_trans _ _ _ (Rabs_triang _ _)); lra.
have cl2ub: Rabs cl2 <= 4*u - 4*(u * u).
  rewrite /cl2.
  suff->:  4*u - 4*(u * u) = rnd_p  (4*u - 4*(u * u)) 
    by rewrite -rnd_p_abs; apply:round_le.
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
have e3ub: Rabs e3 <= 2 * (u * u).
  rewrite /e3.
  have->: 2 * (u * u )= /2 * u * (pow (2 -p)) by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  rewrite bpow_plus  /= IZR_Zpower_pos /= -/u; lra.
set cl3 := rnd_p (cl1 + cl2).
pose e4 := cl3 - (cl1 + cl2).
have cl1cl2: Rabs (cl1 + cl2) <= 6*u - 4*(u * u).
  apply:(Rle_trans _ _ _ (Rabs_triang _ _)); lra.
have cl3ub: Rabs cl3 <= 6*u.
  rewrite /cl3 -rnd_p_abs.
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
have e4ub: Rabs e4 <= 4 * (u * u).
 rewrite /e4.
  have->: 4 * (u * u )= /2 * u * (pow (3 -p)) by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  rewrite bpow_plus  /= IZR_Zpower_pos /= -/u. 
  by apply:(Rle_trans _ (6 * u)); lra.
have hf2Sc: Rabs cl3 <= Rabs ch.
  apply:(Rle_trans _ (6 * u))=>//.
  apply: (Rle_trans _ 1).
   apply: (Rle_trans _ (8 * u)); try lra.
  suff : pow (3 - p) <= pow 0 .
   rewrite bpow_plus  /= IZR_Zpower_pos /= -/u; lra.
   apply:bpow_le; lia.
  have ->:  1 = pow 0 by [].
  rewrite -(round_generic two fexp (Znearest choice) (pow 0)).
  rewrite /ch  -rnd_p_abs; apply/round_le; rewrite /= Rabs_pos_eq; nra.
  by apply:generic_format_bpow; rewrite /fexp; lia.
rewrite (surjective_pairing (Fast2Sum  _ _)).
rewrite F2Sum_correct_abs=>//; try apply: generic_format_round; last by rewrite (round_generic _ _ _ cl1)//.
rewrite (round_generic _ _ _ cl1)//.
case=> zhe  zle.
pose eta := -(xl* yl) + e1 + e2 + e3 + e4.
have xlylub: Rabs (xl * yl) <= u*u.
  rewrite Rabs_mult; clear -ylu xlu upos.
  move : (Rabs_pos xl) (Rabs_pos yl); nra.
have rabs_eta : Rabs eta <=  Rabs(xl * yl)  + Rabs e1 + Rabs e2 + Rabs e3 + Rabs e4.
  rewrite /eta.
  apply:(Rle_trans _ ( (Rabs (xl*yl))+ Rabs e1 + Rabs e2 + Rabs e3 + Rabs e4)); last lra.

   repeat (apply: (Rle_trans _ _ _ (Rabs_triang _ _)); 
     first apply : Rplus_le_compat_r); try lra.
  rewrite Rabs_Ropp ; lra.
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
  ring_simplify ((xh + xl) * (yh + yl) + eta - (xh + xl) * (yh + yl)).

(* 2.6.1 *)
case:(Rle_lt_dec 2 (xh * yh))=>xhyh2.
  apply:(Rle_lt_trans _ ((9 * (u * u)) / (2 * (1 - u) * (1 - u)))); last first.
    apply:(Rmult_lt_reg_r (2 * (1 - u) * (1 - u))).
    clear -upos ult1 ; nra.
    rewrite /Rdiv Rmult_assoc Rinv_l; last by clear -ult1; nra.
    have ->: (2 * (1 - u) * (1 - u)) = 2 - 4 * u + 2* (u*u) by ring.
    suff: 0 < u*u -20* u^3 + 10* (u*u) * (u * u)  by lra.
    (* suff: 0 <= u*u -20* u^3 by clear -u2pos; nra. *)
    suff : u <= /32 by  clear -u2pos; nra.
    change (pow (-p) <= pow (- 5)); apply/bpow_le;lia.
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
    clear - yh1  ylu  upos ult1.
    move/Rabs_le_inv: ylu;nra.
  move =>  hy hx.    
  have hypos : 0 < (yh + yl).
    clear -  yh1   ult1 ylu.
    move/Rabs_le_inv: ylu; lra.
  rewrite Rabs_pos_eq.
    suff h: 0 < (2 * (1 - u) * (1 - u)) <= ((xh + xl) * (yh + yl)) by apply:Rinv_le; lra.
    split;  first lra.
    apply:(Rle_trans _ (xh * (1 -u) * (yh * (1 -u)))).
      clear - xpos hypos upos ult1 xhyh2 xh1   yh1.
      have -> : xh * (1 - u) * (yh * (1 - u)) = (xh * yh) * (1-u) *(1 -u) by ring.
      apply:Rmult_le_compat_r;  nra.
    apply:Rmult_le_compat; nra.
  by clear - xpos hypos; apply/Rlt_le/Rinv_0_lt_compat; nra.

(* xh yh <2*)
have  cl1u: Rabs cl1 <= u.
  rewrite /cl1 -Ropp_minus_distr Rabs_Ropp /ch.
  have ->: u = / 2 * u * (pow 1)  by rewrite /= IZR_Zpower_pos /=; field.
  rewrite /u; apply: error_le_half_ulp'; first lia.
  rewrite Rabs_pos_eq  /= ?IZR_Zpower_pos /= ?Rmult_1_r //;lra.
 have hsxhyh: xh + yh <= 3 -2*u by apply:l5_2F=>//; lra.
have tl1u: Rabs tl1 <= xh * u.
  rewrite /tl1  -rnd_p_abs.
  have -> : xh * u = rnd_p (xh * u).
    by rewrite /u round_bpow round_generic.
  apply:round_le; rewrite Rabs_mult Rabs_pos_eq; try lra.
  by apply:Rmult_le_compat_l; try lra.
have tl2u: Rabs tl2 <= yh * u.
  rewrite /tl2 -rnd_p_abs.
  suff -> : yh * u = rnd_p (yh * u).
    apply:round_le.
    rewrite Rabs_mult Rmult_comm Rabs_pos_eq; try lra.
    apply:Rmult_le_compat_l; try lra.
  by rewrite /u round_bpow round_generic.
have stl12u: Rabs (tl1 + tl2)  <= (3 -2*u) *u.
  apply: (Rle_trans _ _ _ (Rabs_triang _ _)).
  apply:(Rle_trans _ ((xh  + yh)* u)); try lra.
  apply :Rmult_le_compat_r; lra.
have {} cl2ub: Rabs cl2 <= 3 * u.
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
  rewrite -rnd_p_abs.
  by apply:round_le; lra.
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
(* ring_simplify (((xh + xl) * (yh + yl) + eta - (xh + xl) * (yh + yl))). *)
have xlb: 1-u <= xh + xl  by move/Rabs_le_inv: xlu; lra.
have ylb: 1-u <= yh + yl  by move/Rabs_le_inv: ylu; lra.
pose x := xh + xl; pose y := yh + yl.
have xylb : (1 -u) * (1-u) <= (x * y).
 clear - xh1 yh1 ult1 upos xlb ylb ; rewrite /x /y; nra. 
have xyiub: /(x*y) <= / ((1-u) * (1-u)).
  by apply/Rinv_le =>// ; clear - ult1 ; nra.
rewrite Rabs_mult -/x -/y.
have xypos: 0 < x*y by clear -ult1 xylb ; nra.
have xyn0: x*y <> 0 by lra. 
suff etaubxy: Rabs eta < 5 * (u * u) * (x * y).
  apply/(Rmult_lt_reg_r (x*y)) =>//.
  rewrite Rmult_assoc -{2}(Rabs_pos_eq (x*y));  last lra.
  rewrite Rabs_Rinv // Rinv_l // ?Rmult_1_r //.
 by apply/Rabs_no_R0.

(* xh =1 or yh = 1 *)
case:(xh1)=>[xhgt1| xhe1]; last first.
  have {} xhe1:  xh = 1 by [].
  have cl10: cl1 = 0 
     by rewrite /cl1 /ch xhe1 Rmult_1_l round_generic //; ring.
  have e40: e4 = 0.
    rewrite /e4  /cl3 cl10 Rplus_0_l round_generic; first ring.
    by apply:generic_format_round.
  have e10: e1=0.
    rewrite /e1 /tl1 xhe1 Rmult_1_l round_generic //; ring.
  have h: Rabs eta <= 4 * (u * u) 
   by move : rabs_eta; rewrite e40 e10 !Rabs_R0 ; lra.
  apply:(Rle_lt_trans _ (4 * (u * u))) =>//.
  apply: (Rlt_le_trans _ (5 * (u * u) * ((1 - u) * (1 - u)))); last first.
    by apply/Rmult_le_compat;  lra.
  have ->: ( (1 - u) * (1 - u)) = (1 -2*u + u*u) by ring.
  clear -upos u2pos ult1 Hp6.
  suff : u < /16  by nra.
  change (pow (-p) < pow (-4)); apply/bpow_lt; lia.
have xh1pu2: 1 + 2* u <= xh.
  have : succ radix2 fexp 1 <= xh .
    apply/succ_le_lt =>//.
    by change (format (pow 0)); apply/format_bpow.
  rewrite succ_eq_pos; try lra.
  suff->: 2*u = ulp radix2 fexp 1 by [].
  rewrite /u u_ulp1; field.
have x1pu: 1+ u <= x.
  rewrite /x ;  move/Rabs_le_inv: xlu; lra.
(* le meme pour y ; il faudrait factoriser *)
case:(yh1)=>[yhgt1| yhe1]; last first.
  have {} yhe1:  yh = 1 by [].
  have cl10: cl1 = 0 
     by rewrite /cl1 /ch yhe1 Rmult_1_r round_generic //; ring.
  have e40: e4 = 0.
    rewrite /e4  /cl3 cl10 Rplus_0_l round_generic; first ring.
    by apply:generic_format_round.
  have e20: e2=0.
    rewrite /e2 /tl2 yhe1 Rmult_1_r round_generic //; ring.
  have h: Rabs eta <= 4 * (u * u) 
   by move : rabs_eta; rewrite e40 e20 !Rabs_R0 ; lra.
  apply:(Rle_lt_trans _ (4 * (u * u))) =>//.
  apply: (Rlt_le_trans _ (5 * (u * u) * ((1 - u) * (1 - u)))); last first.
    by apply/Rmult_le_compat; lra.
  have ->: ( (1 - u) * (1 - u)) = (1 -2*u + u*u) by ring.
  clear -upos u2pos ult1 Hp6.
  suff : u < /16  by nra.
  change (pow (-p) < pow (-4)); apply/bpow_lt; lia.
have yh1pu2: 1 + 2* u <= yh. 
  have : succ radix2 fexp 1 <= yh .
    apply/succ_le_lt =>//.
    by change (format (pow 0)); apply/format_bpow.
  rewrite succ_eq_pos; try lra.
  suff->: 2*u = ulp radix2 fexp 1 by [].
  rewrite /u u_ulp1; field.
have y1pu: 1+ u <= y.
  rewrite /y ;  move/Rabs_le_inv: ylu; lra.
have xy1pu : (1+u) * (1+u) <= x*y by clear -upos ult1 x1pu y1pu; nra.
have haux : Rabs eta <= 5 * (u * u) -> Rabs eta < 5 * (u * u) * (x * y).
  move=> haux.
  apply:(Rle_lt_trans _ ( 5 * (u * u))) =>//.
  rewrite -[X in X < _] Rmult_1_r.
  by apply: Rmult_lt_compat_l; lra.
(* have b1ltb2':   5 * (u * u) * (x * y) < 55/10 * (u * u) * (x * y). *)
(*   by apply/Rmult_lt_compat_r; lra. *)



case:(Rle_lt_dec (2*u) (Rabs cl2))=> [hcl2|{} cl2ub].
(* 2u <= |cl2| *)
  case:(@ex_mul p cl2 (1-p)).
    + by rewrite bpow_plus -/u.
    + by  apply:generic_format_round.
  move=> Mcl2. 
   have ->:  (2 * pow (- p) * pow (1 - p)) = 4*(u * u).
     rewrite bpow_plus -/u; ring_simplify.
     by have ->: pow 1 = 2 by []; ring.
  move=> cl2E.
  have cl1p2E: cl1 + cl2 =  (IZR (m + Mcl2))* ( 4 * (u *u)).
    rewrite plus_IZR cl2E cl1m4u2;  ring.
  have e40: e4 = 0.
    rewrite /e4 /cl3 round_generic ; first ring.
    pose fx := Float two  (m + Mcl2)%Z  (2* (1 -p)) %Z.
    case: scl12u=>h; last first.
      apply/generic_format_abs_inv; rewrite h.
      change (format ((pow 2) * pow (-p))).
      by rewrite -bpow_plus; apply/format_bpow.
    have hf : cl1 + cl2 = F2R fx.
      rewrite cl1p2E /fx /F2R.
      set e :=( 2 * (1 - p))%Z.
      rewrite /= /e.
      have ->: (2 * (1 - p) = 2 -p -p )%Z by ring.
      by rewrite !bpow_plus /u; have ->: 4 = pow 2 by []; ring.
    apply:(@FLX_format_Rabs_Fnum p _ fx)=>//.
    move: h; 
    rewrite cl1p2E /fx /= Rabs_mult (Rabs_pos_eq (4 * (u * u))); try lra.
    move=>h.
    have {} h:  Rabs (IZR (m + Mcl2)) * u < 1.
      by clear -h upos; nra.
    move/(Rmult_lt_compat_r (pow p)):h. 
    rewrite Rmult_assoc.
    have ->: u * pow p = 1.
      by rewrite /u -bpow_plus; have->: (-p +p = 0)%Z by ring.
    by rewrite Rmult_1_r Rmult_1_l; apply; apply:bpow_gt_0.
  have abs_eta_5: Rabs eta <= 5 * (u*u).
    by move:rabs_eta; rewrite e40 Rabs_R0; lra.
  apply:(Rle_lt_trans _ ( 5 * (u * u))) =>//.
  rewrite -[X in X < _] Rmult_1_r.
  apply: Rmult_lt_compat_l; try lra.
(* cl2 < 2u *)
have tl12ub: Rabs(tl1 + tl2) <= 2*u.
  case:(Rle_lt_dec   (Rabs (tl1 + tl2)) (2*u))=>//.
  move/Rlt_le/(round_le two fexp (Znearest choice)); 
     rewrite rnd_p_abs -/cl2 round_generic; first lra.
  change (format (pow 1 * (pow (-p)))).
  by rewrite -bpow_plus; apply/format_bpow; lia.
have xpos: 0 < xh + xl by  move/Rabs_le_inv: xlu; lra.
have ypos: 0 < yh + yl by move/Rabs_le_inv: ylu; lra.
have {} e3ub: Rabs e3 <= (u * u).
  rewrite /e3.
  have->:(u * u )= /2 * u * (pow (1 -p)) by rewrite /u 
    bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  case:(Rle_lt_dec  (Rabs (tl1 + tl2))  (2 * u)).
    by rewrite bpow_plus.
  move/Rlt_le/(round_le two fexp (Znearest choice)).
  move: cl2ub; rewrite /cl2 -rnd_p_abs (round_generic _ _ _ (2 *u)); first lra.
  change (format ((pow 1)* (pow (-p)))).
  by  rewrite -bpow_plus; apply/format_bpow; lia.

case: (Rlt_le_dec (Rabs tl1) (u/2))=> htl1.
  have ylub: Rabs yl < /2 * u.
    case:(Rlt_le_dec (Rabs yl) (/2*u)) =>//  h.
    have :  / 2 * u  *1 <= Rabs yl * xh.
      apply: Rmult_le_compat; try lra.
    rewrite Rmult_1_r -(Rabs_pos_eq xh); last lra.
    rewrite -Rabs_mult.
    move/(round_le two fexp (Znearest choice)); rewrite rnd_p_abs 
      (Rmult_comm  yl)   -/tl1 round_generic; try lra.
    change (format ((pow (-1)) * ( pow (-p)))).
    by  rewrite -bpow_plus; apply/format_bpow; lia.
  have {} e1ub: Rabs e1 <= /4 * (u * u).
    rewrite /e1.
    have ->:  / 4 * (u * u) =  /2 * u * (pow (-1  -p)).
      by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
    apply: error_le_half_ulp'=>//.
    rewrite bpow_plus  /= IZR_Zpower_pos /= -/u Rmult_1_r.
    case:(Rle_lt_dec   (Rabs (xh * yl)) (/2 *u))=>//.
    move/Rlt_le/(round_le two fexp (Znearest choice)).
    rewrite rnd_p_abs -/tl1 round_generic; first lra.
    by change (format ((pow (-1)) * (pow (-p)))); 
       rewrite -bpow_plus; apply/format_bpow.
  have {} xlylub: Rabs (xl *yl) < /2 * (u * u).
    rewrite Rabs_mult.
    by clear - ylub xlu; move :(Rabs_pos xl) (Rabs_pos yl);  nra.
  have h1 : Rabs eta <= 475/100 * (u * u) by lra.
  lra.
case: (Rlt_le_dec (Rabs tl2) (u/2))=> htl2.
  have xlub: Rabs xl < /2 * u.
    case:(Rlt_le_dec (Rabs xl) (/2*u)) =>//  h.
    have :  / 2 * u  *1 <= Rabs xl * yh.
      apply: Rmult_le_compat; lra.
    rewrite Rmult_1_r -(Rabs_pos_eq yh); last lra.
    rewrite -Rabs_mult.
    move/(round_le two fexp (Znearest choice)); rewrite rnd_p_abs
         -/tl2 round_generic; try lra.
    change (format ((pow (-1)) * ( pow (-p)))).
    by rewrite -bpow_plus; apply/format_bpow; lia.
  have {} e2ub: Rabs e2 <= /4 * (u * u).
    rewrite /e2.
    have ->:  / 4 * (u * u) =  /2 * u * (pow (-1  -p)).
      rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
    apply: error_le_half_ulp'=>//.
    rewrite bpow_plus  /= IZR_Zpower_pos /= -/u Rmult_1_r.
    case:(Rle_lt_dec   (Rabs (xl * yh)) (/2 *u))=>//.
    move/Rlt_le/(round_le two fexp (Znearest choice)).
    rewrite rnd_p_abs -/tl2 round_generic; first lra.
    by change (format ((pow (-1)) * (pow (-p)))); 
       rewrite -bpow_plus; apply/format_bpow.
  have {} xlylub: Rabs (xl *yl) < /2 * (u * u).
    rewrite Rabs_mult.
    by clear - xlub ylu; move :(Rabs_pos xl) (Rabs_pos yl);  nra.
  have h1 : Rabs eta <= 475/100 * (u * u) by lra.
  lra.
case:(@ex_mul  p tl1 (-1 -p)); try  apply/generic_format_round.
  suff->:   pow (-1 - p) =  u / 2 by [].
  by rewrite bpow_plus  /u; rewrite Rmult_comm.
move=> Mtl1.
rewrite bpow_plus -/u.
have ->: (2 * u * (pow (-1) * u)) = u*u.
  by have -> : pow (-1) = /2 by [];field.
move=> tl1Mu2.
case:(@ex_mul  p tl2 (-1 -p)); try  apply/generic_format_round.
  suff->:   pow (-1 - p) =  u / 2 by [].
  by rewrite bpow_plus  /u; rewrite Rmult_comm.
move=> Mtl2.
rewrite bpow_plus -/u.
have ->: (2 * u * (pow (-1) * u)) = u*u.
  have -> : pow (-1) = /2 by [];field.
move=> tl2Mu2.
have tl12Mu2: tl1 + tl2 = IZR (Mtl1 + Mtl2) * (u *u).
 by rewrite tl1Mu2 tl2Mu2 plus_IZR; ring.
have hFtl12: (Rabs (tl1 + tl2) < u -> format ( tl1 + tl2)).
  rewrite tl12Mu2 !Rabs_mult !(Rabs_pos_eq u); try lra.
  rewrite -Rmult_assoc -[X in _ < X]Rmult_1_l.
  move/(Rmult_lt_reg_r _ _ _ upos).
  move/(Rmult_lt_compat_r (pow p) _ _ (bpow_gt_0 two p)).
  rewrite /u Rmult_1_l Rmult_assoc -bpow_plus.
  have ->:  pow (- p + p) = 1 by ring_simplify (-p+p)%Z.
  rewrite Rmult_1_r =>h.
  rewrite -bpow_plus.
  pose f := (Float two  (Mtl1 + Mtl2)  (- p + - p)).
  apply/(@FLX_format_Rabs_Fnum p _  f).
    by rewrite /f /F2R.
  by rewrite /f .
case: tl12ub =>  tl12ub;  last first.
  have Ftl12 : format (tl1 + tl2).
    move:  tl12ub; rewrite -(Rabs_pos_eq (2* u)); try lra.
    case/Rabs_eq_Rabs =>->; try apply/generic_format_opp; 
        have ->: 2 * u = (pow 1 ) * (pow (-p)) by []; rewrite -bpow_plus; 
        apply/format_bpow; lia.
  have e30: e3 = 0 by rewrite /e3 /cl2 round_generic //; ring.
  by move:rabs_eta; rewrite e30 Rabs_R0; lra.
have hFtl12': Zeven (Mtl1 + Mtl2) -> format (tl1+tl2).
  move=> heven.
  move/Zeven_div2 :(heven).
  rewrite  tl12Mu2 => ->.
  rewrite mult_IZR.
  pose f := (Float two  ( Z.div2 (Mtl1 + Mtl2) )  (1 - p + - p)).
  apply/(@FLX_format_Rabs_Fnum p _  f).
    rewrite  -mult_IZR -Zeven_div2 /f /F2R //.
    set M:= Z.div2 (Mtl1 + Mtl2); set e := (1 - p + - p )%Z.
    rewrite /= /M /e !bpow_plus -!Rmult_assoc. 
    have -> : pow 1 = 2 by [].
    by rewrite -mult_IZR Zmult_comm -Zeven_div2.
  rewrite /f /F2R /=.
  apply/(Rmult_lt_reg_r 2); first lra.
  rewrite -(Rabs_pos_eq 2); last lra.
  rewrite -Rabs_mult -mult_IZR Zmult_comm -Zeven_div2 //.
  move: tl12ub ; rewrite  tl12Mu2 !Rabs_mult (Rabs_pos_eq u); try lra.
  rewrite -Rmult_assoc; move/(Rmult_lt_reg_r _ _ _ upos).
  move/(Rmult_lt_compat_r (pow p) _ _ (bpow_gt_0 two p)).
  rewrite Rmult_assoc /u -bpow_plus ; ring_simplify (-p + p)%Z.
  rewrite Rmult_1_r (Rabs_pos_eq 2); lra.
case:(Rlt_le_dec (Rabs (tl1 +tl2)) u)=>//.
  move/ hFtl12=> Ftl12.
  have e30: e3 = 0 by rewrite /e3 /cl2 round_generic //; ring.
  by move:rabs_eta; rewrite e30 Rabs_R0; lra.
move=> tl12lb.
have hmant :  pow p <= Rabs (IZR (Mtl1 + Mtl2)) < pow (1 + p).
  move: tl12lb  tl12ub.
    rewrite  tl12Mu2.
    rewrite -/u; split=>//.
    apply/(Rmult_le_reg_r (u * u)) =>//. 
    suff ->:   pow p * (u * u) = u .
      rewrite -(Rabs_pos_eq (u * u)); try lra.
      by rewrite -Rabs_mult.
    by rewrite /u -!bpow_plus; ring_simplify(p +( -p + -p))%Z.
  apply/(Rmult_lt_reg_r (u*u)); first lra.
  suff->: pow (1 + p) * (u * u) = 2*u.

    by move: tl12ub0 ;  rewrite Rabs_mult (Rabs_pos_eq (u*u)); lra.
  rewrite /u -!bpow_plus. ring_simplify  (1 + p + (- p + - p))%Z.
  by rewrite bpow_plus Rmult_comm.
case:(Zeven_odd_dec   (Mtl1 + Mtl2)).
  move/ hFtl12'=> Ftl12.
  have e30: e3 = 0 by rewrite /e3 /cl2 round_generic //; ring.
  move:rabs_eta; rewrite e30 Rabs_R0; lra.
move/Zodd_bool_iff  => Hodd.
case: (Zeven_ex (Mtl1 +Mtl2))=>M  Me.
have {Me} ME : (Mtl1 + Mtl2)%Z = (2 * M + 1)%Z.
  by rewrite Me; rewrite Zeven.Zeven_odd_bool Hodd.
have hub: IZR (2*M)< IZR (2 * M + 1)< IZR (2*M+2) by split; apply/IZR_lt; lia.
have nFs: ~ format (IZR (2 * M + 1)).
  apply: (generic_format_discrete _ _ _ M).
  rewrite /F2R /cexp -ME (mag_unique _ _ (1+p)).
    set e := fexp (1+p).
    rewrite /= /e /fexp.
    ring_simplify (1 + p -p)%Z.
    have->: pow 1 = 2 by [].
    rewrite -!mult_IZR ME !(Zmult_comm _ 2).
    have->: ((2 * (M + 1)) =  (2 * M + 2))%Z by ring.
    by [].
  by ring_simplify(1 + p - 1)%Z.
have cexpf :  (ce (IZR (2 * M + 1)) = 1)%Z.
  rewrite /cexp /fexp (mag_unique _ _  (1 +p)); first ring.
  have->:  (1 + p - 1 = p)%Z by ring.
  by rewrite -ME.
have rDN: round two  fexp Zfloor (IZR (2 * M + 1))  =  IZR (2 * M).
  rewrite /round /scaled_mantissa .
  rewrite cexpf (Zfloor_imp M) /F2R.
    set f := Float _ _ _.
    by rewrite Rmult_comm mult_IZR ; congr Rmult.
  move: hub.
  have -> : (2 * M + 2 = 2 * (M + 1))%Z by ring.
  rewrite !mult_IZR.
  have ->: pow(-1) = /2 by [].
  lra.
have rUP :  round two  fexp Zceil (IZR (2 * M + 1))  =  IZR (2 * (M+ 1)).
  rewrite round_UP_DN_ulp // rDN ulp_neq_0 ?cexpf.
    by rewrite Zmult_plus_distr_r  Zmult_1_r plus_IZR.
  by apply/not_0_IZR; lia.
have e3E: Rabs e3 = u*u.
  rewrite /e3 /cl2  tl12Mu2 ME.
   rewrite /u -bpow_plus round_bpow!bpow_plus -/u.
   case:(round_DN_or_UP two fexp (Znearest choice) (IZR (2 * M + 1)));
      rewrite ?rDN ?rUP => ->; rewrite plus_IZR.
    ring_simplify (IZR (2 * M) * (u * u) - (IZR (2 * M) + 1) * (u * u)).
    by rewrite Rabs_Ropp Rabs_pos_eq; lra.
  rewrite !mult_IZR !plus_IZR.
  ring_simplify(2 * (IZR M + 1) * (u * u) - (2 * IZR M + 1) * (u * u)).
  by rewrite Rabs_pos_eq; lra.
apply:(Rle_lt_trans _ (5 * (u * u))); last first.
rewrite -[X in X < _]Rmult_1_r; apply/Rmult_lt_compat_l; lra.

have e40: e4= 0.
  rewrite /e4  /cl3 round_generic ; first ring.
  have : cl2 = rnd_p (tl1 +tl2 ) by [].
  rewrite /round/F2R /=.
  have cetl12: ce (tl1 + tl2 ) = (1 - p - p)%Z.
    rewrite tl12Mu2 ME.
    have -> : u * u = pow ( -p + - p) by rewrite /u bpow_plus.
    rewrite cexp_bpow ?cexpf; first ring.
    apply/not_0_IZR; lia.
  have M_even: Zeven (Znearest choice (mant (tl1 + tl2))).
    apply/round_mant_even=>//.
rewrite /middle_point; split =>//.
move=> h.
apply/nFs.

      have -> :IZR (2 * M + 1) =  (IZR (2 * M + 1)) * (u * u)* (pow (p + p)).
        rewrite Rmult_assoc  /u -!bpow_plus.
        by ring_simplify (- p + - p + (p + p))%Z; rewrite Rmult_1_r.
      rewrite -ME - tl12Mu2; apply/formatS =>//; lia.
    rewrite  tl12Mu2 ME.
    have -> : u * u = pow ( -p + - p) by rewrite /u bpow_plus.
    rewrite !round_bpowG rDN rUP.
    rewrite -!Rmult_minus_distr_r.
    congr Rmult.
    rewrite !(plus_IZR, mult_IZR); ring.
  case/Zeven.Zeven_ex: M_even => N NE.
  rewrite NE mult_IZR (Rmult_comm 2) Rmult_assoc.
  have -> : 2 = pow 1 by [].
  rewrite -bpow_plus  cetl12.
  have ->:  pow (1 + (1 - p - p)) = 4 * ( u *u).
    rewrite !bpow_plus /u; have -> : pow 1 = 2 by []; ring.
  move=> cl2M4u2.
  have cl12E : cl1 + cl2 = IZR (m + N) * (4 * (u * u)).
    rewrite cl1m4u2 cl2M4u2 plus_IZR; ring.
  move:  scl12u.
  case.
    rewrite cl12E Rabs_mult (Rabs_pos_eq (4 * (u * u))); try lra.
    move=>h.
    pose f := (Float two  ( m + N)  (2 - p + - p)).
    apply/(@FLX_format_Rabs_Fnum p _  f).
      set e := (2 -p + -p)%Z; rewrite /=; congr Rmult.
      by rewrite /e !bpow_plus /u  ; have->: pow 2 = 4 by []; ring.
    rewrite /f /F2R /=.
    apply/(Rmult_lt_reg_r (4 * (u * u))).
      by lra.
    suff ->: pow p *(4 * (u * u)) = 4*u by lra.
    rewrite /u ; have->: 4 = pow 2 by [].
    rewrite -!bpow_plus; congr bpow; ring.
  rewrite -(Rabs_pos_eq (4 * u)); try lra.
  case/Rabs_eq_Rabs=>->; try apply/generic_format_opp;
      (have ->: 4 * u = pow (2 -p) by rewrite /u bpow_plus);
      apply/format_bpow; lia.

move:rabs_eta; rewrite e40 Rabs_R0; lra.
Qed.



(* Theorem 2.7 *)
Lemma DWTimesDW1_correct_w xh xl yh yl  
                         (DWx:double_word xh xl) (DWy:double_word yh yl):
  let (zh, zl) := DWTimesDW1 xh xl yh yl in
  let xy := ((xh + xl) * (yh + yl))%R in
             (Rabs ((zh + zl - xy) / xy) < 55/10 * (u * u)).
Proof.
have rnd_p_sym := rnd_p_sym.
have upos:= upos.

have ult1 : u < 1 by rewrite /u ; apply:bpow_lt_1; lia.
have u2pos: 0 < u * u by apply:Rmult_lt_0_compat.
have b1ltb2:  5 * (u * u)  < 55 / 10 * (u * u) by lra.

have [[Fxh Fxl] Exh] := DWx.
have [[Fyh Fyl] Eyh] := DWy.
case E1: DWTimesDW1 => [zh zl].
have Hp1:= Hp1.
case:(Req_dec yh 0)=> yh0.
  have yl0: yl = 0.
    by move:Eyh; rewrite  yh0 Rplus_0_l round_generic.
  move:E1; rewrite /DWTimesDW1 yh0 yl0 Rmult_0_r TwoProdE round_0 Fast2MultC Rmult_0_r Fast2Mult0f. 
  rewrite /Fast2Sum /F2SumFLX.Fast2Sum !(Rplus_0_r, Rminus_0_r, Rplus_0_l, round_0).
  case=> <- <-; rewrite Rplus_0_r Rmult_0_r Rminus_0_l /Rdiv Ropp_0 Rmult_0_l Rabs_R0.
  clear -upos; nra.

case:(Req_dec xh 0)=> xh0.
  have xl0: xl = 0.
    by move:Exh; rewrite  xh0 Rplus_0_l round_generic.
  move:E1; rewrite /DWTimesDW1 xh0 xl0 Rmult_0_l TwoProdE  round_0 Fast2Mult0f.
  rewrite /Fast2Sum /F2SumFLX.Fast2Sum !(Rplus_0_r, Rminus_0_r, Rplus_0_l, round_0, Rmult_0_l).
  case=> <- <-; rewrite Rplus_0_r  /Rdiv   Rmult_0_l Rabs_R0.
  by clear -upos; nra.
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
  apply:(Hwlog yh yl  (-xh) (-xl) (-zh) (-zl))=>//; try lra; last  by rewrite DWTimesDW1_Asym_l E1.
  have [[Fxh Fxl] Exh] := DWx.
  split; [split|]; try apply:generic_format_opp=>//.
  have ->:- xh + - xl = -(xh +  xl) by ring.
  by rewrite rnd_p_sym {1}Exh.

wlog yhpos: yh yl  xh xl zh zl DWx DWy  E1 xh0 yh0 x0 y0 xhpos / 0 <= yh.
  move=> Hwlog.
  case:(Rle_lt_dec 0 yh) => yhle0; first by apply:Hwlog.
  have ->: (zh + zl - (xh + xl) * (yh + yl)) / ((xh + xl) * (yh +yl))= 
   ((- zh + - zl - ( xh +  xl) * (- yh + - yl)) / (( xh + xl) * (- yh + - yl)))
    by field; lra.
  apply:(Hwlog (-yh) (-yl)  (xh) (xl) (-zh) (-zl))=>//; try lra; last by rewrite DWTimesDW1_Asym_r E1.
  have [[Fyh Fyl] Eyh] := DWy.
  split; [split|]; try apply:generic_format_opp=>//.
  have ->:- yh + - yl = -(yh +  yl) by ring.
  by rewrite rnd_p_sym  {1}Eyh.
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
  by rewrite DWTimesDW1Sx E1.
wlog [yh1 yh2]: yh yl  zh zl  DWy yh0 y0 yhpos E1/ 1 <= yh <= 2-2*u.
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
  by rewrite DWTimesDW1Sy E1.
have xh2': xh < 2 by lra.
have yh2': yh < 2 by lra.
have h0 : 1 <= xh * yh < 4 by nra.

have ylu:Rabs yl <= u by apply: (double_lpart_u DWy); lra.
have xlu:Rabs xl <= u by apply: (double_lpart_u DWx); lra.
have [[Fxh Fxl] Exh] := DWx.
have [[Fyh Fyl] Eyh] := DWy.
move:E1; rewrite /DWTimesDW1.
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
case:(@ex_mul p xh 0)=>//.
  change (1 <= Rabs xh); rewrite Rabs_pos_eq; lra.
  move=> mxh; rewrite Rmult_1_r -/u => xhE.
case:(@ex_mul p yh 0)=>//.
  change (1 <= Rabs yh); rewrite Rabs_pos_eq; lra.
  move=> myh; rewrite Rmult_1_r -/u => yhE.
have xhyhm4u2: xh*yh = IZR (mxh * myh) * (4* u^2).
  rewrite xhE yhE mult_IZR; ring.
case: (@ex_mul p ch 0)=>//.
    rewrite /ch; rewrite  -rnd_p_abs.
    have ->: pow 0 = rnd_p 1.
    rewrite round_generic //.
      change (format (pow 0)); apply:format_bpow =>//.
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

set tl1 := rnd_p (xh * yl).
pose e1 := tl1 - xh*yl.
have tl1E: tl1 = xh*yl + e1 by rewrite  /e1 /tl1; ring.
have xhylub: Rabs (xh*yl) <= 2*u - 2*(u*u).
  rewrite Rabs_mult Rabs_pos_eq; last lra.
have->: 2 * u - 2 * (u * u) = (2 - 2 * u) * u by ring.
apply:Rmult_le_compat; try apply: Rabs_pos; lra.
have tl1ub: Rabs tl1 <= 2*u -2* (u *u).
  rewrite /tl1   -rnd_p_abs.
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
  rewrite /tl2   -rnd_p_abs.
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
  by apply:(Rle_trans _ _ _ (Rabs_triang _ _)); lra.
have cl2ub: Rabs cl2 <= 4*u - 4*(u * u).
  rewrite /cl2.
  suff->:  4*u - 4*(u * u) = rnd_p  (4*u - 4*(u * u)) 
    by rewrite -rnd_p_abs; apply:round_le.
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
have e3ub: Rabs e3 <= 2 * (u * u).
  rewrite /e3.
  have->: 2 * (u * u )= /2 * u * (pow (2 -p)) by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  rewrite bpow_plus  /= IZR_Zpower_pos /= -/u; lra.
set cl3 := rnd_p (cl1 + cl2).
pose e4 := cl3 - (cl1 + cl2).
have cl1cl2: Rabs (cl1 + cl2) <= 6*u - 4*(u * u).
  apply:(Rle_trans _ _ _ (Rabs_triang _ _)); lra.
have cl3ub: Rabs cl3 <= 6*u.
  rewrite /cl3 -rnd_p_abs.
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
have e4ub: Rabs e4 <= 4 * (u * u).
 rewrite /e4.
  have->: 4 * (u * u )= /2 * u * (pow (3 -p)) by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  rewrite bpow_plus  /= IZR_Zpower_pos /= -/u. 
  by apply:(Rle_trans _ (6 * u)); lra.
have hf2Sc: Rabs cl3 <= Rabs ch.
  apply:(Rle_trans _ (6 * u))=>//.
  apply: (Rle_trans _ 1).
   apply: (Rle_trans _ (8 * u)); try lra.
  suff : pow (3 - p) <= pow 0 .
   rewrite bpow_plus  /= IZR_Zpower_pos /= -/u; lra.
   apply:bpow_le; lia.
  have ->:  1 = pow 0 by [].
  rewrite -(round_generic two fexp (Znearest choice) (pow 0)).
  rewrite /ch  -rnd_p_abs; apply/round_le; rewrite /= Rabs_pos_eq; nra.
  by apply:generic_format_bpow; rewrite /fexp; lia.
rewrite (surjective_pairing (Fast2Sum  _ _)).
rewrite F2Sum_correct_abs=>//; try apply: generic_format_round; last by rewrite (round_generic _ _ _ cl1)//.
rewrite (round_generic _ _ _ cl1)//.
case=> zhe  zle.
pose eta := -(xl* yl) + e1 + e2 + e3 + e4.
have xlylub: Rabs (xl * yl) <= u*u.
  rewrite Rabs_mult; clear -ylu xlu upos.
  move : (Rabs_pos xl) (Rabs_pos yl); nra.
have rabs_eta : Rabs eta <=  Rabs(xl * yl)  + Rabs e1 + Rabs e2 + Rabs e3 + Rabs e4.
  rewrite /eta.
  apply:(Rle_trans _ ( (Rabs (xl*yl))+ Rabs e1 + Rabs e2 + Rabs e3 + Rabs e4)); last lra.

   repeat (apply: (Rle_trans _ _ _ (Rabs_triang _ _)); 
     first apply : Rplus_le_compat_r); try lra.
  rewrite Rabs_Ropp ; lra.
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
  ring_simplify ((xh + xl) * (yh + yl) + eta - (xh + xl) * (yh + yl)).

(* 2.6.1 *)
case:(Rle_lt_dec 2 (xh * yh))=>xhyh2.
  apply:(Rle_lt_trans _ ((9 * (u * u)) / (2 * (1 - u) * (1 - u)))); last first.
    apply:(Rmult_lt_reg_r (2 * (1 - u) * (1 - u))).
    clear -upos ult1 ; nra.
    rewrite /Rdiv Rmult_assoc Rinv_l; last by clear -ult1; nra.
    have ->: (2 * (1 - u) * (1 - u)) = 2 - 4 * u + 2* (u*u) by ring.
    suff: 0 < u*u -20* u^3 + 10* (u*u) * (u * u)  by lra.
    (* suff: 0 <= u*u -20* u^3 by clear -u2pos; nra. *)
    suff : u <= /32 by  clear -u2pos; nra.
    change (pow (-p) <= pow (- 5)); apply/bpow_le;lia.
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
    clear - yh1  ylu  upos ult1.
    move/Rabs_le_inv: ylu;nra.
  move =>  hy hx.    
  have hypos : 0 < (yh + yl).
    clear -  yh1   ult1 ylu.
    move/Rabs_le_inv: ylu; lra.
  rewrite Rabs_pos_eq.
    suff h: 0 < (2 * (1 - u) * (1 - u)) <= ((xh + xl) * (yh + yl)) by apply:Rinv_le; lra.
    split;  first lra.
    apply:(Rle_trans _ (xh * (1 -u) * (yh * (1 -u)))).
      clear - xpos hypos upos ult1 xhyh2 xh1   yh1.
      have -> : xh * (1 - u) * (yh * (1 - u)) = (xh * yh) * (1-u) *(1 -u) by ring.
      apply:Rmult_le_compat_r;  nra.
    apply:Rmult_le_compat; nra.
  by clear - xpos hypos; apply/Rlt_le/Rinv_0_lt_compat; nra.

(* xh yh <2*)
have  cl1u: Rabs cl1 <= u.
  rewrite /cl1 -Ropp_minus_distr Rabs_Ropp /ch.
  have ->: u = / 2 * u * (pow 1)  by rewrite /= IZR_Zpower_pos /=; field.
  rewrite /u; apply: error_le_half_ulp'; first lia.
  rewrite Rabs_pos_eq  /= ?IZR_Zpower_pos /= ?Rmult_1_r //;lra.
 have hsxhyh: xh + yh <= 3 -2*u by apply:l5_2F=>//; lra.
have tl1u: Rabs tl1 <= xh * u.
  rewrite /tl1  -rnd_p_abs.
  have -> : xh * u = rnd_p (xh * u).
    by rewrite /u round_bpow round_generic.
  apply:round_le; rewrite Rabs_mult Rabs_pos_eq; try lra.
  by apply:Rmult_le_compat_l; try lra.
have tl2u: Rabs tl2 <= yh * u.
  rewrite /tl2 -rnd_p_abs.
  suff -> : yh * u = rnd_p (yh * u).
    apply:round_le.
    rewrite Rabs_mult Rmult_comm Rabs_pos_eq; try lra.
    apply:Rmult_le_compat_l; try lra.
  by rewrite /u round_bpow round_generic.
have stl12u: Rabs (tl1 + tl2)  <= (3 -2*u) *u.
  apply: (Rle_trans _ _ _ (Rabs_triang _ _)).
  apply:(Rle_trans _ ((xh  + yh)* u)); try lra.
  apply :Rmult_le_compat_r; lra.
have {} cl2ub: Rabs cl2 <= 3 * u.
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
  rewrite -rnd_p_abs.
  by apply:round_le; lra.
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
(* ring_simplify (((xh + xl) * (yh + yl) + eta - (xh + xl) * (yh + yl))). *)
have xlb: 1-u <= xh + xl  by move/Rabs_le_inv: xlu; lra.
have ylb: 1-u <= yh + yl  by move/Rabs_le_inv: ylu; lra.
pose x := xh + xl; pose y := yh + yl.
have xylb : (1 -u) * (1-u) <= (x * y).
 clear - xh1 yh1 ult1 upos xlb ylb ; rewrite /x /y; nra. 
have xyiub: /(x*y) <= / ((1-u) * (1-u)).
  by apply/Rinv_le =>// ; clear - ult1 ; nra.
rewrite Rabs_mult -/x -/y.
have xypos: 0 < x*y by clear -ult1 xylb ; nra.
have xyn0: x*y <> 0 by lra. 
suff etaubxy: Rabs eta < 55/10 * (u * u) * (x * y).
  apply/(Rmult_lt_reg_r (x*y)) =>//.
  rewrite Rmult_assoc -{2}(Rabs_pos_eq (x*y));  last lra.
  rewrite Rabs_Rinv // Rinv_l // ?Rmult_1_r //.
 by apply/Rabs_no_R0.

(* xh =1 or yh = 1 *)
case:(xh1)=>[xhgt1| xhe1]; last first.
  have {} xhe1:  xh = 1 by [].
  have cl10: cl1 = 0 
     by rewrite /cl1 /ch xhe1 Rmult_1_l round_generic //; ring.
  have e40: e4 = 0.
    rewrite /e4  /cl3 cl10 Rplus_0_l round_generic; first ring.
    by apply:generic_format_round.
  have e10: e1=0.
    rewrite /e1 /tl1 xhe1 Rmult_1_l round_generic //; ring.
  have h: Rabs eta <= 4 * (u * u) 
   by move : rabs_eta; rewrite e40 e10 !Rabs_R0 ; lra.
  apply:(Rle_lt_trans _ (4 * (u * u))) =>//.
  apply: (Rlt_le_trans _ (5 * (u * u) * ((1 - u) * (1 - u)))); last first.
    by apply/Rmult_le_compat;  lra.
  have ->: ( (1 - u) * (1 - u)) = (1 -2*u + u*u) by ring.
  clear -upos u2pos ult1 Hp6.
  suff : u < /16  by nra.
  change (pow (-p) < pow (-4)); apply/bpow_lt; lia.
have xh1pu2: 1 + 2* u <= xh.
  have : succ radix2 fexp 1 <= xh .
    apply/succ_le_lt =>//.
    by change (format (pow 0)); apply/format_bpow.
  rewrite succ_eq_pos; try lra.
  suff->: 2*u = ulp radix2 fexp 1 by [].
  rewrite /u u_ulp1; field.
have x1pu: 1+ u <= x.
  rewrite /x ;  move/Rabs_le_inv: xlu; lra.
(* le meme pour y ; il faudrait factoriser *)
case:(yh1)=>[yhgt1| yhe1]; last first.
  have {} yhe1:  yh = 1 by [].
  have cl10: cl1 = 0 
     by rewrite /cl1 /ch yhe1 Rmult_1_r round_generic //; ring.
  have e40: e4 = 0.
    rewrite /e4  /cl3 cl10 Rplus_0_l round_generic; first ring.
    by apply:generic_format_round.
  have e20: e2=0.
    rewrite /e2 /tl2 yhe1 Rmult_1_r round_generic //; ring.
  have h: Rabs eta <= 4 * (u * u) 
   by move : rabs_eta; rewrite e40 e20 !Rabs_R0 ; lra.
  apply:(Rle_lt_trans _ (4 * (u * u))) =>//.
  apply: (Rlt_le_trans _ (5 * (u * u) * ((1 - u) * (1 - u)))); last first.
    by apply/Rmult_le_compat; lra.
  have ->: ( (1 - u) * (1 - u)) = (1 -2*u + u*u) by ring.
  clear -upos u2pos ult1 Hp6.
  suff : u < /16  by nra.
  change (pow (-p) < pow (-4)); apply/bpow_lt; lia.
have yh1pu2: 1 + 2* u <= yh. 
  have : succ radix2 fexp 1 <= yh .
    apply/succ_le_lt =>//.
    by change (format (pow 0)); apply/format_bpow.
  rewrite succ_eq_pos; try lra.
  suff->: 2*u = ulp radix2 fexp 1 by [].
  rewrite /u u_ulp1; field.
have y1pu: 1+ u <= y.
  rewrite /y ;  move/Rabs_le_inv: ylu; lra.
have xy1pu : (1+u) * (1+u) <= x*y by clear -upos ult1 x1pu y1pu; nra.
have haux : Rabs eta <= 5 * (u * u) -> Rabs eta < 5 * (u * u) * (x * y).
  move=> haux.
  apply:(Rle_lt_trans _ ( 5 * (u * u))) =>//.
  rewrite -[X in X < _] Rmult_1_r.
  by apply: Rmult_lt_compat_l; lra.
have b1ltb2':   5 * (u * u) * (x * y) < 55/10 * (u * u) * (x * y).
  by apply/Rmult_lt_compat_r; lra.



case:(Rle_lt_dec (2*u) (Rabs cl2))=> [hcl2|{} cl2ub].
(* 2u <= |cl2| *)
  case:(@ex_mul p cl2 (1-p)).
    + by rewrite bpow_plus -/u.
    + by  apply:generic_format_round.
  move=> Mcl2. 
   have ->:  (2 * pow (- p) * pow (1 - p)) = 4*(u * u).
     rewrite bpow_plus -/u; ring_simplify.
     by have ->: pow 1 = 2 by []; ring.
  move=> cl2E.
  have cl1p2E: cl1 + cl2 =  (IZR (m + Mcl2))* ( 4 * (u *u)).
    rewrite plus_IZR cl2E cl1m4u2;  ring.
  have e40: e4 = 0.
    rewrite /e4 /cl3 round_generic ; first ring.
    pose fx := Float two  (m + Mcl2)%Z  (2* (1 -p)) %Z.
    case: scl12u=>h; last first.
      apply/generic_format_abs_inv; rewrite h.
      change (format ((pow 2) * pow (-p))).
      by rewrite -bpow_plus; apply/format_bpow.
    have hf : cl1 + cl2 = F2R fx.
      rewrite cl1p2E /fx /F2R.
      set e :=( 2 * (1 - p))%Z.
      rewrite /= /e.
      have ->: (2 * (1 - p) = 2 -p -p )%Z by ring.
      by rewrite !bpow_plus /u; have ->: 4 = pow 2 by []; ring.
    apply:(@FLX_format_Rabs_Fnum p _ fx)=>//.
    move: h; 
    rewrite cl1p2E /fx /= Rabs_mult (Rabs_pos_eq (4 * (u * u))); try lra.
    move=>h.
    have {} h:  Rabs (IZR (m + Mcl2)) * u < 1.
      by clear -h upos; nra.
    move/(Rmult_lt_compat_r (pow p)):h. 
    rewrite Rmult_assoc.
    have ->: u * pow p = 1.
      by rewrite /u -bpow_plus; have->: (-p +p = 0)%Z by ring.
    by rewrite Rmult_1_r Rmult_1_l; apply; apply:bpow_gt_0.
  have abs_eta_5: Rabs eta <= 5 * (u*u).
    by move:rabs_eta; rewrite e40 Rabs_R0; lra.
  apply:(Rle_lt_trans _ ( 5 * (u * u))) =>//.
  rewrite -[X in X < _] Rmult_1_r.
  apply: Rmult_lt_compat; lra.
(* cl2 < 2u *)
have tl12ub: Rabs(tl1 + tl2) <= 2*u.
  case:(Rle_lt_dec   (Rabs (tl1 + tl2)) (2*u))=>//.
  move/Rlt_le/(round_le two fexp (Znearest choice)); 
     rewrite rnd_p_abs -/cl2 round_generic; first lra.
  change (format (pow 1 * (pow (-p)))).
  by rewrite -bpow_plus; apply/format_bpow; lia.
have xpos: 0 < xh + xl by  move/Rabs_le_inv: xlu; lra.
have ypos: 0 < yh + yl by move/Rabs_le_inv: ylu; lra.
have {} e3ub: Rabs e3 <= (u * u).
  rewrite /e3.
  have->:(u * u )= /2 * u * (pow (1 -p)) by rewrite /u 
    bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  case:(Rle_lt_dec  (Rabs (tl1 + tl2))  (2 * u)).
    by rewrite bpow_plus.
  move/Rlt_le/(round_le two fexp (Znearest choice)).
  move: cl2ub; rewrite /cl2 -rnd_p_abs (round_generic _ _ _ (2 *u)); first lra.
  change (format ((pow 1)* (pow (-p)))).
  by  rewrite -bpow_plus; apply/format_bpow; lia.

case: (Rlt_le_dec (Rabs tl1) (u/2))=> htl1.
  have ylub: Rabs yl < /2 * u.
    case:(Rlt_le_dec (Rabs yl) (/2*u)) =>//  h.
    have :  / 2 * u  *1 <= Rabs yl * xh.
      apply: Rmult_le_compat; try lra.
    rewrite Rmult_1_r -(Rabs_pos_eq xh); last lra.
    rewrite -Rabs_mult.
    move/(round_le two fexp (Znearest choice)); rewrite rnd_p_abs 
      (Rmult_comm  yl)   -/tl1 round_generic; try lra.
    change (format ((pow (-1)) * ( pow (-p)))).
    by  rewrite -bpow_plus; apply/format_bpow; lia.
  have {} e1ub: Rabs e1 <= /4 * (u * u).
    rewrite /e1.
    have ->:  / 4 * (u * u) =  /2 * u * (pow (-1  -p)).
      by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
    apply: error_le_half_ulp'=>//.
    rewrite bpow_plus  /= IZR_Zpower_pos /= -/u Rmult_1_r.
    case:(Rle_lt_dec   (Rabs (xh * yl)) (/2 *u))=>//.
    move/Rlt_le/(round_le two fexp (Znearest choice)).
    rewrite rnd_p_abs -/tl1 round_generic; first lra.
    by change (format ((pow (-1)) * (pow (-p)))); 
       rewrite -bpow_plus; apply/format_bpow.
  have {} xlylub: Rabs (xl *yl) < /2 * (u * u).
    rewrite Rabs_mult.
    by clear - ylub xlu; move :(Rabs_pos xl) (Rabs_pos yl);  nra.
  have h1 : Rabs eta <= 475/100 * (u * u) by lra.
  lra.
case: (Rlt_le_dec (Rabs tl2) (u/2))=> htl2.
  have xlub: Rabs xl < /2 * u.
    case:(Rlt_le_dec (Rabs xl) (/2*u)) =>//  h.
    have :  / 2 * u  *1 <= Rabs xl * yh.
      apply: Rmult_le_compat; lra.
    rewrite Rmult_1_r -(Rabs_pos_eq yh); last lra.
    rewrite -Rabs_mult.
    move/(round_le two fexp (Znearest choice)); rewrite rnd_p_abs
         -/tl2 round_generic; try lra.
    change (format ((pow (-1)) * ( pow (-p)))).
    by rewrite -bpow_plus; apply/format_bpow; lia.
  have {} e2ub: Rabs e2 <= /4 * (u * u).
    rewrite /e2.
    have ->:  / 4 * (u * u) =  /2 * u * (pow (-1  -p)).
      rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
    apply: error_le_half_ulp'=>//.
    rewrite bpow_plus  /= IZR_Zpower_pos /= -/u Rmult_1_r.
    case:(Rle_lt_dec   (Rabs (xl * yh)) (/2 *u))=>//.
    move/Rlt_le/(round_le two fexp (Znearest choice)).
    rewrite rnd_p_abs -/tl2 round_generic; first lra.
    by change (format ((pow (-1)) * (pow (-p)))); 
       rewrite -bpow_plus; apply/format_bpow.
  have {} xlylub: Rabs (xl *yl) < /2 * (u * u).
    rewrite Rabs_mult.
    by clear - xlub ylu; move :(Rabs_pos xl) (Rabs_pos yl);  nra.
  have h1 : Rabs eta <= 475/100 * (u * u) by lra.
  lra.
case:(@ex_mul  p tl1 (-1 -p)); try  apply/generic_format_round.
  suff->:   pow (-1 - p) =  u / 2 by [].
  by rewrite bpow_plus  /u; rewrite Rmult_comm.
move=> Mtl1.
rewrite bpow_plus -/u.
have ->: (2 * u * (pow (-1) * u)) = u*u.
  by have -> : pow (-1) = /2 by [];field.
move=> tl1Mu2.
case:(@ex_mul  p tl2 (-1 -p)); try  apply/generic_format_round.
  suff->:   pow (-1 - p) =  u / 2 by [].
  by rewrite bpow_plus  /u; rewrite Rmult_comm.
move=> Mtl2.
rewrite bpow_plus -/u.
have ->: (2 * u * (pow (-1) * u)) = u*u.
  have -> : pow (-1) = /2 by [];field.
move=> tl2Mu2.
have tl12Mu2: tl1 + tl2 = IZR (Mtl1 + Mtl2) * (u *u).
 by rewrite tl1Mu2 tl2Mu2 plus_IZR; ring.
have hFtl12: (Rabs (tl1 + tl2) < u -> format ( tl1 + tl2)).
  rewrite tl12Mu2 !Rabs_mult !(Rabs_pos_eq u); try lra.
  rewrite -Rmult_assoc -[X in _ < X]Rmult_1_l.
  move/(Rmult_lt_reg_r _ _ _ upos).
  move/(Rmult_lt_compat_r (pow p) _ _ (bpow_gt_0 two p)).
  rewrite /u Rmult_1_l Rmult_assoc -bpow_plus.
  have ->:  pow (- p + p) = 1 by ring_simplify (-p+p)%Z.
  rewrite Rmult_1_r =>h.
  rewrite -bpow_plus.
  pose f := (Float two  (Mtl1 + Mtl2)  (- p + - p)).
  apply/(@FLX_format_Rabs_Fnum p _  f).
    by rewrite /f /F2R.
  by rewrite /f .
case: tl12ub =>  tl12ub;  last first.
  have Ftl12 : format (tl1 + tl2).
    move:  tl12ub; rewrite -(Rabs_pos_eq (2* u)); try lra.
    case/Rabs_eq_Rabs =>->; try apply/generic_format_opp; 
        have ->: 2 * u = (pow 1 ) * (pow (-p)) by []; rewrite -bpow_plus; 
        apply/format_bpow; lia.
  have e30: e3 = 0 by rewrite /e3 /cl2 round_generic //; ring.
  by move:rabs_eta; rewrite e30 Rabs_R0; lra.
have hFtl12': Zeven (Mtl1 + Mtl2) -> format (tl1+tl2).
  move=> heven.
  move/Zeven_div2 :(heven).
  rewrite  tl12Mu2 => ->.
  rewrite mult_IZR.
  pose f := (Float two  ( Z.div2 (Mtl1 + Mtl2) )  (1 - p + - p)).
  apply/(@FLX_format_Rabs_Fnum p _  f).
    rewrite  -mult_IZR -Zeven_div2 /f /F2R //.
    set M:= Z.div2 (Mtl1 + Mtl2); set e := (1 - p + - p )%Z.
    rewrite /= /M /e !bpow_plus -!Rmult_assoc. 
    have -> : pow 1 = 2 by [].
    by rewrite -mult_IZR Zmult_comm -Zeven_div2.
  rewrite /f /F2R /=.
  apply/(Rmult_lt_reg_r 2); first lra.
  rewrite -(Rabs_pos_eq 2); last lra.
  rewrite -Rabs_mult -mult_IZR Zmult_comm -Zeven_div2 //.
  move: tl12ub ; rewrite  tl12Mu2 !Rabs_mult (Rabs_pos_eq u); try lra.
  rewrite -Rmult_assoc; move/(Rmult_lt_reg_r _ _ _ upos).
  move/(Rmult_lt_compat_r (pow p) _ _ (bpow_gt_0 two p)).
  rewrite Rmult_assoc /u -bpow_plus ; ring_simplify (-p + p)%Z.
  rewrite Rmult_1_r (Rabs_pos_eq 2); lra.
case:(Rlt_le_dec (Rabs (tl1 +tl2)) u)=>//.
  move/ hFtl12=> Ftl12.
  have e30: e3 = 0 by rewrite /e3 /cl2 round_generic //; ring.
  by move:rabs_eta; rewrite e30 Rabs_R0; lra.
move=> tl12lb.
have hmant :  pow p <= Rabs (IZR (Mtl1 + Mtl2)) < pow (1 + p).
  move: tl12lb  tl12ub.
    rewrite  tl12Mu2.
    rewrite -/u; split=>//.
    apply/(Rmult_le_reg_r (u * u)) =>//. 
    suff ->:   pow p * (u * u) = u .
      rewrite -(Rabs_pos_eq (u * u)); try lra.
      by rewrite -Rabs_mult.
    by rewrite /u -!bpow_plus; ring_simplify(p +( -p + -p))%Z.
  apply/(Rmult_lt_reg_r (u*u)); first lra.
  suff->: pow (1 + p) * (u * u) = 2*u.

    by move: tl12ub0 ;  rewrite Rabs_mult (Rabs_pos_eq (u*u)); lra.
  rewrite /u -!bpow_plus. ring_simplify  (1 + p + (- p + - p))%Z.
  by rewrite bpow_plus Rmult_comm.
case:(Zeven_odd_dec   (Mtl1 + Mtl2)).
  move/ hFtl12'=> Ftl12.
  have e30: e3 = 0 by rewrite /e3 /cl2 round_generic //; ring.
  move:rabs_eta; rewrite e30 Rabs_R0; lra.
move/Zodd_bool_iff  => Hodd.
case: (Zeven_ex (Mtl1 +Mtl2))=>M  Me.
have {Me} ME : (Mtl1 + Mtl2)%Z = (2 * M + 1)%Z.
  by rewrite Me; rewrite Zeven.Zeven_odd_bool Hodd.
have hub: IZR (2*M)< IZR (2 * M + 1)< IZR (2*M+2) by split; apply/IZR_lt; lia.
have nFs: ~ format (IZR (2 * M + 1)).
  apply: (generic_format_discrete _ _ _ M).
  rewrite /F2R /cexp -ME (mag_unique _ _ (1+p)).
    set e := fexp (1+p).
    rewrite /= /e /fexp.
    ring_simplify (1 + p -p)%Z.
    have->: pow 1 = 2 by [].
    rewrite -!mult_IZR ME !(Zmult_comm _ 2).
    have->: ((2 * (M + 1)) =  (2 * M + 2))%Z by ring.
    by [].
  by ring_simplify(1 + p - 1)%Z.
have cexpf :  (ce (IZR (2 * M + 1)) = 1)%Z.
  rewrite /cexp /fexp (mag_unique _ _  (1 +p)); first ring.
  have->:  (1 + p - 1 = p)%Z by ring.
  by rewrite -ME.
have rDN: round two  fexp Zfloor (IZR (2 * M + 1))  =  IZR (2 * M).
  rewrite /round /scaled_mantissa .
  rewrite cexpf (Zfloor_imp M) /F2R.
    set f := Float _ _ _.
    by rewrite Rmult_comm mult_IZR ; congr Rmult.
  move: hub.
  have -> : (2 * M + 2 = 2 * (M + 1))%Z by ring.
  rewrite !mult_IZR.
  have ->: pow(-1) = /2 by [].
  lra.
have rUP :  round two  fexp Zceil (IZR (2 * M + 1))  =  IZR (2 * (M+ 1)).
  rewrite round_UP_DN_ulp // rDN ulp_neq_0 ?cexpf.
    by rewrite Zmult_plus_distr_r  Zmult_1_r plus_IZR.
  by apply/not_0_IZR; lia.
have e3E: Rabs e3 = u*u.
  rewrite /e3 /cl2  tl12Mu2 ME.
   rewrite /u -bpow_plus round_bpow!bpow_plus -/u.
   case:(round_DN_or_UP two fexp (Znearest choice) (IZR (2 * M + 1)));
      rewrite ?rDN ?rUP => ->; rewrite plus_IZR.
    ring_simplify (IZR (2 * M) * (u * u) - (IZR (2 * M) + 1) * (u * u)).
    by rewrite Rabs_Ropp Rabs_pos_eq; lra.
  rewrite !mult_IZR !plus_IZR.
  ring_simplify(2 * (IZR M + 1) * (u * u) - (2 * IZR M + 1) * (u * u)).
  by rewrite Rabs_pos_eq; lra.
apply:(Rle_lt_trans _ (55 /10 * (u * u))); last first.
rewrite -[X in X < _]Rmult_1_r; apply/Rmult_lt_compat_l; lra.

case:(Rlt_le_dec (Rabs tl1) u)=> tl1ubu.
  have {} e1ub: Rabs e1 <= /2 * u * u.
    rewrite /e1.
    have ->:  / 2 * u * u =  /2 * u * (pow ( -p)).
      rewrite /u ; ring.
    apply: error_le_half_ulp'=>//.
    rewrite -/u .
    case:(Rle_lt_dec  (Rabs (xh * yl)) u) =>// h.
    have : rnd_p u <= rnd_p (Rabs (xh * yl)).
      apply/round_le; lra.
    rewrite rnd_p_abs -/tl1 round_generic; try lra.
    change (format (pow (-p))); apply/format_bpow; lia.
  by lra.
case:(Rlt_le_dec (Rabs tl2) u)=> tl2ubu.
  have {} e2ub: Rabs e2 <= /2 * u * u.
    rewrite /e2.
    have ->:  / 2 * u * u =  /2 * u * (pow ( -p)).
      rewrite /u ; ring.
    apply: error_le_half_ulp'=>//.
    rewrite -/u .
    case:(Rle_lt_dec  (Rabs (xl * yh)) u) =>// h.
    have : rnd_p u <= rnd_p (Rabs (xl * yh)).
      apply/round_le; lra.
    rewrite rnd_p_abs -/tl2 round_generic; try lra.
    change (format (pow (-p))); apply/format_bpow; lia.
  by lra.

case:(@ex_mul  p tl1 ( -p)); try  apply/generic_format_round.
  by rewrite -/u.
move=> Mtl1'.
rewrite -/u=> tl1M2u2.
case:(@ex_mul  p tl2 (-p)); try  apply/generic_format_round.
  by rewrite -/u.
move=> Mtl2'; rewrite -/u=> tl2M2u2.
have tl12M2u2: tl1 + tl2 = IZR (Mtl1' + Mtl2') *( 2 * (u *u)).
 by rewrite tl1M2u2 tl2M2u2 plus_IZR; ring.
have Ftl12: format (tl1+tl2).
  pose f := (Float two  (Mtl1' + Mtl2')  (1- p + - p)).
  apply/(@FLX_format_Rabs_Fnum p _  f).
    rewrite tl12M2u2 /f /F2R.
    suff ->:  (2 * (u * u)) = pow (1 - p + - p ) by [].
     by rewrite !bpow_plus  -/u -Rmult_assoc.
  rewrite /f /=.
  apply/(Rmult_lt_reg_r  (2 * (u * u))); first lra.
  move:  tl12ub;  rewrite  tl12M2u2 Rabs_mult (Rabs_pos_eq (2 * (u * u))); try lra.
  suff ->: pow p * (2 * (u * u)) = 2*u by [].
  have ->: 2 = pow 1 by [].
  rewrite /u -!bpow_plus; congr bpow; ring.
have e30: e3 = 0 by rewrite /e3 /cl2 round_generic //; ring.
move:rabs_eta; rewrite e30 Rabs_R0; lra.
Qed.

(* Theorem 2.7 *)
Lemma DWTimesDW1_correct_general xh xl yh yl  (DWx:double_word xh xl) (DWy:double_word yh yl) :
  let (zh, zl) := DWTimesDW1 xh xl yh yl in
  let xy := ((xh + xl) * (yh + yl))%R in
             (Rabs ((zh + zl - xy) / xy) < 55/10 * (u * u)).
Proof.

have rnd_p_sym := rnd_p_sym.
have upos:= upos.
have ult1 : u < 1 by rewrite /u ; apply:bpow_lt_1; lia.
have u2pos: 0 < u * u by apply:Rmult_lt_0_compat.
have h5lt55: 5 * (u * u) < 55/10 * (u * u) by lra.

have [[Fxh Fxl] Exh] := DWx.
have [[Fyh Fyl] Eyh] := DWy.
case E1: DWTimesDW1 => [zh zl].
have Hp1:= Hp1.
case:(Req_dec yh 0)=> yh0.
  have yl0: yl = 0.
    by move:Eyh; rewrite  yh0 Rplus_0_l round_generic.
  move:E1; rewrite /DWTimesDW1 yh0 yl0 Rmult_0_r TwoProdE round_0 Fast2MultC Rmult_0_r Fast2Mult0f. 
  rewrite /Fast2Sum /F2SumFLX.Fast2Sum !(Rplus_0_r, Rminus_0_r, Rplus_0_l, round_0).
  case=> <- <-; rewrite Rplus_0_r Rmult_0_r Rminus_0_l /Rdiv Ropp_0 Rmult_0_l Rabs_R0.
  clear -upos; nra.

case:(Req_dec xh 0)=> xh0.
  have xl0: xl = 0.
    by move:Exh; rewrite  xh0 Rplus_0_l round_generic.
  move:E1; rewrite /DWTimesDW1 xh0 xl0 Rmult_0_l TwoProdE  round_0 Fast2Mult0f.
  rewrite /Fast2Sum /F2SumFLX.Fast2Sum !(Rplus_0_r, Rminus_0_r, Rplus_0_l, round_0, Rmult_0_l).
  case=> <- <-; rewrite Rplus_0_r  /Rdiv   Rmult_0_l Rabs_R0.
  by clear -upos; nra.
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
  apply:(Hwlog yh yl  (-xh) (-xl) (-zh) (-zl))=>//; try lra; last  by rewrite DWTimesDW1_Asym_l E1.
  have [[Fxh Fxl] Exh] := DWx.
  split; [split|]; try apply:generic_format_opp=>//.
  have ->:- xh + - xl = -(xh +  xl) by ring.
  by rewrite rnd_p_sym {1}Exh.

wlog yhpos: yh yl  xh xl zh zl DWx DWy  E1 xh0 yh0 x0 y0 xhpos / 0 <= yh.
  move=> Hwlog.
  case:(Rle_lt_dec 0 yh) => yhle0; first by apply:Hwlog.
  have ->: (zh + zl - (xh + xl) * (yh + yl)) / ((xh + xl) * (yh +yl))= 
   ((- zh + - zl - ( xh +  xl) * (- yh + - yl)) / (( xh + xl) * (- yh + - yl)))
    by field; lra.
  apply:(Hwlog (-yh) (-yl)  (xh) (xl) (-zh) (-zl))=>//; try lra; last by rewrite DWTimesDW1_Asym_r E1.
  have [[Fyh Fyl] Eyh] := DWy.
  split; [split|]; try apply:generic_format_opp=>//.
  have ->:- yh + - yl = -(yh +  yl) by ring.
  by rewrite rnd_p_sym  {1}Eyh.
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
  by rewrite DWTimesDW1Sx E1.
wlog [yh1 yh2]: yh yl  zh zl  DWy yh0 y0 yhpos E1/ 1 <= yh <= 2-2*u.
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
  by rewrite DWTimesDW1Sy E1.
have xh2': xh < 2 by lra.
have yh2': yh < 2 by lra.
have h0 : 1 <= xh * yh < 4 by nra.
have ylu:Rabs yl <= u by apply: (double_lpart_u DWy); lra.
have xlu:Rabs xl <= u by apply: (double_lpart_u DWx); lra.
have [[Fxh Fxl] Exh] := DWx.
have [[Fyh Fyl] Eyh] := DWy.
move:E1; rewrite /DWTimesDW1.
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
case:(@ex_mul p xh 0)=>//.
  change (1 <= Rabs xh); rewrite Rabs_pos_eq; lra.
  move=> mxh; rewrite Rmult_1_r -/u => xhE.
case:(@ex_mul p yh 0)=>//.
  change (1 <= Rabs yh); rewrite Rabs_pos_eq; lra.
  move=> myh; rewrite Rmult_1_r -/u => yhE.
have xhyhm4u2: xh*yh = IZR (mxh * myh) * (4* u^2).
  rewrite xhE yhE mult_IZR; ring.
case: (@ex_mul p ch 0)=>//.
    rewrite /ch; rewrite  -rnd_p_abs.
    have ->: pow 0 = rnd_p 1.
    rewrite round_generic //.
      change (format (pow 0)); apply:format_bpow =>//.
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

set tl1 := rnd_p (xh * yl).
pose e1 := tl1 - xh*yl.
have tl1E: tl1 = xh*yl + e1 by rewrite  /e1 /tl1; ring.
have xhylub: Rabs (xh*yl) <= 2*u - 2*(u*u).
  rewrite Rabs_mult Rabs_pos_eq; last lra.
have->: 2 * u - 2 * (u * u) = (2 - 2 * u) * u by ring.
apply:Rmult_le_compat; try apply: Rabs_pos; lra.
have tl1ub: Rabs tl1 <= 2*u -2* (u *u).
  rewrite /tl1   -rnd_p_abs.
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
  rewrite /tl2   -rnd_p_abs.
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
  by apply:(Rle_trans _ _ _ (Rabs_triang _ _)); lra.
have cl2ub: Rabs cl2 <= 4*u - 4*(u * u).
  rewrite /cl2.
  suff->:  4*u - 4*(u * u) = rnd_p  (4*u - 4*(u * u)) 
    by rewrite -rnd_p_abs; apply:round_le.
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
have e3ub: Rabs e3 <= 2 * (u * u).
  rewrite /e3.
  have->: 2 * (u * u )= /2 * u * (pow (2 -p)) by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  rewrite bpow_plus  /= IZR_Zpower_pos /= -/u; lra.
set cl3 := rnd_p (cl1 + cl2).
pose e4 := cl3 - (cl1 + cl2).
have cl1cl2: Rabs (cl1 + cl2) <= 6*u - 4*(u * u).
  apply:(Rle_trans _ _ _ (Rabs_triang _ _)); lra.
have cl3ub: Rabs cl3 <= 6*u.
  rewrite /cl3 -rnd_p_abs.
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
have e4ub: Rabs e4 <= 4 * (u * u).
 rewrite /e4.
  have->: 4 * (u * u )= /2 * u * (pow (3 -p)) by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  rewrite bpow_plus  /= IZR_Zpower_pos /= -/u. 
  by apply:(Rle_trans _ (6 * u)); lra.
have hf2Sc: Rabs cl3 <= Rabs ch.
  apply:(Rle_trans _ (6 * u))=>//.
  apply: (Rle_trans _ 1).
   apply: (Rle_trans _ (8 * u)); try lra.
  suff : pow (3 - p) <= pow 0 .
   rewrite bpow_plus  /= IZR_Zpower_pos /= -/u; lra.
   apply:bpow_le; lia.
  have ->:  1 = pow 0 by [].
  rewrite -(round_generic two fexp (Znearest choice) (pow 0)).
  rewrite /ch  -rnd_p_abs; apply/round_le; rewrite /= Rabs_pos_eq; nra.
  by apply:generic_format_bpow; rewrite /fexp; lia.
rewrite (surjective_pairing (Fast2Sum  _ _)).
rewrite F2Sum_correct_abs=>//; try apply: generic_format_round; last by rewrite (round_generic _ _ _ cl1)//.
rewrite (round_generic _ _ _ cl1)//.
case=> zhe  zle.
pose eta := -(xl* yl) + e1 + e2 + e3 + e4.
have xlylub: Rabs (xl * yl) <= u*u.
  rewrite Rabs_mult; clear -ylu xlu upos.
  move : (Rabs_pos xl) (Rabs_pos yl); nra.
have rabs_eta : Rabs eta <=  Rabs(xl * yl)  + Rabs e1 + Rabs e2 + Rabs e3 + Rabs e4.
  rewrite /eta.
  apply:(Rle_trans _ ( (Rabs (xl*yl))+ Rabs e1 + Rabs e2 + Rabs e3 + Rabs e4)); last lra.

   repeat (apply: (Rle_trans _ _ _ (Rabs_triang _ _)); 
     first apply : Rplus_le_compat_r); try lra.
  rewrite Rabs_Ropp ; lra.
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
  ring_simplify ((xh + xl) * (yh + yl) + eta - (xh + xl) * (yh + yl)).

case:(Rle_lt_dec 2 (xh * yh))=>xhyh2.
  apply:(Rle_lt_trans _ ((9 * (u * u)) / (2 * (1 - u) * (1 - u)))); last first.


    apply:(Rmult_lt_reg_r (2 * (1 - u) * (1 - u))).
    clear -upos ult1 ; nra.
    rewrite /Rdiv Rmult_assoc Rinv_l; last by clear -ult1; nra.
    have ->: (2 * (1 - u) * (1 - u)) = 2 - 4 * u + 2* (u*u) by ring.
    suff: 0 < u*u -20* u^3 + 10* (u*u) * (u * u)  by lra.
    (* suff: 0 <= u*u -20* u^3 by clear -u2pos; nra. *)
    suff : u <= /32 by  clear -u2pos; nra.
    change (pow (-p) <= pow (- 5)); apply/bpow_le;lia.

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
    clear - yh1  ylu  upos ult1.
    move/Rabs_le_inv: ylu;nra.
  move =>  hy hx.    
  have hypos : 0 < (yh + yl).
    clear -  yh1   ult1 ylu.
    move/Rabs_le_inv: ylu; lra.
  rewrite Rabs_pos_eq.
    suff h: 0 < (2 * (1 - u) * (1 - u)) <= ((xh + xl) * (yh + yl)) by apply:Rinv_le; lra.
    split;  first lra.
    apply:(Rle_trans _ (xh * (1 -u) * (yh * (1 -u)))).
      clear - xpos hypos upos ult1 xhyh2 xh1   yh1.
      have -> : xh * (1 - u) * (yh * (1 - u)) = (xh * yh) * (1-u) *(1 -u) by ring.
      apply:Rmult_le_compat_r;  nra.
    apply:Rmult_le_compat; nra.
  clear - xpos hypos; apply/Rlt_le/Rinv_0_lt_compat; nra.

(* xh yh <2*)

have  cl1u: Rabs cl1 <= u.
  rewrite /cl1 -Ropp_minus_distr Rabs_Ropp /ch.
  have ->: u = / 2 * u * (pow 1)  by rewrite /= IZR_Zpower_pos /=; field.
  rewrite /u; apply: error_le_half_ulp'; first lia.
  rewrite Rabs_pos_eq  /= ?IZR_Zpower_pos /= ?Rmult_1_r //; try lra.
  (* clear - xh1 y1;  nra. *)

 have hsxhyh: xh + yh <= 3 -2*u by apply:l5_2F=>//; lra.


have tl1u: Rabs tl1 <= xh * u.
  rewrite /tl1  -rnd_p_abs.
  have -> : xh * u = rnd_p (xh * u).
    by rewrite /u round_bpow round_generic.
  apply:round_le; rewrite Rabs_mult Rabs_pos_eq; try lra.
  by apply:Rmult_le_compat_l; try lra.
have tl2u: Rabs tl2 <= yh * u.
  rewrite /tl2 -rnd_p_abs.
  suff -> : yh * u = rnd_p (yh * u).
    apply:round_le.
    rewrite Rabs_mult Rmult_comm Rabs_pos_eq; try lra.
    apply:Rmult_le_compat_l; try lra.
  by rewrite /u round_bpow round_generic.

have stl12u: Rabs (tl1 + tl2)  <= (3 -2*u) *u.

  apply: (Rle_trans _ _ _ (Rabs_triang _ _)).
  apply:(Rle_trans _ ((xh  + yh)* u)); try lra.
  apply :Rmult_le_compat_r; lra.

have {} cl2ub: Rabs cl2 <= 3 * u.
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
  rewrite -rnd_p_abs.
  by apply:round_le; lra.
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
have xlb: 1-u <= xh + xl  by move/Rabs_le_inv: xlu; lra.
have ylb: 1-u <= yh + yl  by move/Rabs_le_inv: ylu; lra.
pose x := xh + xl; pose y := yh + yl.
have xylb : (1 -u) * (1-u) <= (x * y).
 clear - xh1 yh1 ult1 upos xlb ylb ; rewrite /x /y; nra. 
have xyiub: /(x*y) <= / ((1-u) * (1-u)).
by apply/Rinv_le =>// ; clear - ult1 ; nra.
rewrite Rabs_mult -/x -/y.
have xypos: 0 < x*y by clear -ult1 xylb ; nra.
have xyn0: x*y <> 0 by lra. 

suff etaubxy: Rabs eta < 55/10 * (u * u) * (x * y).
apply/(Rmult_lt_reg_r (x*y)) =>//.
rewrite Rmult_assoc -{2}(Rabs_pos_eq (x*y));  last lra.
rewrite Rabs_Rinv // Rinv_l // ?Rmult_1_r //.

 by apply/Rabs_no_R0.

(* xh =1 or yh = 1 *)
case:(xh1)=>[xhgt1| xhe1]; last first.
  have {} xhe1:  xh = 1 by [].
  have cl10: cl1 = 0 
     by rewrite /cl1 /ch xhe1 Rmult_1_l round_generic //; ring.
  have e40: e4 = 0.
    rewrite /e4  /cl3 cl10 Rplus_0_l round_generic; first ring.
    by apply:generic_format_round.
  have e10: e1=0.
    rewrite /e1 /tl1 xhe1 Rmult_1_l round_generic //; ring.
  have h: Rabs eta <= 4 * (u * u) 
   by move : rabs_eta; rewrite e40 e10 !Rabs_R0 ; lra.
apply:(Rle_lt_trans _ (4 * (u * u))) =>//.
(* apply:(Rlt_trans _ (5  * (u * u) * (x * y))); last first. *)
(* apply/Rmult_lt_compat_r =>//. *)
(* apply/Rmult_lt_compat_r =>//; lra. *)

apply: (Rlt_le_trans _ (55/10 * (u * u) * ((1 - u) * (1 - u)))); last first.
by clear -upos u2pos xylb ; nra.
have ->: ( (1 - u) * (1 - u)) = (1 -2*u + u*u) by ring.
clear -upos u2pos ult1 Hp6.
suff : u < /16  by nra.
change (pow (-p) < pow (-4)); apply/bpow_lt; lia.
have xh1pu2: 1 + 2* u <= xh.
have : succ radix2 fexp 1 <= xh .
apply/succ_le_lt =>//.
by change (format (pow 0)); apply/format_bpow.
rewrite succ_eq_pos; try lra.
suff->: 2*u = ulp radix2 fexp 1 by [].
rewrite /u u_ulp1; field.



have x1pu: 1+ u <= x.
rewrite /x ;  move/Rabs_le_inv: xlu; lra.
(* le meme pour y ; il faudrait factoriser *)

case:(yh1)=>[yhgt1| yhe1]; last first.
  have {} yhe1:  yh = 1 by [].
  have cl10: cl1 = 0 
     by rewrite /cl1 /ch yhe1 Rmult_1_r round_generic //; ring.
  have e40: e4 = 0.
    rewrite /e4  /cl3 cl10 Rplus_0_l round_generic; first ring.
    by apply:generic_format_round.
  have e20: e2=0.
    rewrite /e2 /tl2 yhe1 Rmult_1_r round_generic //; ring.
  have h: Rabs eta <= 4 * (u * u) 
   by move : rabs_eta; rewrite e40 e20 !Rabs_R0 ; lra.
apply:(Rle_lt_trans _ (4 * (u * u))) =>//.


apply: (Rlt_le_trans _ (5 * (u * u) * ((1 - u) * (1 - u)))); last first.
apply/Rmult_le_compat; lra.
have ->: ( (1 - u) * (1 - u)) = (1 -2*u + u*u) by ring.
clear -upos u2pos ult1 Hp6.
suff : u < /16  by nra.
change (pow (-p) < pow (-4)); apply/bpow_lt; lia.
have yh1pu2: 1 + 2* u <= yh.
have : succ radix2 fexp 1 <= yh .
apply/succ_le_lt =>//.
by change (format (pow 0)); apply/format_bpow.
rewrite succ_eq_pos; try lra.

suff->: 2*u = ulp radix2 fexp 1 by [].
rewrite /u u_ulp1; field.

have y1pu: 1+ u <= y.
rewrite /y ;  move/Rabs_le_inv: ylu; lra.
have xy1pu : (1+u) * (1+u) <= x*y by clear -upos ult1 x1pu y1pu; nra.
have haux : Rabs eta <= 5 * (u * u) -> Rabs eta < 5 * (u * u) * (x * y).
move=> haux.
apply:(Rle_lt_trans _ ( 5 * (u * u))) =>//.
rewrite -[X in X < _] Rmult_1_r.
by apply: Rmult_lt_compat_l; lra.
case:(Rle_lt_dec (2*u) (Rabs cl2))=> [hcl2|{} cl2ub].

(* 2u <= |cl2| *)
  case:(@ex_mul p cl2 (1-p)).
    + by rewrite bpow_plus -/u.
    + by  apply:generic_format_round.
  move=> Mcl2. 
   have ->:  (2 * pow (- p) * pow (1 - p)) = 4*(u * u).
     rewrite bpow_plus -/u; ring_simplify.
     by have ->: pow 1 = 2 by []; ring.
  move=> cl2E.
  have cl1p2E: cl1 + cl2 =  (IZR (m + Mcl2))* ( 4 * (u *u)).
    rewrite plus_IZR cl2E cl1m4u2;  ring.
  have e40: e4 = 0.
    rewrite /e4 /cl3 round_generic ; first ring.

     pose fx := Float two  (m + Mcl2)%Z  (2* (1 -p)) %Z.

case: scl12u=>h; last first.
apply/generic_format_abs_inv; rewrite h.
change (format ((pow 2) * pow (-p))).
by rewrite -bpow_plus; apply/format_bpow.
    have hf : cl1 + cl2 = F2R fx.
      rewrite cl1p2E /fx /F2R.
   set e :=( 2 * (1 - p))%Z.
   rewrite /= /e.
   have ->: (2 * (1 - p) = 2 -p -p )%Z by ring.
   rewrite !bpow_plus /u; have ->: 4 = pow 2 by []; ring.
    apply:(@FLX_format_Rabs_Fnum p _ fx)=>//.

move: h; 
   rewrite cl1p2E /fx /= Rabs_mult (Rabs_pos_eq (4 * (u * u))); try lra.
move=>h.
have {} h:  Rabs (IZR (m + Mcl2)) * u < 1.
by clear -h upos; nra.
move/(Rmult_lt_compat_r (pow p)):h.
rewrite Rmult_assoc.
have ->: u * pow p = 1.
rewrite /u -bpow_plus; have->: (-p +p = 0)%Z by ring.
by [].
by rewrite Rmult_1_r Rmult_1_l; apply; apply:bpow_gt_0.


have abs_eta_5: Rabs eta <= 5 * (u*u).
move:rabs_eta; rewrite e40 Rabs_R0; lra.


  apply:(Rle_lt_trans _ ( 5 * (u * u))) =>//.
rewrite -[X in X < _] Rmult_1_r.
apply: Rmult_lt_compat; lra.

(* cl2 < 2u *)
have tl12ub: Rabs(tl1 + tl2) <= 2*u.
case:(Rle_lt_dec   (Rabs (tl1 + tl2)) (2*u))=>//.

move/Rlt_le/(round_le two fexp (Znearest choice)); rewrite rnd_p_abs -/cl2 round_generic; first lra.
change (format (pow 1 * (pow (-p)))); rewrite -bpow_plus; apply/format_bpow; lia.
have xpos: 0 < xh + xl by  move/Rabs_le_inv: xlu; lra.
have ypos: 0 < yh + yl by move/Rabs_le_inv: ylu; lra.
have {} e3ub: Rabs e3 <= (u * u).
  rewrite /e3.
  have->:(u * u )= /2 * u * (pow (1 -p)) by rewrite /u 
    bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  case:(Rle_lt_dec  (Rabs (tl1 + tl2))  (2 * u)).
    by rewrite bpow_plus.
  move/Rlt_le/(round_le two fexp (Znearest choice)).
  move: cl2ub; rewrite /cl2 -rnd_p_abs (round_generic _ _ _ (2 *u)); first lra.
  change (format ((pow 1)* (pow (-p)))); rewrite -bpow_plus; apply/format_bpow; lia.


  case: (Rlt_le_dec (Rabs tl1) (u/2))=> htl1.
have ylub: Rabs yl < /2 * u.
case:(Rlt_le_dec (Rabs yl) (/2*u)) =>//  h.
have :  / 2 * u  *1 <= Rabs yl * xh.
apply: Rmult_le_compat; try lra.
rewrite Rmult_1_r -(Rabs_pos_eq xh); last lra.
rewrite -Rabs_mult.
move/(round_le two fexp (Znearest choice)); rewrite rnd_p_abs 
(Rmult_comm  yl)   -/tl1 round_generic; try lra.
change (format ((pow (-1)) * ( pow (-p)))); rewrite -bpow_plus; 
   apply/format_bpow; lia.

have {} e1ub: Rabs e1 <= /4 * (u * u).
rewrite /e1.
have ->:  / 4 * (u * u) =  /2 * u * (pow (-1  -p)).
rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  rewrite bpow_plus  /= IZR_Zpower_pos /= -/u Rmult_1_r.

case:(Rle_lt_dec   (Rabs (xh * yl)) (/2 *u))=>//.
move/Rlt_le/(round_le two fexp (Znearest choice)).
rewrite rnd_p_abs -/tl1 round_generic; first lra.
by change (format ((pow (-1)) * (pow (-p)))); rewrite -bpow_plus; apply/format_bpow.

have {} xlylub: Rabs (xl *yl) < /2 * (u * u).
rewrite Rabs_mult.
  by clear - ylub xlu; move :(Rabs_pos xl) (Rabs_pos yl);  nra.

have h1 : Rabs eta <= 475/100 * (u * u) by lra.
apply:(Rlt_trans _ (5 * (u * u) * (x * y)))=>//.

apply:haux;  lra.
 apply/Rmult_lt_compat_r;  lra.




  case: (Rlt_le_dec (Rabs tl2) (u/2))=> htl2.
have xlub: Rabs xl < /2 * u.
case:(Rlt_le_dec (Rabs xl) (/2*u)) =>//  h.
have :  / 2 * u  *1 <= Rabs xl * yh.
apply: Rmult_le_compat; try lra.
rewrite Rmult_1_r -(Rabs_pos_eq yh); last lra.
rewrite -Rabs_mult.
move/(round_le two fexp (Znearest choice)); rewrite rnd_p_abs
     -/tl2 round_generic; try lra.
change (format ((pow (-1)) * ( pow (-p)))); rewrite -bpow_plus; 
   apply/format_bpow; lia.

have {} e2ub: Rabs e2 <= /4 * (u * u).
rewrite /e2.
have ->:  / 4 * (u * u) =  /2 * u * (pow (-1  -p)).
rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  rewrite bpow_plus  /= IZR_Zpower_pos /= -/u Rmult_1_r.

case:(Rle_lt_dec   (Rabs (xl * yh)) (/2 *u))=>//.
move/Rlt_le/(round_le two fexp (Znearest choice)).
rewrite rnd_p_abs -/tl2 round_generic; first lra.
by change (format ((pow (-1)) * (pow (-p)))); rewrite -bpow_plus; apply/format_bpow.

have {} xlylub: Rabs (xl *yl) < /2 * (u * u).
rewrite Rabs_mult.
  by clear - xlub ylu; move :(Rabs_pos xl) (Rabs_pos yl);  nra.

have h1 : Rabs eta <= 475/100 * (u * u) by lra.
apply:(Rlt_trans _ ( 5 * (u * u) * (x * y))); last by apply/Rmult_lt_compat_r; lra.



apply:haux;  lra.
case:(@ex_mul  p tl1 (-1 -p)); try  apply/generic_format_round.
suff->:   pow (-1 - p) =  u / 2 by [].
by rewrite bpow_plus  /u; rewrite Rmult_comm.
move=> Mtl1.
rewrite bpow_plus -/u.
have ->: (2 * u * (pow (-1) * u)) = u*u.
  have -> : pow (-1) = /2 by [];field.
move=> tl1Mu2.

case:(@ex_mul  p tl2 (-1 -p)); try  apply/generic_format_round.
suff->:   pow (-1 - p) =  u / 2 by [].
by rewrite bpow_plus  /u; rewrite Rmult_comm.
move=> Mtl2.
rewrite bpow_plus -/u.
have ->: (2 * u * (pow (-1) * u)) = u*u.
  have -> : pow (-1) = /2 by [];field.
move=> tl2Mu2.
have tl12Mu2: tl1 + tl2 = IZR (Mtl1 + Mtl2) * (u *u).
 by rewrite tl1Mu2 tl2Mu2 plus_IZR; ring.
have hFtl12: (Rabs (tl1 + tl2) < u -> format ( tl1 + tl2)).
rewrite tl12Mu2 !Rabs_mult !(Rabs_pos_eq u); try lra.
rewrite -Rmult_assoc -[X in _ < X]Rmult_1_l.
move/(Rmult_lt_reg_r _ _ _ upos).
move/(Rmult_lt_compat_r (pow p) _ _ (bpow_gt_0 two p)).
rewrite /u Rmult_1_l Rmult_assoc -bpow_plus.
have ->:  pow (- p + p) = 1 by ring_simplify (-p+p)%Z.
rewrite Rmult_1_r =>h.
rewrite -bpow_plus.
pose f := (Float two  (Mtl1 + Mtl2)  (- p + - p)).

apply/(@FLX_format_Rabs_Fnum p _  f).
by rewrite /f /F2R.
by rewrite /f .
case: tl12ub =>  tl12ub;  last first.

have Ftl12 : format (tl1 + tl2).
move:  tl12ub; rewrite -(Rabs_pos_eq (2* u)); try lra.
case/Rabs_eq_Rabs =>->; try apply/generic_format_opp; have ->: 2 * u = (pow 1 ) * (pow (-p)) by []; rewrite -bpow_plus; 

 apply/format_bpow; lia.

have e30: e3 = 0 by rewrite /e3 /cl2 round_generic //; ring.
apply/(Rlt_trans _ (5 * (u * u) * (x * y))) ; last by apply/Rmult_lt_compat_r; lra.

move:rabs_eta; rewrite e30 Rabs_R0; lra.

have hFtl12': Zeven (Mtl1 + Mtl2) -> format (tl1+tl2).

move=> heven.
move/Zeven_div2 :(heven).
rewrite  tl12Mu2 => ->.
rewrite mult_IZR.
pose f := (Float two  ( Z.div2 (Mtl1 + Mtl2) )  (1 - p + - p)).

apply/(@FLX_format_Rabs_Fnum p _  f).
rewrite  -mult_IZR -Zeven_div2 /f /F2R //.
set M:= Z.div2 (Mtl1 + Mtl2); set e := (1 - p + - p )%Z.
      rewrite /= /M /e !bpow_plus -!Rmult_assoc. 
    have -> : pow 1 = 2 by [].
by rewrite -mult_IZR Zmult_comm -Zeven_div2.
rewrite /f /F2R /=.
apply/(Rmult_lt_reg_r 2); first lra.
rewrite -(Rabs_pos_eq 2); last lra.
rewrite -Rabs_mult -mult_IZR Zmult_comm -Zeven_div2 //.
move: tl12ub ; rewrite  tl12Mu2 !Rabs_mult (Rabs_pos_eq u); try lra.
rewrite -Rmult_assoc; move/(Rmult_lt_reg_r _ _ _ upos).
move/(Rmult_lt_compat_r (pow p) _ _ (bpow_gt_0 two p)).
rewrite Rmult_assoc /u -bpow_plus ; ring_simplify (-p + p)%Z.
rewrite Rmult_1_r (Rabs_pos_eq 2); lra.


case:(Rlt_le_dec (Rabs tl1) u)=> tl1ubu.
have {} e1ub: Rabs e1 <= /2 * u * u.
  rewrite /e1.
  have ->:  / 2 * u * u =  /2 * u * (pow ( -p)).
    rewrite /u ; ring.
  apply: error_le_half_ulp'=>//.
  rewrite -/u .
case:(Rle_lt_dec  (Rabs (xh * yl)) u) =>// h.
have : rnd_p u <= rnd_p (Rabs (xh * yl)).
apply/round_le; lra.
rewrite rnd_p_abs -/tl1 round_generic; try lra.
change (format (pow (-p))); apply/format_bpow; lia.
case:(Rlt_le_dec (Rabs (tl1 +tl2)) u).
move/ hFtl12=> Ftl12.
have e30: e3 = 0 by rewrite /e3 /cl2 round_generic //; ring.
apply/(Rlt_trans _ (5* (u * u) * (x * y))); last by apply/Rmult_lt_compat_r; lra.

move:rabs_eta; rewrite e30 Rabs_R0; lra.
move=> tl12lb.

  have hmant :  pow p <= Rabs (IZR (Mtl1 + Mtl2)) < pow (1 + p).
    move: tl12lb  tl12ub.
    rewrite  tl12Mu2.
    rewrite -/u; split=>//.
    apply/(Rmult_le_reg_r (u * u)) =>//. 
      suff ->:   pow p * (u * u) = u .
        rewrite -(Rabs_pos_eq (u * u)); try lra.
        by rewrite -Rabs_mult.
      by rewrite /u -!bpow_plus; ring_simplify(p +( -p + -p))%Z.
    apply/(Rmult_lt_reg_r (u*u)); first lra.
    suff->: pow (1 + p) * (u * u) = 2*u.
      by move: tl12ub0 ;  rewrite Rabs_mult (Rabs_pos_eq (u*u)); lra.
    rewrite /u -!bpow_plus; ring_simplify  (1 + p + (- p + - p))%Z.
    by rewrite bpow_plus Rmult_comm.

case:(Zeven_odd_dec   (Mtl1 + Mtl2)).
move/ hFtl12'=> Ftl12.
have e30: e3 = 0 by rewrite /e3 /cl2 round_generic //; ring.
apply/(Rlt_trans _ (5* (u * u) * (x * y))); last by apply/Rmult_lt_compat_r; lra.
move:rabs_eta; rewrite e30 Rabs_R0; lra.


move/Zodd_bool_iff  => Hodd.


(* cas odd *)
  case: (Zeven_ex (Mtl1 +Mtl2))=>M  Me.
  have {Me} ME : (Mtl1 + Mtl2)%Z = (2 * M + 1)%Z.
   by rewrite Me; rewrite Zeven.Zeven_odd_bool Hodd.
  (* rewrite tl12Mu2  ME => tl12lb. *)
  have hub: IZR (2*M) < IZR (2 * M + 1) <IZR (2*M+2) by split; apply/IZR_lt; lia.
  have nFs: ~ format (IZR (2 * M + 1)).
    apply: (generic_format_discrete _ _ _ M).
    rewrite /F2R /cexp -ME (mag_unique _ _ (1+p)).
      set e := fexp (1+p).
      rewrite /= /e /fexp.
      ring_simplify (1 + p -p)%Z.
      have->: pow 1 = 2 by [].
      rewrite -!mult_IZR ME !(Zmult_comm _ 2).
      have->: ((2 * (M + 1)) =  (2 * M + 2))%Z by ring.
      by [].
    by ring_simplify(1 + p - 1)%Z.

    (* rewrite bpow_plus;  *)
    (* rewrite plus_IZR; apply:(Rle_lt_trans _ _ _ (Rabs_triang _ _)). *)
    (*  have ->: pow 1 = 2 by [];  lra. *)
  have cexpf :  (ce (IZR (2 * M + 1)) = 1)%Z.
    rewrite /cexp /fexp (mag_unique _ _  (1 +p)); first ring.
      have->:  (1 + p - 1 = p)%Z by ring.
      by rewrite -ME.
    (* rewrite -ME plus_IZR bpow_plus; apply:(Rle_lt_trans _ _ _ (Rabs_triang _ _)). *)
    (* by have ->: pow 1 = 2 by []; lra. *)
  have rDN: round two  fexp Zfloor (IZR (2 * M + 1))  =  IZR (2 * M).
    rewrite /round /scaled_mantissa .
    rewrite cexpf (Zfloor_imp M) /F2R.
      set f := Float _ _ _.
      by rewrite Rmult_comm mult_IZR ; congr Rmult.
    move: hub.
    have -> : (2 * M + 2 = 2 * (M + 1))%Z by ring.
    rewrite !mult_IZR.
    have ->: pow(-1) = /2 by [].
    lra.
  have rUP :  round two  fexp Zceil (IZR (2 * M + 1))  =  IZR (2 * (M+ 1)).
    rewrite round_UP_DN_ulp // rDN ulp_neq_0 ?cexpf.
      by rewrite Zmult_plus_distr_r  Zmult_1_r plus_IZR.
    by apply/not_0_IZR; lia.

have e3E: Rabs e3 = u*u.
rewrite /e3 /cl2  tl12Mu2 ME.
 rewrite /u -bpow_plus round_bpow!bpow_plus -/u.
  case:(round_DN_or_UP two fexp (Znearest choice) (IZR (2 * M + 1)));


     rewrite ?rDN ?rUP => ->; rewrite plus_IZR.
 ring_simplify (IZR (2 * M) * (u * u) - (IZR (2 * M) + 1) * (u * u)).
rewrite Rabs_Ropp Rabs_pos_eq; try lra.
 rewrite !mult_IZR !plus_IZR.
ring_simplify(2 * (IZR M + 1) * (u * u) - (2 * IZR M + 1) * (u * u)).
by rewrite Rabs_pos_eq; lra.

(* cas non even *)

have res_inter: Rabs eta <=  55/10 * (u * u) by lra.
apply/(Rle_lt_trans _ (55 / 10 * (u * u)))=>//.
rewrite -[X in X<_]Rmult_1_r.
apply/Rmult_lt_compat_l; lra.
have hint:  5 * (u * u) * (x * y) <  55 / 10 * (u * u) * (x * y).
by apply/Rmult_lt_compat_r; lra.
case:(Rlt_le_dec (Rabs tl2) u)=> tl2ubu.
have {} e2ub: Rabs e2 <= /2 * u * u.
  rewrite /e2.
  have ->:  / 2 * u * u =  /2 * u * (pow ( -p)).
    rewrite /u ; ring.
  apply: error_le_half_ulp'=>//.
  rewrite -/u .
case:(Rle_lt_dec  (Rabs (xl * yh)) u) =>// h.
have : rnd_p u <= rnd_p (Rabs (xl * yh)).
apply/round_le; lra.
rewrite rnd_p_abs -/tl2 round_generic; try lra.
change (format (pow (-p))); apply/format_bpow; lia.
case:(Rlt_le_dec (Rabs (tl1 +tl2)) u).
move/ hFtl12=> Ftl12.
have e30: e3 = 0 by rewrite /e3 /cl2 round_generic //; ring.
move:rabs_eta; rewrite e30 Rabs_R0; lra.
move=> tl12lb.


have hmant :  pow p <= Rabs (IZR (Mtl1 + Mtl2)) < pow (1 + p).
move: tl12lb  tl12ub.

rewrite  tl12Mu2.
    rewrite -/u; split=>//.

apply/(Rmult_le_reg_r (u * u)) =>//. 
suff ->:   pow p * (u * u) = u .
rewrite -(Rabs_pos_eq (u * u)); try lra.
by rewrite -Rabs_mult.
by rewrite /u -!bpow_plus; ring_simplify(p +( -p + -p))%Z.
apply/(Rmult_lt_reg_r (u*u)); first lra.

suff->: pow (1 + p) * (u * u) = 2*u.
by move: tl12ub0 ;  rewrite Rabs_mult (Rabs_pos_eq (u*u)); lra.
rewrite /u -!bpow_plus. ring_simplify  (1 + p + (- p + - p))%Z.
by rewrite bpow_plus Rmult_comm.

case:(Zeven_odd_dec   (Mtl1 + Mtl2)).
move/ hFtl12'=> Ftl12.
have e30: e3 = 0 by rewrite /e3 /cl2 round_generic //; ring.
move:rabs_eta; rewrite e30 Rabs_R0; lra.

move/Zodd_bool_iff  => Hodd.


(* cas odd *)
  case: (Zeven_ex (Mtl1 +Mtl2))=>M  Me.
  have {Me} ME : (Mtl1 + Mtl2)%Z = (2 * M + 1)%Z.
   by rewrite Me; rewrite Zeven.Zeven_odd_bool Hodd.

  have hub: IZR (2*M) < IZR (2 * M + 1) <IZR (2*M+2) by split; apply/IZR_lt; lia.
  have nFs: ~ format (IZR (2 * M + 1)).
    apply: (generic_format_discrete _ _ _ M).
    rewrite /F2R /cexp -ME (mag_unique _ _ (1+p)).
      set e := fexp (1+p).
      rewrite /= /e /fexp.
      ring_simplify (1 + p -p)%Z.
      have->: pow 1 = 2 by [].
      rewrite -!mult_IZR ME !(Zmult_comm _ 2).
      have->: ((2 * (M + 1)) =  (2 * M + 2))%Z by ring.
      by [].
    by ring_simplify(1 + p - 1)%Z.

  have cexpf :  (ce (IZR (2 * M + 1)) = 1)%Z.
    rewrite /cexp /fexp (mag_unique _ _  (1 +p)); first ring.
      have->:  (1 + p - 1 = p)%Z by ring.
      by rewrite -ME.

  have rDN: round two  fexp Zfloor (IZR (2 * M + 1))  =  IZR (2 * M).
    rewrite /round /scaled_mantissa .
    rewrite cexpf (Zfloor_imp M) /F2R.
      set f := Float _ _ _.
      by rewrite Rmult_comm mult_IZR ; congr Rmult.
    move: hub.
    have -> : (2 * M + 2 = 2 * (M + 1))%Z by ring.
    rewrite !mult_IZR.
    have ->: pow(-1) = /2 by [].
    lra.
  have rUP :  round two  fexp Zceil (IZR (2 * M + 1))  =  IZR (2 * (M+ 1)).
    rewrite round_UP_DN_ulp // rDN ulp_neq_0 ?cexpf.
      by rewrite Zmult_plus_distr_r  Zmult_1_r plus_IZR.
    by apply/not_0_IZR; lia.

have e3E: Rabs e3 = u*u.
rewrite /e3 /cl2  tl12Mu2 ME.
 rewrite /u -bpow_plus round_bpow!bpow_plus -/u.
  case:(round_DN_or_UP two fexp (Znearest choice) (IZR (2 * M + 1)));


     rewrite ?rDN ?rUP => ->; rewrite plus_IZR.
 ring_simplify (IZR (2 * M) * (u * u) - (IZR (2 * M) + 1) * (u * u)).
rewrite Rabs_Ropp Rabs_pos_eq; try lra.
 rewrite !mult_IZR !plus_IZR.
ring_simplify(2 * (IZR M + 1) * (u * u) - (2 * IZR M + 1) * (u * u)).
by rewrite Rabs_pos_eq; lra.

(* cas non even *)

have res_inter: Rabs eta <=  55/10 * (u * u) by lra.
apply/(Rle_lt_trans _ (55 / 10 * (u * u)))=>//.
rewrite -[X in X < _]Rmult_1_r.
apply/Rmult_lt_compat_l; lra.
case:(@ex_mul  p tl1 ( -p)); try  apply/generic_format_round.
by rewrite -/u.

move=> Mtl1'.
rewrite -/u=> tl1M2u2.

case:(@ex_mul  p tl2 (-p)); try  apply/generic_format_round.
by rewrite -/u.
move=> Mtl2'; rewrite -/u=> tl2M2u2.
have tl12M2u2: tl1 + tl2 = IZR (Mtl1' + Mtl2') *( 2 * (u *u)).
 by rewrite tl1M2u2 tl2M2u2 plus_IZR; ring.
have Ftl12: format (tl1+tl2).


pose f := (Float two  (Mtl1' + Mtl2')  (1- p + - p)).

apply/(@FLX_format_Rabs_Fnum p _  f).
 rewrite tl12M2u2 /f /F2R.
suff ->:  (2 * (u * u)) = pow (1 - p + - p ) by [].
 by rewrite !bpow_plus  -/u -Rmult_assoc.
rewrite /f /=.
apply/(Rmult_lt_reg_r  (2 * (u * u))); first lra.
move:  tl12ub;  rewrite  tl12M2u2 Rabs_mult (Rabs_pos_eq (2 * (u * u))); try lra.
suff ->: 
pow p * (2 * (u * u)) = 2*u by [].
have ->: 2 = pow 1 by [].

rewrite /u -!bpow_plus; congr bpow; ring.
have e30: e3 = 0 by rewrite /e3 /cl2 round_generic //; ring.
move:rabs_eta; rewrite e30 Rabs_R0; lra.
Qed.

End DWTimesDW1.


Section DWTimesDW2.

(* Hypothesis ZNE : choice = fun n => negb (Z.even n). *)


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


Definition errorDWTDW11 xh xl yh yl  := let (zh, zl) := DWTimesDW11 xh xl yh yl in
  let xy := ((xh + xl) * (yh  + yl))%R in ((zh + zl) - xy).

Definition relative_errorDW11TFP xh xl yh yl  := let (zh, zl) := DWTimesDW11 xh xl yh yl  in
  let xy :=  ((xh + xl) * (yh  + yl))%R  in (Rabs (((zh + zl) - xy)/ xy)).


Lemma  boundDWTDW11_ge_0: 0 < 5 * (u * u).
Proof.
have upos:= upos .
have u2pos: 0 < u * u by apply:Rmult_lt_0_compat.
 lra.
Qed.

Notation double_word := (double_word  p choice).

Fact  DWTimesDW11_Asym_r xh xl yh yl: 
  (DWTimesDW11 xh xl (-yh ) (- yl)) =
     pair_opp   (DWTimesDW11 xh xl yh yl).
Proof.
 rewrite /DWTimesDW11 TwoProdE /=.
(* case=> <- <-. *)
rewrite  !(=^~Ropp_mult_distr_r, rnd_p_sym,  Fast2Sum_asym)  //.
have->: (- (xh * yh) - - rnd_p (xh * yh)) = -((xh * yh) - rnd_p (xh * yh)) by ring.
rewrite !(=^~Ropp_plus_distr, rnd_p_sym,  Fast2Sum_asym) ?Ropp_involutive //.

apply/rnd_p_sym.
Qed.

Fact  DWTimesDW11_Asym_l xh xl yh yl:
  (DWTimesDW11 (-xh) (-xl)  yh yl ) =  pair_opp   (DWTimesDW11 xh xl yh yl).
  Proof.
 rewrite /DWTimesDW11 TwoProdE /=.
rewrite !(=^~Ropp_mult_distr_l, rnd_p_sym,  Fast2Sum_asym) //.
have->: (- (xh * yh) - - rnd_p (xh * yh)) = -((xh * yh) - rnd_p (xh * yh)) by ring.
rewrite !(=^~Ropp_plus_distr, rnd_p_sym,  Fast2Sum_asym) ?Ropp_involutive //.
exact:rnd_p_sym.
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


(* DWTimesDW2 *)
Lemma DWTimesDW11_correct xh xl yh yl  (DWx:double_word xh xl) (DWy:double_word yh yl):
  let (zh, zl) := DWTimesDW11 xh xl yh yl in
  let xy := ((xh + xl) * (yh + yl))%R in
  Rabs ((zh + zl - xy) / xy) < 5* (u * u).
Proof.
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
  by rewrite rnd_p_sym {1}Exh.

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
  by rewrite rnd_p_sym  {1}Eyh.
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
have upos:= upos .
rewrite -/u in upos.
have ult1 : u < 1 by rewrite /u ; apply:bpow_lt_1; lia.
have u2pos: 0 < u * u by apply:Rmult_lt_0_compat.
have xh2': xh <= 2 by lra.
have yh2': yh <= 2 by lra.
have h0 : xh * yh <= 4 by nra.
have ylu:Rabs yl <= u by apply: (double_lpart_u DWy); try lia; lra.
have xlu:Rabs xl <= u by apply: (double_lpart_u DWx); try lia;  lra.
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
case:(@ex_mul p xh 0)=>//.
  change (1 <= Rabs xh); rewrite Rabs_pos_eq; lra.
  move=> mxh; rewrite Rmult_1_r -/u => xhE.
case:(@ex_mul p yh 0)=>//.
  change (1 <= Rabs yh); rewrite Rabs_pos_eq; lra.
  move=> myh; rewrite Rmult_1_r -/u => yhE.
have xhyhm4u2: xh*yh = IZR (mxh * myh) * (4* u^2).
  rewrite xhE yhE mult_IZR; ring.
case: (@ex_mul p ch 0)=>//.
    rewrite /ch; rewrite -rnd_p_abs.
    have ->: pow 0 = rnd_p 1.
    rewrite round_generic //.
      change (format (pow 0)); apply: generic_format_bpow; rewrite /fexp; lia.
    apply: round_le.
    rewrite Rabs_pos_eq; clear - xh1 y1; nra.
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
set tl := rnd_p (xh * yl).
pose e1 := tl - xh*yl.
have tlE: tl = xh*yl + e1 by rewrite  /e1 /tl; ring.
have xhylub: Rabs (xh*yl) <= 2*u - 2*(u*u).
  rewrite Rabs_mult Rabs_pos_eq; last lra.
  have->: 2 * u - 2 * (u * u) = (2 - 2 * u) * u by ring.
  apply:Rmult_le_compat; try apply: Rabs_pos; lra.

have tlub: Rabs tl <= 2*u -2* (u *u).
  rewrite /tl  -rnd_p_abs .
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
    by rewrite -rnd_p_abs ; apply:round_le.
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
  rewrite /cl3 -rnd_p_abs.
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
  rewrite /ch -rnd_p_abs ; apply/round_le; rewrite /= Rabs_pos_eq.
  + nra.
  + apply: Rmult_le_pos; lra.
    apply:generic_format_bpow; rewrite /fexp; lia.
have rnd_p_sym := rnd_p_sym.
rewrite (surjective_pairing (Fast2Sum _ _)).    
rewrite F2Sum_correct_abs=>//;
 try apply: generic_format_round; 
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
    apply: (Rle_lt_trans _ (5*  (u * u) / ((1 + u) * (1 + u)))); last first.
      have h: 1 < ((1 + u) * (1 + u)).
        rewrite -{1}[1]Rmult_1_l; apply:Rmult_lt_compat; lra.
      rewrite -[X in _ < X]Rmult_1_r.
      rewrite /Rdiv; apply:Rmult_lt_compat_l; try lra.
      rewrite -[X in _< X]Rinv_1.
      apply:Rinv_lt; lra.
    set d1 := (2 * (1 - u) * (1 - u)).
    set d2 :=((1 + u) * (1 + u)).
    set u2 := u * u.
    rewrite /Rdiv (Rmult_comm 8) (Rmult_comm 5) 2!Rmult_assoc.
    apply:Rmult_le_compat_l; rewrite /u2; try lra.
    suff : 0 < d1.
      suff: 0 < d2.
        move=> *.
        suff: 8 * d2 < 5 * d1.
          move=> *.
          apply: (Rmult_le_reg_r d1); try lra.
          rewrite Rmult_assoc Rinv_l; try lra.
          rewrite Rmult_1_r; apply: (Rmult_le_reg_r d2); try lra.
          have->: 5 * / d2 * d1 * d2 = 5 * d1 by field; lra.
          lra.
        rewrite /d2 /d1.
        ring_simplify.
        set ue2:= u^2.
        apply: (Rplus_lt_reg_r (-( 8 * ue2 + 16 * u +  8))).
        ring_simplify.
        have ue2pos:= (pow2_ge_0  u).
        clear - upos ue2pos  ult1 Hp5.
        suff : 36 * u < 2 by rewrite /ue2 ; lra.
        suff: u <= /32 by lra.
        change ( pow (-p) <= pow (-5)); apply bpow_le; lia.
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
have hsxhyh: xh + yh <= 3- 2*u by apply:l5_2F.

have tl1u: Rabs tl <= xh * u.
  rewrite /tl  -rnd_p_abs .
 suff -> : xh * u = rnd_p (xh * u).
 apply:round_le.
  rewrite Rabs_mult Rabs_pos_eq; try lra.
  apply:Rmult_le_compat_l; try lra.
  by rewrite /u round_bpow round_generic.
have stl12u: Rabs (tl + xl * yh)  <= 3 * u - 2* (u * u).
  apply: (Rle_trans _ _ _ (Rabs_triang _ _)).
  apply:(Rle_trans _ ((xh  + yh)* u)); last first.
    have ->: 3 * u - 2 * (u * u)= ( 3- 2*u) * u by ring.
    by  apply :Rmult_le_compat_r; lra.
  have tl2u : Rabs (xl * yh) <= yh * u. 
    rewrite Rabs_mult Rmult_comm Rabs_pos_eq; last lra.
    apply:Rmult_le_compat_l =>//; lra.
  apply:(Rle_trans _ ( xh * u + yh * u)); lra.
have F3u: format (3 * u).
    change (format (3 * pow (-p))); apply:formatS; first lia.
  apply:(@FLX_format_Rabs_Fnum _ _(Float two 3 0)).
    rewrite /F2R //=; ring.
    rewrite /=; apply:(Rlt_le_trans _ (pow 2)).
    have->: pow 2 = 4 by [].
    rewrite Rabs_pos_eq; lra.
  by apply: bpow_le; lia.
have cl2u: Rabs cl2 <= 3 * u .
  have ->: 3 * u = rnd_p (3*u) by rewrite round_generic.
   rewrite -rnd_p_abs; apply/round_le; lra.
have scl12u: Rabs (cl1 + cl2) <= 4*u.
  apply: (Rle_trans _ _ _ (Rabs_triang _ _)); lra.



(*   have ->: cl2 = (tl + xl * yh) + e3 by rewrite /e3; ring. *)
(*   apply: (Rle_trans _ _ _ (Rabs_triang _ _)); lra. *)
(* have scl12u: Rabs (cl1 + cl2) <= 4*u + 2* u *u. *)
(*   apply: (Rle_trans _ _ _ (Rabs_triang _ _)); lra. *)
have e4u: Rabs e4 <= 2 * u *u.
  rewrite /e4 /cl3.
  have-> :  2 * u * u = / 2 * pow (- p) * pow (2 - p).
    rewrite bpow_plus -/u /= IZR_Zpower_pos /=; field.
  apply/error_le_half_ulp'; try lia.
  by rewrite bpow_plus.
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
  suff:  3 * (u * u) < (5* Rabs ((xh + xl) * (yh + yl))) * (u * u) by lra.
  apply:Rmult_lt_compat_r; first lra.
  rewrite Rabs_pos_eq; last lra.
  apply: (Rlt_le_trans _ (5 *(( 1- u) *(1-u)))); last first.
    apply:Rmult_le_compat_l; try lra.
    apply:Rmult_le_compat; try lra.
      move/Rabs_le_inv: xlu => [xll xlu];  lra.
    move/Rabs_le_inv: ylu => [yll ylu];  lra.
  suff: u <= /8 by lra.
change (pow (-p) <= pow (-3)); by apply/bpow_le; lia.
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
  suff:  4 * (u * u) < (5 * Rabs ((xh + xl) * (yh + yl))) * (u * u) by lra.
  apply:Rmult_lt_compat_r; first lra.
  rewrite Rabs_pos_eq; last lra.
  apply: (Rlt_le_trans _ (5 *(( 1- u) *(1-u)))); last first.
    apply:Rmult_le_compat_l; try lra.
    apply:Rmult_le_compat; try lra.
      move/Rabs_le_inv: xlu => [xll xlu];  lra.
    move/Rabs_le_inv: ylu => [yll ylu];  lra.
  suff: u <= /16 by lra.
 change (pow (-p) <= pow (-4)); apply/bpow_le; lia.
have xpos: 0 < xh + xl by  move/Rabs_le_inv: xlu; lra.
have ypos: 0 < yh + yl by move/Rabs_le_inv: ylu; lra.
have xypos: 0 < (xh + xl) * (yh + yl) by apply/Rmult_lt_0_compat; lra.
rewrite Rabs_mult Rabs_Rinv; try lra.
rewrite [X in _ * / X  ] Rabs_pos_eq; try lra.
apply:(Rmult_lt_reg_r ((xh + xl) * (yh + yl))) =>//.
rewrite Rmult_assoc Rinv_l ?Rmult_1_r; try lra.
  set x := xh + xl.
set y := yh + yl.
have xh1pu2: 1 + 2* u <= xh.
  have : succ radix2 fexp 1 <= xh .
    apply/succ_le_lt =>//.
    by change (format (pow 0)); apply/format_bpow.
  rewrite succ_eq_pos; try lra.
  suff->: 2*u = ulp radix2 fexp 1 by [].
  rewrite /u u_ulp1; field.
have x1pu: 1+ u <= x by rewrite /x ;move/Rabs_le_inv: xlu; lra.
have yh1pu2: 1 + 2* u <= yh.
    have : succ radix2 fexp 1 <= yh .
    apply/succ_le_lt =>//.
    by change (format (pow 0)); apply/format_bpow.
  rewrite succ_eq_pos; try lra.
  suff->: 2*u = ulp radix2 fexp 1 by [].
  rewrite /u u_ulp1; field.
have y1pu: 1+ u <= y by rewrite /y; move/Rabs_le_inv: ylu; lra.
apply: (Rle_lt_trans _ (5 * (u* u))) =>//; last first.
rewrite -[X in X < _]Rmult_1_r.

apply:Rmult_lt_compat_l;  try lra.
clear -upos x1pu y1pu; nra.
have rabs_eta : Rabs eta <=  Rabs(xl * yl)  + Rabs e1  + Rabs e3 + Rabs e4.
  rewrite /eta.
  apply:(Rle_trans _ ( (Rabs (xl*yl))+ Rabs e1 + Rabs e3 + Rabs e4)); last lra.

   repeat (apply: (Rle_trans _ _ _ (Rabs_triang _ _)); 
     first apply : Rplus_le_compat_r); try lra.
  rewrite Rabs_Ropp ; lra.
have xlylub: Rabs (xl * yl) <= u*u.
  rewrite Rabs_mult; clear -ylu xlu upos.
  move : (Rabs_pos xl) (Rabs_pos yl); nra.

case:(Rle_lt_dec (2*u) (Rabs cl2))=> hcl2.
  case:(@ex_mul p cl2 (1-p)).
    + by rewrite bpow_plus -/u.
    + by  apply:generic_format_round.
  move=> Mcl2.
   have ->:  (2 * pow (- p) * pow (1 - p)) = 4*(u * u).
     rewrite bpow_plus -/u; ring_simplify.
     by have ->: pow 1 = 2 by []; ring.
  move=> cl2E.
have cl12M4u2: cl1 + cl2 = IZR ((mxh * myh) +Mcl2 - (mch * 2 ^ (p - 1))) * (4 * (u * u)).
rewrite /cl1 cl2E xhE yhE chm4u2 !plus_IZR  (mult_IZR mxh) opp_IZR.
ring.
have e40: e4 = 0. 
rewrite /e4 /cl3  round_generic ; first ring.

have : Rabs (cl1 + cl2) <= 4 * u by apply: (Rle_trans  _ _ _ (Rabs_triang _ _)); lra.
case ; last first.
have ->: 4*u = Rabs (4*u) by rewrite Rabs_pos_eq; lra.
case/Rabs_eq_Rabs => ->; try apply/generic_format_opp; change (format (pow 2 * pow (-p)));
rewrite -bpow_plus; apply/format_bpow; lia.
move:  cl12M4u2; set M := (_ -_)%Z.
move=> h1 h2.
    have hh: cl1+cl2 = (F2R (Float two M (2  -p -p))).
      rewrite  h1  /F2R; set exp := (2 - p -p)%Z.
      rewrite /=.
      congr Rmult.
      rewrite /exp !bpow_plus /u.
      have->:pow 2 = 4 by [].
      ring.
   apply:(FLX_format_Rabs_Fnum p hh).
set exp := (2 - p -p)%Z;      rewrite /=.
apply/(Rmult_lt_reg_r (4 * (u * u))); try lra.
rewrite -(Rabs_pos_eq ( (4 * (u * u)))); try lra.
rewrite -Rabs_mult -h1.
suff ->: pow p * Rabs (4 * (u * u)) = 4*u by [].
rewrite Rabs_pos_eq; try lra.
rewrite /u; have ->: 4 = pow 2 by [].
rewrite -!bpow_plus; congr bpow; ring.
move:rabs_eta; rewrite e40 Rabs_R0; lra.
have {}e3ub: Rabs e3 <= u *u.
  rewrite /e3.
  have->: u * u = /2 * u * (pow (1 -p)) by rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'=>//.
  rewrite bpow_plus  /= IZR_Zpower_pos /= -/u Rmult_1_r.

case: (Rle_lt_dec   (Rabs (tl + xl * yh)) (2 *u))=>// h.
suff : 2 * u <= Rabs cl2 by lra.
rewrite -rnd_p_abs.

have ->: 2*u = rnd_p (2 *u).
rewrite round_generic //.
change (format (pow 1 * pow (-p))).
rewrite -bpow_plus; apply/format_bpow; lia.
by apply/round_le; lra.
move:rabs_eta;  lra.
Qed.
End DWTimesDW2.


Section DWTimesDW3.
(* Hypothesis ZNE : choice = fun n => negb (Z.even n). *)


Hypothesis Hp5 : Z.le 5 p.

Local Instance p_gt_0_4_12 : Prec_gt_0 p.
exact: (Z.lt_le_trans _ 5 _ _ Hp5).
Qed.

Fact  Hp1_4_10 : (1 < p)%Z.
Proof. lia. 
Qed.


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


Lemma  boundDWTDW12_ge_0: 0 < 4 * (u * u).
Proof.
have upos:= upos.
have u2pos: 0 < u * u by apply:Rmult_lt_0_compat.
 lra.
Qed.


Notation double_word := (double_word  p choice).


Fact  DWTimesDW12_Asym_r xh xl yh yl  : 
  (DWTimesDW12 xh xl (-yh ) (- yl)) =
     pair_opp (DWTimesDW12 xh xl yh yl). 
Proof.
 rewrite /DWTimesDW12 TwoProdE /=.
rewrite  !(=^~Ropp_mult_distr_r, rnd_p_sym,  Fast2Sum_asym) //.
have->: (- (xh * yh) - - rnd_p (xh * yh)) = -((xh * yh) - rnd_p (xh * yh)) by ring.
by rewrite  !(=^~Ropp_plus_distr, rnd_p_sym,  Fast2Sum_asym) ?Ropp_involutive //; apply/rnd_p_sym.
Qed.

Fact  DWTimesDW12_Asym_l xh xl yh yl: 
  (DWTimesDW12 (-xh) (-xl)  yh yl ) =
       pair_opp (DWTimesDW12 xh xl yh yl). 
Proof.
 rewrite /DWTimesDW12 TwoProdE /=.
rewrite !(=^~Ropp_mult_distr_l, rnd_p_sym,  Fast2Sum_asym) //.
have->: (- (xh * yh) - - rnd_p (xh * yh)) = -((xh * yh) - rnd_p (xh * yh)) by ring.
by rewrite !(=^~Ropp_plus_distr, rnd_p_sym,  Fast2Sum_asym) ?Ropp_involutive //; apply/rnd_p_sym.
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

(* Notation double_lpart_u := (double_lpart_u Hp4). *)

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



(* DWTimesDW3 *)
Lemma DWTimesDW12_correct xh xl yh yl  (DWx:double_word xh xl) (DWy:double_word yh yl):
  let (zh, zl) := DWTimesDW12 xh xl yh yl in
  let xy := ((xh + xl) * (yh + yl))%R in
  Rabs ((zh + zl - xy) / xy) < 4 * (u * u).
Proof.
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
  by rewrite rnd_p_sym {1}Exh.
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
  by rewrite rnd_p_sym  {1}Eyh.
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
have upos:= upos.
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
  rewrite /tl0  -rnd_p_abs .
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
  rewrite /tl1  -rnd_p_abs .
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
  rewrite /cl2 -rnd_p_abs . 
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
  rewrite /cl3 -rnd_p_abs . 
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
have rnd_p_sym:= rnd_p_sym.
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
  rewrite /ch  -rnd_p_abs ; apply/round_le; rewrite /= Rabs_pos_eq; nra.
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
    suff : (u <=/32) by clear - upos u2pos ult1 ; nra.
    change (pow (-p) <= pow (-5)); apply:bpow_le ; lia. 
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
    suff : (u <=/16) by clear - upos u2pos ult1 ; nra.
    change (pow (-p) <= pow (-4)); apply:bpow_le ; lia.
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
    suff : (u <=/16) by clear - upos u2pos ult1 ; nra.
    change (pow (-p) <= pow (-4)); apply:bpow_le ; lia.
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
(*  xhyh2 : xh * yh <= 2
  xh1 : 1 < xh
  yh1 : 1 < yh *)

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
  rewrite  -rnd_p_abs .
  by apply: round_le.
(* a revoir , trop long *)
have ->: rnd_p (3 * u + / 2 * u ^ 3) = 3*u.
  have ->: (3 * u + / 2 * u ^ 3)= (3 + /2* u^2) *u by ring.
  rewrite /u round_bpow.
  congr Rmult.
apply/rbpowpuW'=>//; try lra.
  apply:(@FLX_format_Rabs_Fnum _ _(Float two 3 0)).
    rewrite /F2R //=; ring.
    rewrite /=; apply:(Rlt_le_trans _ (pow 2)).
    have->: pow 2 = 4 by [].
    rewrite Rabs_pos_eq; lra.
  by apply: bpow_le; lia.
split; first by clear ; nra.
rewrite ulp_neq_0; last lra.
rewrite /cexp /fexp (mag_unique_pos _ _ 2).
rewrite bpow_plus -/u; have ->: pow 2 = 4 by []; clear - upos ult1; nra.
rewrite bpow_plus; change ( 4* (/2) <= 3 < 4); lra.

move=> h5.
have hcl3 : Rabs (cl1 + cl2 ) <= 4*u.
  apply: (Rle_trans _ _ _ (Rabs_triang _ _)); lra.
clear cl3ub.
have cl3ub: Rabs cl3  <= 4*u.
  rewrite /cl3 -rnd_p_abs .
  suff ->: 4 * u = rnd_p (4*u ) by apply:round_le.
  rewrite round_generic //.
  have ->: 4* u = pow (2 -p) .
    rewrite bpow_plus /u //.
  apply: generic_format_bpow; rewrite /fexp; lia.
have {} e3ub: Rabs e3 <= 2 * u * u.
  have ->:  2 * u * u = / 2 * pow (- p) * pow (2 + (-p)).
  rewrite bpow_plus -/u /= IZR_Zpower_pos /=; field.
apply/error_le_half_ulp'=>//.
by rewrite bpow_plus.


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

 (* 2.6 *)
have th2_6:  Rabs (eta ) < 5* (u * u) * (x * y).
  apply:(Rle_lt_trans _  (5 * (u * u) + / 2 * (u * u * u))) =>//.

  apply:(Rlt_le_trans _  (5 * (u * u) *  ((1 + u) ^ 2))); last first.
    apply: Rmult_le_compat_l=>//.
    clear -upos; nra.
  have ->:  (1 + u) ^ 2 = 1 + 2*u + u^2 by ring.
  suff: / 2 * (u * u * u) <  10  * u^3 + 5* u ^ 4.
    lra.
  suff : 0< 19 * u^3 + 10 * u^4 by lra.
  clear -upos u2pos; nra.
(* 2.9 *)
case:(@ex_mul p xh 0)=>//.
  change (1 <= Rabs xh); rewrite Rabs_pos_eq; lra.
  move=> mxh; rewrite Rmult_1_r -/u => xhE.
case:(@ex_mul p yh 0)=>//.
  change (1 <= Rabs yh); rewrite Rabs_pos_eq; lra.
  move=> myh; rewrite Rmult_1_r -/u => yhE.
have xhyhm4u2: xh*yh = IZR (mxh * myh) * (4* u^2).
  rewrite xhE yhE mult_IZR; ring.
case: (@ex_mul p ch 0)=>//.
    rewrite /ch; rewrite  -rnd_p_abs .
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
    rewrite rnd_p_abs  -/cl2 round_generic; first lra.
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



End DWTimesDW3.



End Times.

