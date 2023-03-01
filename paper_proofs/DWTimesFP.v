(* Copyright (c)  Inria. All rights reserved. *)

Require Import Psatz ZArith Reals.

From Flocq Require Import Core Relative Sterbenz Operations Plus_error Mult_error.

Require Import mathcomp.ssreflect.ssreflect.
Require Import Bayleyaux.
Require Import DWPlus.
(* From Flocq Require Import Pff2Flocq.*)

Require Import F2Sum (* ToSum.*).


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

Lemma r1m2u (Hp1: (1 < p)%Z): rnd_p (1 - 2* u +  u * u )= 1 - 2* u.
Proof.
rewrite /u.
have ->: 1 = (pow p )* pow (-p) by rewrite -bpow_plus Zegal_left.
have ->: (pow p * pow (- p) - 2 * pow (- p) + pow (- p) * pow (- p))=
    (pow p - 2  + pow (- p) )* (pow (-p)) by ring.
rewrite round_bpow.
have->: pow p * pow (- p) - 2 * pow (- p) =(pow p - 2)*(pow (-p)) by ring.
congr (_ * _).
rewrite /round  /ulp /scaled_mantissa /cexp /fexp /= /F2R /=.
have hmag: (mag radix2 (pow p - 2 + pow (- p))) = p :>Z.
  apply:mag_unique_pos;rewrite /=; split.
    rewrite bpow_plus /= IZR_Zpower_pos /=.
    suff: 2 <= /2* (pow p) by move:(bpow_ge_0 two (-p)); lra.
    suff: pow 2   <=  (pow p).
      rewrite /= IZR_Zpower_pos /=; lra.
    by apply: bpow_le; lia.
  suff: pow (-p) < 2 by lra.
  have ->: 2 = pow 1 by [].
  apply: bpow_lt ; lia.
rewrite hmag Z.sub_diag Z.opp_0 /= !Rmult_1_r ZNE /Znearest.
set z := Zfloor _.
have ->: z= (2^p  -2)%Z.
  rewrite /z.
  apply: Zfloor_imp; rewrite plus_IZR !minus_IZR.
  rewrite (IZR_Zpower two); last lia.
  split; first (move: (bpow_ge_0 two (-p))).
    have Hp0 : (0 < p )%Z by lia.
    move:(bpow_lt_1 two Hp0); lra.
  have Hp0: (0 < p)%Z by lia.
  move:(bpow_lt_1 two Hp0); lra.
rewrite Rcompare_Lt //.
  rewrite minus_IZR (IZR_Zpower two) //; lia.
rewrite minus_IZR (IZR_Zpower two) //; try lia.
suff: pow (-p) < /2 by lra.
have -> : /2 = pow (-1) by [].
apply:bpow_lt ; lia.
Qed.


Section Theorem_4_1.

Hypothesis Hp4 : Z.le 4 p.

Local Instance p_gt_0_4 : Prec_gt_0 p.
exact: (Z.lt_le_trans _ 4 _ _ Hp4).
Qed.


Fact  Hp1_4 : (1 < p)%Z.
Proof. lia. 
Qed.

Notation Hp1 := Hp1_4.



Section multiple.

Lemma ex_mul z k : (pow k)  <= Rabs z  -> format z ->  
   exists (mz:Z), z = IZR mz * (2 * (pow (- p))  * (pow k)).
Proof.
move=>  hle Fz.
case:(ex_shift two fexp z (1 -p + k)) =>//.
rewrite /cexp /fexp.
suff:( 1 + k <= mag radix2 z)%Z by lia.

by apply:mag_ge_bpow; ring_simplify (1 + k -1)%Z.
move=>mz zE.
by exists mz; rewrite zE !bpow_plus.
Qed.


Lemma ex_mul_round  z k : (pow k)  <= Rabs z  -> 
   exists (mz:Z),rnd_p  z = IZR mz * (2 * (pow (- p))  * (pow k)).
Proof.
have Hp1 := Hp1.
move=>  hle.
case:(@ex_mul (rnd_p z) k).
rewrite ZNE -round_NE_abs -ZNE.
have ->: pow k = rnd_p (pow k).
rewrite round_generic //;apply:generic_format_bpow; rewrite /fexp; lia.
by apply:round_le.
apply: generic_format_round.
by move=> mz ->; exists mz.
Qed.

End multiple.

Notation F2Sum  a b :=  (Fast2Sum  p choice a b).
Notation F2Sum_sum  a b := (fst  (F2Sum a b)) .
Notation F2Sum_err a b  := (snd  (F2Sum a b)) .


Fact F2Sum_sumE a b: F2Sum_sum  a b = (rnd_p (a + b)).
Proof. by [] . Qed.


Fact F_F2Sum_err a b: format  (F2Sum_err a b).
Proof. by rewrite /=; apply:generic_format_round. Qed.



Definition Fast2Mult (a b : R) :=
  let pi := rnd_p (a * b) in
  let rho := rnd_p (a * b - pi) in
  (pi, rho).

Notation F2P_prod a b  :=  (fst (Fast2Mult a b)).
Notation F2P_error a b  :=  (snd (Fast2Mult a b)).

Hypothesis F2Mult_correct: 
  forall a b, a * b =  F2P_prod a b +  F2P_error a b.

Fact  F2P_errorE a b: F2P_error a b =  a * b - rnd_p (a * b).
Proof. rewrite {1}F2Mult_correct /=; ring. Qed.

Definition map_pair A B (f: A -> B) (p: A * A) := (f (fst p), f (snd p)).

Fact Fast2MultC a b: Fast2Mult a b = Fast2Mult b a.
Proof. by rewrite /Fast2Mult !(Rmult_comm a b). Qed.


Fact Fast2MultSl a b e : Fast2Mult (a * pow e) b =  map_pair (fun x => x * (pow e)) (Fast2Mult a b).
Proof. rewrite /Fast2Mult . 
have ->: (a * pow e * b) = a * b * (pow e) by ring. 
by rewrite round_bpow -Rmult_minus_distr_r round_bpow.
Qed.

Fact Fast2MultSr a b e : Fast2Mult a  (b * pow e) =  map_pair (fun x => x * (pow e)) (Fast2Mult a b).
Proof. by rewrite Fast2MultC  Fast2MultSl Fast2MultC.  Qed.

Fact Fast2Mult0f  b: Fast2Mult 0  b = (0, 0).
Proof.  by rewrite /Fast2Mult Rmult_0_l !(round_0, Rminus_0_r). Qed.

Fact Fast2Mult_asym_r a b :  Fast2Mult a (-b) = pair_opp (Fast2Mult a b).
Proof.
rewrite /Fast2Mult; have ->: a * (-b) = - (a * b) by ring.
rewrite ZNE round_NE_opp -ZNE.
have Rminus_opp x y : (x - - y) = (x + y) by ring.
rewrite  Rminus_opp /pair_opp /=.
have -> : a * b - rnd_p (a * b) = - ( -(a * b) + rnd_p (a * b)) by ring.
by rewrite  ZNE round_NE_opp -ZNE Ropp_involutive //.
Qed.

Fact Fast2Mult_asym_l a b :  Fast2Mult (-a) (b) = pair_opp (Fast2Mult a b).
Proof.
rewrite /Fast2Mult; have ->: (-a) * (b) = - (a * b) by ring.
rewrite ZNE round_NE_opp -ZNE.
have Rminus_opp x y : (x - - y) = (x + y) by ring.
rewrite  Rminus_opp /pair_opp /=.
have -> : a * b - rnd_p (a * b) = - ( -(a * b) + rnd_p (a * b)) by ring.
by rewrite  ZNE round_NE_opp -ZNE Ropp_involutive //.
Qed.

Fact  Fast2Mult_asym_l_aux  a b c : c = -a -> Fast2Mult c b = pair_opp (Fast2Mult a b).
Proof.
by move => ->; rewrite Fast2Mult_asym_l .
Qed.

Fact  Fast2Mult_asym_r_aux  a b d : d = -b -> Fast2Mult a d = pair_opp (Fast2Mult a b).
Proof.
by move => ->; rewrite Fast2Mult_asym_r.
Qed.




Parameter TwoProd : R -> R -> R * R.

Hypothesis TwoProdE : TwoProd = Fast2Mult. (* or Dekker's algorithm *)


Fact fstE A (a b : A) : fst (a, b) = a. Proof.  by []. Qed.
Fact sndE A ( a b:A):  snd (a, b) =  b. Proof. by []. Qed.
Lemma  boundDWTFP_ge_0: 0 <= 3/2*u^2 + 4*u^3.
Proof.
have upos:= upos p.
have u2pos: 0 < u * u by apply:Rmult_lt_0_compat.
have u3pos: 0 < u ^3.
  by rewrite /= Rmult_1_r;  apply:Rmult_lt_0_compat.
rewrite /=; lra.
Qed.


Section Algo7_pre.
Variables xh xl y:R.
Notation ch := (fst (TwoProd xh y)).
Notation cl1:= (snd (TwoProd xh y)).
Notation   cl2 := (rnd_p (xl * y)).
Notation th := (F2Sum_sum  ch cl2).
Notation tl1 := (F2Sum_err  ch cl2).
Notation tl2 := (rnd_p (tl1 + cl1)).
Notation zh := (F2Sum_sum   th tl2 ).
Notation zl := (F2Sum_err  th tl2 ).
Notation  xy := ((xh + xl) * y).


Definition  DWTimesFP := (zh, zl).
Notation double_word  := (double_word  p choice).
Hypothesis Fy: format y.
Hypothesis DWx: double_word xh xl.



Lemma DWTimesFP_correct_ypow (ypow: is_pow two y)  (xh0 : xh <> 0):
  ((Rabs ((zh + zl - xy) / xy) <= 3/2 * u ^ 2 + 4 * u ^ 3) /\ (double_word zh zl)).
Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
have Hp1: (1 < p)%Z by lia.
case:DWx =>[[Fxh Fxl] xhE].
case (ypow)=> ey yE.
have xlexh: Rabs (xl * y) <= Rabs (xh * y).
  rewrite !Rabs_mult; apply:Rmult_le_compat_r; first by apply:Rabs_pos.
  apply:(Rle_trans _ (/ 2 * ulp radix2 (FLX_exp p) xh)).
    by apply:dw_ulp=>//; apply:DWx.
  apply:(Rle_trans _ (ulp radix2 fexp xh)).
    move:(ulp_ge_0 radix2 fexp xh); lra.
  by apply:ulp_le_abs.
have FP xx (Fxx:format xx): format (xx*y).
  move: yE; rewrite -(Rabs_pos_eq (pow ey)); last by apply:bpow_ge_0.
  case/Rabs_eq_Rabs => ->.
    by apply: formatS =>//.
  by rewrite Ropp_mult_distr_r_reverse; apply/generic_format_opp/formatS.
have che: ch =  (xh * y).
    by rewrite TwoProdE /=  round_generic //; apply:FP.
  have cl10: cl1 = 0.
   by move: che; rewrite TwoProdE /= => che; rewrite   che Rminus_diag_eq // round_0.
    (* rewrite cl10. *)
    have cl2e: cl2 =  (xl * y).
      by rewrite  round_generic //; apply:FP.
  have the : th = xh * y.
    rewrite che cl2e /= -Rmult_plus_distr_r.
    move: yE; rewrite -(Rabs_pos_eq (pow ey)); last by apply:bpow_ge_0.
    case/Rabs_eq_Rabs => ->.
      by rewrite round_bpow -xhE.
    rewrite -Ropp_mult_distr_r ZNE round_NE_opp -ZNE round_bpow -xhE; ring.
  have tl1e : tl1 = xl * y.
    rewrite che cl2e F2Sum_correct_abs //; try apply:FP=>//.
      by move : the; rewrite !fstE che cl2e=>->; ring.
have f2s_corr: Fast2Sum_correct  p choice th tl2.
  apply:F2Sum_correct_abs=>//; try apply:generic_format_round.
  rewrite tl1e cl10 the Rplus_0_r round_generic //; last by apply:FP.
case: (F2Sum_correct_DW Hp1  f2s_corr) => [[Fzh Fzl] zE]; split=>//.
rewrite Rabs0; first exact: boundDWTFP_ge_0.
suff->: (zh + zl - xy) = 0 by rewrite /Rdiv Rmult_0_l.
have ->: zl = th + tl2 - zh by rewrite  f2s_corr.
have tl2e : tl2 =  xl * y.
  by rewrite tl1e cl10 Rplus_0_r round_generic //; apply:FP.
by rewrite the tl2e /=; ring.
Qed.

Lemma DWTimesFP_correct_pre   (xhb: 1 <= xh  <= 2 - 2 * u )  (yb:1 <= y <= 2 - 2 * u ) 
          ( ypow : ~ is_pow radix2 y ):
  ((Rabs ((zh + zl - xy) / xy) <= 3/2 * u ^ 2 + 4 * u ^ 3) /\ (double_word zh zl)).
Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
have Hp1 : (1 < p)%Z by lia.
move:(upos p); rewrite -/u=> upos.
have u1 : u < 1 by rewrite /u ; have ->: 1 =  pow 0 by []; apply:bpow_lt; lia.
have [[Fxh Fxl] Exh] := DWx.
case:(yb)=> y1 y2.
have {}y1: 1 + 2*u <= y.
  case/Rle_lt_or_eq_dec: y1 =>y1; first last.
    suff: (is_pow two y) by [].
    exists 0%Z; rewrite -y1 Rabs_pos_eq  /= ; lra.
  suff ->: 1 + 2 * u = succ two fexp 1.
    apply: succ_le_lt=>//.
    have ->: 1 = pow 0 by [].
    apply:generic_format_bpow; rewrite /fexp; lia.
  rewrite succ_eq_pos; try lra.
  rewrite /u u_ulp1; field.
have h16_0: 1+ 2*u <= xh * y <= 4 - 8*u + 4*u*u.
  split.
    rewrite -(Rmult_1_l (_ + _)).
    apply:Rmult_le_compat;  lra.
  have ->: 4 - 8 * u + 4 * u * u = (2 - 2*u) * (2 - 2*u) by ring.
  apply:Rmult_le_compat; lra.
have  che: ch =  rnd_p (xh * y ) by rewrite TwoProdE. 
have Fch: format ch by rewrite che ; apply:generic_format_round.
have ch0: ch <> 0.
  rewrite che; apply: round_neq_0_negligible_exp;rewrite ?negligible_exp_FLX //.
  by apply:Rmult_integral_contrapositive_currified; lra.
have r1m2u:= (r1m2u Hp1).
have: rnd_p (1 + 2 *u ) <= ch by rewrite che ; apply:round_le; lra.
rewrite round_generic; last first.
  rewrite /u u_ulp1 -Rmult_assoc Rinv_r ; last lra.
  rewrite Rmult_1_l -succ_eq_pos; try lra.
  apply: generic_format_succ.
  have -> : 1 = pow 0 by [].
  apply:generic_format_bpow; rewrite /fexp; lia.
move=> h16_lb.
have: ch <= rnd_p ( 4 - 8 * u + 4 * u * u) by rewrite che; apply:round_le; lra.
have->:  (4 - 8 * u + 4 * u * u)= (1 -2 * u + u * u)* (pow 2 ).
  rewrite /=IZR_Zpower_pos /=; ring.
rewrite round_bpow r1m2u=> h16_ub.
have xhypos: 0 < xh * y by clear -xhb yb; nra.
have cl1e :  cl1 = xh*y - ch. rewrite TwoProdE /=; rewrite round_generic //.
  by rewrite -Ropp_minus_distr; apply/generic_format_opp /mult_error_FLX.
have h17 :Rabs cl1 <= 2*u.
  apply:(Rle_trans _ (/2 * (ulp two fexp (rnd_p (xh * y))))).
    rewrite cl1e che.
    have ->: (xh * y - rnd_p (xh * y)) = -(rnd_p (xh * y) - xh * y) by ring.
    by rewrite Rabs_Ropp;apply:error_le_half_ulp_round.
  rewrite -che ulp_neq_0 // che /fexp bpow_plus -/u.
  set mg := mag _ _ .
  suff /(bpow_le two) mg2: (mg <= 2)%Z.
    apply:(Rle_trans _ (/2 * ((pow 2) * u))).
      apply:Rmult_le_compat_l; try lra.
      apply:Rmult_le_compat_r; lra.
    rewrite /= IZR_Zpower_pos /= ; lra.
  rewrite /mg; apply:mag_le_bpow; rewrite -che //.  
  rewrite Rabs_pos_eq.
    apply:(Rle_lt_trans _ ((1 - 2 * u) * pow 2)) =>//.
    rewrite -{2}(Rmult_1_l (pow 2)).
    apply:Rmult_lt_compat_r; first by apply: bpow_gt_0.
    lra.
  have-> : 0 = rnd_p 0  by rewrite round_0.
  rewrite che; apply: round_le.
  by apply:Rmult_le_pos; lra.
have xh0: xh <> 0 by lra.
have xlu: Rabs xl <= u.
  have:= (dw_ulp Hp1 DWx).
  suff ->:  / 2 * ulp radix2 fexp xh = u by [].
  rewrite ulp_neq_0 // /cexp /fexp  bpow_plus -/u -Rmult_assoc.
  suff -> : / 2 * (pow (mag radix2 xh)) = 1 by ring.
  suff ->:  ((mag radix2 xh)  = 1%Z :>Z).
    rewrite /= IZR_Zpower_pos /=; field.
  apply:mag_unique_pos.
  rewrite /= IZR_Zpower_pos /=; split;lra.
have Fcl2: format cl2 by apply:generic_format_round.
pose error := (zh + zl - xy).
pose e1 :=  (xl * y) -cl2.
pose e2 := tl1 + cl1 - tl2.
rewrite  /Rdiv Rabs_mult  -/error.
have DWz: Rabs tl2 <= Rabs th -> double_word zh zl.
move=>h; have: (Fast2Sum_correct  p choice th tl2).
apply:F2Sum_correct_abs=>  //; try apply:generic_format_round.
move/(F2Sum_correct_DW Hp1).
 by case=> [[Fzh Fzl] zE].
have error_correct:  Rabs cl2 <= Rabs ch -> Rabs tl2 <= Rabs th -> error =  -(e1 + e2).
 move=> h1 h2.
 case:(DWz h2)=> [[Fzh Fzl]] zE.
 rewrite /error /e1 /e2 !F2Sum_correct_abs //; try apply:generic_format_round.
 set ff := F2Sum_sum _ _.
 ring_simplify (ff + (th + rnd_p (ch + cl2 - th + cl1) - ff ) -xy ).
 lra.
 by move:(h2); rewrite F2Sum_correct_abs.
case:(Req_dec xl 0)=>xl0.
  have cl20: cl2 = 0 by rewrite  xl0 Rmult_0_l round_0.
  have e10: e1 = 0 by rewrite /e1 cl20 xl0; ring.
  have tl10: tl1 = 0.
    by rewrite /tl1 cl20 Fast2Sumf0. 
  have e20: e2 = 0 .
  rewrite /e2  tl10 Rplus_0_l round_generic TwoProdE; first ring.
  by apply: generic_format_round.
  
  have htl2th: Rabs tl2 <= Rabs th.
  rewrite  tl10 cl20 Rplus_0_l Fast2Sumf0 // !round_generic //=.
  rewrite (Rabs_pos_eq ch); lra.
     by rewrite TwoProdE; apply: generic_format_round.

  rewrite error_correct ?e10 ?e20 ?Rplus_0_l ?Rabs_R0 //.
    rewrite Rabs_Ropp Rabs_R0 Rmult_0_l; split ; first by  move: boundDWTFP_ge_0; lra.
    by apply:   DWz.
  by rewrite cl20  Rabs_R0; exact:Rabs_pos.
have cl20: cl2 <> 0.
 apply: round_neq_0_negligible_exp;rewrite ?negligible_exp_FLX //.
  by apply:Rmult_integral_contrapositive_currified; lra.
have:Rabs cl2 <= 2 * u - 2* u * u.
  have ->:  2 * u - 2 * u * u = rnd_p ( 2 * u - 2 * u * u).
  rewrite round_generic //.
    have ->: (2 * u - 2 * u * u) = (pow p - 1) * pow (1 +  (-p + -p)).
      rewrite !bpow_plus /= IZR_Zpower_pos /= /u.
      rewrite Rmult_minus_distr_r.
      congr (_ -_); try ring.
      rewrite (Rmult_comm (pow p)) !Rmult_assoc -bpow_plus.
      ring_simplify(-p + p)%Z; rewrite /=; ring.
    apply:formatS =>//.
    apply:generic_format_FLX.
    apply:(FLX_spec _ _ _ (Float two (2 ^ p -1) 0)).
      rewrite /F2R /= minus_IZR (IZR_Zpower two); try ring; lia.
    rewrite /= Z.abs_eq; first lia.
    suff : (1 <= 2^ p )%Z by lia.
    have ->: (1 = 2 ^ 0 )%Z by [].
    apply:Z.pow_le_mono_r; lia.
  rewrite /cl2.
  rewrite ZNE -round_NE_abs -ZNE.
  apply:round_le.
  rewrite Rabs_mult.
  have ->:  2 * u - 2 * u * u = u * (2 - 2*u) by ring.
  apply:Rmult_le_compat =>//; try apply: Rabs_pos.
  rewrite Rabs_pos_eq; lra.
move=> h18.
have h19_0: Rabs e1 <= u * u.
  rewrite /e1 -Ropp_minus_distr Rabs_Ropp.
  apply:(Rle_trans _ (/2 * (ulp two fexp (rnd_p (xl * y))))).
    by apply: error_le_half_ulp_round.
  rewrite ulp_neq_0 // /cexp /fexp bpow_plus /=.
  have : pow (mag radix2 cl2) <= pow (1 -p).
    apply/bpow_le/ mag_le_bpow =>//.
    rewrite bpow_plus -/u /= IZR_Zpower_pos /=.
    suff: 0 < u * u by lra.
    by rewrite /u -bpow_plus; apply:bpow_gt_0.
  have h2:  0 <= /2 by lra.
  move/(Rmult_le_compat_l  (/2) _ _ h2).
  rewrite bpow_plus /= IZR_Zpower_pos /= Rmult_1_r  -Rmult_assoc Rinv_l ?Rmult_1_l ; try lra.
  move/(Rmult_le_compat_r (pow (-p)) _ _ (bpow_ge_0 two (-p))).
  have ->: (round radix2 (fun e : Z => (e - p)%Z) 
                  (Znearest choice) (xl * y)) = cl2 by [].
  
  rewrite /u. lra.
have F2Sc: th + tl1 = ch + cl2.
  rewrite F2Sum_correct_abs //;try lia;  first ring.
  rewrite (Rabs_pos_eq ch); last lra.
  suff: 2 * u - 2 * u * u <= 1 + 2 * u by lra.
  suff: 0 <= u * u by lra.
  by apply: Rmult_le_pos; lra.
have h19: 1 <= th <= 4 - 8*u.
  have-> : 1 = rnd_p (1 + 2 * u * u).
    have r1: 1 = rnd_p (pow 0).
     rewrite  round_generic //; apply: generic_format_bpow; rewrite /fexp; lia.
    apply:Rle_antisym.
      rewrite {1}r1; apply:round_le; rewrite /=.
      suff: 0 <= u * u by lra.
      by apply: Rmult_le_pos; lra.
    have h1: 1 = rnd_p  (1 + pow(-p) / 2) by rewrite r1pu2.
    rewrite [X in _ <= X] h1.
    apply:round_le.
    suff: (pow 2) * u * u <= pow (- p) by rewrite /= IZR_Zpower_pos /=; lra.
    rewrite /u -!bpow_plus; apply: bpow_le; lia.
  have ->: 4 - 8 * u = rnd_p (4 -6*u - 2 * u * u).
    have->: 4 - 6 * u - 2 * u * u = (1 -2* u  +/ 2 *u * (1  - u)) * (pow 2) 
    by rewrite /= IZR_Zpower_pos /=; field.
    rewrite round_bpow.
    have ->:  4 - 8 *u = (1 - 2 *u) * (pow 2) by rewrite /= IZR_Zpower_pos /=;ring.
    congr (_ *_).
    rewrite /u.
    have->: (1 -2 * u) = (pow p -2 )* pow (-p).
      by rewrite Rmult_minus_distr_r -bpow_plus Z.add_opp_diag_r /= /u.
    have ->: (pow p - 2) * pow (- p) + / 2 * pow (- p) * (1 - pow (- p))= 
          ((pow p - 2)  + / 2 *  (1 - pow (- p)))* (pow (-p)) by ring.
    rewrite round_bpow; congr Rmult.
    rewrite /round  /ulp /scaled_mantissa /cexp /fexp /= /F2R /=.
    have hmag: (mag radix2 (pow p - 2 + / 2 * (1 - pow (- p)))) =  p :>Z.
      apply:mag_unique_pos;rewrite /=; split.
        rewrite bpow_plus /= IZR_Zpower_pos /=.
        suff:3 +  (pow (-p))<=   (pow p) by lra.
        apply:(Rle_trans _ (pow 2)).
          rewrite /= IZR_Zpower_pos /=. 
          suff:pow (- p) < 1 by lra.
          apply:bpow_lt_1; lia.
        apply : bpow_le ; lia.
      suff: (1 - (pow (-p))) < 4 by lra.
      move:(bpow_ge_0 two (-p)); lra.
    rewrite hmag  Z.sub_diag Z.opp_0 /= !Rmult_1_r ZNE /Znearest.
    set z := Zfloor _.
    have ->: z= (2^p  -2)%Z.
      rewrite /z.
      apply: Zfloor_imp; rewrite plus_IZR !minus_IZR.
      rewrite (IZR_Zpower two); last lia.
      split; first (move: (bpow_ge_0 two (-p))).
        have Hp0 : (0 < p )%Z by lia.
        move:(bpow_lt_1 two Hp0); lra.
      have Hp0: (0 < p)%Z by lia.
      suff:   (1 - pow (- p)) < 2 by lra.
      move:(bpow_ge_0 two (-p)); lra.
    rewrite Rcompare_Lt //.
      rewrite minus_IZR (IZR_Zpower two) //; lia.
    rewrite minus_IZR (IZR_Zpower two) //; try lia.
    suff: 1 - pow (-p) < 1 by lra.
    move:(bpow_gt_0 two (-p)); lra.
  move/Rabs_le_inv :  h18 => [h18l h18u].
  split; apply : round_le.
    lra.
  move: h16_ub; rewrite /= IZR_Zpower_pos /=; lra.
have : Rabs tl1 <= /2 * (ulp two fexp ( 4 - 8 *u)).
  have ->: tl1 = ch + cl2 - th by lra.
  rewrite /th -Ropp_minus_distr Rabs_Ropp.
  rewrite /tl1.
  apply:(Rle_trans _  ( / 2 * ulp two fexp  th)).
    by rewrite /th; apply:error_le_half_ulp_round.
  apply:Rmult_le_compat_l; try lra.
  apply:ulp_le.
  rewrite !Rabs_pos_eq; try lra.
have ->:  (ulp radix2 fexp (4 - 8 * u))= 4 * u.
  rewrite ulp_neq_0 /cexp /fexp.
    have -> :  (mag radix2 (4 - 8 * u)) =  2%Z  :>Z.
      apply:mag_unique_pos.
      rewrite !bpow_plus /= !IZR_Zpower_pos /= !Rmult_1_r.
      split; move:upos; lra.
    by rewrite bpow_plus /= /u IZR_Zpower_pos /=.
  suff:  (1 - 2*u)<> 0 by lra.
  have -> : 1 = pow 0 by [].
  have->: 2 * u = pow (1 -p).
    by rewrite bpow_plus /u /=  IZR_Zpower_pos  /=.
  move=> h.
  have : pow 0 = pow (1 -p) by lra.
  move/(bpow_inj two); lia.
have->:/2 * ( 4 * u) = 2 * u  by field.
move=> h20.
have htl1cl1: Rabs(tl1 + cl1 ) <=  4*u .
  apply:(Rle_trans _   (Rabs tl1 + Rabs cl1)); first exact:Rabs_triang.
  lra.
have : Rabs tl2 <= rnd_p (4 * u).
  rewrite  ZNE -round_NE_abs -ZNE.
  by apply:round_le.
rewrite (round_generic _ _ _ (4 * u)); last first.
  have->: (4 * u) = pow ( 2 -p).
    by rewrite bpow_plus /= IZR_Zpower_pos /= /u.
  apply:generic_format_bpow; rewrite /fexp; lia.
move => h21.
have:  Rabs e2 <= 2*u*u.
  rewrite /e2.
  rewrite -Ropp_minus_distr Rabs_Ropp.
move:htl1cl1; have ->: 4*u = pow (2 -p) by rewrite /u bpow_plus /= IZR_Zpower_pos /=.
  have->:  2 * u * u = /2 * u * pow (2 -p).
    rewrite /u bpow_plus /= !IZR_Zpower_pos /=; field.
  by apply: error_le_half_ulp'; first lia.
move=> h220. 
(*  Rabs tl2 <= Rabs th *)
have Rabs1: Rabs tl2 <= Rabs th.
  rewrite (Rabs_pos_eq th); last lra.
  apply:(Rle_trans _ (4 *  u)) =>//.
  apply:(Rle_trans _ 1); lra.
split; last by apply:DWz.
 (*  Rabs cl2 <= Rabs ch *)
have Rabs2 : Rabs cl2 <= Rabs ch.
  apply:(Rle_trans _ (1 + 2 * u)); try lra.
    apply:(Rle_trans _ (2 * u - 2 * u * u))=>//.
    have : 0 < u * u by apply:Rmult_lt_0_compat.
    lra.
  by rewrite Rabs_pos_eq; lra.
rewrite error_correct //.
have he :   Rabs (e1 + e2) <= 3* u *u.
  apply:(Rle_trans _   (Rabs e1 + Rabs e2)); first exact:Rabs_triang; lra.
case:(Rle_lt_dec 2 (xh * y))=> xhy2.
  have: 2 - 2*u <= ((xh + xl) * y).
    apply:(Rle_trans _ (xh * (1 -u) * y)).
      suff: 2 * (1 -u) <= xh * y * (1 -u) by lra.
      apply: Rmult_le_compat; lra.
    suff: (-u) * xh * y <= xl * y by lra.
    apply: Rmult_le_compat_r; first lra.
    suff: (-xl) * 1 <= u * xh by lra.
    case:(Rle_lt_dec 0 xl)=> xllt0.
    apply:(Rle_trans _ 0); first lra; apply: Rmult_le_pos ; lra.
      apply: Rmult_le_compat; try lra.
    move: xlu; rewrite -Rabs_Ropp Rabs_pos_eq; lra.
  have h: 0 < 2 - 2 * u by lra.
  move=> h0.
  have h1: 0 < (xh + xl) * y  by lra.
  move/(Rinv_le_contravar _ _ h):h0.
  rewrite Rabs_Rinv; try lra.
  move=> h0.
  apply: (Rle_trans _ ( 3 * u * u /  (2 - 2 * u))).
    rewrite /Rdiv; apply:Rmult_le_compat ; try lra; try apply: Rabs_pos.
    + rewrite Rabs_pos_eq; try lra.
      by apply/Rlt_le /Rinv_0_lt_compat.
    + by rewrite Rabs_Ropp; lra.
    by rewrite Rabs_pos_eq; lra.
  rewrite -!Rmult_assoc !Rmult_1_r.
  have ->: (2 - 2 * u) = 2 * (1 -u) by ring.
  rewrite /Rdiv.
  have->:3 * u * u * / (2 * (1 - u)) =  3 * / 2 * u * u * / (1 -u) by field; lra.
  suff: 0 <=  3 * / 2 * u * u * ( 1 - / (1 - u)) +  4 * u * u * u by lra.
  apply:(Rmult_le_reg_r (1 -u)); try lra.
  field_simplify; try lra.
  (* rewrite /Rdiv Rmult_0_l. *)
  suff : 0 <= (-8 * u ^ 4 + 5 * u ^ 3) by lra.
  have->: -8 * u ^ 4 + 5 * u ^ 3 = (-8  *u + 5) * (u ^ 3) by ring.
  apply:Rmult_le_pos; try lra.
  by rewrite /= Rmult_1_r; repeat (apply:Rmult_le_pos; try lra).
have ch2: Rabs ch <= 2.
  rewrite Rabs_pos_eq; try lra.
   have ->: 2 = pow 1 by rewrite /= IZR_Zpower_pos /=.
  have ->: pow 1 = rnd_p (pow 1).
    by rewrite round_generic //;  apply: generic_format_bpow; rewrite /fexp; lia.
    rewrite TwoProdE.
    apply:round_le; rewrite  /= IZR_Zpower_pos /=; lra.
    have cl1u: Rabs  cl1 <= u.
    have ->: cl1 = xh * y - rnd_p (xh * y)
         by rewrite  {1}F2Mult_correct TwoProdE /=; ring.
  
  rewrite  -Ropp_minus_distr  Rabs_Ropp /u.
  have ->: pow (- p) = / 2 * pow (- p) * pow  1.
    rewrite /=  IZR_Zpower_pos /=; field.
  apply: error_le_half_ulp'; first lia.
  rewrite /= IZR_Zpower_pos /= Rabs_pos_eq; lra.
have: Rabs th <= rnd_p (2 + 2*u -2 *u *u).
  rewrite ZNE -round_NE_abs -ZNE; apply:round_le.
  apply: (Rle_trans _ (Rabs ch + Rabs cl2)); first by apply:Rabs_triang.
  lra.
rewrite Rabs_pos_eq; last lra.
have-> :  rnd_p (2 + 2 * u - 2 * u * u) = 2.
  have->: (2 + 2 * u - 2 * u * u) = (1 + u - u * u) * pow 1 by rewrite /= IZR_Zpower_pos /= ;ring.
  rewrite round_bpow /= IZR_Zpower_pos /= .
  suff -> :  rnd_p (1 + u - u * u) = 1 by ring.
  apply:Rle_antisym.
    have h1e: 1 = rnd_p (1 + u) by rewrite r1pu.
    rewrite [X in _ <= X]h1e.
    apply:round_le; suff: 0 <= u * u by lra.
    apply:Rmult_le_pos; lra.
  have {1}-> : 1 = rnd_p 1.
    have -> : 1 = pow 0 by []. 
    rewrite round_generic //.
    apply:generic_format_bpow; rewrite /fexp; lia.
  apply: round_le.
  have -> : 1 + u - u * u = 1 + u * (1 -u) by ring.
  suff: 0 <= u * (1 - u) by lra.
  apply:Rmult_le_pos ; lra.
move=> th2.
case/Rle_lt_or_eq_dec: th2 => th2; last first.
  have h240: 2 - 4*u -3* u *u <= (xh + xl) * y.
    have ->: ((xh + xl) * y) = th + tl2 - error.
      rewrite /error !F2Sum_correct_abs //; try apply:generic_format_round.
        ring.
      move: Rabs1.
      rewrite F2Sum_correct_abs //; try apply:generic_format_round;
        lra.
    move/Rabs_le_inv : h21.
    have:Rabs (- error) <= 3 * u *u by rewrite Rabs_Ropp error_correct // Rabs_Ropp.
    move/Rabs_le_inv.
    move/Rabs_le_inv : he.
    lra.
  have xypos: 0 < ((xh + xl) * y).
    apply:Rmult_lt_0_compat =>//; try lra.
    move/Rabs_le_inv: xlu; lra.
  move/Rinv_0_lt_compat:xypos=> xyposi.
  rewrite Rabs_Ropp; apply:(Rle_trans _ ( 3 * u * u / (2 -  4 * u - 3 * u * u))).
    rewrite /Rdiv; apply:Rmult_le_compat; (try apply: Rabs_pos)=>//.
    rewrite Rabs_pos_eq; try lra.
    apply:Rinv_le_contravar; try lra.
    suff: 2* u + 2* u * u < 1 by lra.
    apply:(Rle_lt_trans _ (1/2 + 1/8)).
      have up2: u <= (pow (-2)) by rewrite /u; apply: bpow_le; lia.
      rewrite /= IZR_Zpower_pos /= Rmult_1_r in up2.
      apply:Rplus_le_compat ; try lra.
      have -> : 1 /8 = 1/2 * 1/4 by field.
      apply:Rmult_le_compat; lra.
    apply:( Rmult_lt_reg_r 8);lra.
  have u16: u <= /16.
    suff : 16 * u <= 1 by lra.
    have -> : 1 = pow 0 by [].
    have -> : 16 = pow 4 by [].
    rewrite /u -bpow_plus; apply:bpow_le; lia.
  rewrite Rmult_assoc.
  set  u3 := (u * (u * u)).
  set  u2 := (u * u).
  apply: (Rmult_le_reg_r 2); try lra.
  have->:  3 * u2 / (2 - 4 * u - 3 * u2) * 2 =  6 * u2 / (2 - 4 * u - 3 * u2) by lra.
  have ->:  (3 * / 2 * u^2 + 4 * u^3) * 2 = 3 * u^2 + 8 * u^3 by field.
  have dpos : 0 <  (2 - 4 * u - 3 * u2).
    suff: 4 * u + 3 * u2 < 2 by lra.
    have u2_2: u2 <= /16 * /16.
      rewrite /u2; apply:Rmult_le_compat; lra.
    apply: (Rle_lt_trans _ (4 * /16 + 3 * /16 */16)).
      apply: Rplus_le_compat; lra.
    have ->: 2 = 1 +1 by ring.
    by apply:Rplus_lt_compat; lra.
  rewrite /Rdiv; apply: (Rmult_le_reg_r  (2 - 4 * u - 3 * u2)) =>//.
  rewrite Rmult_assoc Rinv_l; last lra.
  rewrite Rmult_1_r.
  have->: (3 * u^2 + 8 * u^3) * (2 - 4 * u - 3 * u2) = 
  6*u^2 + 16 * u^3 - 12 * u^2 * u -32 * u^3 * u -9* u^2 * u^2 - 24 * u^3 * u^2 by rewrite /u2;  ring.
  rewrite /u2.
  suff: 0 <= 16 * u^3 - 12 * u^2 * u - 32 * u^3 * u - 9 * u^2 * u^2 - 24 * u^3 * u^2 by lra.
  rewrite  -!Rmult_assoc !Rmult_1_r.
  have ->: 16 * u * u * u - 12 * u * u * u = 4 * u * u * u by ring.
  have ->: 4 * u * u * u - 32 * u * u * u * u - 9 * u * u * u * u - 24 * u * u * u * u * u = 
    (4 - 41 *u - 24 * u * u) *( u * u * u) by ring.
  repeat (apply:Rmult_le_pos; try lra).
  suff: 41 * u + 24 * u * u <= 4 by lra.
  apply:(Rle_trans _ (48 * u + 24 * u * u)) ; try lra.
  have: 48 * u <= 3  by lra.
  suff : 24 * u * u <= 1 by lra.
  suff : u * u <= /24 by lra.
  have -> : /24 = /4 * /6 by field.
  apply : Rmult_le_compat; lra.
(* th < 2*)
have {} h20 : Rabs tl1 <= u.
  have ->: tl1 = ch + cl2 - th by lra.
  rewrite /th -Ropp_minus_distr Rabs_Ropp.
  rewrite /tl1.
  apply:(Rle_trans _  ( / 2 * ulp two fexp  th)).
    by rewrite /th; apply:error_le_half_ulp_round.
  rewrite ulp_neq_0 ; try lra.
  rewrite /cexp /fexp bpow_plus.
  rewrite -(Rmult_1_l u) /u -Rmult_assoc;   apply:Rmult_le_compat_r.
    by apply:bpow_ge_0.
  have -> : 1 = /2 * 2 by field.
  apply:Rmult_le_compat; try lra.
    by apply:bpow_ge_0.
  have ->: 2 = pow 1 by [].
  apply:bpow_le.
  apply:mag_le_bpow.
  change (th <> 0); lra.
  change (Rabs th < 2); rewrite Rabs_pos_eq; lra.
have h21': Rabs tl2 <= 2 * u.
  rewrite /tl2.
  rewrite ZNE  -round_NE_abs -ZNE.
  have -> : 2 * u = rnd_p ( 2 * u) .
    rewrite round_generic //.
    suff ->: 2 * u = pow (1 -p) by apply:generic_format_bpow; rewrite /fexp ; lia.
    by rewrite /u bpow_plus.
  apply/round_le/(Rle_trans _ ((Rabs tl1) + (Rabs cl1))); first by  apply:Rabs_triang.
  lra.
have h220':  Rabs e2 <= u * u.
  rewrite /e2 /tl2 -Ropp_minus_distr Rabs_Ropp.
  have ->: u * u = /2* u * (pow (1  - p)).
    rewrite bpow_plus /= IZR_Zpower_pos /= /u; field.
  apply: error_le_half_ulp'; try lia.
  apply:(Rle_trans _ ((Rabs tl1) + (Rabs cl1))); first by  apply:Rabs_triang.
  rewrite bpow_plus -/u;have ->: pow 1 = 2 by [].
  lra.  
have fub: Rabs error <= 2 * u *u.
  rewrite error_correct // Rabs_Ropp; apply: (Rle_trans _ ((Rabs e1) + (Rabs e2))); 
    first by  apply:Rabs_triang.
  lra.
rewrite Rabs_Ropp.
have eub:   Rabs ( (e1 + e2)) <= 2*u*u.
  apply:(Rle_trans _ (Rabs e1 + Rabs e2)); first apply:Rabs_triang.
  lra.
have eub': Rabs (e1 + e2) <= (3* /2) * u * u.
  case:(Rlt_le_dec (Rabs cl2) u)=>cl2_u.
    have e1_u2:  Rabs e1 <= /2* u * u.
      rewrite /e1 /cl2 -Ropp_minus_distr Rabs_Ropp Rmult_assoc.
      suff hucl2: ulp two fexp cl2 <= u*u.
        apply:(Rle_trans _ ( / 2 * ulp two fexp  (rnd_p (xl * y)))).
          by apply:error_le_half_ulp_round.
        rewrite -/cl2; lra.
      rewrite ulp_neq_0 // /cexp /fexp bpow_plus /u.
      apply Rmult_le_compat_r.
      apply:bpow_ge_0.
      apply:bpow_le.
      by apply: mag_le_bpow.
    apply:(Rle_trans _ (Rabs e1 + Rabs e2)); first apply:Rabs_triang; lra.
  suff ->: e2 = 0.
    rewrite Rplus_0_r; have u2pos: 0 < u * u by apply: Rmult_lt_0_compat.
    lra.
  rewrite /e2 [X in _ - X]round_generic;  first ring.
  rewrite /u in cl2_u.
  have [mcl2 cl2E]:= (ex_mul (-p) cl2_u Fcl2).
  have ch_u: pow (- p) <= Rabs ch by apply:(Rle_trans _ (Rabs cl2)).
  have [mch chE]:= (ex_mul (-p) ch_u Fch).
  have chcl2m: ch + cl2 = IZR ( mch + mcl2) * (2 * pow (- p) * pow (- p)).
    rewrite plus_IZR; lra.

  have  chcl2m':ch + cl2  =  @F2R two  {| Fnum := ( mch + mcl2) ; Fexp := (1 - p - p) |}.
    set e := (1 - p - p)%Z.
    by rewrite /F2R /= chcl2m /e !bpow_plus.
  have [mth thE]:=(round_repr_same_exp two fexp (Znearest choice)  (mch + mcl2) (1 - p - p)).
  move:thE; rewrite   -chcl2m'.
  set e := (1 - p - p)%Z; rewrite /F2R  =>thE.
  rewrite /= in thE.
  have tl1E: tl1=  ch + cl2  -th by lra.
  have {} tl1E: tl1 = IZR (mch + mcl2 - mth) * (2 * pow (- p) * pow (- p)).
      
  rewrite tl1E  chcl2m /=  thE !minus_IZR !plus_IZR !bpow_plus -/e /= IZR_Zpower_pos /= ; ring.
  case:(xhb)=> xh1 xh2.
  move: (xh1); have ->: 1 = pow 0 by [].
  rewrite -{1}(Rabs_pos_eq xh); try lra; move=>xh1'.
  have [mxh xhE]:=  (ex_mul 0 xh1' Fxh).
  have y1' : (pow 0 ) <= Rabs y.
    apply:(Rle_trans _ (1 + 2 * u))=>//; rewrite /= ?Rabs_pos_eq ;lra.
  have [my yE]:=  (ex_mul 0 y1' Fy).
  have xhy_mltpl: xh * y = IZR (mxh * my) * (4 * u *u).
    rewrite xhE yE mult_IZR /= /u;   ring.
  have tl2E: tl1 + cl1 = IZR (mcl2 - mth +2 * (mxh*my)) * (2 * pow (- p) * pow (- p)).
  rewrite  tl1E cl1e chE xhy_mltpl.
    rewrite !(plus_IZR , minus_IZR, mult_IZR).
    have->: 4*u*u= 2 * 2 * pow(-p) * pow(-p) by rewrite /u.
    ring.
  have: Rabs (tl1 + cl1 ) <= 2 * u.
    apply: (Rle_trans _ ((Rabs tl1) + (Rabs cl1))); first by apply:Rabs_triang.
    lra.
  rewrite tl2E Rabs_mult (Rabs_pos_eq (2 * pow (- p) * pow (- p))).
  move/(Rmult_le_compat_r (pow (p -1)) _ _ (bpow_ge_0 two (p -1))).
    have ->:  2 * u * pow (p - 1) = 1.
      rewrite bpow_plus /= IZR_Zpower_pos /= /u -!Rmult_assoc.
      suff: pow (- p) * pow p = 1 by lra.
      by rewrite -!bpow_plus; ring_simplify(-p + p)%Z.
    set m :=  (mcl2 - mth + 2 * (mxh * my))%Z.
    rewrite Rmult_assoc.
    have->:  (2 * pow (- p)) * pow (- p) * pow (p - 1) = pow (-p).
      have ->: 2 = pow 1 by [].
      rewrite -!bpow_plus.
      by ring_simplify(1 + - p + - p + (p - 1))%Z.
    move=>h.
    have -> : (2 * pow (- p) * pow (- p)) = pow (1 - p - p).
      by rewrite !bpow_plus.
    apply:formatS =>//.
    have h1:  Rabs (IZR m) <= (pow p).
      apply: (Rmult_le_reg_r (pow (-p))).
        by apply : bpow_gt_0.
      by rewrite -bpow_plus; ring_simplify(p + - p)%Z.
    case:h1=>h1.
      apply:(@FLX_format_Rabs_Fnum  p _  (Float two m 0)); rewrite /F2R //=; ring.
    apply:generic_format_abs_inv.
    rewrite h1; apply:generic_format_bpow; rewrite /fexp; lia.
  have -> : (2 * pow (- p) * pow (- p)) = pow (1 - p - p) by rewrite !bpow_plus.
  exact:bpow_ge_0.
apply:(Rle_trans _ ( (3 * / 2 * (u * u)) * / ( (1 - u) * (1 + 2 *u)))).
  rewrite /Rdiv; apply: Rmult_le_compat; try apply:Rabs_pos; try lra.
  have: 0 < (xh + xl) * y.
    apply: Rmult_lt_0_compat ; try lra.
    apply:(Rlt_le_trans _ (1 - u)).
      have : pow (-p) < pow 0.
        apply: bpow_lt ;lia.
      rewrite /u /=; lra.
    move/Rabs_le_inv: xlu; lra.
  move=> hd.
  rewrite Rabs_pos_eq; last by move/Rinv_0_lt_compat: hd; lra.
  apply: Rinv_le.
    apply: Rmult_lt_0_compat ; lra.
  apply:Rmult_le_compat; try lra.
  move/Rabs_le_inv: xlu; lra.
apply:(Rle_trans _ (3 * / 2 * (u * u))).
  rewrite -[X in _ <= X]Rmult_1_r.
  apply:Rmult_le_compat; try lra.
      suff: 0 <= (u * u) by lra.
      apply:Rmult_le_pos; lra.
    apply/Rlt_le/Rinv_0_lt_compat/Rmult_lt_0_compat ; lra.
  rewrite -[X in _ <= X]Rinv_1.
  apply:  Rinv_le; try lra.
  have->: (1 - u) * (1 + 2 * u) = 1 + u * (1 - 2 * u) by ring.
  suff: 0 <= u * (1 - 2*u) by lra.
  apply: Rmult_le_pos;     lra.
suff: 0 <=  u * (u * u) by lra.
repeat apply:Rmult_le_pos; lra.
Qed.

End Algo7_pre.

Fact Fast2Sum_asym_aux:
       forall a b c d : R, c = -a -> d = -b -> 
F2Sum c d  = pair_opp (F2Sum a b).
Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
move=> a b c d -> ->; by rewrite Fast2Sum_asym.
Qed.



Fact  DWTimesFP_Asym_r xh xl y  :
  (DWTimesFP xh xl (-y)) = pair_opp (DWTimesFP xh xl (y)).
Proof.
rewrite /DWTimesFP TwoProdE.
 apply:Fast2Sum_asym_aux; rewrite Fast2Mult_asym_r /pair_opp.
set ff := (fst (- F2P_prod xh y, - F2P_error xh y)).
have -> : ff = - F2P_prod xh y by rewrite /ff.
rewrite  (@Fast2Sum_asym_aux (F2P_prod xh y) (rnd_p (xl * y)))=>//=.
 by rewrite Ropp_mult_distr_r_reverse ZNE round_NE_opp //.

rewrite fstE sndE.
rewrite Ropp_mult_distr_r_reverse ZNE round_NE_opp -ZNE.
rewrite  (@Fast2Sum_asym_aux (F2P_prod xh y) (rnd_p (xl * y))) // sndE.
by rewrite -Ropp_plus_distr ZNE round_NE_opp. 
Qed.

Fact  DWTimesFP_Asym_l xh xl y :
         (DWTimesFP (-xh) (-xl)  y) =  pair_opp (DWTimesFP xh xl (y)).
Proof.
 rewrite /DWTimesFP TwoProdE.
 apply:Fast2Sum_asym_aux; rewrite Fast2Mult_asym_l  /pair_opp.
rewrite fstE (@Fast2Sum_asym_aux (F2P_prod xh y) (rnd_p (xl * y)))=>//=.
by rewrite Ropp_mult_distr_l_reverse ZNE round_NE_opp.
rewrite fstE sndE  Ropp_mult_distr_l_reverse ZNE round_NE_opp -ZNE.
rewrite  (@Fast2Sum_asym_aux (F2P_prod xh y) (rnd_p (xl * y))) // sndE.
by rewrite -Ropp_plus_distr ZNE round_NE_opp.
Qed.



Fact  DWTimesFPSx xh xl y e:
         (DWTimesFP (xh * pow e) (xl * pow e)  y) = map_pair (fun x =>  x * (pow e)) (DWTimesFP  xh xl y).
Proof.
 rewrite /DWTimesFP TwoProdE.
have->: (F2P_prod (xh * pow e) y) =  (F2P_prod xh y) * (pow e).
  by rewrite /= (Rmult_comm xh) Rmult_assoc (Rmult_comm (pow e)) round_bpow.
have ->: (xl * pow e * y) = (xl * y) * (pow e) by ring.
rewrite round_bpow Fast2SumS //;  try apply:generic_format_round.
  rewrite fstE sndE  Fast2MultSl /map_pair sndE fstE -Rmult_plus_distr_r sndE !round_bpow.
rewrite  Fast2SumS //; apply:generic_format_round.
Qed.


Fact  DWTimesFPSy xh xl y  e:
         (DWTimesFP xh xl   (y* pow e)) =  map_pair (fun x =>  x * (pow e)) (DWTimesFP  xh xl y).
Proof.
 rewrite /DWTimesFP TwoProdE.
have->: (F2P_prod xh (y * pow e) ) =  (F2P_prod xh y) * (pow e).
by rewrite  /= -Rmult_assoc round_bpow.
rewrite -(Rmult_assoc xl) round_bpow Fast2SumS //;  try apply:generic_format_round.
 rewrite fstE sndE  Fast2MultSr /map_pair sndE fstE  -Rmult_plus_distr_r sndE !round_bpow.
rewrite  Fast2SumS //; apply:generic_format_round.
Qed.

(* to remove *)
Definition errorDWTFP' xh xl y := let (zh, zl) := DWTimesFP xh xl y in
  let xy := ((xh + xl) * y)%R in (Rabs ((zh + zl) - xy)).

Definition errorDWTFP xh xl y := let (zh, zl) := DWTimesFP xh xl y in
  let xy := ((xh + xl) * y)%R in ((zh + zl) - xy).

Definition relative_errorDWTFP xh xl y := let (zh, zl) := DWTimesFP xh xl y in
  let xy := ((xh + xl) * y)%R in (Rabs (((zh + zl) - xy)/ xy)).


Notation double_word xh xl := (double_word  p choice xh xl).


(* Theorem 4.1 *)
Lemma DWTimesFP_correct xh xl y (DWx:double_word xh xl) (Fy : format y):
  let (zh, zl) := DWTimesFP xh xl y in
  let xy := ((xh + xl) * y)%R in
  ((Rabs ((zh + zl - xy) / xy) <= 3/2 * u ^ 2 + 4 * u ^ 3) /\ (double_word zh zl)).
Proof.
have round0 x: x = 0 -> rnd_p x = 0 by move => -> ; rewrite round_0.
have [[Fxh Fxl] Exh] := DWx.
case E1: DWTimesFP => [zh zl].
move=> xy.
have Hp1:= Hp1.
pose x := xh + xl.
case:(Req_dec xh 0)=> xh0.
  have xl0: xl = 0.
    by move:Exh; rewrite  xh0 Rplus_0_l round_generic.
  move:E1; rewrite /DWTimesFP xh0 xl0 Rmult_0_l TwoProdE  round_0 Fast2Mult0f.
  rewrite /Fast2Sum /F2SumFLX.Fast2Sum !(Rplus_0_r, Rminus_0_r, Rplus_0_l, round_0).
  rewrite /=; case => <- <-.
  rewrite Rplus_0_r Rminus_0_l {1}/xy xh0 xl0 /Rdiv  Rplus_0_l Rmult_0_l.
  rewrite Ropp_0 Rmult_0_l Rabs_R0; split;first exact: boundDWTFP_ge_0.
  by split;[split; apply:generic_format_0| rewrite Rplus_0_r round_0].
have x0: xh + xl <> 0.
  move=> x0; apply:xh0.
  by rewrite Exh; apply: round0.
case:(Req_dec y 0)=> y0.
  move:E1; rewrite /DWTimesFP y0  Rmult_0_r TwoProdE  round_0 Fast2MultC Fast2Mult0f.
  rewrite /Fast2Sum /F2SumFLX.Fast2Sum !(Rplus_0_r, Rminus_0_r, Rplus_0_r, round_0).
  rewrite /=; case => <- <-.
  rewrite Rplus_0_r Rminus_0_l {1}/xy y0 /Rdiv Rmult_0_r.
  rewrite Ropp_0 Rmult_0_l Rabs_R0;  split;first exact: boundDWTFP_ge_0.
  by split;[split; apply:generic_format_0| rewrite Rplus_0_r round_0].
case:(is_pow_dec two y)=> ypow.
  by move:E1; rewrite /DWTimesFP; case=> <- <-; apply: DWTimesFP_correct_ypow.
rewrite /xy; clear Fxh Fxl Exh xy x.
wlog ypos: y xh xl zh zl DWx Fy  E1 xh0 y0 ypow x0 / 0 <= y.
  move=> Hwlog.
  case:(Rle_lt_dec 0 y) => yle0.
    apply:Hwlog => //.
  have ->: (zh + zl - (xh + xl) * y) / ((xh + xl) * y)= 
        ((- zh + - zl - (xh + xl) * - y) / ((xh + xl) * - y)) by field.
  case:(Hwlog (-y) xh xl (-zh) (-zl) DWx)=>//; try lra.
  + by apply: generic_format_opp. 
  + by rewrite DWTimesFP_Asym_r E1.
  + by move=>nypow; apply:ypow; rewrite -(Ropp_involutive y); 
    apply:is_pow_opp.
  move=> h [[Fzh Fzl] Ezhzl]; split=>//; split.
    by rewrite -(Ropp_involutive zh) -(Ropp_involutive zl);
    split;  apply:generic_format_opp. 
  have {1}->: zh = - rnd_p (- zh + - zl) by rewrite -Ezhzl; ring.
  have->: (- zh + - zl) = - (zh + zl) by ring.
  rewrite ZNE round_NE_opp -ZNE; ring.

wlog xhpos: y xh xl zh zl DWx Fy  E1 xh0 y0 ypow ypos x0 / 0 <= xh.
  move=> Hwlog.
  case:(Rle_lt_dec 0 xh) => xhle0.
    by apply:Hwlog.
  have ->: (zh + zl - (xh + xl) * y) / ((xh + xl) * y)= ((- zh + - zl - (- xh + - xl) * y) / ((- xh + - xl) * y)) 
   by field; lra.   
  have [[Fxh Fxl] Exh] := DWx.
  case:  (Hwlog y (-xh) (-xl) (-zh) (-zl))=>//; try lra.
  split; [by split; apply:generic_format_opp|].
  + rewrite {1}Exh; have->: (- xh + - xl) = - (xh + xl) by ring.
    by rewrite ZNE round_NE_opp -ZNE.    
  + by rewrite DWTimesFP_Asym_l E1.
  move=> hle [[Fzh Fzl] zhlE]; split=>//; split.
    by rewrite -(Ropp_involutive zh) -(Ropp_involutive zl); 
     split; apply:generic_format_opp.
  have->:  (zh + zl) = - (- zh + - zl) by ring.
  rewrite ZNE round_NE_opp -ZNE   -zhlE; ring.
have {} xhpos: 0 < xh by lra.
have {} ypos: 0 < y by lra.

wlog [xh1 xh2]: xl xh  zh zl DWx   xh0 x0 xhpos E1/ 1 <= xh  <= 2-2*u.
  move=> Hwlog.
  have [[Fxh Fxl] Exh] := DWx.
  case: (scale_generic_12 Fxh xhpos)=> exh Hxhs.
  have xhp0: 0 <  xh * pow exh by lra.
  have ->: (zh + zl - (xh + xl) * y) / ((xh + xl) * y) = 
         (zh * pow exh  + zl * pow exh  - 
         (xh * pow exh + xl * pow exh) * y) / 
           ((xh * pow exh + xl * pow exh) * y).
    field.
    split; try lra; split; try lra.
    rewrite -Rmult_plus_distr_r.
    apply: Rmult_integral_contrapositive; move:(bpow_gt_0 two exh); lra.
  case:(Hwlog (xl* pow exh) (xh* pow exh) (zh* pow exh) (zl* pow exh))
     =>//; try lra.
  + split;[split|]; try apply:formatS=>//.
    by rewrite -Rmult_plus_distr_r round_bpow -Exh.
  + rewrite -Rmult_plus_distr_r; apply: Rmult_integral_contrapositive; 
     move:(bpow_gt_0 two exh); lra.
  + by rewrite DWTimesFPSx E1.
  move=> hle [[Fzh Fzl] zhlE]; split=>//; split.
    rewrite -(Rmult_1_r zh)  -(Rmult_1_r zl).
    have ->: 1 = pow exh * pow (-exh).
      by rewrite -bpow_plus Zplus_opp_r.
    by rewrite -!Rmult_assoc; split; apply:formatS.
  apply:(Rmult_eq_reg_r (pow exh)).
    by rewrite -round_bpow Rmult_plus_distr_r.
  move:(bpow_gt_0 two exh); lra.

wlog [y1 y2]: y  zh zl  Fy y0 ypow  ypos E1/ 1 <= y <= 2-2*u.
  move=> Hwlog.
  case: (scale_generic_12 Fy ypos)=> ey Hys.
  have ->: (zh + zl - (xh + xl) * y) / ((xh + xl) * y) = 
         (zh * pow ey  + zl * pow ey - (xh  + xl) * y * pow ey) / ((xh + xl ) * y * pow ey).
    field;  move:(bpow_gt_0 two ey); lra.
  rewrite Rmult_assoc; case:(Hwlog (y * pow ey) (zh * (pow ey)) 
                              (zl * (pow ey)))=>//; try lra.
  + by apply:formatS.
  + move=> [ eyp Heyp]; apply:ypow.
    exists (eyp - ey)%Z.
    move:   Heyp; rewrite !Rabs_pos_eq; try lra.
    rewrite bpow_plus=> <-; rewrite Rmult_assoc -bpow_plus Z.add_opp_diag_r /=; ring.
  + by  rewrite DWTimesFPSy E1.
 move=> hle [[Fzh Fzl] zhlE]; split=>//; split.
rewrite -(Rmult_1_r zh)  -(Rmult_1_r zl).
    have ->: 1 = pow ey * pow (-ey).
      by rewrite -bpow_plus Zplus_opp_r.
    by rewrite -!Rmult_assoc; split; apply:formatS.
  apply:(Rmult_eq_reg_r (pow ey)).
    by rewrite -round_bpow Rmult_plus_distr_r.
  move:(bpow_gt_0 two ey); lra.
  (* case:(DWTimesFP_correct_pre Fy DWx (conj xh1 xh2)  (conj y1 y2) ypow). *)
  move:(E1); rewrite /DWTimesFP.
  case=> <- <-.
  apply:DWTimesFP_correct_pre =>//; lra.
Qed.

Lemma DWTimesFP_bound xh xl y (DWx:double_word xh xl) (Fy : format y):
  let (zh, zl) := DWTimesFP xh xl y in
  let xy := ((xh + xl) * y)%R in
  (Rabs ((zh + zl - xy) / xy) <= 3/2 * u ^ 2 + 4 * u ^ 3).
Proof.
move: (DWTimesFP_correct DWx Fy ).
by case:DWTimesFP => [zh zl] //=; case.
Qed.

Lemma DWTimesFP_DWres xh xl y (DWx:double_word xh xl) (Fy : format y):
  let (zh, zl) := DWTimesFP xh xl y in (double_word zh zl).
Proof.
move: (DWTimesFP_correct DWx Fy ).
by case:DWTimesFP => [zh zl] //=; case.
Qed.

Lemma DWTimesFP_pos xh xl y (DWx:double_word xh xl) (Fy : format y):
   0 < xh -> 0 < y -> 
  let (zh, zl) := DWTimesFP xh xl y in 0 <= zh.
Proof.
move=> xhpos ypos.
 move:( DWTimesFP_bound  DWx Fy ).
move:( DWTimesFP_DWres  DWx Fy ).
case h :DWTimesFP => [zh zl].
move=>[[Fzh Fzl] zE].
rewrite /=.
move=> hb.
suff: 0 <= zh + zl .
  move/(round_le two fexp (Znearest choice)).
  by rewrite round_0 -zE.
have xpos: 0 < xh + xl.
  case:(Rlt_le_dec  0 (xh + xl) )=> // /(round_le two fexp (Znearest choice)).
  case:DWx=> _ <-.
  rewrite round_0; lra.
have upos:= (upos p); rewrite -/u in upos.
have u2pos: 0 < u*u by nra.
move/Rabs_le_inv:  hb.
case.
set xy := ((xh + xl) * y).
have-> : (zh + zl - xy) / xy =  (zh + zl)/ xy -1.
  field.
  apply:Rmult_integral_contrapositive_currified=>//;  lra.
rewrite !Rmult_1_r; move=> haux _.
apply:(Rmult_le_reg_r (/xy)).
  rewrite /xy.
  by apply:Rinv_0_lt_compat ; clear -ypos xpos; nra.
rewrite Rmult_0_l.
apply:(Rle_trans _ (1  -  (3 / 2 * (u * u) + 4 * (u * (u * u))))).
  clear -upos u2pos Hp4.
  suff :3 / 2 * (u * u) + 4*(u * (u * u)) <= 1 by lra.
  apply:(Rle_trans _ (2 * (u*u))).
    suff: 4*u <= /2 by nra.
    change ((pow 2) * u <= pow (-1)).
    rewrite /u -bpow_plus; apply:bpow_le; lia.
  rewrite /u; change (pow 1  * (pow (- p) * pow (- p)) <= pow 0).
  rewrite -!bpow_plus; apply:bpow_le; lia.
lra.
Qed.

Lemma DWTimesFP_zhpos xh xl y (DWx:double_word xh xl) (Fy : format y) zh :
   0 < xh -> 0 < y -> 
  zh = fst  (DWTimesFP xh xl y )-> 0 <= zh.
Proof.
move=>xh0 y0.
move: (DWTimesFP_pos DWx Fy xh0 y0).
by case h:  (DWTimesFP xh xl y)=> [rh rl] /= ? ->.
Qed.

End Theorem_4_1.

Section Algo8.


Hypothesis Hp3 : Z.le 3 p.

Local Instance p_gt_0_3 : Prec_gt_0 p.
exact: (Z.lt_le_trans _ 3 _ _ Hp3).
Qed.


Fact Hp1_3 : (1 < p)%Z.
Proof. lia. 
Qed.

Notation Hp1 := Hp1_3.

Notation double_word  := (double_word  p choice ).


Hypothesis TwoProdE : TwoProd = Fast2Mult. (* or Dekker's algorithm *)


Definition DWTimesFP8 (xh xl y : R) :=
  let (ch, cl1) := TwoProd xh y in
  let cl2 := rnd_p (xl * y) in
  let cl3 := rnd_p (cl1 + cl2) in
  Fast2Sum  p choice ch cl3.



Fact  DWTimesFP8_Asym_r xh xl y: 
  (DWTimesFP8 xh xl (-y)) = pair_opp (DWTimesFP8 xh xl y).

 Proof.
rewrite /DWTimesFP8 TwoProdE /=.
apply:Fast2Sum_asym_aux; 
rewrite ZNE !(=^~Ropp_mult_distr_r, round_NE_opp,  Fast2Sum_asym_aux) -ZNE //.
have ->: - (xh * y) - - rnd_p (xh * y) = - ((xh * y) -  rnd_p (xh * y)) by ring.
by rewrite ZNE !(=^~Ropp_plus_distr, round_NE_opp) ?Ropp_involutive  -ZNE //.
Qed.

Fact  DWTimesFP8_Asym_l xh xl y  : 
         (DWTimesFP8 (-xh) (-xl)  y) =  pair_opp (DWTimesFP8 xh xl y).

Proof.
  rewrite /DWTimesFP8 TwoProdE /=.
    apply:Fast2Sum_asym_aux;   
      rewrite ZNE !(=^~Ropp_mult_distr_l, round_NE_opp) -ZNE //.
have ->: - (xh * y) - - rnd_p (xh * y) = - ((xh * y) -  rnd_p (xh * y)) by ring.
by rewrite ZNE !(=^~Ropp_plus_distr, round_NE_opp) ?Ropp_involutive  -ZNE //.
Qed.


Fact  DWTimesFP8Sx xh xl y e: (DWTimesFP8 (xh * pow e) (xl * pow e)  y) = map_pair (fun x =>  x * (pow e)) (DWTimesFP8 xh xl y).

Proof.
  rewrite /DWTimesFP8 TwoProdE /=.
  rewrite !(Rmult_comm _ y) !(=^~Rmult_assoc, round_bpow, =^~Rmult_plus_distr_r, =^~Rmult_minus_distr_r,  Fast2SumS  ) //=;  apply:generic_format_round.
Qed.

Fact  DWTimesFP8Sy xh xl y e:
         (DWTimesFP8 xh xl   (y* pow e)) = map_pair (fun x =>  x * (pow e)) (DWTimesFP8 xh xl y).
Proof.
 rewrite /DWTimesFP8 TwoProdE /=.
rewrite  !(=^~Rmult_assoc, round_bpow, =^~Rmult_plus_distr_r,Fast2SumS,=^~Rmult_minus_distr_r ) //; 
   apply:generic_format_round.
Qed.

(* to remove *)
Definition errorDWTFP8' xh xl y := let (zh, zl) := DWTimesFP8 xh xl y in
  let xy := ((xh + xl) * y)%R in (Rabs ((zh + zl) - xy)).

Definition errorDWTFP8 xh xl y := let (zh, zl) := DWTimesFP8 xh xl y in
  let xy := ((xh + xl) * y)%R in ((zh + zl) - xy).

Definition relative_errorDWTFP8 xh xl y := let (zh, zl) := DWTimesFP8 xh xl y in
  let xy := ((xh + xl) * y)%R in (Rabs (((zh + zl) - xy)/ xy)).


Notation formatS := (formatS Hp1).


Lemma  boundDWTFP8_ge_0: 0 <= 3*u^2.
Proof.
have upos: 0 < u by rewrite /u ; exact:upos.
by repeat apply:Rmult_le_pos; lra.
Qed.

Lemma formatMbpow x y (Fx: format  x) (ypow: is_pow two  y): format (x * y).
Proof.
case:ypow => ey.
case:(Rle_lt_dec 0 y)=> y0.
  rewrite Rabs_pos_eq // => ->; apply:formatS =>//; lia.
rewrite Rabs_left;last lra.
move/Ropp_eq_compat; rewrite Ropp_involutive => ->.
by rewrite Ropp_mult_distr_r_reverse; apply/generic_format_opp/formatS.
Qed.



Lemma DWTimesFP8_correct xh xl y (DWx:double_word xh xl) (Fy : format y):
  let (zh, zl) := DWTimesFP8 xh xl y in
  let xy := ((xh + xl) * y)%R in
  Rabs ((zh + zl - xy) / xy) <= 3 * u ^ 2.
Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
have Hp1 := Hp1.
have [[Fxh Fxl] Exh] := DWx.
case E1: DWTimesFP8 => [zh zl].
move=> xy.
pose x := xh + xl.
case:(Req_dec xh 0)=> xh0.
  have xl0: xl = 0.
    by move:Exh; rewrite  xh0 Rplus_0_l round_generic.
  move:E1; rewrite /DWTimesFP8 xh0 xl0 Rmult_0_l TwoProdE  round_0 Fast2Mult0f.
  rewrite /Fast2Sum /F2SumFLX.Fast2Sum !(Rplus_0_r, Rminus_0_r, Rplus_0_l, round_0).
  case=> <- <-.
  rewrite Rplus_0_r Rminus_0_l {1}/xy xh0 xl0 /Rdiv  Rplus_0_l Rmult_0_l.
  rewrite Ropp_0 Rmult_0_l Rabs_R0.
  exact: boundDWTFP8_ge_0.
have x0: xh + xl <> 0.
  move=> x0; apply:xh0.
  by rewrite Exh x0 round_0.
case:(Req_dec y 0)=> y0.
  move:E1; rewrite /DWTimesFP8 y0  Rmult_0_r TwoProdE  round_0 Fast2MultC Fast2Mult0f.
  rewrite /Fast2Sum /F2SumFLX.Fast2Sum !(Rplus_0_r, Rminus_0_r, Rplus_0_r, round_0).
  case=> <- <-; rewrite Rplus_0_r Rminus_0_l {1}/xy y0 /Rdiv Rmult_0_r.
  rewrite Ropp_0 Rmult_0_l Rabs_R0.
  exact: boundDWTFP8_ge_0.
case:(is_pow_dec two y)=> ypow.
  case (ypow)=> ey yE.
  suff ->: Rabs ((zh + zl - xy) / xy) = 0 by apply: boundDWTFP8_ge_0.
  suff-> : (zh + zl - xy) = 0  by rewrite /Rdiv Rmult_0_l Rabs_R0.
  move:E1; rewrite /DWTimesFP8 TwoProdE /=.
  set ch := rnd_p (xh * y).
  set cl1 :=  rnd_p (xh * y - ch).
  have che: ch =  (xh * y).
    by rewrite /ch round_generic //; apply: formatMbpow.
  rewrite  -/ch che.
  have cl10: cl1 = 0.
    by rewrite /cl1 che Rminus_diag_eq // round_0.
  rewrite cl10.
  set cl2 := rnd_p (xl * y).
  have Fcl2: format cl2 by apply: generic_format_round.
  have cl2e: cl2 =  (xl * y).
    by rewrite /cl2 round_generic //; apply: formatMbpow.
  rewrite Rplus_0_l  (round_generic _ _ _ cl2) //.
rewrite (surjective_pairing (Fast2Sum  _ _ _ _)).
rewrite cl2e  F2Sum_correct_abs =>//; (try lia); (try apply:formatMbpow=>//=).
case=> <- <- /=; rewrite /xy; ring.
    rewrite !Rabs_mult; apply:Rmult_le_compat_r; try apply:Rabs_pos.
    apply:(Rle_trans _ (/ 2 * ulp radix2 (FLX_exp p) xh)).
    apply:dw_ulp=>//; apply:DWx.
    apply:(Rle_trans _ (ulp radix2 fexp xh)).
      move:(ulp_ge_0  radix2 fexp xh); lra.
    by apply:ulp_le_abs.
rewrite /xy ; clear xy  Fxh Fxl Exh x .
wlog ypos: y xh xl zh zl DWx Fy  E1 xh0 y0 ypow x0 / 0 <= y.
  move=> Hwlog.
  case:(Rle_lt_dec 0 y) => yle0.
    by apply:Hwlog.
  have ->: (zh + zl - (xh + xl) * y) / ((xh + xl) * y)= 
           ((- zh + - zl - (xh + xl) * - y) / ((xh + xl) * - y)) by field.
  apply:(Hwlog (-y) xh xl (-zh) (-zl))=>//; try lra.
      by apply: generic_format_opp. 
    by rewrite DWTimesFP8_Asym_r E1 /pair_opp.
  by move=>nypow; apply:ypow; rewrite -(Ropp_involutive y); apply:is_pow_opp.
wlog xhpos: y xh xl zh zl DWx Fy  E1 xh0 y0 ypow ypos x0 / 0 <= xh.
  move=> Hwlog.
  case:(Rle_lt_dec 0 xh) => xhle0.
    by apply:Hwlog.
  have ->: (zh + zl - (xh + xl) * y) / ((xh + xl) * y)= 
              ((- zh + - zl - (- xh + - xl) * y) / ((- xh + - xl) * y)) 
   by field; lra.
  apply:(Hwlog y (-xh) (-xl) (-zh) (-zl))=>//; try lra; last first.
  by rewrite DWTimesFP8_Asym_l E1.
  have [[Fxh Fxl] Exh] := DWx.
  split; [split|]; try apply:generic_format_opp=>//.
  have ->:- xh + - xl = -(xh +  xl) by ring.
  by rewrite ZNE round_NE_opp -ZNE {1}Exh.
have {} xhpos: 0 < xh by lra.
have {} ypos: 0 < y by lra.
wlog [xh1 xh2]: xl xh  zh zl DWx   xh0 x0 xhpos E1/ 1 <= xh  <= 2-2*u.
  move=> Hwlog.
  have [[Fxh Fxl] Exh] := DWx.
  case: (scale_generic_12 Fxh xhpos)=> exh Hxhs.
  have xhp0: 0 <  xh * pow exh by lra.
  have ->: (zh + zl - (xh + xl) * y) / ((xh + xl) * y) = 
         (zh * pow exh  + zl * pow exh  - 
         (xh * pow exh + xl * pow exh) * y) / ((xh * pow exh + xl * pow exh) * y).
    field.
    split; try lra; split; try lra.
    rewrite -Rmult_plus_distr_r.
    apply: Rmult_integral_contrapositive; move:(bpow_gt_0 two exh); lra.
  apply:Hwlog=>//; try lra.
      split;[split|]; try apply:formatS=>//.
      by rewrite -Rmult_plus_distr_r round_bpow -Exh.
    rewrite -Rmult_plus_distr_r; apply: Rmult_integral_contrapositive; 
      move:(bpow_gt_0 two exh); lra.
  by rewrite DWTimesFP8Sx E1.
wlog [y1 y2]: y  zh zl  Fy y0 ypow  ypos E1/ 1 <= y <= 2-2*u.
  move=> Hwlog.
  case: (scale_generic_12 Fy ypos)=> ey Hys.
  have ->: (zh + zl - (xh + xl) * y) / ((xh + xl) * y) = 
   (zh * pow ey  + zl * pow ey - (xh  + xl) * y * pow ey) / ((xh + xl ) * y * pow ey).
    field;  move:(bpow_gt_0 two ey); lra.
  rewrite Rmult_assoc; apply:Hwlog=>//; try lra.
     by apply:formatS.
    move=> [ eyp Heyp]; apply:ypow.
    exists (eyp - ey)%Z.
    move:   Heyp; rewrite !Rabs_pos_eq; try lra.
    rewrite bpow_plus=> <-; rewrite Rmult_assoc -bpow_plus Z.add_opp_diag_r /=; ring.
      by rewrite DWTimesFP8Sy E1.
(* ici *)
move:(upos p); rewrite -/u=> upos.
have u1 : u < 1 by rewrite /u ; have ->: 1 =  pow 0 by []; apply:bpow_lt; lia.
have [[Fxh Fxl] Exh] := DWx.
have {} y1: 1 + 2*u <= y.
  case/Rle_lt_or_eq_dec: y1 =>y1; first last.
    suff: (is_pow two y) by [].
    exists 0%Z; rewrite -y1 Rabs_pos_eq  /= ; lra.
  suff ->: 1 + 2 * u = succ two fexp 1.
    apply: succ_le_lt=>//.
    have ->: 1 = pow 0 by [].
    apply:generic_format_bpow; rewrite /fexp; lia.
  rewrite succ_eq_pos; try lra.
  rewrite /u u_ulp1; field.
have hxhy: 1+ 2*u <= xh * y <= 4 - 8*u + 4*u*u.
  split.
    rewrite -(Rmult_1_l (_ + _)).
    apply:Rmult_le_compat;  lra.
  have ->: 4 - 8 * u + 4 * u * u = (2 - 2*u) * (2 - 2*u) by ring.
  apply:Rmult_le_compat; lra.
pose ch := rnd_p (xh * y ).
have Fch: format ch by apply:generic_format_round.
have: rnd_p (1 + 2 *u ) <= ch by apply:round_le; lra.
rewrite round_generic; last first.
  rewrite /u u_ulp1 -Rmult_assoc Rinv_r ; last lra.
  rewrite Rmult_1_l -succ_eq_pos; try lra.
  apply: generic_format_succ.
  have -> : 1 = pow 0 by [].
  apply:generic_format_bpow; rewrite /fexp; lia.
move=> h16_lb.
have: ch <= rnd_p ( 4 - 8 * u + 4 * u * u) by apply:round_le; lra.
have->:  (4 - 8 * u + 4 * u * u)= (1 -2 * u + u * u)* (pow 2 ).
  rewrite /=IZR_Zpower_pos /=; ring.
have ch0: ch <> 0 by lra.
rewrite round_bpow  r1m2u // => h16_ub.
pose cl1 := xh*y - ch.
have Fcl1: format cl1.
  by rewrite /cl1 -Ropp_minus_distr; apply/generic_format_opp /mult_error_FLX.
have h17 :Rabs cl1 <= 2*u.
  apply:(Rle_trans _ (/2 * (ulp two fexp (rnd_p (xh * y))))).
    rewrite /cl1 /ch.
    have ->: (xh * y - rnd_p (xh * y)) = -(rnd_p (xh * y) - xh * y) by ring.
    by rewrite Rabs_Ropp;apply:error_le_half_ulp_round.
  rewrite -/ch ulp_neq_0 // /cexp /fexp bpow_plus -/u.
  set mg := mag _ _ .
  suff /(bpow_le two) mg2: (mg <= 2)%Z.
    apply:(Rle_trans _ (/2 * ((pow 2) * u))).
      apply:Rmult_le_compat_l; try lra.
      apply:Rmult_le_compat_r; lra.
    rewrite /= IZR_Zpower_pos /= ; lra.
  rewrite /mg; apply:mag_le_bpow =>//; rewrite Rabs_pos_eq; try lra.
  apply:(Rle_lt_trans _ ((1 - 2 * u) * pow 2)) =>//.
  rewrite -{2}(Rmult_1_l (pow 2)).
  apply:Rmult_lt_compat_r; first by apply: bpow_gt_0.
  lra.
have xlu: Rabs xl <= u.
  have:= (dw_ulp Hp1 DWx).
  suff ->:  / 2 * ulp radix2 fexp xh = u by [].
  rewrite ulp_neq_0 // /cexp /fexp bpow_plus -/u -Rmult_assoc.
  suff -> : / 2 * (pow (mag radix2 xh)) = 1 by ring.
  suff ->:  ((mag radix2 xh)  = 1%Z :>Z).
    rewrite /= IZR_Zpower_pos /=; field.
  apply:mag_unique_pos.
  rewrite /= IZR_Zpower_pos /=; split;lra.
pose cl2 := rnd_p (xl * y).
have Fcl2: format cl2 by apply:generic_format_round.
pose error :=  errorDWTFP8 xh xl y.
have: error =  errorDWTFP8 xh xl y by [].
rewrite /errorDWTFP8 E1.
move:E1; rewrite /DWTimesFP8 TwoProdE /= -/cl2 -/cl1 -/ch.
rewrite (round_generic _ _ _ cl1); last apply:Fcl1.
pose e1 :=  (xl * y) -cl2.
pose cl3 := rnd_p (cl1 + cl2).
pose e2:= cl1 + cl2 - cl3.
pose e := e1 + e2.
(* à sortit et factoriser *)

have:Rabs cl2 <= 2 * u - 2* u * u.
  have ->:  2 * u - 2 * u * u = rnd_p ( 2 * u - 2 * u * u).
  rewrite round_generic //.
    have ->: (2 * u - 2 * u * u) = (pow p - 1) * pow (1 +  (-p + -p)).
      rewrite !bpow_plus /= IZR_Zpower_pos /= /u.
      rewrite Rmult_minus_distr_r.
      congr (_ -_); try ring.
      rewrite (Rmult_comm (pow p)) !Rmult_assoc -bpow_plus.
      ring_simplify(-p + p)%Z; rewrite /=; ring.
    apply:formatS =>//.
    apply:generic_format_FLX.
    apply:(FLX_spec _ _ _ (Float two (2 ^ p -1) 0)).
      rewrite /F2R /= minus_IZR (IZR_Zpower two); try ring; lia.
    rewrite /= Z.abs_eq; first lia.
    suff : (1 <= 2^ p )%Z by lia.
    have ->: (1 = 2 ^ 0 )%Z by [].
    apply:Z.pow_le_mono_r; lia.
  rewrite /cl2.
  rewrite ZNE -round_NE_abs -ZNE.
  apply:round_le.
  rewrite Rabs_mult.
  have ->:  2 * u - 2 * u * u = u * (2 - 2*u) by ring.
  apply:Rmult_le_compat =>//; try apply: Rabs_pos.
  rewrite Rabs_pos_eq; lra.
move=> h18.
(* à sortir et factoriser *)
case:(Req_dec xl 0)=>xl0.
  have cl20: cl2 = 0 by rewrite /cl2 xl0 Rmult_0_l round_0.
  have e10: e1 = 0 by rewrite /e1 cl20 xl0; ring.
  have e20: e2 = 0 .
    rewrite /e2  /cl3 cl20 Rplus_0_r round_generic //;  ring.
    rewrite  cl20 Rplus_0_r (round_generic _ _ _ cl1) //.
    rewrite (surjective_pairing (Fast2Sum _ _ _ _)).
  rewrite F2Sum_correct_abs // ; last first.
    rewrite (Rabs_pos_eq ch); lra.
  case=> <- <- => errorE.
  rewrite -errorE.
  have ->: error = 0.
    rewrite errorE xl0; rewrite  /cl1; ring.
  rewrite Rabs_mult /Rdiv Rabs_R0 Rmult_0_l.
  exact: boundDWTFP8_ge_0.
have  cl20: cl2 <> 0.
 apply: round_neq_0_negligible_exp;rewrite ?negligible_exp_FLX //.
  by apply:Rmult_integral_contrapositive_currified.
have h19_0: Rabs e1 <= u * u.
  rewrite /e1 -Ropp_minus_distr Rabs_Ropp /cl2.
  apply:(Rle_trans _ (/2 * (ulp two fexp (rnd_p (xl * y))))).
    by apply: error_le_half_ulp_round.
  rewrite ulp_neq_0 // /cexp -/cl2 /fexp bpow_plus.
  have : pow (mag radix2 cl2) <= pow (1 -p).
    apply/bpow_le/ mag_le_bpow =>//.
    rewrite bpow_plus -/u /= IZR_Zpower_pos /=.
    suff: 0 < u * u by lra.
    by rewrite /u -bpow_plus; apply:bpow_gt_0.
  have h2:  0 <= /2 by lra.
  move/(Rmult_le_compat_l  (/2) _ _ h2).
  rewrite bpow_plus /= IZR_Zpower_pos /= Rmult_1_r  -Rmult_assoc Rinv_l ?Rmult_1_l ; try lra.
  move/(Rmult_le_compat_r (pow (-p)) _ _ (bpow_ge_0 two (-p))).
  rewrite /u; lra.
have hcl12:Rabs (cl1 + cl2) <= 4 * u - 2 * u *u.
  apply:(Rle_trans _ (Rabs cl1 + Rabs cl2)); first by apply:Rabs_triang.
  lra.
move/(round_le two fexp (Znearest choice)):(hcl12).
rewrite ZNE round_NE_abs -ZNE -/cl3.
have -> : rnd_p (4 * u - 2 * u * u) = 4 * u.
  have -> : (4 * u - 2 * u * u) = (1 - /2*u)*(pow (2 - p)).
    rewrite bpow_plus /= IZR_Zpower_pos /= -/u; field.
  rewrite round_bpow /u (Rmult_comm (/2)) r1mu2 //  -?ZNE  bpow_plus.
  have ->: 4 = pow 2 by [].
  ring.
  move=> cl3_4u.
  rewrite (surjective_pairing (Fast2Sum _   _ _ _)).
rewrite F2Sum_correct_abs //; try apply:generic_format_round; last first.
  apply:(Rle_trans _ (4 * u)); try lra.
  rewrite Rabs_pos_eq ;lra.
have e2ub: Rabs e2 <= 2 * (u * u).
  rewrite /e2 /cl3 -Ropp_minus_distr Rabs_Ropp.
  have ->: 2 * (u * u) = /2*u *(pow (2 -p)).
    by rewrite bpow_plus /u /= IZR_Zpower_pos /= ; field.
  rewrite /u; apply: error_le_half_ulp'; first lia.
  rewrite bpow_plus  -/u /= IZR_Zpower_pos /=.
  apply:( Rle_trans _ (4 * u - 2 * u * u)) =>//.
  suff: 0 <=  2 * u * u by lra.
  repeat apply:Rmult_le_pos; lra.
case=> <- <-=> errorE.
rewrite -errorE.
have {} errorE: error = - (e1 + e2).
  rewrite errorE /e1/e2  /cl1; ring.
rewrite errorE Rabs_mult Rabs_Ropp.
have:  Rabs (e1 + e2)<= 3 * (u * u).
  apply:(Rle_trans _ (Rabs e1 + Rabs e2)); first by apply:Rabs_triang.
  lra.
move=> h.
suff hxy:  1 <=  ((xh + xl) * y).
  have : 0 < ((xh + xl) * y) by lra.
  move/Rinv_0_lt_compat => hinv.
  rewrite (Rabs_pos_eq (/_)); try lra.
  rewrite -[X in _ <= X]Rmult_1_r.
  apply:Rmult_le_compat; try lra.
    by apply:Rabs_pos.
  have->: 1 = /1 by field.
  apply: Rinv_le; lra.
apply:(Rle_trans _ ((1 - u) * (1 + 2 * u))).
  have -> : (1 - u) * (1 + 2 * u) = 1 + u * (1 - 2 * u) by ring.
  suff: 0<=  u * (1 - 2 * u) by lra.
  apply: Rmult_le_pos ; lra.
apply:Rmult_le_compat; try lra.
apply:Rplus_le_compat =>//.
move/Rabs_le_inv : xlu; lra.
Qed.
End Algo8.

Section Algo9.


Hypothesis Hp3 : Z.le 3 p.

Local Instance p_gt_0_3_9 : Prec_gt_0 p.
exact: (Z.lt_le_trans _ 3 _ _ Hp3).
Qed.

Notation Hp1 := (Hp1_3 Hp3).

Notation double_word  := (double_word  p choice ).


Hypothesis TwoProdE : TwoProd = Fast2Mult. (* or Dekker's algorithm *)


Definition FMA a b c := rnd_p (a + b * c).

Definition DWTimesFP9 (xh xl y : R) :=
  let (ch, cl1) := TwoProd xh y in
  let cl3 :=  FMA  cl1 xl y in (Fast2Sum  p choice ch cl3).

Fact  DWTimesFP9_Asym_r xh xl y  : 
  (DWTimesFP9 xh xl (-y)) = pair_opp  (DWTimesFP9 xh xl y).
 Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
 rewrite /DWTimesFP9 TwoProdE /FMA /=.
rewrite ZNE !(=^~Ropp_mult_distr_r, round_NE_opp,  Fast2Sum_asym) -ZNE //.
have ->: - (xh * y) - - rnd_p (xh * y) = - ((xh * y) -  rnd_p (xh * y)) by ring.
rewrite ZNE !(=^~Ropp_plus_distr, round_NE_opp,  Fast2Sum_asym) ?Ropp_involutive  -ZNE //.
Qed.

 Fact  DWTimesFP9_Asym_l xh xl y :
    (DWTimesFP9 (-xh) (-xl)  y) = pair_opp  (DWTimesFP9 xh xl y).
Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
 rewrite /DWTimesFP9 TwoProdE /FMA /=.
rewrite ZNE !(=^~Ropp_mult_distr_l, =^~Ropp_mult_distr_r, round_NE_opp,  Fast2Sum_asym) -ZNE //.
have ->: - (xh * y) - - rnd_p (xh * y) = - ((xh * y) -  rnd_p (xh * y)) by ring.
by rewrite ZNE !(=^~Ropp_plus_distr, round_NE_opp,  Fast2Sum_asym) ?Ropp_involutive  -ZNE //.
Qed.


Fact  DWTimesFP9Sx xh xl y e:
  (DWTimesFP9 (xh * pow e) (xl * pow e)  y) = map_pair (fun x =>  x * (pow e))  (DWTimesFP9 xh xl  y).
Proof.
 rewrite /DWTimesFP9 TwoProdE /FMA /=.
by rewrite !(Rmult_comm _ y) !(=^~Rmult_assoc, round_bpow, =^~Rmult_plus_distr_r,Fast2SumS,=^~Rmult_minus_distr_r ) 
  !(Rmult_comm y)//; apply:generic_format_round.
Qed.

Fact  DWTimesFP9Sy xh xl y e:
  (DWTimesFP9 xh xl   (y* pow e)) =
         map_pair (fun x =>  x * (pow e))  (DWTimesFP9 xh xl  y).
Proof.
 rewrite /DWTimesFP9 TwoProdE /FMA /=.
by rewrite  !(=^~Rmult_assoc, round_bpow, =^~Rmult_plus_distr_r,Fast2SumS,=^~Rmult_minus_distr_r ) //; 
   apply:generic_format_round.
Qed.


Definition errorDWTFP9 xh xl y := let (zh, zl) := DWTimesFP9 xh xl y in
  let xy := ((xh + xl) * y)%R in ((zh + zl) - xy).

Definition relative_errorDWTFP9 xh xl y := let (zh, zl) := DWTimesFP9 xh xl y in
  let xy := ((xh + xl) * y)%R in (Rabs (((zh + zl) - xy)/ xy)).

Notation formatS := (formatS Hp1).


Lemma  boundDWTFP9_ge_0: 0 <= 2*u^2.
Proof.
have upos: 0 < u by rewrite /u ; exact:upos.
by repeat apply:Rmult_le_pos; lra.
Qed.


Lemma DWTimesFP9_correct xh xl y (DWx:double_word xh xl) (Fy : format y):
  let (zh, zl) := DWTimesFP9 xh xl y in
  let xy := ((xh + xl) * y)%R in
  (Rabs ((zh + zl - xy) / xy) <= 2 * u ^ 2) /\ double_word zh zl.


Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
have Hp1 := Hp1.
have [[Fxh Fxl] Exh] := DWx.
case E1: DWTimesFP9 => [zh zl].
move=> xy.
pose x := xh + xl.
case:(Req_dec xh 0)=> xh0.
  have xl0: xl = 0.
    by move:Exh; rewrite  xh0 Rplus_0_l round_generic.
  move:E1; rewrite /DWTimesFP9 xh0 xl0  TwoProdE  /FMA  Rmult_0_l Fast2Mult0f Rplus_0_l round_0.
  rewrite /Fast2Sum /F2SumFLX.Fast2Sum !(Rplus_0_r, Rminus_0_r, Rplus_0_l, round_0).
  case=> <- <-.
  rewrite Rplus_0_r Rminus_0_l {1}/xy xh0 xl0 /Rdiv  Rplus_0_l Rmult_0_l.
  rewrite Ropp_0 Rmult_0_l Rabs_R0.
  split; first exact: boundDWTFP9_ge_0.
  by split; [split;  apply:generic_format_0| rewrite Rplus_0_r round_0].

have x0: xh + xl <> 0.
  by move=> x0; apply:xh0; rewrite Exh x0 round_0.
case:(Req_dec y 0)=> y0.
  move:E1; rewrite /DWTimesFP9 y0 TwoProdE  /FMA  Rmult_0_r Fast2MultC Fast2Mult0f Rplus_0_r round_0.
  rewrite /Fast2Sum /F2SumFLX.Fast2Sum !(Rplus_0_r, Rminus_0_r, Rplus_0_r, round_0).
  case=> <- <-; rewrite Rplus_0_r Rminus_0_l {1}/xy y0 /Rdiv Rmult_0_r.
  rewrite Ropp_0 Rmult_0_l Rabs_R0.
  split; first exact: boundDWTFP9_ge_0.
  by split; [split;  apply:generic_format_0| rewrite Rplus_0_r round_0].
case:(is_pow_dec two y)=> ypow.
case (ypow)=> ey yE.
 move:E1; rewrite /DWTimesFP9 TwoProdE /FMA  /=.
  set ch := rnd_p (xh * y).
  set cl1 :=  rnd_p (xh * y - ch).
  have che: ch =  (xh * y).
    by rewrite /ch round_generic //; apply: formatMbpow.
  rewrite  -/ch che.
  have cl10: cl1 = 0.
    by rewrite /cl1 che Rminus_diag_eq // round_0.
  rewrite cl10 Rplus_0_l.
  set cl2 := rnd_p (xl * y).
  have Fcl2: format cl2 by apply: generic_format_round.
  have cl2e: cl2 =  (xl * y).
    by rewrite /cl2 round_generic //; apply: formatMbpow.
  have f2sc: (Fast2Sum_correct  p choice (xh * y) cl2).
    apply: F2Sum_correct_abs=>//.
      by apply:formatMbpow.
    rewrite cl2e !Rabs_mult; apply:Rmult_le_compat_r; try apply:Rabs_pos.
    apply:(Rle_trans _ (/ 2 * ulp radix2 (FLX_exp p) xh)).
      by apply:dw_ulp=>//; apply:DWx.
    apply:(Rle_trans _ (ulp radix2 fexp xh)).
      by move:(ulp_ge_0  radix2 fexp xh); lra.
        by apply:ulp_le_abs.
        move=> zE.
        split; last first.
   
move :(F2Sum_correct_DW' Hp1  f2sc).

move:zE; case=> <- <- //.     

  suff ->: Rabs ((zh + zl - xy) / xy) = 0 by apply: boundDWTFP9_ge_0. 
  suff-> : (zh + zl - xy) = 0  by rewrite /Rdiv Rmult_0_l Rabs_R0. 
  move: zE; rewrite (surjective_pairing (Fast2Sum   _ _ _ _)) f2sc. 
  case=> <- <-.
  by rewrite  cl2e /xy; ring.

rewrite /xy ; clear xy  Fxh Fxl Exh x .
wlog ypos: y xh xl zh zl DWx Fy  E1 xh0 y0 ypow x0 / 0 <= y.
  move=> Hwlog.
  case:(Rle_lt_dec 0 y) => yle0.
    by apply:Hwlog.
  have ->: (zh + zl - (xh + xl) * y) / ((xh + xl) * y)= 
           ((- zh + - zl - (xh + xl) * - y) / ((xh + xl) * - y)) by field.
  case:(Hwlog (-y) xh xl (-zh) (-zl))=>//; try lra.
      by apply: generic_format_opp. 
    by rewrite DWTimesFP9_Asym_r E1.
  by move=>nypow; apply:ypow; rewrite -(Ropp_involutive y); apply:is_pow_opp.
  move=> a [[Fzh Fzl] zE].
  split=>//; split.
  by rewrite -(Ropp_involutive zh) -(Ropp_involutive zl); split ;  
     apply: generic_format_opp.
  move: zE; have->: (- zh + - zl)= - (zh + zl) by ring.
  by rewrite ZNE round_NE_opp -ZNE; lra.
wlog xhpos: y xh xl zh zl DWx Fy  E1 xh0 y0 ypow ypos x0 / 0 <= xh.
  move=> Hwlog.
  case:(Rle_lt_dec 0 xh) => xhle0.
    by apply:Hwlog.
  have ->: (zh + zl - (xh + xl) * y) / ((xh + xl) * y)= 
              ((- zh + - zl - (- xh + - xl) * y) / ((- xh + - xl) * y)) 
   by field; lra.
  case:(Hwlog y (-xh) (-xl) (-zh) (-zl))=>//; try lra; try rewrite DWTimesFP9_Asym_l E1 //.
    have [[Fxh Fxl] Exh] := DWx.
    split; [split|]; try apply:generic_format_opp=>//.
    have ->:- xh + - xl = -(xh +  xl) by ring.
    by rewrite ZNE round_NE_opp -ZNE {1}Exh.
  split =>//.
  by rewrite -(Ropp_involutive zh) -(Ropp_involutive zl); apply: DW_sym.
have {} xhpos: 0 < xh by lra.
have {} ypos: 0 < y by lra.
wlog [xh1 xh2]: xl xh  zh zl DWx   xh0 x0 xhpos E1/ 1 <= xh  <= 2-2*u.
  move=> Hwlog.
  have [[Fxh Fxl] Exh] := DWx.
  case: (scale_generic_12 Fxh xhpos)=> exh Hxhs.
  have xhp0: 0 <  xh * pow exh by lra.
  have ->: (zh + zl - (xh + xl) * y) / ((xh + xl) * y) = 
         (zh * pow exh  + zl * pow exh  - 
         (xh * pow exh + xl * pow exh) * y) / ((xh * pow exh + xl * pow exh) * y).
    field.
    split; try lra; split; try lra.
    rewrite -Rmult_plus_distr_r.
    apply: Rmult_integral_contrapositive; move:(bpow_gt_0 two exh); lra.
  case:(Hwlog (xl * pow exh)  (xh * pow exh)(zh * pow exh) (zl * pow exh))  =>//; try lra.
      split;[split|]; try apply:formatS=>//.
      by rewrite -Rmult_plus_distr_r round_bpow -Exh.
    rewrite -Rmult_plus_distr_r; apply: Rmult_integral_contrapositive; 
      move:(bpow_gt_0 two exh); lra.
  by rewrite DWTimesFP9Sx E1.
  move=> a [[Fzh Fzl] zE]; split =>//.
  have hpow: forall x, x = x* pow  exh * pow (- exh).
   move => x; rewrite Rmult_assoc -bpow_plus; 
      have ->: (exh + -exh = 0)%Z by ring.
   by rewrite Rmult_1_r.
  rewrite (hpow zh) (hpow zl); split;[split; apply:formatS|]=>//.
  by rewrite -Rmult_plus_distr_r round_bpow {1}zE.

wlog [y1 y2]: y  zh zl  Fy y0 ypow  ypos E1/ 1 <= y <= 2-2*u.
  move=> Hwlog.
  case: (scale_generic_12 Fy ypos)=> ey Hys.
  have ->: (zh + zl - (xh + xl) * y) / ((xh + xl) * y) = 
   (zh * pow ey  + zl * pow ey - (xh  + xl) * y * pow ey) / ((xh + xl ) * y * pow ey).
    field;  move:(bpow_gt_0 two ey); lra.
  rewrite Rmult_assoc; case:(Hwlog( y * pow ey) (zh * pow ey) ( zl * pow ey)) =>//; try lra.
     by apply:formatS.
    move=> [ eyp Heyp]; apply:ypow.
    exists (eyp - ey)%Z.
    move:   Heyp; rewrite !Rabs_pos_eq; try lra.
    rewrite bpow_plus=> <-; rewrite Rmult_assoc -bpow_plus Z.add_opp_diag_r /=; ring.
  by rewrite DWTimesFP9Sy E1.
  move=> a [[Fzh Fzl] zE]; split =>//.
  have hpow: forall x, x = x* pow  ey  * pow (- ey).
   move => x; rewrite Rmult_assoc -bpow_plus; 
      have ->: (ey + -ey = 0)%Z by ring.
   by rewrite Rmult_1_r.
  rewrite (hpow zh) (hpow zl); split;[split; apply:formatS|]=>//.
  by rewrite -Rmult_plus_distr_r round_bpow {1}zE.
move:(upos p); rewrite -/u=> upos.
have u1 : u < 1 by rewrite /u ; have ->: 1 =  pow 0 by []; apply:bpow_lt; lia.
have [[Fxh Fxl] Exh] := DWx.

have {} y1: 1 + 2*u <= y.
  case/Rle_lt_or_eq_dec: y1 =>y1; first last.
    suff: (is_pow two y) by [].
    exists 0%Z; rewrite -y1 Rabs_pos_eq  /= ; lra.
  suff ->: 1 + 2 * u = succ two fexp 1.
    apply: succ_le_lt=>//.
    have ->: 1 = pow 0 by [].
    apply:generic_format_bpow; rewrite /fexp; lia.
  rewrite succ_eq_pos; try lra.
  rewrite /u u_ulp1; field.
have hxhy: 1+ 2*u <= xh * y <= 4 - 8*u + 4*u*u.
  split.
    rewrite -(Rmult_1_l (_ + _)).
    apply:Rmult_le_compat;  lra.
  have ->: 4 - 8 * u + 4 * u * u = (2 - 2*u) * (2 - 2*u) by ring.
  apply:Rmult_le_compat; lra.
pose ch := rnd_p (xh * y ).
have Fch: format ch by apply:generic_format_round.
have: rnd_p (1 + 2 *u ) <= ch by apply:round_le; lra.
rewrite round_generic; last first.
  rewrite /u u_ulp1 -Rmult_assoc Rinv_r ; last lra.
  rewrite Rmult_1_l -succ_eq_pos; try lra.
  apply: generic_format_succ.
  have -> : 1 = pow 0 by [].
  apply:generic_format_bpow; rewrite /fexp; lia.
move=> h16_lb.
have: ch <= rnd_p ( 4 - 8 * u + 4 * u * u) by apply:round_le; lra.
have->:  (4 - 8 * u + 4 * u * u)= (1 -2 * u + u * u)* (pow 2 ).
  rewrite /=IZR_Zpower_pos /=; ring.
have ch0: ch <> 0 by lra.
rewrite round_bpow  r1m2u // => h16_ub.
pose cl1 := xh*y - ch.
have Fcl1: format cl1.
  by rewrite /cl1 -Ropp_minus_distr; apply/generic_format_opp /mult_error_FLX.
have h17 :Rabs cl1 <= 2*u.
  apply:(Rle_trans _ (/2 * (ulp two fexp (rnd_p (xh * y))))).
    rewrite /cl1 /ch.
    have ->: (xh * y - rnd_p (xh * y)) = -(rnd_p (xh * y) - xh * y) by ring.
    by rewrite Rabs_Ropp;apply:error_le_half_ulp_round.
  rewrite -/ch ulp_neq_0 // /cexp /fexp bpow_plus -/u.
  set mg := mag _ _ .
  suff /(bpow_le two) mg2: (mg <= 2)%Z.
    apply:(Rle_trans _ (/2 * ((pow 2) * u))).
      apply:Rmult_le_compat_l; try lra.
      apply:Rmult_le_compat_r; lra.
    rewrite /= IZR_Zpower_pos /= ; lra.
  rewrite /mg; apply:mag_le_bpow =>//; rewrite Rabs_pos_eq; try lra.
  apply:(Rle_lt_trans _ ((1 - 2 * u) * pow 2)) =>//.
  rewrite -{2}(Rmult_1_l (pow 2)).
  apply:Rmult_lt_compat_r; first by apply: bpow_gt_0.
  lra.
have xlu: Rabs xl <= u.
  have:= (dw_ulp Hp1 DWx).
  suff ->:  / 2 * ulp radix2 fexp xh = u by [].
  rewrite ulp_neq_0 // /cexp /fexp bpow_plus -/u -Rmult_assoc.
  suff -> : / 2 * (pow (mag radix2 xh)) = 1 by ring.
  suff ->:  ((mag radix2 xh)  = 1%Z :>Z).
    rewrite /= IZR_Zpower_pos /=; field.
  apply:mag_unique_pos.
  rewrite /= IZR_Zpower_pos /=; split;lra.

(* diff from algo8*)
pose error :=  errorDWTFP9 xh xl y.
have: error =  errorDWTFP9 xh xl y by [].
rewrite /errorDWTFP9 E1.
move:E1; rewrite /DWTimesFP9 TwoProdE /FMA /=  -/cl1 -/ch.
rewrite (round_generic _ _ _ cl1 Fcl1).

pose cl3 := rnd_p (cl1 + xl * y).
pose e:= cl1 + xl * y  - cl3.

case:(Req_dec xl 0)=>xl0.
  have cl30: cl1 + xl * y = cl1 by rewrite xl0; ring.
  have e0 : e = 0 by rewrite /e /cl3 cl30 round_generic //; ring.
  rewrite cl30 (round_generic _ _ _ cl1) //.
  move=> he.
  have f2sc: (Fast2Sum_correct  p choice ch cl1).
  apply: F2Sum_correct_abs => // ; last first.
    rewrite (Rabs_pos_eq ch); lra.
  move =>errorE.
  split; last first.
    move :(F2Sum_correct_DW' Hp1  f2sc).
    by move:he; case=> <- <-.
  move:he errorE;rewrite (surjective_pairing (Fast2Sum   _ _ _ _)) f2sc; case=> <- <- //.
  move => errorE.
  rewrite -errorE.
  have err0: error = 0.
    rewrite errorE xl0; rewrite  /cl1;
    ring.
  rewrite err0 Rabs_mult /Rdiv Rabs_R0 Rmult_0_l.
   exact: boundDWTFP9_ge_0.
have hcl12:Rabs (cl1 + xl * y ) <= 4 * u - 2 * u *u.
  apply:(Rle_trans _ (Rabs cl1 + Rabs (xl * y))); first by apply:Rabs_triang.
  rewrite Rabs_mult (Rabs_pos_eq y); last lra.
  have : Rabs xl * y <= u * (2 -2 * u).
    apply:Rmult_le_compat; try apply: Rabs_pos; lra.
  lra.
move/(round_le two fexp (Znearest choice)):(hcl12).
rewrite ZNE round_NE_abs -ZNE -/cl3.
have -> : rnd_p (4 * u - 2 * u * u) = 4 * u.
  have -> : (4 * u - 2 * u * u) = (1 - /2*u)*(pow (2 - p)).
    rewrite bpow_plus /= IZR_Zpower_pos /= -/u; field.
  rewrite round_bpow /u (Rmult_comm (/2)) r1mu2 //  -?ZNE  bpow_plus.
  have ->: 4 = pow 2 by [].
  ring.
  move=> cl3_4u.
  rewrite (surjective_pairing (Fast2Sum  _ _ _ _)).
  have f2sc: (Fast2Sum_correct  p choice ch cl3).
  apply: F2Sum_correct_abs => //; try apply:generic_format_round; last first.
  apply:(Rle_trans _ (4 * u)); try lra.
  rewrite Rabs_pos_eq ;lra.
have eub: Rabs e <= 2 * (u * u).
  rewrite /e /cl3 -Ropp_minus_distr Rabs_Ropp.
  have ->: 2 * (u * u) = /2*u *(pow (2 -p)).
    by rewrite bpow_plus /u /= IZR_Zpower_pos /= ; field.
  rewrite /u; apply: error_le_half_ulp'; first lia.
  rewrite bpow_plus  -/u /= IZR_Zpower_pos /=.
  apply:( Rle_trans _ (4 * u - 2 * u * u)) =>//.
  suff: 0 <=  2 * u * u by lra.
  repeat apply:Rmult_le_pos; lra.
  move=>zE errE.
  split; last first.
  move:zE; case => <- <-; 
  by apply: F2Sum_correct_DW' =>//.
move:zE errE; rewrite  f2sc. 
case=> <- <-=> errorE.
rewrite -errorE.
have {} errorE: error = - e .
  by rewrite errorE /e /cl1; ring.
rewrite errorE Rabs_mult Rabs_Ropp.
suff hxy:  1 <=  ((xh + xl) * y).
  have : 0 < ((xh + xl) * y) by lra.
  move/Rinv_0_lt_compat => hinv.
  rewrite (Rabs_pos_eq (/_)); try lra.
  rewrite -[X in _ <= X]Rmult_1_r.
  apply:Rmult_le_compat; try lra.
    by apply:Rabs_pos.
  have->: 1 = /1 by field.
  apply: Rinv_le; lra.
apply:(Rle_trans _ ((1 - u) * (1 + 2 * u))).
  have -> : (1 - u) * (1 + 2 * u) = 1 + u * (1 - 2 * u) by ring.
  suff: 0<=  u * (1 - 2 * u) by lra.
  apply: Rmult_le_pos ; lra.
apply:Rmult_le_compat; try lra.
apply:Rplus_le_compat =>//.
move/Rabs_le_inv : xlu; lra.
Qed.
End Algo9.

End Times.
