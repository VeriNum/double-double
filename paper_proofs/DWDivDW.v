(* Copyright (c)  Inria. All rights reserved. *)

Require Import Psatz ZArith Reals.


From Flocq Require Import Core Relative Sterbenz Operations Plus_error Mult_error.

Require Import mathcomp.ssreflect.ssreflect.
Require Import Bayleyaux.
Require Import DWPlus.
Require Import DWTimesFP.

(* use the bounds of original paper *)
Require Import DWTimesDW_original.
Require Import F2Sum.



Set Implicit Arguments.
Require Import ZArith Znumtheory.

Local Open Scope R_scope.


Local Notation two := radix2 (only parsing).
Local Notation pow e := (bpow two e).
Fact twole3: (two <= 3)%Z. Proof. by rewrite /=; lia. Qed.

Section Div.

Variables p : Z.
Hypothesis   Hp1 : (1 < p)%Z.
Local Instance p_gt_0 : Prec_gt_0 p.
now apply Z.lt_trans with (2 := Hp1).
Qed.



Variable choice : Z -> bool.
Hypothesis ZNE : choice = fun n => negb (Z.even n).

Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format two fexp).
Local Notation ce := (cexp two fexp).
Local Notation mant := (scaled_mantissa two fexp).
Local Notation rnd_p := (round two fexp (Znearest choice)).
Local Notation rnd_p_le := (round_le two fexp (Znearest choice)).
Let u := pow (-p).

Notation double_word xh xl := (double_word  p choice xh xl).



Definition TwoSum x y := (rnd_p (x + y), TwoSum_err p choice  x y).
(* Notation F2S_err a b := (F2Sum_err p choice a b). *)
Notation Fast2Sum := (Fast2Sum  p choice).
(* (a b :R) := (rnd_p (a +b), F2S_err a b). *)
Notation Fast2Mult := (Fast2Mult p choice).
Notation F2P_prod a b  :=  (fst (Fast2Mult a b)).
Notation F2P_error a b  :=  (snd (Fast2Mult a b)).


Hypothesis Fast2Mult_correct: 
  forall a b, a * b =  F2P_prod a b +  F2P_error a b.

Notation F2P_errorE := (F2P_errorE Fast2Mult_correct).


Hypothesis TwoProdE : TwoProd = Fast2Mult. (* or Dekker's algorithm *)

Notation DWTimesFP := (DWTimesFP p choice).

Lemma dw_u xh xl (DWx: double_word  xh xl):   Rabs xl <= u * Rabs xh.
Proof.
case:(DWx)=> [[Fxh Fxl] xE].

  have->: u* Rabs xh =  / 2 * bpow two  (- p + 1) * Rabs (rnd_p (xh + xl)).
    rewrite -xE.
    rewrite bpow_plus -/u.
    have-> : pow 1 = 2 by [].
    have->: / 2 * (u * 2)= u by field.
    by [].
  rewrite -Rabs_Ropp.
  have->: -xl = rnd_p (xh + xl) - (xh + xl) by rewrite -xE; ring.
  by apply: relative_error_N_FLX_round; first lia.
Qed.

Lemma dw_pos xh xl (DWx: double_word  xh xl)(xhpos:  0 <xh):  0 < xh + xl.
Proof.
case:(Rlt_le_dec 0 (xh + xl)) => //.
case:DWx=>[[Fxh Fxl] xE].
move/rnd_p_le; rewrite -xE round_0; lra.
Qed.

Lemma dw_n0 xh xl (DWx: double_word  xh xl)(xhn0:  xh<> 0):  xh + xl <> 0.
Proof.
move=> x0; apply: xhn0.
case:DWx=>[_ xE].
by rewrite xE x0 round_0.
Qed.

Lemma dw_S xh xl e (DWx: double_word  xh xl):
      double_word (xh* pow e) (xl * pow e).
Proof.
  case:(DWx)=> [[Fxh Fxl] xE].
  split; [split|]; try (apply:formatS =>//; lia).
  by rewrite -Rmult_plus_distr_r round_bpow -xE.
Qed.


Section Algo15.

Fact DTas_r: forall  th yh yl,  fst (DWTimesFP yh yl (-th ))= - fst (DWTimesFP yh yl th ).
Proof.
  move=> th yyh yyl.
  pose zh := fst (DWTimesFP yyh  yyl th).
  pose zl := snd (DWTimesFP yyh yyl th).
  by rewrite  (DWTimesFP_Asym_r ZNE  TwoProdE yyh yyl th ).
Qed.

Fact DTas_l: forall th yyh yyl,  fst (DWTimesFP (-yyh) (-yyl) th)= - fst (DWTimesFP yyh yyl th ).
Proof.
move=> th yyh yyl.
pose zh := fst (DWTimesFP yyh  yyl th).
pose zl := snd (DWTimesFP yyh yyl th).
by rewrite (DWTimesFP_Asym_l ZNE  TwoProdE yyh yyl th ).
Qed.

Fact DTf0 a b: DWTimesFP a b 0 = (0 ,0).
Proof.
by rewrite /DWTimesFP TwoProdE /=
          !(Rmult_0_r, round_0, Rplus_0_r, Rminus_0_l, Ropp_0).
Qed.  
  
  
Fact DW_opp: forall a b , double_word a b-> double_word (-a) (-b).
Proof.
move=> a b [[Fa Fb] aE].
split;[split; by apply:generic_format_opp|].
have->: (- a + - b) = -(a +b) by ring.
by rewrite ZNE round_NE_opp  -ZNE -aE.
Qed.

Section algo15_pre.

Variables xh xl yh yl :R.
Notation th := (rnd_p (xh/yh)).
Notation rh  := (fst (DWTimesFP yh yl th)).
Notation rl  := (snd (DWTimesFP yh yl th)).
Notation pih := (fst(TwoSum xh (-rh))).
Notation pil := (snd (TwoSum xh (-rh))).
Notation dh := (rnd_p (pil - rl)).
Notation dl := (rnd_p (dh + xl)).
Notation  d := (rnd_p (pih + dl)).
Notation tl := (rnd_p (d/yh)).

Definition DWDivDW1 := (Fast2Sum th tl).
Hypothesis yhn0: yh <> 0.
Hypotheses (DWx:double_word xh xl) (DWy:double_word yh yl).

Notation y := (yh + yl).
Notation x := (xh + xl).

Notation eta := ((rh + rl - (y*th)) / (y*th)).

Fact h44:rh + rl = th*y * (1 + eta).
Proof.
have upos: 0 < u by rewrite /u; apply: bpow_gt_0.
have u2pos : 0 < u*u by nra.
have yn0:= (dw_n0 DWy yhn0).
case:(Req_dec xh 0)=> xh0.
   rewrite xh0 /Rdiv !(Rmult_0_l, round_0) DTf0 /=; ring.
have xn0:= (dw_n0 DWx xh0).
field; split=>//.
case : (Req_dec  th 0)=>// th0.
suff : xh = 0 by [].
have: xh / yh = 0 by apply: (FLX_round_N_eq0 Hp1 th0 ).
case/ Rmult_integral=>//; by move:(Rinv_neq_0_compat yh yhn0).
Qed.

Fact h44a  (Hp4: (4<= p)%Z): Rabs eta <= 3 / 2 * (u * u) + 4 * (u * (u * u)).
Proof.
have yn0:= (dw_n0 DWy yhn0).
have Fth : format th by apply:generic_format_round.
move :(DWTimesFP_correct ZNE Hp4 Fast2Mult_correct TwoProdE DWy Fth).
case H: (DWTimesFP yh yl th)=>[rh rl].
by rewrite /= -/th -/u Rmult_1_r; case.
Qed.

Fact DWr (Hp4: (4<= p)%Z): double_word rh rl.
Proof.
have Fth : format th by apply:generic_format_round.
move :(DWTimesFP_correct ZNE Hp4 Fast2Mult_correct TwoProdE DWy Fth).
case H: (DWTimesFP yh yl th)=>[rh rl].
by rewrite /= -/th -/u Rmult_1_r; case.
Qed.


Fact h46aux (Hp4: (4 <= p)%Z): 
              (3*u + 9/2*u^2 + 19/2*u^3 + 33/2*u^4 + 27/2* u^5 + 4*u^6) <= 
              (3 * u + 6 * (u * u)).
Proof.
have upos: 0 < u by rewrite /u; apply: bpow_gt_0.
have u2pos : 0 < u*u by nra.
have ult1 : u < 1 by rewrite /u; apply: bpow_lt_1; lia.
rewrite !Rplus_assoc; apply:Rplus_le_compat_l.
suff:   9  * u ^ 2 + 19 * u ^ 3 + 33 * u ^ 4 + 27 * u ^ 5 + 8 * u ^ 6 <=
  12 * (u * u) by lra.
suff: 19 * u ^ 3 + 33 * u ^ 4 + 27 * u ^ 5 + 8 * u ^ 6 <= 3 * u^2 by lra.

suff: (19 * u  + (33 * u ^ 2 + (27 * u ^ 3 + 8 * u ^ 4)))<= 3 by nra.
suff u3: u <= /8.
 have : 8 * u ^ 4 <= u^3. 
      have->:  u^3 = 8 * ((/8) * u^3) by field.
      apply:Rmult_le_compat_l; first lra.
      have->:  u ^ 4 = u * u^3 by ring.
      apply:Rmult_le_compat_r;  nra.
    suff: 28 * u ^ 3 + 33 * u ^ 2 + 19 * u <= 3 by lra.
    apply:(Rle_trans _ (24 * u)); last by lra.
    have->: 28 * u ^ 3 + 33 * u ^ 2 + 19 * u = (28 * u ^ 2 + 33 * u  + 19) * u by ring.
    apply:Rmult_le_compat_r; first  lra.
    suff:  28 * u ^ 2 + 33 * u   <= 5 by lra.
    apply:(Rle_trans _ (40 * u)); last by lra.
    have->:  28 * u ^ 2 + 33 * u =  (28 * u + 33 )*u by ring.
    apply:Rmult_le_compat_r; lra.
change (pow (-p) <= pow (-3) ); apply:bpow_le; lia.
Qed.

Fact  h46 (xhpos : 0 < xh)(Hp4: (4<= p)%Z): Rabs (rh - xh) <= (3 * u + 6 * (u * u)) * xh.
Proof.
have upos:=(upos p); rewrite -/u in upos.
have u2pos: 0 < u * u by nra.
have  ult1: u < 1 by change (pow (-p) < pow 0); apply bpow_lt; lia.
apply:(Rle_trans _ ((3*u + 9/2*u^2 + 19/2*u^3 + 33/2*u^4 + 27/2* u^5 + 4*u^6)*xh));last first.
  apply: Rmult_le_compat_r; first lra.
  by apply:h46aux.
have h44:= h44.
have h44a := (h44a Hp4).
have DWr:= (DWr Hp4).
case:(DWr)=>[[Frh Frl]rE].
case:(rnd_epsl Hp1 choice (rh + rl)) =>  e1; rewrite -rE -/u =>[] [eru e1E].
have rlE: rl = - e1 * (rh+rl).
move: (e1E); ring_simplify( (rh + rl) * (1 + e1)); lra.
move:(e1E); rewrite h44.
case: DWy=> Fy yE.
case:(rnd_epsr Hp1 choice (yh + yl)) =>  ey;  rewrite -yE -/u =>[] [eyu eyE].
have yE': y = (1+ ey) * yh by rewrite {2}eyE; field; move/Rabs_le_inv: eyu; lra.
rewrite {1}yE'.
case:(rnd_epsl Hp1 choice (xh/yh)) =>  e0; rewrite -/u =>[] [e0u e0E].
rewrite {2}e0E.
have yn0:= (dw_n0 DWy   yhn0).
have->: xh / yh * (1 + e0) * ((1 + ey) * yh) * (1 + eta) * (1 + e1) = 
          xh * (1 + e0) * (1 + ey)  * (1 + e1) * (1 + eta).
  field; split;[|split]=>//.
  rewrite e0E; apply: Rmult_integral_contrapositive_currified.
     apply: Rmult_integral_contrapositive_currified; first lra.
    by apply: Rinv_neq_0_compat.
  move/Rabs_le_inv: e0u; lra.
move=> rhE.
have h44':= (Rabs_le_inv _ _ h44a).
have eru':= (Rabs_le_inv _ _ eru).
have er0':= (Rabs_le_inv _ _ e0u).
have eyu':= (Rabs_le_inv _ _ eyu).
have rhu: rh <= xh * (1+u)^3 * (1+ 3/2*u^2 + 4*u^3).
  clear - upos u2pos ult1  xhpos eru'   er0'  eyu' rhE  h44' Hp4.
  rewrite rhE; apply:Rmult_le_compat; last lra.
  + repeat (apply:Rmult_le_pos; try lra).
  + suff: (3 / 2 * (u * u) + 4 * (u * (u * u))) <= 1 by lra.
    apply:(Rle_trans _ (2*u^2)).
      suff:   8*u <= 1 by nra.
      change(pow 3 * pow(-p) <= pow 0); rewrite -bpow_plus ; apply:bpow_le;lia.
    rewrite /= Rmult_1_r; change(pow 1 * (pow (-p)* pow(-p)) <= pow 0).
    rewrite  -!bpow_plus ; apply:bpow_le;lia.
  rewrite !Rmult_assoc; apply: Rmult_le_compat_l; first lra.
  rewrite /= Rmult_1_r; repeat apply:Rmult_le_compat; try lra.
  nra.
have rhl: xh * (1 - u)^3 * (1- 2*u^2) <= rh.
  clear - upos u2pos ult1  xhpos eru'   er0'  eyu' rhE  h44' Hp4.
  rewrite rhE; apply:Rmult_le_compat.
  + repeat (apply:Rmult_le_pos; try lra).
  + suff: 2*u^2 <= 1 by lra.
    rewrite /= Rmult_1_r; change (pow 1 * (pow (-p) * pow (-p)) <= pow 0).
    rewrite -!bpow_plus; apply:bpow_le; lia.
  + rewrite !Rmult_assoc; apply:Rmult_le_compat_l; first lra.
    rewrite /= Rmult_1_r;repeat apply:Rmult_le_compat; try lra.
    apply:Rmult_le_pos; lra.
  apply:(Rle_trans _ ( 1- (3 / 2 * (u * u) + 4 * (u * (u * u))))); last lra.
  suff:  8 *u <=  1  by nra.
  change (pow 3 * pow (-p) <= pow 0); rewrite -bpow_plus ; apply:bpow_le;lia.

apply:Rabs_le.
set f := _ + 4*_.
suff : (- (f -1)) * xh<= rh <= (1 + f) * xh  by lra.
split.
  apply:(Rle_trans _ (xh * (1 - u) ^ 3 * (1 - 2 * u ^ 2))) =>//.
  rewrite Rmult_comm Rmult_assoc; apply:Rmult_le_compat_l; first lra.
  rewrite /f; ring_simplify.
  suff : 0 <= 8 * u ^ 6 + 31*u ^ 5 + 21 * u ^ 4 + 29 * u ^ 3 + 11* u ^ 2 by lra.
  clear -upos u2pos.
  have ->:  8 * u ^ 6 + 31*u ^ 5 + 21 * u ^ 4 + 29 * u ^ 3 + 11* u ^ 2 =  
          (8 * u ^4 + 31*u ^ 3 + 21 * u ^ 2 + 29 * u  + 11) * u^2 by ring.
  suff : 0<=  8 * u ^4 + 31*u ^ 3 + 21 * u ^ 2 + 29 * u  + 11 by nra.
  nra.
apply:(Rle_trans _ (xh * (1 + u) ^ 3 * (1 + 3 / 2 * u ^ 2 + 4 * u ^ 3)))=>//.
rewrite Rmult_assoc Rmult_comm; apply: Rmult_le_compat_r; first lra.
  rewrite /f;lra.
Qed.

End algo15_pre.

Section algo15_prop.
(* 4 <= p et non 3 pour la correction de DWTimesFP *) 
Lemma Algo15_P (xh xl yh yl :R) (Hp4: (4 <= p)%Z) (yhn0: yh <> 0)(DWx:double_word xh xl)
(DWy:double_word yh yl) :
 let th := rnd_p (xh/yh) in 
 let rh := fst (DWTimesFP yh yl th) in
    format (xh - rh).
Proof.
wlog xhpos :  xh xl DWx/ 0 <= xh.
  move=> Hwlog.
  case:(Rle_lt_dec 0 xh) => xhle0; first by apply:(Hwlog xh xl).
  have->: (xh / yh) = - ((-xh)/yh) by field.
  rewrite ZNE round_NE_opp -ZNE=> th; rewrite /th   DTas_r.
  set f := fst _.
  have->: xh - - f = - (-xh - f) by ring.
  apply:generic_format_opp.
  by apply:(Hwlog (-xh) (-xl)); try lra; apply:  DW_opp.
wlog yhpos :  yh yl yhn0  DWy / 0 < yh.
  move=> Hwlog.
  case:(Rlt_le_dec 0 yh) => yhlt0; first by apply:Hwlog. 
  have->: (xh / yh) = - (xh/(- yh)) by field. 
  rewrite ZNE round_NE_opp -ZNE => th; rewrite  DTas_r -DTas_l.
  by apply:Hwlog; try lra;apply:  DW_opp. 
case:   xhpos => xhpos; last first.
  have:(rnd_p (xh / yh)) =0 by rewrite  -xhpos /Rdiv Rmult_0_l round_0.
  rewrite /DWTimesFP /= -xhpos => ->.
  rewrite TwoProdE /= !(Rmult_0_r, round_0, Rplus_0_r, Rplus_0_l, Rminus_0_r).
  apply:generic_format_0.
set x := xh + xl.
set y := yh + yl.
move=>th.
have Fth: format th by rewrite /th; apply:generic_format_round.
move :(DWTimesFP_correct ZNE Hp4 Fast2Mult_correct TwoProdE DWy Fth).

(* h44 *)
have := (h44 yhn0 DWx DWy).
case H: (DWTimesFP yh yl th)=>[rh rl].
rewrite -/y /= -/th.
set eta := ((rh + rl - (y*th)) / (y*th)).
rewrite -/th; move=> h44.
move=> [h44a [[h44bh h44bl] rhE]].
have := (h46 yhn0 DWx DWy xhpos Hp4).
case h': (DWTimesFP yh yl th)=>[rrh rrl].
rewrite H in h'; case h'=>/= h46.
have upos: 0 < u by rewrite /u; apply: bpow_gt_0.
have u2pos : 0 < u*u by nra.
have ult1 : u < 1 by rewrite /u; apply: bpow_lt_1; lia.
have: Rabs (rh - xh )<= /2* xh.
  apply:(Rle_trans _ ((3 * u + 6 * (u * u)) * xh))=>//.
  apply:Rmult_le_compat_r; first  lra.
  apply:(Rle_trans _ (4 * u)).
    suff:  6 * (u * u) <= u by lra.
    have->: 6 * (u * u)= 6*u*u by ring.
    rewrite -[X in _ <= X]Rmult_1_l.
    apply:Rmult_le_compat_r; first  lra.  
    apply:(Rle_trans _ (8* u)); first lra.
    change (pow 3 * u <= pow 0).
    by rewrite -bpow_plus; apply bpow_le; lia.
    change (pow 2 * u <= pow (-1)); rewrite -bpow_plus; apply bpow_le; lia.
move=> h.
apply:sterbenz' =>//.
  by case:(DWx); case.

move/Rabs_le_inv: h.
case; move/(Rplus_le_compat_r xh)=>h1;  move/(Rplus_le_compat_r xh)=>h2; split; lra.
Qed.

Lemma Algo15_cor (xh xl yh yl :R) (Hp4: (4 <= p)%Z) (yhn0: yh <> 0)(DWx:double_word xh xl)
(DWy:double_word yh yl) :
 let th := rnd_p (xh/yh) in 
 let rh := fst (DWTimesFP yh yl th) in
 let rl  := snd (DWTimesFP yh yl th) in
 let (pih, pil) := (TwoSum xh (-rh)) in 
 let dh := rnd_p (pil - rl) in 
  pih = xh -rh /\ pil = 0 /\ dh = -rl.
Proof.
  case:(DWx)=> [[Fxh Fxl] xE].
  move=>th rh rl.
  rewrite (surjective_pairing (TwoSum _ _ )) /=.

 set pih := fst (TwoSum xh (-rh)); set pil := snd (TwoSum xh (-rh));
  set dh := rnd_p (pil - rl).
have h:  rnd_p (xh + - rh) = xh - rh.
rewrite round_generic //.
apply: (Algo15_P _ _ DWx)=>//.
have Frh: format rh.
  rewrite /rh /DWTimesFP  TwoProdE /=; apply:generic_format_round.
have pil0: pil = 0.

rewrite  /pil /= TwoSum_correct //= /TwoSum_sum /= ?h; first ring.
 by apply:generic_format_opp.
move:(pil0); rewrite  h /pil /= => ->; split=>//; split=>//.
rewrite /dh pil0  Rminus_0_l round_generic //; apply:generic_format_opp.
by rewrite /rl /DWTimesFP  TwoProdE /=; apply:generic_format_round.
Qed.

Lemma  Algo15_pih  (xh xl yh yl :R) (Hp4: (4 <= p)%Z) (yhn0: yh <> 0)(DWx:double_word xh xl)
(DWy:double_word yh yl) :
 let th := rnd_p (xh/yh) in 
 let rh := fst (DWTimesFP yh yl th) in 
 let (pih, pil) := (TwoSum xh (-rh)) in 
  pih = xh -rh.
Proof.
 case:  (Algo15_cor  Hp4 (yhn0: yh <> 0)(DWx:double_word xh xl)
(DWy:double_word yh yl)) => he _.
by rewrite /TwoSum  /= he.
Qed.

Lemma  Algo15_pil (xh xl yh yl :R) (Hp4: (4 <= p)%Z) (yhn0: yh <> 0)(DWx:double_word xh xl)
(DWy:double_word yh yl) :
 let th := rnd_p (xh/yh) in 
 let rh := fst (DWTimesFP yh yl th) in 
 let (pih, pil) := (TwoSum xh (-rh)) in 
  pil = 0.
Proof.
 case:  (Algo15_cor  Hp4 (yhn0: yh <> 0)(DWx:double_word xh xl)
(DWy:double_word yh yl)) => _ [he  _].
by rewrite /TwoSum  /= he.
Qed.

Lemma  Algo15_dh (xh xl yh yl :R) (Hp4: (4 <= p)%Z) (yhn0: yh <> 0)(DWx:double_word xh xl)
(DWy:double_word yh yl) :
 let th := rnd_p (xh/yh) in 
 let rh := fst (DWTimesFP yh yl th) in 
 let rl := snd (DWTimesFP yh yl th) in 
 let (pih, pil) := (TwoSum xh (-rh)) in 
  rnd_p (pil - rl)  =  -rl.
Proof.
 case:  (Algo15_cor  Hp4 (yhn0: yh <> 0)(DWx:double_word xh xl)
(DWy:double_word yh yl)) => _ [_   he].
by rewrite /TwoSum  /= he.
Qed.



End algo15_prop.


End Algo15.

Section Algo16.

Section algo16_pre.
    
Variables xh xl yh yl :R.
Notation th := (rnd_p (xh/yh)).
Notation rh  := (fst (DWTimesFP yh yl th)).
Notation rl  := (snd (DWTimesFP yh yl th)).
Notation pih :=  (xh - rh).
Notation dl := (rnd_p (xl - rl)).
Notation  d := (rnd_p (pih + dl)).
Notation tl := (rnd_p (d/yh)).

(* Notation  DWDivDW2 := (Fast2Sum th tl). *)
Hypothesis yhn0: yh <> 0.
Hypotheses (DWx:double_word xh xl) (DWy:double_word yh yl).

Notation y := (yh + yl).
Notation x := (xh + xl).

Notation eta := ((rh + rl - (y*th)) / (y*th)).


End algo16_pre.

  

Definition DWDivDW2(xh xl yh yl :R) :=
let th := rnd_p (xh/yh) in
let (rh, rl ) := (DWTimesFP yh yl th) in
let pih := xh -rh in 
let dl := rnd_p (xl -rl) in
let d := rnd_p (pih + dl) in
let tl := rnd_p (d/yh) in (Fast2Sum th tl).



Lemma DWDivWP1_2 (xh xl yh yl :R) 
                (Hp4: (4 <= p)%Z) (yhn0: yh <> 0)
                (DWx:double_word xh xl)(DWy:double_word yh yl) : 
                (DWDivDW1  xh xl yh yl ) = (DWDivDW2 xh xl yh yl).
Proof.
move:(Algo15_dh Hp4  yhn0 DWx DWy ).
move:(Algo15_pil Hp4  yhn0 DWx DWy ).
move:(Algo15_pih Hp4  yhn0 DWx DWy ).
rewrite /DWDivDW1 /DWDivDW2.
set  th := rnd_p (xh/yh).
case h: DWTimesFP => [rh rl] /=.
have->: (xh + - rh)= xh -rh by ring.
have<- : (- rl + xl)= xl -rl by ring.
by move=>-> -> ->.
Qed.

Fact  DWDivDW2_Asym_r xh xl yh yl  (yn0: yh <> 0): 
  (DWDivDW2 xh xl (-yh) (-yl)) =pair_opp   (DWDivDW2 xh xl yh yl).
Proof.
  have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
  rewrite /DWDivDW2.
set th := rnd_p (xh/yh).
have ->: (rnd_p (xh / - yh)) = -th.
rewrite /th; have ->: xh / - yh = - (xh / yh) by field.
  by rewrite ZNE round_NE_opp -ZNE.
  
  have->: DWTimesFP (- yh) (- yl) (- th) =  DWTimesFP yh yl th.
  
    by rewrite (DWTimesFP_Asym_l ZNE TwoProdE) (DWTimesFP_Asym_r ZNE TwoProdE) /pair_opp !Ropp_involutive.
    rewrite (surjective_pairing (DWTimesFP _ _ _)).
    set rh := fst _.  set rl := snd _.        
    set f:= _ / (-yh).
    
  have -> : f  = -(rnd_p (xh - rh + rnd_p (xl - rl)) /yh) by rewrite /f ; field.
  set  g := _/yh.
  by rewrite ZNE round_NE_opp -ZNE Fast2Sum_asym /=.

Qed.

Fact  DWDivDW2_Asym_l xh xl yh yl (yn0: yh <> 0):
  (DWDivDW2 (-xh) (-xl) yh yl) = pair_opp   (DWDivDW2 xh xl yh yl).
Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
rewrite /DWDivDW2.
set th := rnd_p (xh/yh).
have ->: rnd_p (-xh /  yh)  = - th.
  have ->: -xh /  yh = - (xh /yh) by field.
  by rewrite ZNE round_NE_opp -ZNE /th.
rewrite (DWTimesFP_Asym_r  ZNE TwoProdE).
rewrite (surjective_pairing (DWTimesFP _ _ _)).
set rh := fst _.  
set rl := snd _.   
rewrite /=.
have->:(- xl - - rl) = - (xl -rl) by ring.
rewrite ZNE round_NE_opp -ZNE.
have->: (- xh - - rh + - rnd_p (xl - rl))= - ( xh - rh + rnd_p (xl - rl)) by ring.
rewrite ZNE round_NE_opp -ZNE.
have->: - rnd_p (xh - rh + rnd_p (xl - rl)) / yh = 
         -(rnd_p (xh - rh + rnd_p (xl - rl)) / yh )
     by field.
rewrite ZNE round_NE_opp -ZNE.
by rewrite Fast2Sum_asym.
Qed.

(* to move *)
Fact  DWTimesFP_0_r xh xl : DWTimesFP xh xl 0 = (0, 0).
Proof.
by rewrite /DWTimesFP TwoProdE  F2P_errorE /=
          !(Rmult_0_r, round_0, Rminus_0_r, Rplus_0_r).
Qed.


(* Theorem 7.1 *)
Lemma DWDDW_correct xh xl yh yl  (DWx: double_word xh xl) (DWy: double_word yh yl)
                                 (Hp7: (7 <= p)%Z)(yhn0 : yh <> 0):
  let (zh, zl) := DWDivDW2 xh xl yh yl  in
  let xy := ((xh + xl) / (yh + yl))%R in
  Rabs ((zh + zl - xy) / xy) <= 15*u^2 + 56 * u^3.
Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
have := (upos p); rewrite -/u  => upos.
have u2pos: 0 < u*u by nra.
have ult1: u < 1 by change (pow (-p) < pow 0); apply:bpow_lt; lia.

have  yn0: yh + yl <> 0.
  move=> y0; apply:yhn0.
  case:  DWy=> [[Fyh Fyl]] yE.
  by rewrite yE y0 round_0.
wlog xhpos :  xh xl DWx/ 0 <= xh.
  move=> Hwlog.
  case:(Rle_lt_dec 0 xh) => xhle0; first by apply:(Hwlog xh xl).
  move:( Hwlog (-xh) (-xl)).
  case he: (DWDivDW2 (- xh) (- xl) yh yl) => [zh zl].
  case he':( DWDivDW2 xh xl yh yl) =>[zzh zzl].
  move:(DWDivDW2_Asym_l xh xl yl yhn0).
  rewrite he he'.
   case=> -> -> /=.
  have ->: ((- zzh + - zzl - (- xh + - xl) / (yh + yl)) / ((- xh + - xl) / (yh + yl)))=
         ((zzh + zzl - (xh + xl) / (yh + yl)) / ((xh + xl) / (yh + yl))).
 field.
    split=>//.
    have xhn0: xh <> 0 by lra.
    have  xn0: xh + xl <> 0.
      move=> xn0; apply:xhn0.
      case:  DWx=> [[Fxh Fxl]] xE.
      by rewrite xE xn0 round_0.
   split; lra.
  apply; try lra.
  by apply:DW_opp.

case:   xhpos => xhpos; last first.
have xl0: xl = 0.
case:DWx => [[Fxh Fxl]].
by rewrite -xhpos Rplus_0_l round_generic.
rewrite /DWDivDW2 xl0 -xhpos /Rdiv !( Rplus_0_r, Rminus_0_r ,Rmult_0_l, round_0, Rminus_0_l ).
rewrite  DWTimesFP_0_r /= !( Rplus_0_r, Rminus_0_r ,Rmult_0_l, round_0, Rminus_0_l, Ropp_0, Rabs_R0 ).
nra.

have xhn0 : xh <> 0 by lra.
have xpos:= (dw_pos DWx xhpos).
have  xn0: xh + xl <> 0 by lra.
wlog yhpos :  yh yl yhn0 yn0 DWy / 0 < yh.
  move=> Hwlog.
  case:(Rlt_le_dec 0 yh) => yhlt0; first by apply:Hwlog. 
 move:( Hwlog (-yh) (-yl)).
  case he: (DWDivDW2 xh xl (-yh)(- yl)) => [zh zl].
  case he':( DWDivDW2 xh xl yh yl) =>[zzh zzl].
 move:(DWDivDW2_Asym_r xh xl yl yhn0).
  rewrite he /= he'.  case=> -> ->.
have->: ((- zzh + - zzl - (xh + xl) / (- yh + - yl)) / ((xh + xl) / (- yh + - yl)))=
 ((zzh + zzl - (xh + xl) / (yh + yl)) / ((xh + xl) / (yh + yl))).
by field; lra.
apply; try lra.
  by apply:DW_opp.

  
case:(DWx)=> [[Fxh Fxl]] xE.
case:(DWy)=> [[Fyh Fyl]] yE.
pose y := yh + yl.
pose x := xh + xl.
have ypos:= (dw_pos DWy yhpos); rewrite -/y in ypos.
have iypos: 0 < /y.
  by rewrite /y; apply:Rinv_0_lt_compat.

(* from previous th*)

case:(rnd_epsr Hp1 choice (yh + yl)) =>  ey;  rewrite -yE. 
rewrite -/y -/u;
move=> [eyhu yhE].

case:(rnd_epsl Hp1 choice (xh + xl)) =>  ex;  rewrite -xE. 
rewrite -/x; 
move=> [exhu xhE].
have posep1 e: Rabs e <= u -> 0 < 1+e by case/Rabs_le_inv; lra.
rewrite (surjective_pairing (DWDivDW2 xh xl yh yl)).
move=> xy.
(* from previous th*)
have yyhE: y/yh = 1 + ey.
  rewrite yhE; field; split=>//.
  move/Rabs_le_inv: eyhu.
  move:(bpow_ge_0 two p).
  have : (pow (-p) <1)  by apply:bpow_lt_1; lia.
  lra.
have iyh: (/yh) =  (1 + ey)/y .
  by rewrite yhE; field; split=>//; move: (posep1 ey eyhu);lra.
  
case resE:  DWDivDW2 =>[zh  zl].
move: resE; rewrite /DWDivDW2.


set th := rnd_p (xh/yh).
case:(rnd_epsl Hp1 choice (xh / yh)) => e0; rewrite -/u=> [[e0u]].
rewrite -/th=> the0.
have thE: th = (1+e0)*(1+ ex) * (1+ey)* (x/y).
  rewrite the0 xhE   /Rdiv iyh; by field.
have ep1pos e : Rabs e <= u -> 1-u  <= 1 + e <= 1+u.
  move/Rabs_le_inv; lra.
have thub: th <= (1+u)^3*(x/y).
  clear -upos u2pos ult1 ep1pos e0u exhu eyhu thE xpos iypos .
  move:  (ep1pos e0 e0u) (ep1pos ex exhu)(ep1pos _  eyhu).  
  rewrite thE /x => *; apply:Rmult_le_compat_r.
    nra.
  rewrite /=  Rmult_1_r Rmult_assoc.
  apply:Rmult_le_compat;  nra.
have thlb: (1 -u)^3*(x/y) <= th.
  clear -upos u2pos ult1 ep1pos e0u exhu eyhu thE xpos iypos .
  move:  (ep1pos e0 e0u) (ep1pos ex exhu)(ep1pos _  eyhu).  
  rewrite thE /x => *; apply:Rmult_le_compat_r.
    nra.
  rewrite /=  Rmult_1_r Rmult_assoc.
  apply:Rmult_le_compat; try lra.
    apply:Rmult_le_pos; lra.
  apply:Rmult_le_compat; lra.
case rhlE: DWTimesFP  =>[rh  rl].
rewrite (surjective_pairing (Fast2Sum _ _)).
set pih := xh -rh ; 
set dl := rnd_p (xl -rl).

case:(rnd_epsl Hp1 choice (xl - rl)) => e2.
rewrite -/u -/dl => [[e2u dlE]].
have xlub: Rabs xl <= u* xh. 
  rewrite -(Rabs_pos_eq xh); last lra.
  exact: dw_u.
have ylub: Rabs yl <= u* yh. 
  rewrite -(Rabs_pos_eq yh); last lra.
  exact: dw_u.
have DWr: (double_word  rh rl).
  have Fth: format th by rewrite /th; apply:generic_format_round.
  have Hp4: (4 <= p)%Z by lia.
  move:(DWTimesFP_DWres ZNE Hp4 Fast2Mult_correct TwoProdE DWy Fth).
  case h:  (DWTimesFP yh yl th)=>[rh0 rl0].
  have: (rh0, rl0) = (rh, rl) by rewrite -rhlE -h.
  by case => -> ->.
case: (DWr)=>[[Frh Frl] rE].
have thpos: 0 < (xh/yh).
  rewrite /Rdiv; apply:Rmult_lt_0_compat ; first lra.
  apply: Rinv_0_lt_compat ; lra.
  
have rlub: Rabs rl <= u* rh.
  have ->: u* rh =  / 2 * bpow two  (- p + 1) * Rabs (rnd_p (rh + rl)).
    rewrite -rE.
    rewrite Rabs_pos_eq; last first.
      have Hp4: (4 <= p)%Z by lia.
      have Fth: format th by rewrite /th; apply:generic_format_round.
      apply:(DWTimesFP_zhpos ZNE Hp4 Fast2Mult_correct TwoProdE DWy Fth); try lra.
        rewrite /th.
        suff: rnd_p 0 <= rnd_p (xh / yh).
          case; rewrite round_0 //.
          by move/(@eq_sym _ 0)/eq_0_round_0_FLX; lra.
        apply:round_le; lra.
      by move:rhlE; case h: (DWTimesFP yh yl th)=> [rrh rrl] /=; case.
    rewrite bpow_plus -/u.
    change(  u * rh = / 2 * (u * 2) * rh); field.
  rewrite -Rabs_Ropp.
  have ->: -rl =  rnd_p (rh + rl) - (rh + rl) by rewrite -rE; ring.
  apply:relative_error_N_FLX_round; lia.
  set zzh := fst _.
  set zzl := snd _.
  case =>/=; rewrite /zzh /zzl => zhE zlE.
  
have:Rabs (xl -rl) <= u* xh + u*rh.
apply:(Rle_trans _ (Rabs xl + Rabs rl)); last lra.
  have -> : xl -rl = xl + - rl by ring.
  rewrite -(Rabs_Ropp rl).
  by apply: Rabs_triang.
have->:  u * xh + u * rh = u*xh + u*((rh -xh) +xh) by ring.
move=> haux.
have:  Rabs (xl - rl) <= u * xh + u * (Rabs (rh -xh) +xh).
  apply: (Rle_trans _ (u * xh + u * (rh - xh + xh)))=>//.
  apply/Rplus_le_compat_l/Rmult_le_compat_l; first lra.
  move:(Rle_abs (rh - xh)); lra.
  move=> haux'.
have Hp4: (4 <= p)%Z by lia.
have := (h46 yhn0 DWx DWy xhpos Hp4).
case h': (DWTimesFP yh yl th)=>[rrh rrl].
rewrite rhlE in h'; case h'=>/= h46.

have haux0: Rabs (xl - rl) <= u*xh + u* ((3*u + 6* (u*u))*xh +xh) by nra.
have haux1: Rabs (xl - rl) <= (2* u + 3*(u*u) + 6 * (u*u*u)) * xh by lra.
set d := rnd_p (pih + dl).
case:(rnd_epsl Hp1 choice (pih + dl)) => e3.
rewrite -/u -/d =>  [[e3u dE]].

pose alpha := ((xl - rl) * (e2 + e3 + e2 * e3) + (xh - rh) * e3)/ xh.
have ixh0: 0 < (/xh) by  apply/Rinv_0_lt_compat; lra.
have : d = x - (rh + rl ) + alpha*xh.
  rewrite dE /pih dlE /alpha; rewrite /x;field; lra.
  have h48: Rabs alpha <= 7* (u*u) + 15 *u * (u *u).
  rewrite /alpha Rabs_mult (Rabs_pos_eq (/xh)); last  lra.
  set a := (xl -rl)*_.
  set b := (xh -rh )* _.
  apply:(Rmult_le_reg_r xh); rewrite // Rmult_assoc Rinv_l ?Rmult_1_r; last lra.
  apply:(Rle_trans _ _  _  (Rabs_triang _ _)).
  have aub: Rabs a <= (2 * u + 3 * (u * u) + 6 * (u * u * u)) * xh * Rabs (e2 + e3 + e2 * e3).
    rewrite /a Rabs_mult.
    by apply: Rmult_le_compat_r =>//; apply:Rabs_pos.
  have bub: Rabs b <= (3 * u + 6 * (u * u)) * xh * Rabs e3.
    rewrite /b Rabs_mult.
    have ->: (xh - rh) = - (rh -xh) by ring.
    by rewrite Rabs_Ropp; apply: Rmult_le_compat_r =>//; apply:Rabs_pos.
  apply:(Rle_trans _ _ _ (Rplus_le_compat _ _ _ _   aub  bub)).
  rewrite Rmult_assoc (Rmult_comm xh).
  rewrite (Rmult_assoc _ xh (Rabs e3)) (Rmult_comm xh) -!(Rmult_assoc _ _ xh).
  rewrite -Rmult_plus_distr_r.
  apply:Rmult_le_compat_r; first lra.
  apply: (Rle_trans _ (7* u^2  + 14 * u^3 + 15*u^4 + 6*u^5)).
    have:  Rabs (e2 + e3 + e2 * e3)<= 2*u + u*u.
      apply/(Rle_trans _ _  _  (Rabs_triang _ _))/Rplus_le_compat.
      + apply/(Rle_trans _ _  _  (Rabs_triang _ _)); lra.
      + by rewrite Rabs_mult; apply/Rmult_le_compat; try lra; apply/Rabs_pos.
    clear -upos u2pos  e3u Hp7.
    set e5 := _ + _ *_.
    move:(Rabs_pos e5) (Rabs_pos e3).
    rewrite /e5=> *.
    set b1 := _ * (Rabs e3).
    set a1 := _* Rabs _.
    have: b1 <= 3*u^2 + 6 * u^3 by rewrite /b1 ; nra.
    suff : a1 <= 4*u^2 + 8*u^3+ 15*u^4 + 6*u^5 by lra.
    rewrite /a1.
    have ->:  4 * u ^ 2 + 8 * u ^ 3 + 15 * u ^ 4 + 6 * u ^ 5 = 
              (2 * u + 3 * (u * u) + 6 * (u * u * u)) * (2 * u + u * u) by ring.
    by apply:Rmult_le_compat_l;  nra.
  suff: 7 + 14*u + 15 * u^2 + 6* u^3 <= 7 + 15*u by nra.
  suff: 15 * u + 6 * u ^ 2 <= 1 by nra.
  apply: (Rle_trans _ (16*u)).
    suff: 6 * u <= 1 by nra.
    apply: (Rle_trans _ (8*u)); first lra.
    change (pow 3 * pow (-p) <= pow 0).
   rewrite -bpow_plus; apply/bpow_le; lia.
  change(pow 4 * pow (-p) <= pow 0);  rewrite -bpow_plus; apply/bpow_le;lia.
  move =>dE'.

pose eta := ((rh + rl - (y*th)) / (y*th)).
have := (h44 yhn0 DWx DWy).
clear h' rrh rrl.
move:(rhlE); case h: (DWTimesFP yh yl th)=> [rrh rrl] /=.
 case=> -> ->.
rewrite -/y -/th -/eta=> h44.

have h49: d/yh = (x - th * y)/y * (y/yh) - (eta * th*y)/yh + alpha* (xh/yh).
  rewrite dE' h44; field; split; rewrite /y; lra.
have h50: Rabs (x - th *y) <= xh * ( 3*u + u^2).
  have->: x - th*y = xh -th*yh + xl + -(th*yl) by rewrite /x/y; ring.
have h43: xh -th*yh = -(xh * e0) by rewrite the0; field.
  apply:(Rle_trans _ (Rabs  (xh - th * yh) + Rabs xl + Rabs (- (th * yl)))).
    apply/(Rle_trans _ _  _  (Rabs_triang _ _))/Rplus_le_compat_r.
    by apply/(Rle_trans _ _  _  (Rabs_triang _ _))/Rplus_le_compat_r/Req_le.
  rewrite h43 !Rabs_Ropp Rabs_mult Rabs_pos_eq; last lra.
  have : Rabs (th*yl) <= u * yh * (Rabs th).
    by rewrite Rabs_mult Rmult_comm; apply:Rmult_le_compat_r => //;  apply: Rabs_pos.
  move=> haux2.
  have->: xh * (3 * u + u ^ 2) = xh * u + xh * u + xh * u * (1 + u) by ring.
  apply:Rplus_le_compat.
    apply:Rplus_le_compat; last lra.
    apply: Rmult_le_compat_l; lra.
  apply:(Rle_trans _ (u * yh * Rabs th))=>//.
  rewrite the0 Rabs_mult -Rmult_assoc.
  have he: u * yh * Rabs (xh / yh) = u* xh.
    rewrite Rabs_mult !Rabs_pos_eq; last lra.
      field; lra.
    nra.
  apply: Rmult_le_compat.
  + by rewrite he; nra.
  + by apply: Rabs_pos.
  + by rewrite he; lra.
  apply:(Rle_trans _ _  _  (Rabs_triang _ _)).
  rewrite Rabs_pos_eq;  lra.
pose beta := (ey* (x-th*y)/y - th*(1+ey)*eta + alpha *(xh/yh)).
have h51: d / yh = (x - th*y)/y + beta.
  rewrite h49.
  have->: eta * th * y / yh = eta * th * (y /yh) by field.
  by rewrite /beta yyhE; field.
have bub: Rabs beta <= (12* u^2 + 39* u^3 + 44 * u^4 + 17* u^5)* x/y.
  rewrite /beta.
  apply:(Rle_trans _ _  _  (Rabs_triang _ _)).
  apply:(Rle_trans _  (Rabs (ey * (x - th * y) / y) + Rabs ( - th * (1 + ey) * eta)+ 
                      Rabs (alpha * (xh / yh)))).
    apply/Rplus_le_compat_r/(Rle_trans _ _  _  (Rabs_triang _ _)).
    apply/Rplus_le_compat_l/Req_le; congr Rabs; ring.
  have haux10:  Rabs (ey * (x - th * y) / y) <= u*((3*u + u^2)* (1+u)*x/y).
    rewrite !Rabs_mult Rmult_assoc.
    apply/Rmult_le_compat=>//; first by apply:Rabs_pos.
      by apply:Rmult_le_pos; apply:Rabs_pos.
    rewrite Rmult_assoc (Rabs_pos_eq (/y));last by apply/Rlt_le/Rinv_0_lt_compat.
    apply:Rmult_le_compat_r.
      by apply/Rlt_le/Rinv_0_lt_compat.
    apply:(Rle_trans _ (xh * (3 * u + u ^ 2)))=>//.
    rewrite Rmult_comm; apply/Rmult_le_compat_l; first nra.
    rewrite xhE Rmult_comm; apply/Rmult_le_compat_r.
      rewrite -/x in xpos; lra.
    apply/Rplus_le_compat_l.
    by case:(Rabs_le_inv _ _ exhu); rewrite -/u.
  have haux12: Rabs (alpha * (xh / yh)) <= (7 * u^2 + 15 * u^3) * ((1+ u)^2 * (x/y)).
    rewrite Rabs_mult; apply/Rmult_le_compat; try lra; try  apply:Rabs_pos.
    rewrite Rabs_mult !Rabs_pos_eq; try lra.
      rewrite xhE yhE. 
      have->:  / (y / (1 + ey)) = (1 + ey)/y.
        by field; split; rewrite /y ; move:(ep1pos ey eyhu);  lra.
      have->:  x * (1 + ex) * ((1 + ey) / y) = (1+ ex) * (1+ ey) * (x/y) by field.
      apply:Rmult_le_compat_r. 
        clear - xpos iypos ; rewrite /x;   nra.
      apply:Rmult_le_compat; try apply/Rlt_le/posep1=>//.
         by case: (ep1pos ex).
      by case: (ep1pos ey); lra.
    by apply/Rlt_le/Rinv_0_lt_compat.
  have haux13: Rabs(- th * (1 + ey) * eta) <= (1+u)^3*(2*u^2)*(x/y).
    have->: - th * (1 + ey) * eta = -( th * (1 + ey) * eta) by ring.
    rewrite Rabs_Ropp 2!Rabs_mult.
(*th prec *)
    (* have  h44a: Rabs eta <= 3 / 2 * (u * u) + 4 * (u * (u * u)). *)

    move:(h44a  xh yhn0 DWy Hp4 ).
    rewrite /eta.
    clear h  rrh rrl.
    move:(rhlE); case h: (DWTimesFP yh yl th)=> [rrh rrl] //=.
    case=> hh hl.
    rewrite hh hl.
    rewrite -/y -/th -/eta => h44a.
    have thge0: 0 <= th.
      by rewrite /th -(round_0 two fexp (Znearest choice)); apply/round_le; lra.
    rewrite (Rabs_pos_eq th) //  Rmult_assoc.
    have ->: (1 + u) ^ 3 * (2 * u ^ 2) * (x / y) =  (1 + u) ^ 3 * (x / y)* (2 * u ^ 2) by ring.
    apply:Rmult_le_compat=>//.
    apply/Rmult_le_pos; apply:Rabs_pos.
    apply:(Rle_trans _ ((1+u)* (3/2*u^2+4*u^3))).
      apply:Rmult_le_compat; try apply:Rabs_pos; try lra.
      have heyhu:=(ep1pos ey eyhu).
      rewrite Rabs_pos_eq; lra.
    ring_simplify.
    suff: 8 * u ^ 4 + 11* u ^ 3   <= u ^ 2 by lra.
    have->:  8 * u ^ 4 + 11* u ^ 3  =  (8 * u ^ 2 +11 * u)* u^2 by ring.
    clear - upos u2pos ult1 Hp7.
    suff :  (8 * u ^ 2 + 11 * u) <= 1 by nra.
    apply:(Rle_trans _ (12*u)).
      suff: 8 * u  <= 1  by nra.
      change(pow 3 * pow (-p) <= pow 0).
      rewrite -bpow_plus; apply:bpow_le; lia.
    apply:(Rle_trans _ (16*u)); first lra.
    change(pow 4 * pow(-p) <= pow 0).
    rewrite -bpow_plus; apply:bpow_le; lia.
  lra.
set tl:= rnd_p (d / yh).
case:(rnd_epsl Hp1 choice (d/yh)) => e4.
rewrite -/u -/tl =>  [[e4u tlE]].
pose gamma := (x - th*y)/y * e4 + beta + e4*beta.
have h53 : tl = (x - th*y)/y + gamma.
  by rewrite tlE h51 /gamma; ring.
have h54: Rabs gamma <= (15*u^2 + 55* u^3 + 84*u^4 +61* u^5 + 17*u^6)* (x/y).
  rewrite /gamma.
  apply/(Rle_trans _ _  _  (Rabs_triang _ _)).
  have haux2:  Rabs ((x - th * y) / y * e4 ) <= xh/y * (3*u + u^2) *u.
    rewrite Rabs_mult; apply:Rmult_le_compat =>//; try apply:Rabs_pos.
    rewrite Rabs_mult (Rabs_pos_eq (/y)); last lra.
    have->: xh / y * (3 * u + u ^ 2) = xh * (3 * u + u ^ 2) * /y by field.
    apply:Rmult_le_compat_r; lra.
  rewrite Rabs_mult.
  have {} haux2: Rabs ((x - th * y) / y * e4)  <= (3 * u + u ^ 2) * u *(1+u)* (x/y).
    apply:(Rle_trans _ (xh / y * (3 * u + u ^ 2) * u) _ haux2).
    rewrite Rmult_assoc (Rmult_comm (xh/y)) !Rmult_assoc.
    apply:Rmult_le_compat_l; try lra.
    apply:Rmult_le_compat_l; try lra.
    rewrite -Rmult_assoc /Rdiv; apply:Rmult_le_compat_r; try lra.
    rewrite xhE Rmult_comm; apply: Rmult_le_compat_r; first (rewrite /x; lra).
    by case : (ep1pos _ exhu).
  have:  Rabs ((x - th * y) / y * e4 + beta) <=  Rabs ((x - th * y) / y * e4) + Rabs beta.
    by apply:Rabs_triang.
  clear -  haux2   bub   e4u.
  move: (Rabs_pos beta) (Rabs_pos e4); nra.
have thlE: th + tl = (x/y) + gamma by rewrite h53; field; lra.
have tlub: Rabs tl <=
           x/y*((15 * u ^ 2 + 55 * u ^ 3 + 84 * u ^ 4 + 61 * u ^ 5 + 17 * u ^ 6)+
                            (3*u + 3*u^2 + u^3)).
  apply:Rabs_le.
  move: h54.
  set a := _ + 17*_.
  set b := _+ u^3.
  move/Rabs_le_inv  => [h54a h54b].
  have ->: tl = x/y + gamma -th by rewrite -thlE; ring.
  have: -th <= -(1 - u) ^ 3 * (x / y) by lra.
  move=>*.
  have:  x / y + gamma - th <= x/y + (x/y) * a - (1 - u) ^ 3 * (x / y) by lra.
  have->: x/y + (x/y) * a - (1 - u) ^ 3 * (x / y) = (x/y) * (a + (3*u -3*u^2 + u^3)) by ring.
  move=>*.
  split; last first.
    apply: (Rle_trans _  (x / y * (a + (3 * u - 3 * u ^ 2 + u ^ 3))))=>//.
    apply:Rmult_le_compat_l; first by rewrite /x; clear - xpos iypos; nra.
    by rewrite /b; lra.
  have: - (1+u)^3* (x/y) <= -th  by lra.
  move=>*.
  have:  x/y - (a * (x / y)) - (1+u)^3* (x/y) <=  x / y + gamma - th by lra.
  have->: x/y - (a * (x / y)) - (1+u)^3* (x/y) = - (x/y) * (a +b) by rewrite /b ; ring.
  lra.
move : zhE zlE; rewrite F2Sum_correct_abs //; try lia.
+ move=> zhE zlE.
  have->: zh + zl = (x/y) + gamma by rewrite -zhE -zlE thlE; ring.
  rewrite /xy; ring_simplify(x / y + gamma - x / y).
  rewrite Rabs_mult.
  apply:(Rmult_le_reg_r (x/y)).
    rewrite /x; clear - xpos iypos; nra.
  rewrite (Rabs_pos_eq (/ (x / y))).
    rewrite Rmult_assoc Rinv_l ?Rmult_1_r //.
      apply:(Rle_trans _ _ _   h54).
      apply:Rmult_le_compat_r.
        by clear - xpos iypos; rewrite /Rdiv /x; nra.
      clear - upos u2pos ult1 Hp7.
(*  15 * u ^ 2 + 55 * u ^ 3 + 84 * u ^ 4 + 61 * u ^ 5 + 17 * u ^ 6 <=
  15 * (u * u) + 56 * (u * (u * u)) *)
      suff: 84 * u ^ 4 + 61 * u ^ 5 + 17 * u ^ 6 <= u ^3 by lra.
      have->: 84 * u ^ 4 + 61 * u ^ 5 + 17 * u ^ 6 =
              (84 * u  + 61 * u ^ 2 + 17 * u ^ 3)* u^3 by ring.
      rewrite -[X in _ <= X]Rmult_1_l.
      apply:Rmult_le_compat_r.
        nra.
      apply:(Rle_trans _ (128 *u)).
        suff :  61 * u + 17 * u ^ 2 <= 32  by nra.
        apply:(Rle_trans _ (64 *u)).
          suff:   32 * u  <= 2 by nra.
          change(pow 5 * pow (-p) <= pow 1);rewrite -bpow_plus; apply:bpow_le; lia. 
        change(pow 6 * pow (-p) <= pow 5);rewrite -bpow_plus; apply:bpow_le; lia. 
      change(pow 7 * pow (-p) <= pow 0);rewrite -bpow_plus; apply:bpow_le; lia. 
    rewrite /x; clear - xpos iypos; nra.
  apply/Rlt_le/Rinv_0_lt_compat; clear - xpos iypos; rewrite /Rdiv /x; try nra; try lia.
+ by apply:generic_format_round.
+ by apply:generic_format_round.
apply: (Rle_trans _ _ _ tlub).
rewrite Rabs_pos_eq.
  apply:(Rle_trans _ _ _  _ thlb ).
  rewrite Rmult_comm;  apply: Rmult_le_compat_r.
    rewrite /x; clear - xpos iypos; nra.
  ring_simplify.
  suff:   17 * u ^ 6 + 61 * u ^ 5 + 84 * u ^ 4 + 57 * u ^ 3 + 15 * u ^ 2 +
           6 * u  <= 1.
    lra.
  clear -upos u2pos ult1 Hp7.
  apply:(Rle_trans _ (8*u)); last first.
    by change (pow 3 * pow(-p) <= pow 0);  rewrite -bpow_plus; apply:bpow_le; lia.
  suff: 17 * u ^ 6 + 61 * u ^ 5 + 84 * u ^ 4 + 57 * u ^ 3 + 15 * u ^ 2 <=
           2*u by lra.
  suff : 17 * u ^ 5 + 61 * u ^ 4 + 84 * u ^ 3 + 57 * u ^ 2 + 15 * u  <= 2 by nra.
  apply:(Rle_trans _ (16*u)); last first.
    by change(pow 4 * pow (-p) <= pow 1);rewrite -bpow_plus; apply:bpow_le; lia. 
  suff : 17 * u ^ 4 + 61 * u ^ 3 + 84 * u ^ 2 + 57 * u   <= 1  by nra.
  apply:(Rle_trans _ (64*u)); last first.
    by change( pow 6 * pow (-p) <= pow 0); rewrite -bpow_plus; apply:bpow_le; lia.
  suff:  17 * u ^ 3+ 61 * u ^ 2+ 84 * u <= 4  by nra.
  apply:(Rle_trans _ (128 *u)); last first.
    by change( pow 7 * pow (-p) <= pow 2); rewrite -bpow_plus; apply:bpow_le; lia.
  suff:  17 * u ^ 2 + 61 * u <= 32  by nra.
  apply:(Rle_trans _ (64 *u)); last first.
    by change( pow 6 * pow (-p) <= pow 5); rewrite -bpow_plus; apply:bpow_le; lia.
  suff:  32 * u  <= 2 by nra.
  by change( pow 5* pow (-p) <= pow 1);  rewrite -bpow_plus; apply:bpow_le; lia.
clear - thlb  upos u2pos ult1 xpos iypos.
apply:(Rle_trans _ ((1 - u) ^ 3 * (x / y))) =>//; rewrite /x.
apply: Rmult_le_pos; rewrite /= /Rdiv.
  by apply: Rmult_le_pos;  nra.
nra.
Qed.

End Algo16.


Lemma Prop7_2 y (Fy: format y) (yn0: y <> 0) : let t := rnd_p (/y) in format (y*t -1).
Proof.
rewrite /=.
wlog ypos : y Fy yn0 / 0 < y.
  move=> Hwlog.
  case:(Rlt_le_dec 0 y); first by apply:Hwlog.
  case=>// yneg.
suff -> : y * rnd_p (/ y) = (-y) * rnd_p (/(-y)).
    apply: Hwlog; try lra.
    by apply:generic_format_opp.
  have-> : / - y = - (/y) by field.
  by rewrite ZNE round_NE_opp -ZNE; ring.
clear yn0.
wlog hy: y Fy ypos / 1 <= y <= 2-2*u.
  move=> hwlog.
  case: (scale_generic_12 Fy ypos)=> ey Hys; last first.
  suff ->: y * rnd_p ( / y) = (y * pow ey) *  rnd_p (/ (y * pow ey)).
    apply:hwlog=>//.
(* arg Z-> bool ??? *)
      by apply:formatS.
    by move:(bpow_gt_0 two p); nra.
  have ->: / (y * pow ey) = /y * (pow(-ey)).
    have peygt0:=(bpow_gt_0 two ey);
    apply:(Rmult_eq_reg_r (pow(ey))); try lra.
    rewrite Rmult_assoc -bpow_plus ; ring_simplify (- ey+ ey)%Z; rewrite /=.
    field; split; lra.
  rewrite round_bpow. 
  have->: y * pow ey * (rnd_p ( / y) * pow (- ey)) = y * (rnd_p ( / y)) * (pow ey * pow (- ey)) by ring.
  rewrite -bpow_plus ; ring_simplify ( ey+ -ey)%Z;rewrite /=; ring.
set t := rnd_p (/ y).
have upos:= (upos p); rewrite -/u in upos.
have ult1: u < 1.
  change( pow (-p) < pow 0); apply:bpow_lt; lia.
have [iylb iyub]: /(2-2*u) <= /y <= 1.
  split.
    apply:Rinv_le; lra.
  apply:(Rmult_le_reg_r y)=>//.
  rewrite Rinv_l; lra.
have :/2 <= /y.
  apply:(Rle_trans  _ (/ (2 - 2 * u)))=>//.
  apply:Rinv_le; lra.
move/rnd_p_le.
rewrite -/t.
have->: /2 = pow (-1) by [].
  rewrite round_generic; last by apply:generic_format_bpow; rewrite /fexp; lia.
have <-:  /2 = pow (-1) by []=> tlb.
have tub: t <= 1.
  have ->: 1 = rnd_p 1.
    by change (pow 0 = rnd_p (pow 0)); rewrite round_generic //;  apply:generic_format_bpow; rewrite /fexp; lia.
  by rewrite /t; apply:round_le.
have: Rabs (t - /y) <= u/2.
have ->: u/2 = / 2 * pow (- p) * pow 0.
  change (u/2 = / 2 * u * 1); field.
  apply:error_le_half_ulp'=> /=;  try lia.
  by rewrite Rabs_pos_eq=>//; apply/Rlt_le/Rinv_0_lt_compat.
move/Rabs_le_inv=> [hlb hub].
have haux : u/2 <= u/y.
  apply:(Rmult_le_compat_l); first lra.
  apply:Rinv_le; lra.
have: (1-u)/y <= t <= (1 +u)/y by lra.
case; move/(Rmult_le_compat_r y _ _  (Rlt_le 0 y ypos)).
rewrite Rmult_assoc Rinv_l ?Rmult_1_r; last lra.
move=> haux1.
move/(Rmult_le_compat_r y _ _  (Rlt_le 0 y ypos)).
rewrite [X in _ <= X]Rmult_assoc  Rinv_l ?Rmult_1_r; last lra.
move=> haux2.
have : -u <= 1 - y*t <= u by lra.
case :(@ex_mul p y 0)=>//.
  by rewrite Rabs_pos_eq /= ; lra.
rewrite /= -/u Rmult_1_r => my yE.
 case :(@ex_mul p t (-1))=>//.
  rewrite Rabs_pos_eq=>//; lra.
  by apply:generic_format_round.
have->: (2 * pow (- p) * pow (-1)) = u .
  by change( 2* u * (/2) = u); field.
move=> mt tE.
have : 1 -y*t = 1 - (IZR (my * mt) )   *2* u^2 by rewrite mult_IZR yE tE; ring.
have ->:  1 - IZR (my * mt) * 2 * u ^ 2 = (pow (2*p -1) -  IZR (my * mt)) *( 2 * u ^ 2).
  rewrite Rmult_minus_distr_r.
  suff ->: pow (2 * p - 1) * (2 * u ^ 2) = 1 by ring.
  rewrite !bpow_plus.
  have ->: (2*p = p + p)%Z by ring.
  rewrite bpow_plus /u.
  ring_simplify.
  have->: 2 * pow p ^ 2 * pow (- (1)) * pow (- p) ^ 2 = 2* pow (- (1))* (pow p *pow (- p)) ^ 2 by ring.
  rewrite -bpow_plus; ring_simplify (p + -p)%Z.
  change( pow 1 * pow (-1) * 1 ^2 = 1).
  rewrite -bpow_plus; ring_simplify (1 + -1)%Z=>/=; ring.
move=> ytE ytb.
have: Rabs (pow (2 * p - 1) - IZR (my * mt)) < pow p.
  move/Rabs_le:ytb; rewrite   ytE Rabs_mult ( Rabs_pos_eq (2 * u ^ 2)); last by clear -upos; nra.
  rewrite -!Rmult_assoc Rmult_1_r -[X in _ <= X]Rmult_1_l.
  move/(Rmult_le_reg_r _ _ _ upos).
  set rabs := Rabs _.
  move => h.
  apply:(Rle_lt_trans _ (pow (p -1))).
    apply:(Rmult_le_reg_r (2 *u)).
      lra.
    suff -> : pow (p - 1) * (2 * u)= 1 by lra.
    change(pow (p - 1) * (pow 1  * pow (-p)) = 1).
    by rewrite -!bpow_plus;  ring_simplify (p - 1 + (1 + - p))%Z.
  apply: bpow_lt; lia.
move=> hrabs.
have->: (y * t - 1) = - (1 -y*t) by ring.
apply:generic_format_opp.
rewrite ytE.
have->: (2 * u ^ 2) = pow (1 - 2*p).
  have ->: u ^ 2 = u * u by ring.
  change (pow 1  * (pow (-p)  * pow (-p)) =  pow (1 - 2 * p)).
  rewrite -!bpow_plus.
  congr bpow; ring.
apply:formatS =>//.
apply/generic_format_FLX.
pose f := (Float two  (2^(2*p -1) - my* mt) 0).
apply/(FLX_spec _ _ _ f); rewrite /f; set q := (2*p -1)%Z; rewrite /F2R /=.
  rewrite Rmult_1_r minus_IZR.
  rewrite -IZR_Zpower /= /q //; lia.
apply:lt_IZR.
rewrite abs_IZR minus_IZR  !(IZR_Zpower two); rewrite /q //;  lia.
Qed.


Section Algo17.

Section Algo17_pre.
Variables (xh xl yh yl :R).

Notation th := (rnd_p (/yh)).
Notation rh := (1 -yh*th).
Notation rl := (- (rnd_p (yl*th))).
Notation eh := (fst  (Fast2Sum  rh rl)).
Notation el:= (snd (Fast2Sum  rh rl)).



Notation dh := (fst (DWTimesFP9 p choice eh el th)).
Notation dl :=  (snd (DWTimesFP9 p choice eh el th)).
Notation mh := (fst (DWPlusFP p choice  dh dl th)).
Notation  ml := (snd (DWPlusFP p choice  dh dl th)).
Let  DWDivDW3 := (DWTimesDW12 p choice  xh xl mh ml).
Hypothesis yb: 1 <= yh <= 2 - 2 * u.


Hypotheses (DWx: double_word xh xl) (DWy: double_word yh yl) (Hp14: (14 <= p)%Z).


 Lemma DWDDW3_correct_aux  :
  let (zh, zl) := DWDivDW3   in
  let xy := ((xh + xl) / (yh + yl))%R in
  Rabs ((zh + zl - xy) / xy) <= 98/10*u^2.
 Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
   have upos:= (upos p); rewrite -/u in upos.
   have ult1 :  u < 1 by  rewrite /u; apply: bpow_lt_1; lia.
   have u2pos: 0 < u*u by nra.
   case:(DWy)=> [[Fyh Fyl] yE].
   
   rewrite /=.
   have hiy2: /2 < /yh.
   apply:Rinv_lt; lra.
   have hiy1: /yh <= 1 by  rewrite -Rinv_1; apply: Rinv_le;  lra.
   have thb: /2 <= th <= 1.
   have->: /2 = rnd_p (/2).
   change (pow (-1) = rnd_p (pow (-1))).
   by rewrite round_generic //; apply: generic_format_bpow; rewrite /fexp; lia.
   
     have->: 1 = rnd_p (1).
   change (pow (0) = rnd_p (pow (0))).
   by rewrite round_generic //; apply: generic_format_bpow; rewrite /fexp; lia.
   split; apply: round_le; lra.
   
   have theb:Rabs (th - /yh) <= u/2.
   have ->: u/2 = /2 * pow (-p) * pow 0 by rewrite -/u /=; field.
   apply: error_le_half_ulp'; first lia.
   by rewrite Rabs_pos_eq /=; lra.
   have Frh: format rh.
   rewrite -(Ropp_involutive rh); apply/generic_format_opp.
   rewrite Ropp_minus_distr; apply/Prop7_2 =>//; lra.
   set y  := yh + yl.
   have yn0: y <> 0 by  apply:(dw_n0 DWy); lra.
   
have h57 : th * (2 - y * th) - /y = -y * (th - /y) ^2 by field.

have ylu: Rabs yl <= u.
  rewrite /u; apply/(double_lpart_u ZNE _ DWy); try lia; lra.
have ryhth: Rabs (yl * th) <= u.
  rewrite Rabs_mult (Rabs_pos_eq th); last lra.
  nra.
have rrl: Rabs rl <= u. rewrite Rabs_Ropp.
  rewrite ZNE -round_NE_abs -ZNE.
  have ->: u = rnd_p u .
    rewrite round_generic -/u //; apply: generic_format_bpow; rewrite /fexp;lia.
  by apply:round_le.
have h57': Rabs (rl + yl*th) <= u^2/2.
  rewrite -Rabs_Ropp Ropp_plus_distr Ropp_involutive. 
  have ->:  u ^ 2 / 2 = /2 * (pow (-p)) * pow (-p) by rewrite /u; field.
  by apply:error_le_half_ulp'; rewrite /u //; lia.
have rhu: Rabs rh <= u.
  have ->: rh = - (yh* (th - /yh)) by field; lra.
  rewrite Rabs_Ropp Rabs_mult Rabs_pos_eq; last lra.
  have ->: u = 2 * (u/2) by field.
  apply: Rmult_le_compat; try lra.
  by apply:Rabs_pos.

pose eta := rl + yl*th.
have ehlE: el = rh + rl  -eh.
  have hyh : (pow 0 ) <= Rabs yh by rewrite /= Rabs_pos_eq; lra.
  case:(ex_mul  0 hyh Fyh)=> myh yhE.
  have hth : pow (-1) <= Rabs th by change (/2 <= Rabs th); rewrite Rabs_pos_eq; lra.
  have Fth: format th by apply:generic_format_round.
  case:(ex_mul  (-1) hth  Fth)=> mth thE.
  have rhE: yh*th = IZR (myh*mth) * (2 * u^2).
    rewrite thE yhE  mult_IZR -/u.
    have ->:  pow (-1) = /2 by [].
    rewrite /=;field.
  have h1 : pow (-p) <= Rabs 1. 
    change (pow (-p) <= Rabs (pow 0)); rewrite  Rabs_pos_eq ;last (rewrite /=;lra); apply:bpow_le; lia.
  have F1: format 1 by change (format (pow 0)); apply:generic_format_bpow; rewrite /fexp; lia.
  case : (ex_mul (-p) h1 F1)=> m1 E1.
  have rhE': rh = IZR (m1 -  (myh * mth)) * (2 * u ^ 2).
    rewrite  rhE E1.
    have ->: (2 * pow (- p) * pow (- p)) = 2 * u^2 by rewrite /u; ring.
    rewrite -Rmult_minus_distr_r -minus_IZR; ring.
  pose frh := (Float two ((m1 - myh * mth))(1- 2 * p)).
  case: (Req_dec yl 0) => yl0.
    have ->: rl = 0 by rewrite yl0 Rmult_0_l round_0 Ropp_0.
    rewrite Fast2Sumf0 //=; ring.
  have ylth0: yl * th <> 0 by apply:Rmult_integral_contrapositive_currified ; lra.
  have rl0:  rl <> 0.
    suff: rnd_p (yl * th) <> 0 by lra.
    apply:round_neq_0_negligible_exp; by rewrite ?negligible_exp_FLX.
  rewrite /el /=; apply: (F2Sum_correct_proof  Hp1  _  _ Frh )=>//.
    by apply/generic_format_opp/generic_format_round.
  exists frh; split.
    rewrite /frh /F2R.
    set m := ((m1 - myh * mth) )%Z.
    set frhe := (1-2 * p )%Z.
    rewrite /= E1 rhE /m /frhe.
    have->: pow (1 - 2 * p) = 2 * u ^2.
      have -> :(1- (2*p)  = 1 + ((- p) + -p))%Z by ring.
      rewrite /u !bpow_plus; have ->: pow 1 = 2 by [];ring.
    rewrite -/u.
    have ->: (2 * u * u) = (2 * u ^ 2) by ring.
    rewrite minus_IZR; ring.
  have->:  Fexp frh = (1 -2 *p)%Z by rewrite /frh /F2R //=.
  rewrite /cexp {1}/fexp.
  suff: (mag radix2 rl <= 1 -  p)%Z by lia.
  apply:mag_le_bpow=>//.
  apply:(Rle_lt_trans  _ u)=>//.
  rewrite /u bpow_plus.
  change (pow (-p) < 2 * (pow (-p))).
  move:(bpow_gt_0 two (-p) ); lra.
  (* move:(rhu). *)
  (* rewrite rhE' Rabs_mult -abs_IZR. *)
  (* have ->: (Fnum frh) = (m1 - myh * mth) %Z by rewrite /frh. *)
  (* move/(Rmult_le_compat_r (pow (2*p -1)) _ _ (bpow_ge_0 two (2*p -1))). *)
  (* rewrite Rabs_pos_eq;  last by clear - upos; nra. *)
  (* rewrite Rmult_assoc. *)
  (* have ->:  (2 * u ^ 2 * pow (2 * p - 1)) = 1. *)
  (*   have->: (2 * p - 1 = p + p -1)%Z by ring. *)
  (*   rewrite /u !bpow_plus. *)
  (*   have->:   2 * pow (- p) ^ 2 * (pow p * pow p * pow (- (1))) =  *)
  (*                     2 * (pow(-p) *(pow p)) * (pow(-p) *(pow p)) * pow (- (1)) by ring. *)
  (*   rewrite -bpow_plus. *)
  (*   have->: (-p + p = 0)%Z by ring. *)
  (*   have ->: pow (- (1)) = /2 by []. *)
  (*   rewrite /=; field. *)
  (* rewrite Rmult_1_r. *)
  (* have ->: u * pow (2 * p - 1) = pow (p -1). *)
  (*   have->: (2*p = p + p)%Z by ring. *)
  (*   rewrite /u -bpow_plus; congr bpow; ring. *)
  (* move=>h. *)
  (* apply:le_IZR; rewrite minus_IZR. *)
  (* apply:(Rle_trans _ (pow (p - 1)))=>//. *)
  (* rewrite bpow_plus IZR_Zpower; last lia. *)
  (* have->:pow(-1) = /2 by []. *)
  (* suff: 1 <= (pow p)/2  by nra. *)
  (* apply:(Rmult_le_reg_r 2); first lra. *)
  (* have->:  pow p / 2 * 2 = pow p by field. *)
  (* rewrite Rmult_1_l. *)
  (* change (pow 1 <= pow p); apply:bpow_le; lia. *)
have h58:  eh + el = 1 - yh*th -yl*th + eta by rewrite /eta ehlE; ring.
have rhlu: Rabs (rh + rl) <= 2 *u  by apply:(Rle_trans _ _  _  (Rabs_triang _ _)); lra.
have ehu: Rabs eh <= 2*u.
rewrite /=.
rewrite ZNE  -round_NE_abs -ZNE.
suff ->: 2 * u = rnd_p (2 *u) by apply: round_le.
suff->: 2*u = pow (1 - p) by 
   rewrite round_generic //;apply:generic_format_bpow; rewrite /fexp; lia.
by change ((pow 1 * pow (-p)) = pow(1 -p)); rewrite bpow_plus.
have elu: Rabs el <= u^2.
  rewrite  ehlE   /= -Ropp_minus_distr Rabs_Ropp.
  have ->:  u * (u * 1 )= /2 * u * pow (1-p).
  rewrite /u bpow_plus;have->: pow 1 = 2 by []; field.
  apply:error_le_half_ulp'; first lia.
  by rewrite bpow_plus; have->: pow 1 = 2.  
pose e := eh + el.
have eE: e = rh + rl by rewrite /e ehlE; ring.
have eu: Rabs e <= 2*u by rewrite eE; apply:(Rle_trans _ _  _  (Rabs_triang _ _)); lra.
pose omega1 :=   (dh + dl - e*th)/(e*th).
have dh0: e = 0 -> dh = 0.
  move=> e0; rewrite /e /= -eE e0 /DWTimesFP9 TwoProdE /FMA /= 
    !(round_0, Rmult_0_l,Rplus_0_l, Rminus_0_r, Rminus_0_l) 
    ZNE round_NE_opp -ZNE (round_generic _ _ _ rh) //.
  have->: rl - - rh = 0 by lra. 
  by rewrite !(round_0, Rmult_0_l).
have  dl0:  e = 0 ->  dl = 0.
  move=> e0;rewrite /e /= -eE e0 /DWTimesFP9 TwoProdE /FMA /= 
   !(round_0, Rmult_0_l,Rplus_0_l, Rminus_0_r, Ropp_0, Rminus_0_l).
   rewrite (round_generic _ _ _  (-rh)); last by apply/generic_format_opp.
  have->: rl - - rh = 0 by lra. 
  by rewrite !(round_0, Rmult_0_l, Rminus_0_r).
have o1_0 : e = 0 -> omega1 = 0.
  move=> e0; rewrite /omega1.
  have->: (dh + dl - e * th)= 0  by rewrite dh0 // dl0 //  e0 //; ring.
  by rewrite /Rdiv Rmult_0_l.
have h59a : dh + dl = e*th * (1 + omega1).
  case:(Req_dec e 0)=> e0.
    rewrite dh0 //  /e /= -eE e0 /DWTimesFP9 TwoProdE /FMA /= 
    !(round_0, Rmult_0_l,Rplus_0_l, Rminus_0_r, Rminus_0_l, Ropp_0).
    rewrite ZNE round_NE_opp -ZNE (round_generic _ _ _ rh) //.
    have->: rl - - rh = 0 by lra. 
    by rewrite !(round_0, Rmult_0_l, Rminus_0_r).
  rewrite /omega1 ; field; split=>//.
  apply:round_neq_0_negligible_exp; first  by rewrite ?negligible_exp_FLX.
  apply/Rinv_neq_0_compat; lra.
have h59: Rabs omega1 <= 2* u^2.
  case:(Req_dec e 0)=> e0.
    rewrite   o1_0 // Rabs_R0; clear - upos ; nra.
  rewrite /omega1/u.
  have Hp3 : (3 <= p)%Z by lia.
  have DWe : double_word eh el.
    by apply: F2Sum_correct_DW.
have Fth: format th by apply: generic_format_round.

move: (@DWTimesFP9_correct _ _ ZNE Hp3 TwoProdE eh el th DWe Fth).
 case H:  DWTimesFP9 => [zh zl].
case.
by rewrite fstE sndE /e.

have DWe : double_word eh el by apply:F2Sum_correct_DW'.
have Hp3 : (3 <= p)%Z by lia.
have Fth: format th by apply:generic_format_round.

have DWd : double_word dh dl.

move : (DWTimesFP9_correct ZNE Hp3 TwoProdE DWe Fth).
case H: (DWTimesFP9 p choice eh el th) => [zh zl].
by case.

case: (DWPlusFP_correct Hp1 ZNE Hp3 Fth DWd).
rewrite / relative_errorDWFP.

set omega2 := (mh + ml - (dh + dl + th))/ (dh + dl +th).

have h60a: mh + ml = (th + dh +dl)*(1 + omega2).

  case:(Req_dec (dh + dl + th) 0) => h0.
    case:(DWd)=> [[Fdh Fdl] dE].
    have f2s0 x (Fx: format x):  Fast2Sum (-x) x = (0 ,0).
      rewrite /Fast2Sum /F2SumFLX.Fast2Sum.
      have ->: -x + x = 0 by ring.
      rewrite round_0 Rminus_0_l Ropp_involutive (round_generic _ _ _ x) //.
      have ->: x - x = 0 by ring.
      by  rewrite round_0.
    have mh0: mh = 0 /\ ml = 0.
      rewrite /DWPlusFP.
      rewrite TwoSum_correct // TwoSum_sumE.
      have ->: dh + th = -dl by lra.
      have ->: rnd_p (- dl) = -dl by rewrite ZNE round_NE_opp -ZNE round_generic.
      have->: (- dl - - dl) = 0 by ring.
      rewrite Rplus_0_r (round_generic _ _ _  dl) //.
      by rewrite f2s0 //. 
    case:mh0 => -> ->.
    have ->: th + dh + dl = 0 by lra.
    ring.
  by rewrite /omega2; field.
rewrite -/u.
move=>  h59' DWm.
(* have  h60b: Rabs omega2 <=  2*u^2 + 5*u^3. *)
(*   apply: (Rle_trans _  (pow (1 - 2 * p) / (1 - pow (1 - p))))=>//. *)
(*   apply: DWPlusFP_baux; lia. *)
 
 pose alpha := e*omega1 + omega2 + omega2*e + omega2*omega1*e.
have h61: mh + ml = th + e*th + alpha *th.
  case:(Req_dec e 0)=> e0.
    rewrite h60a /alpha e0 dh0 // dl0 //  o1_0 //.
    by ring.
  rewrite   /alpha /omega1 /omega2  h60a  h59a.
  field.
  split; first lra; split =>//.
  have ->:   e * th * (1 + omega1) + th = th * (1 + e  * (1 + omega1)) by ring.
  apply: Rmult_integral_contrapositive_currified; try lra.
  suff: 0 < 1 + e * (1 + omega1) by lra.
  have: Rabs ( e * (1 + omega1)) <= 2*u * (1 + 2* u^2).
    rewrite Rabs_mult; apply: Rmult_le_compat; (try apply:Rabs_pos) =>//.
    apply:(Rle_trans _ _  _  (Rabs_triang _ _)); apply:Rplus_le_compat =>//.
    by rewrite Rabs_pos_eq; lra.
  move / Rabs_le_inv.
  suff: 0 < 1  - (2 * u * (1 + 2 * u ^ 2)) by lra.
  suff: (2 * u * (1 + 2 * u ^ 2)) < 1 by lra.
  apply:(Rlt_trans _( 4*u)).
    suff: (2*u) * (2* u^2) < (2*u) * 1  by lra.
    apply: Rmult_lt_compat_l.
      clear -upos ; nra.
    have ->: u^2 = u * u by ring.
    have ->:   2 * (u * u) = pow (1 -p -p).
      rewrite !bpow_plus /u. 
      have ->: 2 = pow 1 by []; ring.
    change   (pow (1 - p - p) < pow 0).
    apply:bpow_lt; lia.
  change (pow 2 * pow (-p) < pow 0).
  rewrite -bpow_plus.
  apply:bpow_lt ; lia.
(*ici*)
have: Rabs alpha <=  2*u^2 + 9 * u^3.
  rewrite /alpha.
  apply:(Rle_trans _ ((Rabs (e * omega1))+ (Rabs omega2) + (Rabs (omega2*e))+(Rabs (omega2 * omega1 * e)))).
    apply:(Rle_trans _ _  _  (Rabs_triang _ _)); apply: Rplus_le_compat_r.
    apply:(Rle_trans _ _  _  (Rabs_triang _ _)); apply: Rplus_le_compat_r.
    apply:(Rle_trans _ _  _  (Rabs_triang _ _)); apply: Rplus_le_compat_r; lra.
  have: Rabs (e * omega1) <= (2*u)*(2*u^2).
    by rewrite Rabs_mult; apply:Rmult_le_compat ; try lra; try apply:Rabs_pos.
  have:  Rabs (omega2 * e) <= (2*u^2 )*(2*u).
    by rewrite Rabs_mult; apply:Rmult_le_compat ; try lra; try apply:Rabs_pos.
  have:  Rabs (omega2 * omega1 * e) <=   (2*u^2 )*(2*u^2)*(2*u).
    rewrite 2!Rabs_mult.
    apply:Rmult_le_compat ; try lra; try apply:Rabs_pos.
      by apply: Rmult_le_pos;apply: Rabs_pos.
    by apply:Rmult_le_compat ; try lra; try apply:Rabs_pos.
  move => *.
  apply:(Rle_trans _ (2*u^2 + 8*u^3 + 8 *u^5)).
lra.

  suff : 8 * u ^ 5 <= u^3.
    lra.

  clear -upos Hp14.
have ->: 8 * u^5  = (8*u^2)* u^3 by ring.
  rewrite -[X in _ <= X] Rmult_1_l.
  apply:Rmult_le_compat_r; try nra.
  have u16: u <= /4.
    change (pow (-p) <= pow (-2)).
    apply:bpow_le; lia.
  nra.
(*la*)
move=> h62.
have h62b: mh +ml = th * (2-y*th) + th* (eta + alpha).
  rewrite h61 /e h58.
  have-> : rh - yl * th = 1 - y*th by rewrite /y; ring.
  ring.
 
have h62c: Rabs (mh +ml -/y )= 
           Rabs (th * (2 - y * th) - /y + th * (eta + alpha)).
  by rewrite h62b; congr Rabs; ring.

have ypos: 0 < y.
  by rewrite /y; move/Rabs_le_inv:   ylu ; lra.
have h63: Rabs (mh + ml - / y) <= 
                y * (th - /y)^2 + th* (5/2*u^2 + 9 * u^3).
  rewrite h62c h57.
  apply:(Rle_trans _ _  _  (Rabs_triang _ _)).
  have-> : - y * (th - / y) ^ 2 = - ( y * (th - / y) ^ 2) by ring.
  rewrite Rabs_Ropp Rabs_pos_eq.
    apply:Rplus_le_compat_l.
    rewrite Rabs_mult Rabs_pos_eq; last lra.
    apply: Rmult_le_compat_l; first lra.
    apply:(Rle_trans _ _  _  (Rabs_triang _ _)); try lra.
    rewrite /eta.
    lra.
  apply: Rmult_le_pos; first lra.
  by apply: pow2_ge_0.

pose z := y^2 * (th - /y)^2.
have zE: z = y^2 * ((th -/yh) + (y -yh)/(y * yh))^2.
  rewrite /z; field; lra.

have h1 :  Rabs (th -/yh) <= u/2.
  have ->: (u/2) =  /2 * pow (-p) * pow 0.
    change ( pow (-p) * (pow (-1)) = pow (-1) * pow (-p) * 1).
    ring.
  apply: error_le_half_ulp'; first lia.
  change (  Rabs (/ yh) <=1); rewrite Rabs_pos_eq; lra.
have ymupos: u < y.
  rewrite /y.
  apply: (Rlt_le_trans _ (1 -u))=> //.
    suff: 2* u < 1 by lra.
    change (pow 1 * pow (-p) <  pow 0).
    rewrite -bpow_plus;  apply:bpow_lt; lia.
  by  move/Rabs_le_inv:   ylu; lra.
have h2: Rabs ((y -yh) / (y * yh)) <= u/(y * (y -u)).
  rewrite Rabs_mult; apply:Rmult_le_compat; try apply: Rabs_pos.
    have ->: (y - yh) = - (yh - y) by ring.
    rewrite Rabs_Ropp.
    rewrite yE /y.
    suff ->: u =  / 2 * (ulp two fexp (rnd_p (yh + yl))) by apply: error_le_half_ulp_round.
    rewrite -yE ulp_neq_0; try lra.
    rewrite /cexp /fexp (mag_unique_pos _ _ 1).
      change (pow (-p) = pow (-1) * pow (1 - p)).
      rewrite !bpow_plus -Rmult_assoc -bpow_plus.
       have -> : pow (-1 +1) = 1.
         have->: (-1 +1)%Z = 0%Z by ring.
         by [].
      ring.
    have->: (1 -1)%Z = 0%Z by ring.
    change (1 <= yh < 2); lra.
(* clear - ymupos upos  ult1   yb hiy2  hiy1 yE ZNE. *)

    rewrite Rabs_Rinv;  last by clear - ymupos upos  ult1   yb hiy2  hiy1 yE ZNE;   nra.
    
  rewrite Rabs_pos_eq; last by clear - ymupos upos  ult1   yb; nra.
  apply: Rinv_le; first by clear - ymupos upos  ult1   yb;nra.
  apply:Rmult_le_compat; try lra.
  suff: y - yh <= u by lra.
  suff: Rabs (y -yh) <= u by move/Rabs_le_inv; lra.
  have->: y - yh = - (yh -y) by ring.
  rewrite Rabs_Ropp yE /y.
  suff ->: u =  / 2 * (ulp two fexp (rnd_p (yh + yl))) by apply: error_le_half_ulp_round.
  rewrite -yE ulp_neq_0; try lra.
  rewrite /cexp /fexp (mag_unique_pos _ _ 1).
   change (pow (-p) = pow (-1) * pow (1 - p)).
  rewrite !bpow_plus -Rmult_assoc -bpow_plus.
    have -> : pow (-1 +1) = 1.
      have->: (-1 +1)%Z = 0%Z by ring.
      by [].
    ring.
  have->: (1 -1)%Z = 0%Z by ring.
  change (1 <= yh < 2); lra.
have h3: Rabs (th - / yh + (y - yh) / (y * yh)) <= u * ( /2 + /(y *(y -u))).
  apply:(Rle_trans _ _  _  (Rabs_triang _ _));  lra.
move/(pow_maj_Rabs _ _ 2):h3.
have->: (u * (/ 2 + / (y * (y - u)))) ^ 2 =
        u^2 * (/ 2 + / (y * (y - u))) ^ 2 by ring.
move=> h3.
have h63a: z <= y^2 * (u ^ 2 * (/ 2 + / (y * (y - u))) ^ 2).
  rewrite zE.
  apply:Rmult_le_compat_l=>//; try apply: pow2_ge_0.

  have haux1: 0 <= yl -> 1 <= y by rewrite /y; lra.
  have haux2: 1 < yh -> 1 <= y.
  move=> hyh1.
  have hyh: 1 + 2*u <= yh.
    have ->: 1 +2*u = succ two fexp 1.
    rewrite succ_eq_pos; last lra.
      apply: Rplus_eq_compat_l.
      rewrite /u u_ulp1; field.
    apply:succ_le_lt=>//.
    change (format (pow 0)); apply:generic_format_bpow; rewrite /fexp; lia.
   move/ Rabs_le_inv :   ylu; rewrite /y; lra.
   (* ici ou là *)
   
have F1: format 1 by change (format (pow 0));
     apply:generic_format_bpow; rewrite /fexp; lia.
case:(Req_dec (xh + xl) 0) => x0.
  rewrite /DWDivDW3.
  case H:  DWTimesDW12 => [zh zl].
    move:(H); rewrite / DWTimesDW12 TwoProdE.
    case:(DWx)=>[[Fxh Fxl] xE].
    have xh0: xh = 0 by rewrite xE x0 round_0.
    have xl0: xl = 0 by lra.
    rewrite /Fast2Mult xh0 xl0 !(Rmult_0_l, round_0, Rminus_0_r, Rplus_0_l, round_round) // Fast2Sum0f; 
      try apply:generic_format_round; try apply:generic_format_0.
    case => <- <-.
    rewrite  /Rdiv !(Rplus_0_r, Rmult_0_l,  Rminus_0_r) Rabs_R0.
      clear -upos; nra.
case:(Rle_lt_dec 1 y) => hy1; last first.
  have yl0 : yl  < 0 .
    case: (Rlt_le_dec yl 0 )=>//.
     move/haux1; lra.
  have yhE: yh = 1.
    by case: yb; case=>//; move/haux2; lra.
  rewrite /DWDivDW3; case H:  DWTimesDW12 => [zh zl].
  have  ryl1 :   rnd_p (- yl + 1) = 1.
    have : 1 <= -yl + 1  by lra.
    move/(round_le two fexp (Znearest choice)).
    have -> : rnd_p 1 = 1.
      by change (rnd_p (pow 0) = 1); rewrite round_generic //; apply: generic_format_bpow; rewrite /fexp; lia.
    have :  rnd_p (- yl + 1)<= 1.
      apply : round_N_le_midp=>//.
      have <-: 1 +2*u = succ two fexp 1.
        rewrite succ_eq_pos; last lra.
      apply: Rplus_eq_compat_l.
      rewrite /u u_ulp1; field.
      move: ylu; rewrite -Rabs_Ropp; move/ Rabs_le_inv.
      have->: (1 + (1 + 2 * u)) / 2 = 1 + u by field.
      case=>_; case; first lra.
      move=> ylE.
      move:yE ;  rewrite yhE.
      have->:  yl = -u  by lra.
      rewrite round_generic //; try lra.
      (* format (1 -u) *)
      have He: (1 -u ) =  F2R (Float two (2 ^ p  -1 )%Z (-p)).
        rewrite /F2R /= plus_IZR /u (IZR_Zpower two) /=; last lia.
        rewrite Rmult_plus_distr_r -bpow_plus.
        ring_simplify(p + -p)%Z; rewrite /=; ring.
      apply:(FLX_format_Rabs_Fnum p He).
      rewrite /= minus_IZR (IZR_Zpower two); last lia.
      rewrite Rabs_pos_eq;  try lra.
      suff: pow 0 <= pow p.
        rewrite /=; lra.
      apply: bpow_le; lia.
    lra.
  move:(H).
  have th1: th = 1.
    by rewrite yhE Rinv_1 round_generic.
  have rh0 : rh = 0 by rewrite th1 yhE  ; ring.
  have rlE: rl = -yl.
    by rewrite th1 Rmult_1_r round_generic.
  have eh0: eh = -yl.
    by rewrite rh0 Fast2Sum0f //; rewrite rlE; apply:generic_format_opp.
  have el0: el =  0.
    by rewrite rh0 Fast2Sum0f //; rewrite rlE; apply:generic_format_opp.
  have [dhE dlE]: dh = -yl /\ dl = 0.
    rewrite /DWTimesFP9 TwoProdE /FMA .
    rewrite el0 th1 /= !Rmult_1_r.
    have->: rnd_p yl  = yl by rewrite round_generic.
    have ->: (1 - yh + - yl) = -yl by rewrite yhE; ring.
    rewrite ZNE !round_NE_opp -ZNE round_round; last lia.
    have -> : rnd_p yl = yl by rewrite round_generic.  
    have haux: (- yl - - yl) = 0 by ring.
    by rewrite !(haux, Rplus_0_r, round_0)  ZNE round_NE_opp -ZNE
                 round_generic // haux !(round_0, Rminus_0_r).
  have [mhE mlE]: mh = 1 /\ ml = -yl.
    rewrite dhE dlE th1 /DWPlusFP Rplus_0_l.
    rewrite F2Sum_correct_abs //; try apply:generic_format_round.
      rewrite fstE TwoSum_correct //.
        rewrite TwoSum_sumE ryl1.
        have->:  (- yl + 1 - 1)= -yl by ring.
        have->: rnd_p (-yl) = -yl by rewrite round_generic //; apply:generic_format_opp.
        have-> : 1 + -yl = -yl + 1 by ring.
        rewrite ryl1; split; ring.
      by apply:generic_format_opp.
    rewrite TwoSum_correct //; first last.
      by apply:generic_format_opp.
    rewrite TwoSum_sumE ryl1.
    have->:  (- yl + 1 - 1)= -yl by ring.
    have->: rnd_p (-yl) = -yl by rewrite round_generic //; apply:generic_format_opp.
    rewrite Rabs_Ropp (Rabs_pos_eq 1);  lra.
  have Hp4: (4 <= p)%Z by lia.
  move:( DWTimesDW12_correct ZNE Hp4 TwoProdE DWx DWm).
  case HH: DWTimesDW12 => [zzh zzl].
  set m:= mh + ml.
  rewrite /=.
  move=> h h'.
  move: h; case: h'=> -> ->.
  have->: (zh + zl - (xh + xl) * m) / ((xh + xl) * m) = ((zh + zl)/(xh + xl)) * /m -1 .
    field.
    rewrite /m;split;   lra.
  have->: ((zh + zl - (xh + xl) / y) / ((xh + xl) / y)) = ((zh + zl)/(xh + xl)) *y - 1.
    field; split;  lra.
  set zz:= (zh + zl) / (xh + xl).
  rewrite -/u=>/Rabs_lt_inv hlu.
  apply: Rabs_le.
  rewrite Rmult_1_r.
  suff: 1 - 98/10 * u^2 <= zz*y <= 1 + 98/10 * u^2 by lra.
  have hh: 1 - 5*u^2 < zz* /m < 1 + 5*u^2 by lra.
  have:1 - 5*u^2 < zz * / m  < 1 + 5 * u ^ 2 by lra.
  have  m0: 0 < m.
    rewrite /m mhE mlE.
    move/Rabs_le_inv : ylu ; clear -upos  ult1 ; lra.
  case.
  move/(Rmult_lt_compat_r  m _ _  m0).
  rewrite Rmult_assoc Rinv_l ?Rmult_1_r; last lra.
  move/ (Rmult_lt_compat_r   y _ _ ypos)=> hlb.
  move/(Rmult_lt_compat_r  m _ _  m0).
  rewrite Rmult_assoc Rinv_l ?Rmult_1_r; last lra.
  move/ (Rmult_lt_compat_r   y _ _ ypos)=> hub.
  split; [apply:(Rle_trans _ ((1 - 5 * u ^ 2) * m * y))|
        apply:(Rle_trans _ ((1 + 5 * u ^ 2) * m * y))]; try lra.
    rewrite (Rmult_assoc _ m).
    have->: m*y= 1 - yl^2.
      rewrite /m /y mhE mlE yhE; ring.
    have->: (1 - 5 * u ^ 2) * (1 - yl ^ 2) = 1 - yl^2 - 5*u^2 + 5* u^2* yl^2 by ring.
    suff: 0 <=  98 / 10 * u ^ 2   - yl ^ 2 - 5 * u ^ 2 + 5 * u ^ 2 * yl ^ 2 by lra.
    suff: yl^2 <=  48 / 10 * u ^ 2 + 5 * u ^ 2 * yl ^ 2  by lra.
    have : 0 <= 5 * u ^ 2 * yl ^ 2.
      clear - upos; move:(pow2_ge_0 yl); apply: Rmult_le_pos;   nra.
    suff:  yl ^ 2 <= 48 / 10 * u ^ 2 by lra.
    apply:(Rle_trans _ (u^2)).
      by apply: pow_maj_Rabs.
    suff : 0 <= 38/10 * u^2 by lra.
    by clear -upos; nra.
  rewrite (Rmult_assoc _ m).
  have->: m*y= 1 - yl^2 by rewrite /m /y mhE mlE yhE; ring.
  have->:   (1 + 5 * u ^ 2) * (1 - yl ^ 2) = 1 -yl^2 +  5 * u ^ 2 -  5 * u ^ 2* yl^2 by ring.
  suff: 0<=  yl ^ 2 +  5 * u ^ 2 * yl ^ 2+  48 / 10 * u ^ 2 by lra.
  have : 0 <= 5 * u ^ 2 * yl ^ 2.
    clear - upos; move:(pow2_ge_0 yl); apply: Rmult_le_pos;   nra.
  move:(pow2_ge_0 yl); lra.
have:   y ^ 2 *  (/ 2 + / (y * (y - u))) ^ 2
        <= (/ 2 + / ((1 - u))) ^ 2.
  have ->:   y ^ 2 *  (/ 2 + / (y * (y - u))) ^ 2 = (y/2 + /(y-u))^2.
    field.
    lra.
suff h:  (y / 2 + / (y - u)) <= (/ 2 + / (1 - u)).
  apply: Rmult_le_compat; try lra.
      have->: 0 = 0 + 0 by ring.
      apply:Rplus_le_compat; try lra.
      apply/Rlt_le/Rinv_0_lt_compat;lra.
    rewrite  Rmult_1_r.
    have->: 0 = 0 + 0 by ring.
    apply:Rplus_le_compat; try lra.
    apply/Rlt_le/Rinv_0_lt_compat;lra.
  suff:   y  + 2/ (y - u) <= 1 + 2/ (1 - u)by lra.
  apply:(Rmult_le_reg_r ((y -u)*(1-u))).
    clear -ult1 ymupos; nra.
  rewrite 2!Rmult_plus_distr_r.
  have->:  2 / (y - u) * ((y - u) * (1 - u)) = 2 * (1 -u) by field; lra.
  have ->:  2 / (1 - u) * ((y - u) * (1 - u)) = 2* (y -u) by field; lra.
  rewrite Rmult_1_l.
  set ymu := y-u.
  set um1 := 1-u.
  suff : (y -1) *(ymu *um1) <= 2 * (ymu - um1).
    lra.
  have ->: (ymu - um1) = y -1 by rewrite /ymu /um1; ring.
  suff: 0<= (y -1) * (2 -  (ymu * um1)) by lra.
  have rpart: 0 <= (2 -  (ymu * um1)).
   rewrite /ymu /um1.
    have yub: y <= 2-u.
    rewrite /y ; move/Rabs_le_inv:   ylu; lra.
    have h0 : 1 -u <= y.
        rewrite /y ; move/Rabs_le_inv:   ylu; lra.
        have h4: 1-2*u <= y -u <= 2 -2*u by lra.
    have h5: -2 +2*u <= - (y -u) <= -1 + 2*u by lra.
    have h6: (-2 + 2*u) * (1 -u) <=   - (y - u) * (1 - u) <= (-1 + 2*u)* ( 1-u).
clear -h5 upos ult1 ; nra.
have: 2+  (-2 + 2 * u) * (1 - u) <= 2 - (y - u) * (1 - u) by lra.

suff:   0<= 2 + (-2 + 2 * u) * (1 - u)  by lra.
ring_simplify.
have->: -2 * u ^ 2 + 4 * u = (-2*u + 4) * u by ring.
apply: Rmult_le_pos;last lra.
suff : 2 * u <= 4 by lra.
suff:  u <= /16 by lra.
change (pow (-p) <= pow (-4)); apply:bpow_le; lia.
apply:Rmult_le_pos; lra.
move=> h63b.

have h63c: y^2*(th - /y)^2 <= 2298/1000 * u^2.
  apply:(Rle_trans _ (36481/15876* u^2)); last by lra.
  clear -upos u2pos ult1 hy1   hiy1   thb  hy1   h63b h63a  Hp14.
have hi1mu: 0 < /(1 -u) by apply: Rinv_0_lt_compat; lra.


  apply: (Rle_trans _ ((/2 + /(1 - u))^2*u^2)); rewrite -/z; first nra.
  apply:(Rle_trans _ ((/ 2 + / (1 - /64)) ^ 2 * u ^ 2)); last  lra.
  apply:Rmult_le_compat_r; try nra.
  apply: pow_incr; split; try  nra.
  apply:Rplus_le_compat_l.
  apply: Rinv_le; try lra.
  suff: u <= /64 by lra.
  change (pow (-p) <= pow (-6)); apply: bpow_le; lia.
have h63d: Rabs (mh + ml - /y) <= /y * 2298 / 1000 * u ^ 2 + th * (5 / 2 * u ^ 2 + 9 * u ^ 3).
  clear -upos u2pos ult1 hy1   hiy1   thb  hy1   h63b h63a  Hp14 h63c h63.
  apply:(Rle_trans _ (/y * (y^2 * (th - / y) ^ 2) + th * (5 / 2 * u ^ 2 + 9 * u ^ 3))).
    by have-> :  / y * (y ^ 2 * (th - / y) ^ 2) =     y * (th - / y) ^ 2 by field; lra.
apply: Rplus_le_compat_r.
 have : 0 < /y by apply: Rinv_0_lt_compat ; lra.
nra.
pose x := xh + xl.
clear haux1 haux2.
have h63e: Rabs (x * (mh + ml) - x/y) <= 
                (Rabs x) /y * 2298 / 1000 * u ^ 2 + (Rabs x) * th * (5 / 2 * u ^ 2 + 9 * u ^ 3).
have ->: x * (mh + ml) - x / y = x * ((mh + ml) -/y) by field; lra.
rewrite Rabs_mult.
have->:   Rabs x / y * 2298 / 1000 * u ^ 2 + Rabs x * th * (5 / 2 * u ^ 2 + 9 * u ^ 3) =
           Rabs x *( / y * 2298 / 1000 * u ^ 2 +  th * (5 / 2 * u ^ 2 + 9 * u ^ 3)) by field; lra.
 by apply:Rmult_le_compat_l; first by apply:Rabs_pos.
have h63f: Rabs th <= (1 + u)^2/y.
  case: (rnd_epsl Hp1 choice (/yh)); rewrite -/u => e1 [ /Rabs_le_inv e1ub thE]. 
  case: (rnd_epsr Hp1 choice y ); rewrite -/u=> e2 [/Rabs_le_inv e2ub yE2].
  rewrite thE Rabs_mult !Rabs_pos_eq; try  lra.
  rewrite /Rdiv;  have ->: /y = /(1 + e2)* /yh.
    rewrite yE -/y yE2; field; split; lra.
  have ->: (1 + u) ^ 2 * (/ (1 + e2) * / yh) = /yh * ( (1 + u) ^ 2 * (/ (1 + e2))) by ring.
  apply:Rmult_le_compat_l; first lra.
  apply:(Rmult_le_reg_r (1 + e2)); first lra.
  rewrite Rmult_assoc Rinv_l ?Rmult_1_r; clear  - e1ub    e2ub upos ult1; nra.
pose phi_u := 2298 / 1000 * u ^ 2 + (1 + u)^2 * (5 / 2 * u ^ 2 + 9 * u ^ 3).
have h64: Rabs (x * (mh + ml) - x / y) <=  Rabs x / y * phi_u.
  rewrite Rabs_pos_eq in h63f; last lra.
  rewrite /phi_u; apply:(Rle_trans _ _ _  h63e).
  rewrite (Rmult_plus_distr_l ( Rabs x / y)).
  apply: Rplus_le_compat ; try lra.
  rewrite -Rmult_assoc; apply: Rmult_le_compat_r.
    clear -upos u2pos ; nra.
  rewrite /Rdiv Rmult_assoc; apply:Rmult_le_compat_l; first by apply:Rabs_pos.
  rewrite /Rdiv Rmult_comm in  h63f.
  clear -upos u2pos h63f ; nra.
  rewrite / DWDivDW3; 
  case H: DWTimesDW12 => [zh zl].

  have Hp4: (4 <= p)%Z by lia.
  move:( DWTimesDW12_correct ZNE Hp4 TwoProdE DWx DWm).
move: (H).
  case HH: DWTimesDW12 => [zzh zzl].
  set m:= mh + ml.
  rewrite /=.
case => -> ->.
move=>h64a.
have m0: 0 < m.
rewrite /m h61.
have->:   (th + e * th + alpha * th) = th* (1 + e + alpha) by ring.
apply: Rmult_lt_0_compat; first lra.
move/Rabs_le_inv :   eu.
move/Rabs_le_inv :  h62 .
move => haux1 haux2; 
apply: (Rlt_le_trans _ (1 -2*u - (2 * u ^ 2 + 9 * u ^ 3)) ); last lra.
clear - upos u2pos Hp14.
suff : u <= /4 by nra.
change (pow (-p) <= pow (-2)); apply: bpow_le; lia.
have haux1: 0 < Rabs (xh + xl) * m .
apply: Rmult_lt_0_compat; last lra.
by apply: Rabs_pos_lt.
 
have: Rabs  (zh + zl - (xh + xl) * m)< 5* u^2 * ((Rabs x) * m).
apply:( Rmult_lt_reg_r  (/ (Rabs (xh + xl) * m))).
  by apply: Rinv_0_lt_compat.
rewrite /x Rmult_assoc Rinv_r ?Rmult_1_r; last lra.
move:h64a; rewrite -/u.
rewrite Rabs_mult Rabs_Rinv.
have->: Rabs ((xh + xl) * m) = (Rabs (xh + xl) * m).
rewrite Rabs_mult (Rabs_pos_eq m)//; lra.
lra.
clear -   x0   m0 ; nra.
move=> h64b.

have h65:  Rabs (zh + zl - (xh + xl) * m) < (Rabs x)/y * ( 5 * u ^ 2 + 5*u^2* phi_u).
  apply:(Rlt_le_trans _ (5 * u ^ 2 * (Rabs (x * m)))).
  rewrite Rabs_mult (Rabs_pos_eq m); lra.

  have->:  (x * m) = (x/y + (x*m -  x/y)) by ring.
  apply:(Rle_trans _  (  5 * u ^ 2 * Rabs (x / y) + 5 * u ^ 2 * (Rabs (x * m -x/y)))).
    rewrite -Rmult_plus_distr_l.
    apply:(Rmult_le_compat_l);  first by clear -upos ; nra.
    by apply: (Rabs_triang _ _).
  rewrite Rmult_plus_distr_l.
  apply:Rplus_le_compat; first rewrite Rmult_comm Rabs_mult (Rabs_pos_eq (/y)) /Rdiv.
      lra.
    apply/Rlt_le/Rinv_0_lt_compat ; lra.
  have ->: Rabs x / y * (5 * u ^ 2 * phi_u) = 5 * u ^ 2 *(Rabs x / y * phi_u) by ring.
  apply: Rmult_le_compat_l =>//;  by clear -upos; nra.

have hiy: 0 </y by apply: Rinv_0_lt_compat;  lra.

rewrite -/x Rabs_mult.
apply: (Rmult_le_reg_r  (Rabs x /y)).
  apply: Rmult_lt_0_compat=>//.
  by apply: Rabs_pos_lt.
rewrite Rmult_assoc.
have ->: (Rabs (/ (x / y)) * (Rabs x / y)) = 1.
  rewrite Rabs_Rinv.
    rewrite Rabs_mult (Rabs_pos_eq (/y)); last lra.
    rewrite /Rdiv Rinv_l //.
    apply: Rmult_integral_contrapositive_currified =>//.
      by apply: Rabs_no_R0.
    by lra.
  apply: Rmult_integral_contrapositive_currified; try lra.
  rewrite /x; lra.

rewrite !Rmult_1_r.
have ->: zh + zl - x / y = (zh + zl - (xh + xl) * m) + (  (xh + xl) * m - x/y).
  by ring.
apply:(Rle_trans _ _  _  (Rabs_triang _ _))=>//.
apply:(Rle_trans _  (Rabs x / y * (5 * u ^ 2 + 5 * u ^ 2 * phi_u)  +
                     Rabs x / y * phi_u )).
  apply:Rplus_le_compat; first lra.
  rewrite -/x /m; lra.
rewrite - Rmult_plus_distr_l.
rewrite Rmult_comm.
apply:Rmult_le_compat_r.
  by apply: Rmult_le_pos; try lra; apply:Rabs_pos.
have->: (u * u) = u^2 by ring.
have phi_uE : phi_u = u^2 * ( 2298 / 1000 + (1 + u) ^ 2 *( 5 / 2 + 9 * u)) by rewrite /phi_u; ring.
rewrite {2}phi_uE.
have ->:   5 * u ^ 2 + 5 * u ^ 2 * phi_u +
  u ^ 2 * (2298 / 1000 + (1 + u) ^ 2 * (5 / 2 + 9 * u)) =
   (5 + 5* phi_u +  (2298 / 1000 + (1 + u) ^ 2 * (5 / 2 + 9 * u)))* u^2 by ring.
apply:Rmult_le_compat_r; first lra.
rewrite  phi_uE.
field_simplify.


have u14: u<= /16384 .
change (pow (-p) <= pow (-14)).
  by apply: bpow_le; lia.
have->:   (90000 * u ^ 5 + 205000 * u ^ 4 + 158000 * u ^ 3 + 88980 * u ^ 2 + 
           28000 * u + 19596) / 2000 =
            45 * u ^ 5 + 1025/10 * u ^ 4 + 79 * u ^ 3 +4449/ 100* u ^ 2 +
              14 * u + 9798 / 1000.
  by field.
 suff :  45 * u ^ 5 + 1025 / 10 * u ^ 4 + 79 * u ^ 3 + 4449 / 100 * u ^ 2 +
       19 * u <=1/500 by lra.
apply: (Rle_trans _ (20*u) ) ; try lra.
clear -upos u2pos u14.
suff : (  45 * u ^ 4 + 1025 / 10 * u ^ 3 + 79 * u ^ 2 + 4449 / 100 * u ) <= 1 by nra.
suff:  4500 * u ^ 4 + 10250  * u ^ 3 + 7900 * u ^ 2 + 4449 * u <= 100 by nra.
apply:(Rle_trans _ (6400 * u)); last lra.
suff:   4500 * u ^ 3 + 10250 * u ^ 2 + 7900 * u  <=
          951  by nra.
nra.
Qed.

End  Algo17_pre.


 (* chnage name DWTimesFP 3-> 9 *)
Notation th yh := (rnd_p (/yh)).
Notation rh yh := (1 -yh*(th yh)).
Notation rl yh yl:= (- (rnd_p (yl*(th yh)))).
Notation eh yh yl := (rnd_p ((rh yh) +(rl yh yl))).
Notation el yh yl := (snd (Fast2Sum (rh yh) (rl yh yl))).


Notation dh yh yl := (fst (DWTimesFP9 p choice (eh yh yl) (el yh yl) (th yh))).
Notation dl yh yl :=  (snd (DWTimesFP9 p choice (eh yh yl) (el yh yl) (th yh))).
Notation mh yh yl := (fst (DWPlusFP p choice  (dh yh yl) (dl yh yl) (th yh))).
Notation ml yh yl := (snd (DWPlusFP p choice  (dh yh yl) (dl yh yl) (th yh))).

Let  DWDivDW3 xh xl yh yl := (DWTimesDW12 p choice  xh xl (mh yh yl)  (ml yh yl)).

Fact  DWDivDW3_Asym_l (xh xl yh yl :R):  
  (DWDivDW3  (-xh) (-xl)  yh yl) =  pair_opp (DWDivDW3  xh xl    yh yl).
Proof. by rewrite /DWDivDW3 DWTimesDW12_Asym_l. 
Qed.

Fact mh_Asym yh yl (yhn0: yh <> 0): mh (-yh) (-yl) = -(mh yh yl).
Proof.
  have thE: th(-yh) = - th (yh).
   have->: /(- yh) = - /yh by field.

  
  
  by rewrite ZNE round_NE_opp -ZNE.
  have rhE: rh (-yh) = rh yh by rewrite thE; ring.
  have rlE: rl (-yh) (-yl) = rl yh yl.
  by rewrite thE Rmult_opp_opp.
  have ehE : eh (-yh) (-yl) = eh (yh) yl by rewrite rhE rlE.
  have elE : el (-yh) (-yl) = el (yh) yl by rewrite rhE rlE.
  have dhE : dh (-yh) (-yl) = -dh (yh) yl.
  rewrite ehE elE thE.

  set dl := DWTimesFP9 _ _ _ _ _.
  
   case H: DWTimesFP9 => [zh zl].
      by rewrite /dl (@DWTimesFP9_Asym_r _ _  ZNE TwoProdE  (eh (yh) yl) (el yh yl) ( (th yh))) H.
   
    have dlE : dl (-yh) (-yl) = -dl (yh) yl.
  rewrite ehE elE thE.
     
  set dl := DWTimesFP9 _ _ _ _ _.
  
   case H: DWTimesFP9 => [zh zl].
     by rewrite /dl (@DWTimesFP9_Asym_r _ _  ZNE TwoProdE  (eh (yh) yl) (el yh yl) ( (th yh)) ) H.
   rewrite dhE dlE thE.
   
  
   set ml := DWPlusFP _ _ _ _ _.
by rewrite /ml DWPlusFP_Asym.
Qed.

Fact mhlS yh yl e (yhn0: yh <> 0) (Hp3: (3 <= p)%Z):
  mh (yh * pow e ) (yl * pow  e) = (mh yh yl)* pow (-e) /\
   ml (yh * pow e ) (yl * pow  e) = (ml yh yl)* pow (-e).
Proof.
  have thE: th(yh* pow e) =  (th (yh))* pow (-e).
  have->: /(yh * (pow e)) =  /yh  * pow (-e).
  have powegt0:= (bpow_gt_0 two e).
  apply:(Rmult_eq_reg_r (pow e)); last lra.
  rewrite Rmult_assoc -bpow_plus; ring_simplify (-e + e)%Z => /=.
  field; split; lra.
    by rewrite round_bpow.

    have rhE: rh (yh* pow e) = rh yh.
    rewrite thE.
    have->:  yh * pow e * (th yh * pow (- e)) = yh * (th yh) *(pow e * pow (-e)) by ring.
    by rewrite -bpow_plus Z.add_opp_diag_r /= Rmult_1_r //.
    have rlE: rl (yh* pow e) (yl* pow e) = rl yh yl.
        rewrite thE.
        have->:  yl * pow e * (th yh * pow (- e)) = yl * (th yh) *(pow e * pow (-e))by ring.
          by rewrite -bpow_plus Z.add_opp_diag_r /= Rmult_1_r //.
  have ehE : eh (yh* pow e) (yl*pow e) = eh yh yl by rewrite rhE rlE.
  have elE : el (yh*pow e) (yl* pow e) = el yh yl by rewrite rhE rlE.
  
    
  have dhE : dh (yh*pow e) (yl*pow e) = (dh (yh) yl)* pow (-e).
                                         
  rewrite ehE elE thE.
  set f:= fst _.
  case h: DWTimesFP9 => [zh zl].
  rewrite /f.
   by rewrite DWTimesFP9Sy ?h.      
   have dlE: dl (yh*pow e) (yl*pow e) = (dl (yh) yl)* pow (-e).
                                         
  rewrite ehE elE thE.
  set f:= snd _.
  case h: DWTimesFP9 => [zh zl].
  rewrite /f.
    by rewrite DWTimesFP9Sy  ?h.  
    rewrite dhE dlE thE.
    set f := fst _; case H: DWPlusFP => [zh zl].
    rewrite /f.  
rewrite DWPlusFPS // ?fstE 2?sndE; 
  try (rewrite /DWTimesFP9 TwoProdE; apply:generic_format_round);
  last apply: generic_format_round.
by move:H; rewrite /DWPlusFP; case => <- <-.
Qed.

Fact ml_Asym yh yl (yhn0: yh <> 0): ml (-yh) (-yl) = -(ml yh yl).
Proof.
  have thE: th(-yh) = - th (yh).
   have->: /(- yh) = - /yh by field.

  
  
  by rewrite ZNE round_NE_opp -ZNE.
  have rhE: rh (-yh) = rh yh by rewrite thE; ring.
  have rlE: rl (-yh) (-yl) = rl yh yl.
  by rewrite thE Rmult_opp_opp.
  have ehE : eh (-yh) (-yl) = eh (yh) yl by rewrite rhE rlE.
  have elE : el (-yh) (-yl) = el (yh) yl by rewrite rhE rlE.
  have dhE : dh (-yh) (-yl) = -dh (yh) yl.
  rewrite ehE elE thE.

  set dl := DWTimesFP9 _ _ _ _ _.
  
   case H: DWTimesFP9 => [zh zl].
      by rewrite /dl DWTimesFP9_Asym_r ?H.
    have dlE : dl (-yh) (-yl) = -dl (yh) yl.
  rewrite ehE elE thE.
     
  set dl := DWTimesFP9 _ _ _ _ _.
  
   case H: DWTimesFP9 => [zh zl].
     by rewrite /dl DWTimesFP9_Asym_r ?H.
   rewrite dhE dlE thE.
   
  
  by rewrite DWPlusFP_Asym.
Qed.

Fact  DWDivDW3_Asym_r (xh xl yh yl :R)  (yhn0: yh <> 0):
  (DWDivDW3  xh xl (-yh)  (-yl)) = pair_opp (DWDivDW3  xh xl yh yl).
Proof.
  (* case H: (DWDivDW3  xh )=> [zh zl]. *)
  rewrite /DWDivDW3  ml_Asym // mh_Asym //.
  by apply:DWTimesDW12_Asym_r.
Qed.

Fact DWDivDW3Sy (xh xl yh yl :R) e (yhn0: yh <> 0) (Hp4 : (4 <= p)%Z):
  (DWDivDW3  xh xl (yh * pow e)  (yl * pow e)) =  map_pair (fun x => x * pow (-e))
      (DWDivDW3   xh xl  yh yl).
Proof.
  (* case H:  (DWDivDW3  xh )=> [zh zl]. *)
  rewrite /DWDivDW3.  (* mhlS.  DWTimesDW12Sy. *)


  case:(@mhlS  yh yl e)=>//; try lia; move => -> ->.
  by rewrite  DWTimesDW12Sy.
Qed.


  

(* Theorem 7.3 *)
Lemma DWDDW3_correct xh xl yh yl  (DWx: double_word xh xl) (DWy: double_word yh yl)
                                 (Hp14: (14 <= p)%Z)(yhn0 : yh <> 0):
  let (zh, zl) := DWDivDW3 xh xl yh yl  in
  let xy := ((xh + xl) / (yh + yl))%R in
  Rabs ((zh + zl - xy) / xy) <= 98/10*u^2.
Proof.
have := (upos p); rewrite -/u  => upos.
have u2pos: 0 < u*u by nra.
have ult1: u < 1 by change (pow (-p) < pow 0); apply:bpow_lt; lia.
case:(DWx)=>[[Fxh Fxl] xE].
case:(Req_dec xh 0)=> [xh0 |xhn0].
  have xl0: xl = 0.
    by move:xE; rewrite  xh0 Rplus_0_l round_generic.
  suff ->:  DWDivDW3 xh xl yh yl = (0 ,0).
    rewrite /= xl0 xh0 /Rdiv !(Rplus_0_r, Rmult_0_l, Rminus_0_r)  Rabs_R0.
    nra.
  rewrite /DWDivDW3   /DWTimesDW12 /= TwoProdE /= xh0 xl0
             !(Rmult_0_l , round_0, Rplus_0_l, Rminus_0_r)Fast2Sumf0 //; apply: generic_format_0.
have xn0 := (dw_n0 DWx xhn0).
wlog ypos : yh  yl DWy yhn0 / 0 < yh.
  move=> Hwlog.
  case:(Rlt_le_dec 0 yh); first by apply:Hwlog.
  case=>// yneg.

  move:(DWDivDW3_Asym_r xh  xl yl yhn0).
  case H:  (DWDivDW3 xh xl yh yl) => [zh zl] H'.
  rewrite /=.
   have->: ((zh + zl - (xh + xl) / (yh + yl)) / ((xh + xl) / (yh + yl))) =
       ((-zh + -zl -  (xh + xl) / (-yh + -yl)) / ((xh + xl) /( -yh + -yl))).
   field.
   have yn0 := (dw_n0 DWy yhn0).
   split;[|split]; lra.
 by move:(Hwlog (-yh) (-yl) (DW_opp DWy)) =>/=; rewrite H' /=; apply; lra.
clear yhn0.
wlog hy: yh yl  DWy ypos / 1 <= yh <= 2-2*u.
  move=> hwlog.
  case:(DWy)=>[[Fyh Fyl] yE].
  case: (scale_generic_12 Fyh ypos)=> eyh Hyhs.
  rewrite -/u in Hyhs.
  have yhS_pos : 0 < yh * pow eyh by move:(bpow_gt_0 two eyh); nra.
  move:(hwlog (yh * pow eyh) (yl * pow eyh) (dw_S eyh DWy) yhS_pos Hyhs ).
  clear yhS_pos.
  rewrite /=.
  case H:(DWDivDW3 xh xl yh yl) =>[zh zl].
    have yhn0 : yh <> 0 by lra.
  have Hp4: (4 <= p)%Z by lia.
  move:(@DWDivDW3Sy xh xl yh yl eyh yhn0 Hp4).

  
  case H':DWDivDW3 =>[zzh zzl]. 
  rewrite H; case=> -> ->.
  set r1 := Rabs _.
  set r2 := Rabs _.
  suff-> : r1 = r2 by [].
  rewrite /r1 /r2.
  congr Rabs.
  suff ->: pow (- eyh) = / (pow eyh).
  field.
  repeat split; try lra.
  apply: dw_n0=>//;lra.
  rewrite -Rmult_plus_distr_r.
  apply:Rmult_integral_contrapositive; split.
   apply: dw_n0=>//;lra.
   move:(bpow_gt_0 two eyh); lra.
   move:(bpow_gt_0 two eyh); lra.
     by rewrite bpow_opp.
rewrite/=.
by apply: DWDDW3_correct_aux.
Qed.


End  Algo17.


End Div.

