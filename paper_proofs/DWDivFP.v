(* Copyright (c)  Inria. All rights reserved. *)

Require Import Psatz ZArith Reals.

From Flocq Require Import Core Relative Sterbenz Operations Plus_error Mult_error.

From Flocq Require Import Div_sqrt_error.

Require Import mathcomp.ssreflect.ssreflect.
Require Import Bayleyaux.
Require Import DWPlus.
Require Import DWTimesFP.
Require Import F2Sum.


Set Implicit Arguments.
Require Import ZArith Znumtheory.
Section MoreZarith.



Lemma rel_prime_2_odd a : rel_prime 2 (2 * a + 1).
Proof.
apply: bezout_rel_prime; apply: (Bezout_intro _ _ _ (-a) 1); ring.
Qed.

Lemma rel_prime_pow2_odd p a : 0 < p -> rel_prime (2 ^ p) (2 * a + 1).
Proof.
move=> p0.
rewrite -(Z.abs_eq p); last first.
  by apply: Z.lt_le_incl.
rewrite -Nat2Z.inj_abs_nat.
rewrite -Zpower_nat_Z; elim: (Z.abs_nat p) => [ | n IHn].
  by rewrite Zpower_nat_0_r; apply rel_prime_1.
rewrite Zpower_nat_succ_r.
apply/rel_prime_sym/rel_prime_mult.
  by apply/rel_prime_sym/rel_prime_2_odd.
by apply:rel_prime_sym.
Qed.

Lemma gcd_pow2_odd p a : 0 < p -> Z.gcd (2 ^ p) (2 * a + 1) = 1.
Proof.
by rewrite Zgcd_1_rel_prime; apply: rel_prime_pow2_odd.
Qed.

End  MoreZarith.

Local Open Scope Z_scope.
Local Open Scope R_scope.

Local Notation two := radix2 (only parsing).
Local Notation pow e := (bpow two e).



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

Section Algo14.

Definition TwoSum x y := (rnd_p (x + y), TwoSum_err p choice  x y).
(* Notation F2S_err a b := (F2Sum_err p choice a b). *)
Notation Fast2Sum := (Fast2Sum   p choice).
Notation Fast2Mult := (Fast2Mult p choice).
Notation F2P_prod a b  :=  (fst (Fast2Mult a b)).
Notation F2P_error a b  :=  (snd (Fast2Mult a b)).


Hypothesis Fast2Mult_correct: 
  forall a b, a * b =  F2P_prod a b +  F2P_error a b.

Notation F2P_errorE := (F2P_errorE Fast2Mult_correct).


Hypothesis TwoProdE : TwoProd = Fast2Mult. (* or Dekker's algorithm *)



Definition DWDivFP1 (xh xl y :R) :=
let th := rnd_p (xh/y) in
let (pih, pil ) := (TwoProd th y) in
let (dh, d') := (TwoSum xh (-pih)) in
let d'' := rnd_p (xl -pil) in 
let dl := rnd_p (d' + d'') in
let d := rnd_p (dh + dl) in
let tl := rnd_p (d/y) in (Fast2Sum th tl).

Definition DWDivFP2 (xh xl y :R) :=
let th := rnd_p (xh/y) in
let (pih, pil ) := (TwoProd th y) in
let dh  := xh -pih  in
let dl := rnd_p (xl - pil) in 
let d := rnd_p (dh + dl) in
let tl := rnd_p (d/y) in (Fast2Sum th tl).



Fact xhmpih_exact (xh y :R) (Fxh: format xh)( y0: y <> 0): 
                  rnd_p (xh  - rnd_p (rnd_p (xh / y) * y)) = xh -rnd_p (rnd_p (xh / y) * y).
Proof.
rewrite round_generic //.
  wlog xhpos :  xh Fxh/ 0 <= xh.
    move=> Hwlog.
    case:(Rle_lt_dec 0 xh) => xhle0; first by apply:Hwlog. 
    have->: (xh / y) = - ((-xh)/y) by field.
    rewrite ZNE round_NE_opp -ZNE.
    have ->: - rnd_p (- xh / y) * y = -( rnd_p (- xh / y) * y) by ring.
    rewrite ZNE round_NE_opp -ZNE.
    have ->:(xh  - - rnd_p (rnd_p (- xh / y) * y)) = - (-xh + -rnd_p  (rnd_p (- xh / y) * y)) by ring.    apply/generic_format_opp/Hwlog; try lra.
    by apply/generic_format_opp.
  set th := rnd_p (xh / y).
  set pih := rnd_p (th * y).
  set pil := rnd_p (th * y - pih).
  apply:sterbenz'=>//.
    by rewrite /pih; apply:generic_format_round.
  case:(rnd_epsl Hp1 choice (xh/y))=> e0 [re0 the].
  case:(rnd_epsr Hp1 choice (th*y))=> e1 [re1 pihe].
  rewrite -/pih in pihe.
  rewrite pihe /th the.
  have ult1 : (pow (-p)) < 1 by  apply:bpow_lt_1; lia.
  have upos:= (upos p).
  have ul : pow (-p) <= /4.
    have ->: /4 = pow (-2) by [].
    apply:bpow_le; lia.
  have : Rabs e1 <= /4 by lra.
  move/Rabs_le_inv=> [re1l re1u].
  have : Rabs e0 <= /4 by lra.
  move/Rabs_le_inv => [re0l re0u].
  have ->:  xh / y * (1 + e0) * y / (1 + e1)= xh * (1 + e0) / (1 + e1).
    field; split;lra.
  rewrite /Rdiv Rmult_assoc (Rmult_comm 2); split; apply:Rmult_le_compat_l=>//.
    apply:(Rmult_le_reg_l 2); try lra.
    rewrite Rinv_r; try lra; 
      apply:(Rmult_le_reg_r (1 + e1)); try lra.
    rewrite Rmult_1_l !Rmult_assoc Rinv_l; lra.
  apply:(Rmult_le_reg_r (1 + e1)); try lra.
  rewrite !Rmult_assoc  Rinv_l; lra.
Qed.


Lemma DWDivFP1_2 (xh xl y :R) (Fxh: format xh)( y0: y <> 0) : (DWDivFP1  xh xl y) = (DWDivFP2 xh xl y).
Proof.
rewrite /DWDivFP1 /DWDivFP2.
rewrite TwoProdE /=.
have valid_exp: Valid_exp fexp by apply: (FLX_exp_valid p).
set th := rnd_p (xh / y).
set pih := rnd_p (th * y).
set pil := rnd_p (th * y - pih).
have  xhmpih_exact := (xhmpih_exact Fxh y0).
rewrite /pih /th.
set err:=   TwoSum_err _ _ _ _ .
have ->: err = 0.
  rewrite /err TwoSum_correct ?TwoSum_sumE=>//=.
    rewrite   xhmpih_exact; ring.
  apply:generic_format_opp; rewrite /pih.
  by apply:generic_format_round.
rewrite Rplus_0_l // xhmpih_exact round_round //;lia.
Qed.

Fact  DWDivFP_Asym_r xh xl y (yn0: y <> 0):  
  (DWDivFP2 xh xl (-y)) = pair_opp   (DWDivFP2 xh xl y).
Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
 rewrite /DWDivFP2 TwoProdE /=.
set th := rnd_p (xh/y).
have ->: rnd_p (xh / - y)  = - th.
  have ->: xh / - y = - (xh /y) by field.
  by rewrite ZNE round_NE_opp -ZNE /th.
have ->: - th * - y = th * y by ring.
set pih := rnd_p (th * y); set pil := rnd_p (th * y - pih); set dh := xh -pih.
set dl :=  rnd_p (xl - pil); set d := rnd_p (dh + dl).
have ->: d / - y = - (d/y) by field.
by rewrite ZNE round_NE_opp -ZNE Fast2Sum_asym.
Qed.

Fact  DWDivFP_Asym_l xh xl y  (yn0: y <> 0): 
  (DWDivFP2 (-xh) (-xl)  y) = pair_opp (DWDivFP2 xh xl y).
Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
rewrite /DWDivFP2 TwoProdE /=.
set th := rnd_p (xh/y).
have ->: rnd_p ((-xh) /  y)  = - th.
  have ->: -xh / y = - (xh /y) by field.
  by rewrite ZNE round_NE_opp -ZNE /th.
have ->: - th * y = -(th * y) by ring.
rewrite ZNE round_NE_opp -ZNE.
set pih := rnd_p (th * y).
have->: (- (th * y) - - pih) = - ((th * y) - pih) by ring.
rewrite ZNE round_NE_opp -ZNE.
set pil := rnd_p (th * y - pih).
have->: (- xl - - pil) = - (xl - pil) by ring.
rewrite ZNE round_NE_opp -ZNE.
have->: (- xh - - pih + - rnd_p (xl - pil))= -(xh -pih + rnd_p (xl - pil)) by ring.
set dh := xh -pih; set dl :=  rnd_p (xl - pil).
rewrite ZNE round_NE_opp -ZNE.
set d := rnd_p (dh + dl).
have ->: -d / y = - (d/y) by field.
by rewrite ZNE round_NE_opp -ZNE Fast2Sum_asym.
Qed.

Fact  DWDivFPSy xh xl y e (yn0: y <> 0):
  (DWDivFP2 xh xl   (y* pow e)) =  
     map_pair (fun x =>  x/ (pow e))  (DWDivFP2 xh xl y).
Proof.
rewrite /DWDivFP2 TwoProdE /=.
set th := rnd_p (xh/y).
have ->: rnd_p ((xh) /  ( y * pow e))  = th/ (pow e).
  have ->: xh / (y* pow e) = (xh /y) / (pow e).
    field; split=>//; move:(bpow_gt_0 two e); lra.
  have-> : xh / y / pow e = (xh/y) * (pow (-e)).
    apply: (Rmult_eq_reg_r (pow e)); last by move:(bpow_gt_0 two e); lra.
    rewrite Rmult_assoc -bpow_plus; ring_simplify (-e + e)%Z; rewrite /= Rmult_1_r; field; split=>//.
    by move:(bpow_gt_0 two e); lra.
  by rewrite round_bpow /th bpow_opp.
have->: (th / pow e * (y * pow e)) = th * y.
  field; move:(bpow_gt_0 two e); lra.
set pih := rnd_p (th * y).
set pil := rnd_p (th * y - pih).
set dh := xh -pih; set dl :=  rnd_p (xl - pil).
set d := rnd_p (dh + dl).
have->: d / (y * pow e) = (d/y) * (pow (-e)).
  rewrite bpow_opp; field; split =>//; move:(bpow_gt_0 two e); lra.
rewrite round_bpow.
rewrite /Rdiv -bpow_opp Fast2SumS //; apply:generic_format_round.
Qed.

Fact  DWDivFPSx xh xl y  e (yn0: y <> 0):
  (DWDivFP2 (xh* pow e) (xl* pow e) y) =
     map_pair (fun x =>  x* (pow e))  (DWDivFP2 xh xl y).
Proof.
rewrite /DWDivFP2 TwoProdE /=.
set th := rnd_p (xh/y).
have ->: rnd_p ((xh * pow e) / y )  = th* (pow e).
  have ->: xh * pow e / y  = (xh /y) *(pow e).
    by field.
  by rewrite /th round_bpow.
have->: (th  * pow e * y ) = th * y * pow e by ring.
rewrite round_bpow.
set pih := rnd_p (th * y).
have->: th * y * pow e - pih * pow e = (th * y - pih)* pow e by ring.
rewrite round_bpow.
set pil := rnd_p (th * y - pih).
have->: (xl * pow e - pil * pow e)= (xl - pil) * pow e by ring.
rewrite round_bpow.
have->: xh * pow e - pih * pow e = (xh - pih) * pow e by ring.
set dh := xh -pih; set dl :=  rnd_p (xl - pil).
rewrite -Rmult_plus_distr_r round_bpow.
set d := rnd_p (dh + dl).
have->: d * (pow e) / y = (d/y) * (pow (e)) by field.
 by rewrite round_bpow Fast2SumS //= ; apply:generic_format_round.
Qed.


Definition relative_errorDWDFP xh xl y := let (zh, zl) := DWDivFP2  xh xl y in
  let xy := ((xh + xl) / y)%R in (Rabs (((zh + zl) - xy)/ xy)).

Definition errorDWDFP xh xl y := let (zh, zl) := DWDivFP2  xh xl y in
  let xy := ((xh + xl) / y)%R in (Rabs (((zh + zl) - xy))).

Notation double_word xh xl := (double_word  p choice xh xl).


Lemma l6_1_pre0  a v vm x m:
  a <= x <= a + v ->
  m = a + v/2 ->  vm <= Rabs (x - m) ->
  Rabs (a - x) <=  v / 2 - vm \/
  Rabs (a + v - x) <=  v/ 2 - vm.
Proof.
intros; split_Rabs; lra.
Qed.

Lemma l6_1_pre1  a v vm x m:
  a <= x <= a + v ->
  m = a + v/2 ->  0 < vm <= Rabs (x - m) ->
  Rabs (a - x) <=  v / 2 - vm < Rabs (a + v - x) \/
  Rabs (a + v - x) <=  v/ 2 - vm < Rabs (a - x) .
intros;split_Rabs;lra.
Qed.

Lemma l6_1_pre a m v vm x r:
  a <= x <= a + v ->
  Rabs(r - x) <= Rabs(a - x) ->
  Rabs(r - x) <= Rabs(a + v - x) ->
  m = a + v/2 ->  vm <= Rabs (x - m) ->
  Rabs (r - x) <=  v / 2 - vm.
Proof. intros;split_Rabs;lra. Qed.


Lemma l6_1_1 a b (Fa : format a) (Fb : format b): 1 <= a < 2 -> 1 <= b < 2 ->
   1 <= a/b -> Rabs (rnd_p (a/b) - a/b) <= u - (2 /b) *(u * u).
Proof.
move => ha hb hab .
case:(Req_dec (rnd_p (a/b) - a/b) 0)=> Hab.
  rewrite Hab Rabs_R0.
  have upos := (upos p).
  have : 0 < u < /2 .
    have->: /2 = pow (-1) by [].
    rewrite /u; split; try lra; apply:bpow_lt; lia.
  move =>[ u0 u2].
  (* suff: u <= 1 - 2/b * u by nra. *)
  suff: (2 * u)/ b <= 1 by nra.
  apply:(Rmult_le_reg_r b); try nra.
  rewrite Rmult_assoc Rinv_l ?Rmult_1_l ?Rmult_1_r; lra.
have Fnab: ~(format (a/b)).
  move=> Fab; apply Hab.
  rewrite round_generic //; ring.
move: (Fa) (Fb); rewrite /generic_format /F2R /= /cexp /fexp.
set Ma := Ztrunc  _.
set Mb := Ztrunc _ .
rewrite (mag_unique two a 1); last first.
  rewrite Zeq_minus // /= Rabs_pos_eq ?IZR_Zpower_pos /=;  lra.
rewrite (mag_unique two b 1); last first.
  rewrite Zeq_minus // /= Rabs_pos_eq ?IZR_Zpower_pos /=;  lra.
move=> maE mbE.
pose midp :=  (round two  fexp Zfloor (a/b) + round two fexp Zceil (a/b))/2. 
have: /2 < /b  by nra.
have: /b <= 1.
  have ->: 1 = /1 by field.
  apply:Rinv_le; lra.
move=> b1 b2.
have ab2: a/b < 2 by nra.
have ab2' : /2 <= a/b by nra.
have huab: ulp radix2 fexp (a / b) = 2*u.
  rewrite ulp_neq_0; last lra.
  rewrite /cexp /fexp (mag_unique two (a/b) 1).
    by rewrite bpow_plus.
  rewrite Rabs_pos_eq /= ?IZR_Zpower_pos /=; lra.
have midpE : midp = round two fexp Zfloor (a/b)+ / 2 * ulp two fexp (a/b).
  rewrite /midp round_UP_DN_ulp //.
  field.
rewrite -/fexp.
have : format (round radix2 fexp Zfloor (a / b)) by apply: generic_format_round.
rewrite /generic_format /F2R /=.
set Mmu := Ztrunc _.
set mid_exp := pow _.
have ->: mid_exp = pow (1 -p).
  rewrite /mid_exp /cexp /fexp.
  rewrite mag_DN; last first.
    apply:(Rlt_le_trans _ (/2)); first  lra.
    suff -> : /2 = round radix2 (fun e : Z => (e - p)%Z) Zfloor (/2) by  apply : round_le; lra.
    have->: /2 = pow (-1) by [].
    rewrite round_generic //.
    apply:generic_format_bpow; lia.
  rewrite (mag_unique _ _ 1) //.
  rewrite Rabs_pos_eq /= ?IZR_Zpower_pos /=;  lra.
move=> ablE.
move:(midpE).
rewrite ablE.
rewrite ulp_neq_0; last lra.
rewrite /cexp /fexp (mag_unique _ _ 1) //;last first.
  rewrite Rabs_pos_eq /= ?IZR_Zpower_pos /=;  lra.
rewrite bpow_plus.
have->: IZR Mmu * (pow 1 * pow (- p)) + / 2 * (pow 1 * pow (- p)) = (2 *(IZR Mmu) +1) * pow (-p) 
  by rewrite /= IZR_Zpower_pos /=; field.
move=> midpE'.
have : a/b - midp = ((pow p) * IZR Ma - IZR Mb * (2* IZR Mmu +1))/ IZR Mb * pow (-p).
  rewrite maE mbE midpE' bpow_plus.
  have->: pow 1 = 2 by [].
  case:(Req_dec (IZR Mb) 0)=> Mb0.
  move:mbE; rewrite Mb0; lra.
  field_simplify=>//; last split =>//.
    rewrite (Rmult_assoc (IZR Ma))  -bpow_plus.
    have-> : pow (- p + p ) = 1 by ring_simplify (- p + p)%Z.
    by field.
  move:(bpow_gt_0 two (-p)); lra.
rewrite -IZR_Zpower; last lia.
have Mb1: (1 <= Mb)%Z.
  suff:  (0 < Mb)%Z by lia.
  apply:lt_IZR.
  rewrite mbE in hb; move:(bpow_gt_0 two (1 -p)); nra.
have Mb2p: (Mb <= radix2 ^ p - 1)%Z.
  rewrite - (Z.abs_eq  Mb); try lia.
  rewrite /Mb; apply: FLX_mant_le=>//;  lia.
have MbR1: 1 <= IZR Mb by apply: IZR_le.
have upos:= (upos p).
have->: (IZR (radix2 ^ p) * IZR Ma - IZR Mb * (2 * IZR Mmu + 1)) = 
                     IZR ((radix2 ^ p) * Ma - Mb * (2 * Mmu + 1))%Z.
  by rewrite !(=^~mult_IZR, =^~plus_IZR, =^~minus_IZR).
case:(Z.eq_dec (radix2 ^ p * Ma - Mb * (2 * Mmu + 1)) 0)=> Num0.
  have: (  (2 * Mmu + 1) * Mb = Ma * radix2 ^ p )%Z by lia.
  move/Zdivide_intro=> h.
  have:  (radix2 ^ p |  Mb).
    apply:(Z.gauss _ (2 * Mmu + 1))=>//.
    apply:gcd_pow2_odd; lia.
  move=>hMbd.
  have : ( (radix2 ^ p)<= Mb )%Z.
    apply:Z.divide_pos_le=>//.
    lia.
  lia.
have Mbi0: 0 < /IZR Mb.
  apply: Rinv_0_lt_compat ; lra.
have: (1 <= Z.abs (radix2 ^ p * Ma - Mb * (2 * Mmu + 1)))%Z.
  suff: (0 <  Z.abs (radix2 ^ p * Ma - Mb * (2 * Mmu + 1)))%Z by lia.
  by apply Z.abs_pos.
move=>/IZR_le  hh habmidp.
have: /IZR Mb * (pow (-p))<= Rabs(a/b -midp).
  rewrite   habmidp.
  rewrite abs_IZR in  hh.
  rewrite /Rdiv !Rabs_mult (Rabs_pos_eq  (/ IZR Mb)); try lra.
  rewrite (Rabs_pos_eq  (pow (- p))); try lra.
  rewrite -[X in X <= _ ]Rmult_1_l Rmult_assoc.
  apply:Rmult_le_compat; try lra.
  apply:Rmult_le_pos; lra.
move=>h0.
have abmidp: 2 * (u * u)/b <= Rabs (a / b - midp).
  rewrite {1}mbE /u bpow_plus.
  have ->: 2 = pow 1 by [].
  suff->:  pow 1 * (pow (- p) * pow (- p)) / (IZR Mb * (pow 1 * pow (- p))) = /
                            IZR Mb * pow (- p) by [].
  field; split; first lra.
  split.
    move:(bpow_gt_0 two (-p)); lra.
  have->: pow 1 = 2 by [].
  lra.
set u2:= u * u.
have ->: u = ulp radix2 fexp (a / b) /2.
  rewrite ulp_neq_0 ; last lra; rewrite /cexp/fexp (mag_unique _ _ 1).
    rewrite bpow_plus -/u.
    have->: pow 1 = 2 by [].
    field.
  rewrite Rabs_pos_eq /= ?IZR_Zpower_pos /=;  lra.
set err  := Rabs _.
case: (Req_dec err  0)=> rn0.
  rewrite rn0 huab /u2.
  clear - upos hb Hp1.
  suff :  2 / b * (u * u) <=   u by lra.
  suff: 2/b * u <= 1 by rewrite /u; nra.
  apply :(Rmult_le_reg_r b).
    lra.
  field_simplify.
    (* rewrite /Rdiv Rinv_1 !Rmult_1_r. *)
    suff : u  <= /2 by nra.
    have ->: /2 = pow (-1) by [].
    rewrite /u; apply bpow_le; lia.
  lra.
apply:(@l6_1_pre (round radix2 fexp Zfloor (a / b)) midp).
+ rewrite -round_UP_DN_ulp.
    by apply:round_DN_UP_le.
  move=> Fab; apply:rn0.
  by rewrite /err round_generic // Rabs0; ring.
+ case:(round_N_pt two fexp choice (a/b)).
  move => _; apply.
  by apply:generic_format_round.
+ case:(round_N_pt two fexp choice (a/b))=>_; apply.
  rewrite huab.
  suff ->: 2 * u = ulp two fexp (round radix2 fexp Zfloor (a / b)).
    apply: generic_format_succ_aux1.
      apply:(Rlt_le_trans _ 1); try lra.
      suff->: 1 = round radix2 fexp Zfloor 1.
        by apply:round_le.
      have ->: 1 = pow 0 by [].
      rewrite round_generic //.
      apply: generic_format_bpow.
      by rewrite /fexp; lia.
    by apply:generic_format_round.
  by rewrite ulp_DN ?huab //; lra.
+ rewrite midpE; field.
rewrite /u2; lra.
Qed.

Lemma l6_1_2 a b (Fa : format a) (Fb : format b): 1 <= a < 2 -> 1 <= b < 2 ->
    a/b < 1  -> Rabs (rnd_p (a/b) - a/b) <= u/2 -  /b *(u * u).
Proof.
move => ha hb hab .
case:(Req_dec (rnd_p (a/b) - a/b) 0)=> Hab.
  rewrite Hab Rabs_R0.
  have upos := (upos p).
  have : 0 < u < /2 .
    have->: /2 = pow (-1) by [].
    rewrite /u; split; try lra; apply:bpow_lt; lia.
  move =>[ u0 u2].
  (* suff: u <= 1 - 2/b * u by nra. *)
  suff: (2 * u)/ b <= 1 by nra.
  apply:(Rmult_le_reg_r b); try nra.
  rewrite Rmult_assoc Rinv_l ?Rmult_1_l ?Rmult_1_r; lra.
have Fnab: ~(format (a/b)).
  move=> Fab; apply Hab.
  rewrite round_generic //; ring.
move: (Fa) (Fb); rewrite /generic_format /F2R /= /cexp /fexp.
set Ma := Ztrunc  _.
set Mb := Ztrunc _ .
rewrite (mag_unique two a 1); last first.
  rewrite Zeq_minus // /= Rabs_pos_eq ?IZR_Zpower_pos /=;  lra.
rewrite (mag_unique two b 1); last first.
  rewrite Zeq_minus // /= Rabs_pos_eq ?IZR_Zpower_pos /=;  lra.
move=> maE mbE.
pose midp :=  (round two  fexp Zfloor (a/b) + round two fexp Zceil (a/b))/2. 
have: /2 < /b.
  apply: Rinv_lt; lra.
have: /b <= 1.
  have ->: 1 = /1 by field.
  apply:Rinv_le; lra.
move=> b1 b2.
have ab2' : /2 <= a/b by nra.
have huab: ulp radix2 fexp (a / b) = u.
  rewrite ulp_neq_0; last lra.
  rewrite /cexp /fexp (mag_unique two (a/b) 0).
    by rewrite bpow_plus Rmult_1_l.
  rewrite Rabs_pos_eq /= ?IZR_Zpower_pos /=; lra.
have midpE : midp = round two fexp Zfloor (a/b)+ / 2 * ulp two fexp (a/b).
  rewrite /midp round_UP_DN_ulp //.
  field.
rewrite -/fexp.
have : format (round radix2 fexp Zfloor (a / b)) by apply: generic_format_round.
rewrite /generic_format /F2R /=.
set Mmu := Ztrunc _.
set mid_exp := pow _.
have ->: mid_exp = pow ( -p).
  rewrite /mid_exp /cexp /fexp.
  rewrite mag_DN; last first.
    apply:(Rlt_le_trans _ (/2)); first  lra.
    suff -> : /2 = round radix2 (fun e : Z => (e - p)%Z) Zfloor (/2) by  apply : round_le; lra.
    have->: /2 = pow (-1) by [].
    rewrite round_generic //.
    apply:generic_format_bpow; lia.
  rewrite (mag_unique _ _ 0) //.
  rewrite Rabs_pos_eq /= ?IZR_Zpower_pos /=;  lra.
move=> ablE.
move:(midpE).
rewrite ablE.
rewrite ulp_neq_0; last lra.
rewrite /cexp /fexp (mag_unique _ _ 0) //;last first.
  rewrite Rabs_pos_eq /= ?IZR_Zpower_pos /=;  lra.
rewrite bpow_plus Rmult_1_l.
have->: IZR Mmu * pow (- p) + / 2 *  pow (- p) = (2 *(IZR Mmu) +1) * pow (-1 - p).
  by rewrite bpow_plus /= IZR_Zpower_pos /=; field.
move=> midpE'.
have : a/b - midp = ((pow (p+1)) * IZR Ma - IZR Mb * (2* IZR Mmu +1))/ IZR Mb * pow (-1 -p).
  rewrite maE mbE midpE' bpow_plus.
  have->: pow 1 = 2 by [].
  case:(Req_dec (IZR Mb) 0)=> Mb0.
  move:mbE; rewrite Mb0; lra.
  field_simplify=>//; last split =>//.
    suff ->: 2 * IZR Ma * pow (-1 - p) * pow p = IZR Ma by [].
    rewrite  bpow_plus !Rmult_assoc -bpow_plus.
    have-> : pow (- p + p ) = 1 by ring_simplify (- p + p)%Z.
    have->: pow (-1) = /2 by [].
    by field.
  move:(bpow_gt_0 two (1-p)); lra.
rewrite -IZR_Zpower; last lia.
have Mb1: (1 <= Mb)%Z.
  suff:  (0 < Mb)%Z by lia.
  apply:lt_IZR.
  rewrite mbE in hb; move:(bpow_gt_0 two (1 -p)); nra.
have Mb2p: (Mb <= radix2 ^ p - 1)%Z.
  rewrite - (Z.abs_eq  Mb); try lia.
  rewrite /Mb; apply: FLX_mant_le=>//;  lia.
have MbR1: 1 <= IZR Mb by apply: IZR_le.
have upos:= (upos p).
have->: (IZR (radix2 ^ (p+1)) * IZR Ma - IZR Mb * (2 * IZR Mmu + 1)) = 
                     IZR ((radix2 ^ (p+1)) * Ma - Mb * (2 * Mmu + 1))%Z.
  by rewrite !(=^~mult_IZR, =^~plus_IZR, =^~minus_IZR).
case:(Z.eq_dec (radix2 ^ (p+1) * Ma - Mb * (2 * Mmu + 1)) 0)=> Num0.
  have: (  (2 * Mmu + 1) * Mb = Ma * radix2 ^ (p +1))%Z by lia.
  move/Zdivide_intro=> h.
  have:  (radix2 ^ (p +1)|  Mb).
    apply:(Z.gauss _ (2 * Mmu + 1))=>//.
    apply:gcd_pow2_odd; lia.
  move=>hMbd.
  have : ( (radix2 ^ (p+1))<= Mb )%Z.
    apply:Z.divide_pos_le=>//.
    lia.

rewrite Zpower_plus; try lia.

have-> : (radix2 ^ 1 = 2)%Z by [].
lia.
have Mbi0: 0 < /IZR Mb.
  apply: Rinv_0_lt_compat ; lra.
have: (1 <= Z.abs (radix2 ^ (p+1) * Ma - Mb * (2 * Mmu + 1)))%Z.
  suff: (0 <  Z.abs (radix2 ^ (p+1) * Ma - Mb * (2 * Mmu + 1)))%Z by lia.
  by apply Z.abs_pos.
move=>/IZR_le  hh habmidp.
have: /IZR Mb * (pow (-1-p))<= Rabs(a/b -midp).
  rewrite   habmidp.
  rewrite abs_IZR in  hh.
  rewrite /Rdiv !Rabs_mult (Rabs_pos_eq  (/ IZR Mb)); try lra.
  have pow_pos := (bpow_gt_0 two (-1 -p)).
  rewrite (Rabs_pos_eq  (pow (-1 - p))); try lra.
  rewrite -[X in X <= _ ]Rmult_1_l Rmult_assoc.
  apply:Rmult_le_compat; try lra.
  apply:Rmult_le_pos; lra.
move=>h0.
have abmidp:  (u * u)/b <= Rabs (a / b - midp).
  rewrite {1}mbE /u bpow_plus.
  suff ->:  pow (- p) * pow (- p) / (IZR Mb * (pow 1 * pow (- p))) =  / IZR Mb * pow (-1 - p) by [].
  field_simplify; try lra.
    rewrite bpow_plus/= ?IZR_Zpower_pos  /=; field; lra.
  split; try lra; split; rewrite /= ?IZR_Zpower_pos  /=;  lra.
set u2:= u * u.
rewrite -huab.
set err  := Rabs _.
case: (Req_dec err  0)=> rn0.
  rewrite rn0 huab /u2.
  clear - upos hb Hp1.
  suff :  /b * (u * u) <=   u/2 by lra.
  suff: 2/b * u <= 1 by rewrite /u; nra.
  apply :(Rmult_le_reg_r b).
    lra.
  field_simplify.
    (* rewrite /Rdiv Rinv_1 !Rmult_1_r. *)
    suff : u  <= /2 by nra.
    have ->: /2 = pow (-1) by [].
    rewrite /u; apply bpow_le; lia.
  lra.
apply:(@l6_1_pre (round radix2 fexp Zfloor (a / b)) midp).
+ rewrite -round_UP_DN_ulp.
    by apply:round_DN_UP_le.
  move=> Fab; apply:rn0.
  by rewrite /err round_generic // Rabs0; ring.
+ case:(round_N_pt two fexp choice (a/b)).
  move => _; apply.
  by apply:generic_format_round.
+ case:(round_N_pt two fexp choice (a/b))=>_; apply.
  rewrite huab.
  suff ->: u = ulp two fexp (round radix2 fexp Zfloor (a / b)).
    apply: generic_format_succ_aux1.
      apply:(Rlt_le_trans _ (/2)); try lra.
      suff->: /2 = round radix2 fexp Zfloor (/2).
        by apply:round_le.
      have ->: /2 = pow (-1) by [].
      rewrite round_generic //.
      apply: generic_format_bpow.
      by rewrite /fexp; lia.
    by apply:generic_format_round.
  by rewrite ulp_DN ?huab //; lra.
+ rewrite midpE; field.
rewrite /u2; lra.
Qed.


Fact l6_2_aux b :  1 <= b ->  u/2 -  /b *(u * u)<=  u - (2 /b) *(u * u).
Proof.
move=> ble1.
(* suff: 0 <= u/2 - /b * (u * u) by nra. *)
have upos : 0 < u by apply:upos.

suff: u/b <= /2 by nra.
apply:(Rmult_le_reg_r (2*b)); first lra.
field_simplify ; try lra.
(* rewrite /Rdiv Rinv_1 !Rmult_1_r. *)
apply:(Rle_trans _ 1)=>//.
have->: 1 = pow 0 by [].

have ->: 2 = pow 1 by [].
rewrite /u -bpow_plus.
apply bpow_le; lia.
Qed.


Fact l6_2 a b (Fa : format a) (Fb : format b): 1 <= a < 2 -> 1 <= b < 2 
                -> Rabs (rnd_p (a/b) - a/b) <= u - (2 /b) *(u * u).
Proof.
move=> ha hb.
case:(Rle_lt_dec 1 (a/b))=> hab.
  by apply: l6_1_1.
apply:(Rle_trans _ (u/2 -  /b *(u * u))).

  by apply: l6_1_2.
apply: l6_2_aux; lra.
Qed.


(* Theorem 6.1 *)

Lemma DWDFP_correct xh xl y (DWx: double_word xh xl) (Fy : format y) (Hp4: (4 <= p)%Z)(yn0 : y <> 0):
  let (zh, zl) := DWDivFP2 xh xl y in
  let xy := ((xh + xl) / y)%R in
  Rabs ((zh + zl - xy) / xy) <= 7/2*(u * u).
Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
case:(is_pow_dec two y).
  move=>[ e ye].
  rewrite /DWDivFP2 TwoProdE.
  have rq : forall x,  rnd_p (x / y) = (rnd_p x) /y.
    move=>x ; rewrite /Rdiv.
    have: Rabs (/y) = pow (-e) by rewrite Rabs_Rinv // ye bpow_opp.
    rewrite -(Rabs_pos_eq (pow (-e))); last by  apply: bpow_ge_0.
    case/Rabs_eq_Rabs=> ->.
      by rewrite round_bpow.
    have ->: x * - pow (- e) = - (x * pow (- e)) by ring.
    rewrite ZNE round_NE_opp -ZNE  round_bpow; ring.
  case: (DWx)=> [[Fxh Fxl] xE].
  rewrite (rq xh).
  have->: rnd_p xh = xh by rewrite round_generic.
  (* rewrite TwoProdE /=. *)
 rewrite /Fast2Mult.
  have->:  xh / y * y  = xh by field.
  have->: rnd_p xh = xh by rewrite round_generic.
  have ->: xh -xh = 0 by ring.
  rewrite round_0 Rminus_0_r Rplus_0_l round_round //.
  have->: rnd_p xl = xl by rewrite round_generic.
  rewrite (rq xl).
  have->: rnd_p xl = xl by rewrite round_generic.
  case:(Req_dec xl 0)=> xl0.
    rewrite xl0.
    have ->: 0 / y = 0 by field.
    have Fxhy : format (xh /y).
      suff ->: xh / y = rnd_p (xh/y) by apply:generic_format_round.
      by rewrite rq round_generic.
    rewrite Fast2Sumf0 //.
    rewrite !Rplus_0_r Rabs0.
      rewrite /u ; move: (bpow_ge_0 two (-p)); nra.
    by ring_simplify  (xh / y - xh / y); rewrite /Rdiv Rmult_0_l.
  rewrite (surjective_pairing (Fast2Sum  _ _))
                 F2Sum_correct_cexp //=.
  + have ->: (xh / y + xl / y) = (xh + xl) /y by field.
    rewrite rq -xE.
    have->: ((xh / y + ((xh + xl) / y - xh / y) - (xh + xl) / y)) = 0 by ring.
    rewrite {1}/Rdiv Rmult_0_l Rabs_R0.
    rewrite /u ; move: (bpow_ge_0 two (-p)); nra.
  + have->: xh = rnd_p xh by rewrite round_generic.
    by rewrite -rq; apply: generic_format_round.
  + have->: xl = rnd_p xl by rewrite round_generic.
    by rewrite -rq; apply: generic_format_round.
  rewrite /cexp.
  apply/monotone_exp/mag_le_abs.
  move/Rinv_neq_0_compat:(  yn0 ); nra.
  rewrite /Rdiv !Rabs_mult; apply/Rmult_le_compat_r.
    by apply/Rabs_pos.
  apply:(Rle_trans _  (/2 * ulp two fexp xh)).
    by apply: (dw_ulp Hp1 DWx).
  apply: (Rle_trans _  (ulp two fexp xh)).
    suff: (0 <= ulp radix2 fexp xh) by lra.
    by apply:ulp_ge_0.
  apply: ulp_le_abs=>// xh0.
  have: rnd_p (xh + xl ) <> 0.
    by rewrite xh0 Rplus_0_l round_generic.
  by rewrite -xE xh0.
case:(DWx)=>[[Fxh Fxl] xE].
case:(Req_dec xh 0)=> xh0.
  have xl0: xl = 0.
    by move:xE; rewrite  xh0 Rplus_0_l round_generic.
move=> ynpow.
case E1: DWDivFP2 => [zh zl].
move=> xy.
rewrite /xy; clear xy.
move : (E1); rewrite /DWDivFP2 TwoProdE /=.
  rewrite xh0 xl0 /Rdiv !(Rmult_0_l, round_0, Rplus_0_l,  Rminus_0_l, Ropp_0).
  case=> <- <-.
  rewrite !(Rplus_0_r, round_0, Rminus_0_r, Rmult_0_l) Rabs0 //.
  nra.
move=> ynpow.
case E1:DWDivFP2=>[zh zl].
move=> xy.
rewrite /xy {xy Fxh Fxl xE}.
wlog ypos: y xh xl zh zl DWx Fy  E1   yn0 xh0 ynpow  / 0 <= y.
  move=>Hwlog.
  case:(Rle_lt_dec 0 y) => yle0; first by apply:Hwlog.
  have ->: (zh + zl - (xh + xl) / y) / ((xh + xl) / y) = 
            ((- zh + - zl - (xh + xl) / (- y)) / ((xh + xl) /( - y))).
    field.
    split =>//.
    move=> xhxl0; apply: xh0.
    case:(DWx) => [[Fxh Fxl] xE].
    by rewrite xE   xhxl0 round_0.
  apply:Hwlog=>//; try nra; first last.
  + move=> *; apply: ynpow.
    have ->: y = - (- y) by ring.
    by apply:is_pow_opp.
  + by rewrite DWDivFP_Asym_r // E1.
  by apply: generic_format_opp.
have {} ypos : 0 < y by lra.
wlog [y1 y2]: y  zh zl  Fy yn0 ynpow  ypos E1/ 1 <= y <= 2-2*u.
  move=>Hwlog.
  case: (scale_generic_12 Fy ypos)=> ey Hys.
  have ->: (zh + zl - (xh + xl) / y) / ((xh + xl) / y) = 
         (zh / pow ey  + zl / pow ey - (xh  + xl) /( y * pow ey)) / ((xh + xl ) /( y * pow ey)).
    field; split ; first by move:(bpow_gt_0 two ey); lra.
    split=> //.
    move=> xhxl0; apply xh0.
    case:(DWx) => [[Fxh Fxl] xE].
    by rewrite xE   xhxl0 round_0.
  apply:Hwlog; last by rewrite /u.
  + by apply:formatS.
  + move: (bpow_gt_0 two ey); nra.
  + move=> [e he]; apply: ynpow.
    exists (e -ey)%Z.
    rewrite bpow_plus.
    move: he; rewrite Rabs_mult !Rabs_pos_eq; move:(bpow_gt_0 two ey); try nra.
    move=>*.
    apply:(Rmult_eq_reg_r  (pow ey)).
      rewrite Rmult_assoc -bpow_plus.
      by ring_simplify (-ey + ey)%Z; rewrite /= Rmult_1_r.
    by move:(bpow_gt_0 two ey); lra.
  + by move:(bpow_gt_0 two ey); nra.
  by rewrite DWDivFPSy // E1.
wlog xpos:  xh xl zh zl DWx   E1 xh0   / 0 <= xh.
  move=>Hwlog.
  case:(Rle_lt_dec 0 xh) => xhle0; first by apply:Hwlog.
  have ->: (zh + zl - (xh + xl) / y) / ((xh + xl) / y) = 
            ((- zh + - zl - (-xh + -xl) / y) / ((-xh + -xl) /y)).
    field.
    split =>//.
    suff: xh + xl <> 0 by lra.
    move=> xhxl0; apply: xh0.
    case:(DWx) => [[Fxh Fxl] xE].
    by rewrite xE   xhxl0 round_0.
  apply:Hwlog=>//; try nra.
    case:(DWx) => [[Fxh Fxl] xE].
    split; [split|idtac].
    + by apply:generic_format_opp.
    + by apply:generic_format_opp.
    have->:  (- xh + - xl) = - (xh + xl) by ring.
    by rewrite ZNE round_NE_opp -ZNE -xE.
  by rewrite DWDivFP_Asym_l // E1.
have {xpos} xhpos : 0 < xh by lra.
wlog [xh1 xh2]: xh xl  zh zl  DWx {xh0} xhpos E1/ 1 <= xh <= 2-2*u.
  move=>Hwlog.
  case:(DWx) => [[Fxh Fxl] xE].
  case: (scale_generic_12 Fxh xhpos)=> exh Hxhs.
  have xhxl0: xh + xl <> 0 by move=> xhxl0; apply: xh0; rewrite xE  xhxl0 round_0.
  have ->: (zh + zl - (xh + xl) / y) / ((xh + xl) / y) = 
         (zh * pow exh  + zl * pow exh - (xh* pow exh   + xl* pow exh) /( y )) / ((xh  * (pow exh) + xl * (pow exh)) /( y )).
    field; split;  first by lra.
    by split=>//;rewrite -Rmult_plus_distr_r;  move:(bpow_gt_0 two exh); nra.
  apply:Hwlog=>//.
  + split; first by split ; apply:formatS.
    by rewrite   -Rmult_plus_distr_r round_bpow [in LHS]xE.
  + by move:(bpow_gt_0 two exh); lra.
  by rewrite DWDivFPSx // E1.
have yinvpos: 0 < /y by apply: Rinv_0_lt_compat.
have {} y1: 1 + 2*u <= y.
  case:y1=>y1.
    suff ->: 1 + 2*u = succ two  fexp  1.
      apply: succ_le_lt=> //.
      have ->: 1 = pow 0 by [].
      by apply:generic_format_bpow; rewrite /fexp ; lia.
    rewrite succ_eq_pos; try lra.
    by apply:Rplus_eq_compat_l; rewrite /u u_ulp1 ; field.
  suff: is_pow radix2 y by [].
  by exists 0%Z; rewrite -y1 Rabs_pos_eq //=;  lra.
have xlu: Rabs xl <= u.
  suff <-:  / 2 * ulp radix2 fexp xh = u by apply:  (dw_ulp Hp1 DWx).
rewrite ulp_neq_0; last lra.
rewrite /cexp /u /fexp.
rewrite (mag_unique two xh 1).
rewrite bpow_plus /= IZR_Zpower_pos /= ; field.
rewrite bpow_plus /=  IZR_Zpower_pos /= Rabs_pos_eq ?Rmult_1_r ?Rinv_r; try lra.
move:(upos p); rewrite -/u; lra.
have h30: 1/(2 - 2*u) <= xh/y <= (2 - 2*u) / (1 + 2*u).
  clear -  yn0    ypos  y2   xhpos  xh1  xh2    y1 Hp1; move:(upos p); rewrite -/u=> upos.
  have ult1: u < 1 by rewrite /u; apply:bpow_lt_1; lia.
  rewrite /Rdiv; split; apply: Rmult_le_compat; try lra.
  + apply/Rlt_le/Rinv_0_lt_compat; lra.
  + apply/Rinv_le; lra.
  + apply/Rlt_le/Rinv_0_lt_compat; lra.
   apply/Rinv_le; lra.
have h30a: 1/2 + u/2 < 1/(2 - 2*u).
  clear -  yn0    ypos  y2   xhpos  xh1  xh2    y1 Hp1; move:(upos p); rewrite -/u=> upos.
  have ult1: u < 1 by rewrite /u; apply:bpow_lt_1; lia.
  have->: 1 / 2 + u / 2 = (1 + u) /2 by field.
  have->:  (2 - 2 * u) =  (1 - u) *2 by field.
  rewrite /Rdiv Rinv_mult_distr; try lra.
  rewrite Rmult_1_l; apply:Rmult_lt_compat_r; try lra.
  apply:(Rmult_lt_reg_r (1 - u)); try lra.
  rewrite Rinv_l; try lra.
  have u2pos: 0 < u * u by apply:Rmult_lt_0_compat; lra.
  nra.
move:(upos p); rewrite -/u=> upos.
have h30b: (2 - 2*u)/(1 + 2 *u) < 2 - 5 *u.
  apply: (Rmult_lt_reg_r (1 + 2 *u));  try lra.
  rewrite /Rdiv Rmult_assoc Rinv_l ?Rmult_1_r; try lra.
  suff : 10 * u * u < u by lra.
  suff: u < 1/10 by nra.
  apply:(Rle_lt_trans _ (1/16)); try lra.
  have ->: 1/16 = pow (-4).
    rewrite /= IZR_Zpower_pos /=; field.
  rewrite /u; apply:bpow_le; lia.
have: 1/2 + u/2 < xh /y < 2 - 5*u by lra.
pose th := rnd_p (xh/y). 
move=> [hl hu].
have Fdmsu : format (2 - 6 * u).
  have->: 2 - 6*u = (1 - 3* u) * 2 by ring.
  have ->: 2 = pow 1 by [].
  apply:formatS=>//.
  have xE : 1 - 3 * u = F2R (Float two (2^p -3)%Z (-p)).
    rewrite /F2R /= minus_IZR /u (IZR_Zpower two); last lia.
    by rewrite Rmult_minus_distr_r -bpow_plus Z.add_opp_diag_r.
  apply:(FLX_format_Rabs_Fnum p xE).
  rewrite /= minus_IZR  (IZR_Zpower two); last lia.
  rewrite Rabs_pos_eq; try lra.
  suff : 4 <= pow p by lra.
  have ->: 4 = pow 2 by [].
  apply:bpow_le; lia.
have dmsu : 0 < 2 - 6 * u.
  suff : 3*u < 2 by lra.
  suff : u < /2 by nra.
  rewrite /u; have ->: /2 = pow (-1) by [].
  apply: bpow_lt ; lia.
have Fdpu : format (1/2 + u).
  have xE : 1/2 + u = F2R (Float two (2 ^ (p -1) + 1)%Z (-p)).
    rewrite /F2R /= plus_IZR /u (IZR_Zpower two);last lia.  
    rewrite Rmult_plus_distr_r -bpow_plus Rmult_1_l.
    ring_simplify(p - 1 + - p)%Z.
    by have->: pow (- (1)) = /2 by []; field.
  apply:(FLX_format_Rabs_Fnum p  xE).
  rewrite /= plus_IZR (IZR_Zpower two); last lia.
  rewrite Rabs_pos_eq; last first.
    by move:(bpow_ge_0 two (p -1)); lra.
  rewrite bpow_plus /= IZR_Zpower_pos  /=.
  suff : 2 <  pow p by lra.
  have ->: 2 = pow 1 by [].
  apply:bpow_lt; lia.
have h31b:1/2 + u <= rnd_p (xh/y).
  apply:round_N_ge_midp=>//.
  rewrite notpow_pred //; try lia.
    rewrite ulp_neq_0 /cexp /fexp ; last lra.
    rewrite (mag_unique two _ 0); last first.
      have ->:  (0 - 1)%Z = (-1)%Z by ring.
      have ->: pow (-1) = /2 by [].
      rewrite Rabs_pos_eq; last first.
        rewrite /u; move:(bpow_ge_0 two (-p)); lra.
      split; first lra.
      rewrite /=.
      suff: u < /2 by lra.
      rewrite /u; have ->: /2 = pow (-1) by [].
      apply:bpow_lt; lia.
    ring_simplify (0 -p)%Z.
    move:hl; rewrite /u; lra.
  case:(is_pow_dec two  (1 / 2 + u))=>// hpow.
  case:hpow=> e.
  rewrite Rabs_pos_eq.
    move=> xe.
    have : 1/2 < 1/2 + u by lra.
    have: 1/2 + u < 1 .
      suff: u < /2 by lra.
      rewrite /u ; have ->: /2 = pow (-1) by [].
      apply bpow_lt ; lia.
    rewrite xe.
    have {1}-> : 1 = pow 0 by [].
    move/lt_bpow=> e0.
    rewrite /Rdiv.
    have ->: /2 = pow (-1) by [].
    rewrite Rmult_1_l.
    move/lt_bpow=> e1.
    lia.
  rewrite /u; move:(bpow_ge_0 two (-p)); lra.
have h31a: rnd_p (xh/y) <= 2 - 6 * u.
  apply:round_N_le_midp=>//.
  rewrite succ_eq_pos; last lra.
  rewrite ulp_neq_0 /cexp /fexp ; last lra.
  rewrite (mag_unique two _ 1); last first.
    rewrite /= IZR_Zpower_pos /=  !Rmult_1_r Rabs_pos_eq; try lra.
    split; last  by  lra.
    suff: u <= /8 by lra.
    have ->: /8 = pow (-3) by [].
    rewrite /u ; apply:bpow_le; lia.
  ring_simplify (2 - 6 * u + (2 - 6 * u + pow (1 - p))).
  rewrite bpow_plus /= IZR_Zpower_pos /= -/u.
  lra.
move:(E1).
rewrite /DWDivFP2 TwoProdE /= -/th.
set  pih := rnd_p (th * y).
set pil := rnd_p(th *y - pih).
have pihlE : th * y = pih + pil.
  by rewrite [in LHS]Fast2Mult_correct /= /pil /pih.
set dh := xh -pih.
set dl := rnd_p (xl - pil).
set d := rnd_p (dh + dl).
pose e1 := dl - (xl -pil).
pose e2 := d - (dh + dl).
set  tl := rnd_p (d/y).
pose e3 := tl -d/y.
pose e := e1 + e2.
pose x := xh + xl.
have dE: d = x - th*y + e.
  rewrite  /x /th /e /e1 /e2 /dh /dl pihlE; ring.
have thtlE: th + tl = x/y + e/y + e3.
  rewrite  /e3 /e /e1 /e2 /dh /x.
  field_simplify=>//.
  rewrite Rplus_assoc (Rplus_comm pil)  -pihlE.
  by field.
case:(DWx) => [[Fxh Fxl] xE].
have h34: Rabs (th -xh/y) <= u - 2/y *(u *u).
  by rewrite /th; apply:l6_2=>//; lra.
have h35: Rabs (th*y -xh) <= 2*u -4* (u * u).
  apply:(Rle_trans _ (u*y -2* (u *u))).
    have ->: (th * y - xh) = (th - xh / y)*y by field.
    rewrite Rabs_mult (Rabs_pos_eq y); last by  lra.
    have->:  u * y - 2 * (u * u) = ( u - 2 / y * (u * u)) * y by field; lra.
    apply:Rmult_le_compat_r; lra.
  clear - y1 y2 upos; nra.
have h36 : Rabs (th *y) <= 2 - 4*(u*u).
  have->: th*y = (th*y -xh) + xh by ring.
  apply :(Rle_trans _ _  _  (Rabs_triang _ _)).
  rewrite (Rabs_pos_eq xh); lra.
have h37a: Rabs pil <= u.
  have->: pil = - (pih - th*y) by rewrite pihlE; ring.
  rewrite  /pih Rabs_Ropp.
  apply:(Rle_trans _ (/ 2 * ulp two fexp (th*y))); first by apply:error_le_half_ulp.
  suff thy0: th * y <> 0.
    rewrite ulp_neq_0 /cexp /fexp // bpow_plus -/u.
    set m := (mag radix2 (th * y)).
    suff: (pow m) <= 2 by clear - upos; nra.
    have ->: 2 = pow 1 by [].
    apply:bpow_le.
    rewrite /m -(mag_unique_pos two  (2 - 4 * (u * u)) 1).
      apply: mag_le_abs=>//.
      rewrite (Rabs_pos_eq  (2 - 4 * (u * u))) //.
      suff: (u * u) <= /2  by lra.
      have ->: /2 = pow (-1) by [].
      rewrite /u -bpow_plus; apply: bpow_le; lia.
    rewrite /= IZR_Zpower_pos /=.
    split; clear -upos Hp1; try nra.
    suff: (u * u) <= /4  by lra. 
    have ->: /4 = pow (-2) by [].
    rewrite /u -bpow_plus; apply: bpow_le; lia.
  apply:Rmult_integral_contrapositive_currified; try lra.
  rewrite /th.
  apply:round_neq_0_negligible_exp.
    by apply:negligible_exp_FLX.
  rewrite /Rdiv.
  apply:Rmult_integral_contrapositive; split;  lra.
have h37b : Rabs (xl -pil) <= 2*u .
  apply :(Rle_trans _ _  _  (Rabs_triang _ _)).
  rewrite Rabs_Ropp; lra.
have h37: Rabs e1 <= u * u.
  have->:  u * u =  / 2 * pow (- p) * pow (1 -p).
    rewrite bpow_plus -/u /= IZR_Zpower_pos /=; field.
  rewrite /e1 /dl.
  apply: error_le_half_ulp'; first lia.
  rewrite bpow_plus  -/u /= IZR_Zpower_pos /=; lra.
move/Rabs_le_inv:(h35)=> h35'.
have: xh - 2*u <= th*y <= xh + 2*u by clear -h35' upos; nra.
case; move/(round_le two fexp (Znearest choice)) => h38a /(round_le two fexp (Znearest choice)) h38b.
have ulpxh : ulp two fexp xh = 2*u.
  have xh0 : xh <> 0 by lra.
  rewrite ulp_neq_0 // /cexp /fexp.
  rewrite (mag_unique_pos two  xh  1).
    by rewrite bpow_plus -/u.
  ring_simplify(1-1)%Z; rewrite /= IZR_Zpower_pos /=; lra.
have Fxh2u: format (xh + 2 * u) by rewrite - ulpxh;apply:generic_format_succ_aux1=>//.
have Fxhm2u: format  (xh - 2 * u).
  case: (Req_dec xh 1)=> xhe1.
    rewrite xhe1.
    have xhE : 1 - 2* u = F2R (Float two (2 ^ p  -2 )%Z (-p)).
      rewrite /F2R /= plus_IZR /u (IZR_Zpower two) /=;last lia.  
      rewrite Rmult_plus_distr_r -bpow_plus.
      have ->: (p + -p = 0)%Z by ring.
      rewrite /=; ring.
    apply:(FLX_format_Rabs_Fnum p xhE).
    rewrite /= plus_IZR (IZR_Zpower two) ; last lia.
    rewrite opp_IZR Rabs_pos_eq; try  lra.
    suff : 2 <= pow p by lra.
    have ->: 2 = pow 1 by [].
    apply:bpow_le; lia.
  rewrite -ulpxh; apply:generic_format_pred_aux1; try lra.
    by [].
  rewrite (mag_unique_pos two  xh  1).
    have ->: (1-1 = 0)%Z by ring.
    rewrite /=; lra.
  have ->: (1-1 = 0)%Z by ring.
  by rewrite /= IZR_Zpower_pos /=; lra.
have h38: xh - 2*u <= pih <= xh + 2*u.
  have ->:   xh - 2 * u = rnd_p (xh -2*u) by rewrite round_generic.
  have ->:   xh +  2 * u = rnd_p (xh + 2*u) by rewrite round_generic.
  have u2pos: 0 < u * u by clear -upos; nra.
  rewrite /pih; split; apply: round_le; lra.
have h39a: Rabs dh <= 2*u.
  by rewrite /dh; apply:Rabs_le; lra.
have h39b: Rabs dl <= 2*u.
  rewrite /dl.
  move/(round_le two fexp (Znearest choice)):h37b.
  rewrite ZNE round_NE_abs -ZNE -/dl round_generic //.
  have->: 2 = pow 1 by [].
  rewrite /u -bpow_plus; apply: generic_format_bpow; rewrite /fexp; lia.
have h39c: Rabs (dh + dl) <= 4*u by  apply :(Rle_trans _ _  _  (Rabs_triang _ _)); lra.
have h39: Rabs e2 <= 2* (u * u).
  have ->:  2* (u * u) = /2 * pow (-p) * pow (2 -p).
    rewrite bpow_plus /= IZR_Zpower_pos /= -/u; field.
  apply: error_le_half_ulp'=>//.
  rewrite bpow_plus /= IZR_Zpower_pos /= -/u; lra.
 move/(round_le two fexp (Znearest choice)): h39c.
rewrite ZNE round_NE_abs -ZNE -/dl [X in _<= X]round_generic -/d; last first.
  have->: 4 * u =  pow (2 - p).
    have->:  4 = pow 2 by [].
    by rewrite bpow_plus  /u.
  apply:generic_format_bpow; rewrite /fexp; lia.
move=> h39d.
have h39e: Rabs(d/y) < 4*u.
clear - h39d yn0 y2 y1 upos.
have iy0: 0</y by apply:Rinv_0_lt_compat; lra.
  rewrite Rabs_mult (Rabs_pos_eq (/y)); last lra.
  have: /y < /1  by apply: Rinv_lt; lra.
  nra.
have h39f: Rabs tl <= 4 *u.
  have ->: 4 *u = rnd_p (4*u).
    rewrite round_generic //. 
    have ->: 4 * u = pow (2 -p) by rewrite bpow_plus -/u.
    by apply:generic_format_bpow; rewrite /fexp; lia.
  rewrite /tl ZNE -round_NE_abs -ZNE; apply:round_le; lra.
have th0: th <> 0.
  rewrite /th; apply:round_neq_0_negligible_exp.
    by apply:negligible_exp_FLX.
  rewrite /Rdiv; apply:Rmult_integral_contrapositive; split; lra.
(* cas e=> zhE zlE. *)
move=>E2.
have h39g: zh + zl = th + tl.
  move:E2;  rewrite (surjective_pairing (Fast2Sum  _ _))
                  F2Sum_correct_abs //=; try apply:generic_format_round.
    case => <- <-; ring.
  apply:(Rle_trans _ (4 * u)).
    by rewrite -/tl.
  rewrite Rabs_pos_eq.
    apply:(Rle_trans _ (1/2 + u)) =>//.
      suff : 4 * u <= /2 by lra.
      have ->: 4 = pow 2 by [].
      have ->: /2 = pow (-1) by [].
      rewrite /u -bpow_plus; apply:bpow_le; lia.
    have->: 0 = rnd_p 0 by rewrite round_0.
    apply:round_le.
    clear  - ypos xh1.
    rewrite /Rdiv; apply: Rmult_le_pos; try lra.
    suff: 0 < /y by lra.
    by apply:Rinv_0_lt_compat .
have xpos: 0 < x.
  rewrite /x.
  move/Rabs_le_inv : xlu.
  lra.
case: (Rle_lt_dec y x)=>hxy.
  move/(round_le two fexp (Znearest choice)): (hxy).
  rewrite /x -xE. 
  have <-: y = rnd_p y by rewrite round_generic.
  move=> yxh.
  have th1:  1 <= th.
    rewrite /th.
    suff->: 1 = rnd_p 1.
      apply:round_le.
      clear - xh1 y1  ypos  yxh.
      apply: (Rmult_le_reg_r y)=>//.
      rewrite /Rdiv Rmult_assoc Rinv_l; lra.
    have->: 1 = pow 0 by [].
    rewrite round_generic //; apply:generic_format_bpow; rewrite /fexp; lia.
  have :pih = xh -2*u \/ pih = xh \/ pih = xh+2*u.
    case:  h38 => xh2u_ub.
    case; last first.
      by move ->; right; right.
    move=> pihltxh.
    case: xh2u_ub; last by move ->; left.
    move=> xh2ultpih.
    have: pih <=  pred two fexp (xh + 2 * u).
      apply:pred_ge_gt=>//.
      by rewrite /pih; apply:generic_format_round.
    rewrite -ulpxh -succ_eq_pos ?pred_succ_pos //; try lra; move => pihlexh.
    have: (succ two fexp (xh - 2*u))<= pih.
      apply: succ_le_lt=>//.
      by rewrite /pih; apply:generic_format_round.
    rewrite -ulpxh -notpow_pred=>//; try lia.
      rewrite succ_pred_pos=>//.
      by move=> xhlepih; right; left; lra.
    case:(is_pow_dec two  (xh ))=>// hpow.
    case:hpow=> exh.
    rewrite Rabs_pos_eq; try lra.
    move=> xe.
    have: 1 < xh by lra.
    have : xh < 2 by lra.
    rewrite xe.
    have->: 1 = pow 0 by [].
    have ->: 2 = pow 1 by [].
    move/lt_bpow=>exh1.
    move/lt_bpow; lia.
  move=> pih_val.
  have dh_val: dh = -2*u \/ dh = 0 \/ dh = 2*u.
    by rewrite /dh; lra.
  have e1e2ub: Rabs (e1 + e2) <= 5/2*(u *u).
    case:dh_val=> dh_val.
      have: -u + 4* (u * u) <= dl <= 2*u.
        rewrite /dl.
        have:  pil <= -4 * (u * u).
          have->:pil = th*y - pih by rewrite pihlE; ring.
          have->:   th * y - pih  = (th*y -xh) + (xh - pih) by ring.
          by move: dh_val; rewrite /dh; move/Rabs_le_inv:  h35; lra.
        have: -u <= pil.
          by move/Rabs_le_inv:   h37a; lra.
        move/Rabs_le_inv: xlu => *.
        have hxlpil: -u + 4 * (u * u) <=  xl -pil <= 2*u  by lra.
        case:(hxlpil) =>/rnd_p_le; rewrite round_generic; first last.
          have -> : (- u + 4 * (u * u)) = - (( 1 - 4*u) *u) by ring.
          apply:generic_format_opp; rewrite /u; apply: formatS =>//.
          have->: (1 - 4 * pow (- p))= (pow p - 4)* pow (-p).
            by rewrite Rmult_minus_distr_r -bpow_plus; ring_simplify(p + -p)%Z ; 
               rewrite /=; ring.
          apply:formatS=>//.
          have He: (pow p - 4) =  F2R (Float two (2 ^ p  -4 )%Z (0)).
            rewrite /F2R /= plus_IZR /u (IZR_Zpower two) /=;last lia; ring.
          apply:(FLX_format_Rabs_Fnum p He).
          rewrite /= minus_IZR (IZR_Zpower two);  last lia.
          rewrite Rabs_pos_eq; first lra.
          suff : 4 <= pow p by lra.
          have ->: 4 = pow 2 by [].
          by apply: bpow_le ; lia.
        rewrite -/dl => dl_lb.
        move/rnd_p_le; rewrite (round_generic _ _ _ (2 *u)); first last.
          have->: 2*u = pow (1 - p) by rewrite bpow_plus -/u.
          by apply:generic_format_bpow; rewrite /fexp; lia.
        by rewrite -/dl.
      move=> hdl_b.
      case: (Rle_lt_dec u dl)=> dlu.
        have Fdhl: format (dh + dl).
          have ->: dh + dl = dl - (- dh) by ring.
          apply:sterbenz.
          + by rewrite /dl; apply:generic_format_round.
          + rewrite /dh; apply/generic_format_opp. 
            by rewrite /pih -xhmpih_exact // ; apply: generic_format_round.
          rewrite dh_val; lra.
        have e20: e2 = 0 by rewrite /e2 /d  round_generic //; ring.
        rewrite e20 Rplus_0_r.
        clear -upos h37; nra.
      apply :(Rle_trans _ _  _  (Rabs_triang _ _)).
      suff:Rabs e1 <= /2*(u *u) by lra.
      have->:  /2*(u *u) = /2 * pow (-p) * pow (-p) by rewrite /u; ring.
      apply:error_le_half_ulp'=>//.
      case:(Rle_lt_dec (Rabs (xl - pil)) (pow (- p)))=>//.
      move/Rlt_le/rnd_p_le; rewrite round_generic /u.
        rewrite ZNE round_NE_abs -ZNE -/dl.
        move / Rabs_ge_inv; rewrite -/u; clear - upos dlu hdl_b ; nra.
      by apply:generic_format_bpow; rewrite /fexp; lia.
    case:  dh_val => dh_val.
      have->: e2 = 0.
        rewrite /e2 /d dh_val Rplus_0_l round_generic /dl; first ring.
        by apply:generic_format_round.
      by rewrite Rplus_0_r; clear - h37 upos; nra.
    have pilE:pil = th*y - pih by rewrite pihlE; ring.
    have:  -2*u <= dl <=  u - 4*(u *u).
      rewrite /dl.
      have:  4 * ( u * u) <= pil.
        have->:pil = th*y - pih by rewrite pihlE; ring.
        have->:   th * y - pih  = (th*y -xh) + (xh - pih) by ring.
        by move: dh_val; rewrite /dh; move/Rabs_le_inv:  h35; lra.
      have: pil <= u.
        by move/Rabs_le_inv:   h37a; lra.
      move/Rabs_le_inv: xlu => *.
      have hxlpil: -(2*u) <=  xl -pil <= u -4* (u * u) by lra.
      case:(hxlpil) =>/rnd_p_le; rewrite round_generic; first last.
        apply:generic_format_opp.
        have ->: 2 * u = pow (1 -p) by rewrite /u bpow_plus .
        by apply:generic_format_bpow;rewrite /fexp; lia. 
      move=>aux1 /rnd_p_le;rewrite (round_generic _ _ _ (u - 4* (u *u))); first last.
        have->: (u - 4 * (u * u)) = (1 -4*u)*u by ring.
        rewrite /u; apply: formatS =>//.
        have->: (1 - 4 * pow (- p))= (pow p - 4)* pow (-p).
          by rewrite Rmult_minus_distr_r -bpow_plus; ring_simplify(p + -p)%Z ; 
             rewrite /=; ring.
        apply:formatS=>//.
        have He: (pow p - 4) =  F2R (Float two (2 ^ p  -4 )%Z (0)).
          rewrite /F2R /= plus_IZR /u (IZR_Zpower two) /=;last lia; ring.
        apply:(FLX_format_Rabs_Fnum p  He).
        rewrite /= minus_IZR (IZR_Zpower two);  last lia.
        rewrite Rabs_pos_eq; first lra.
        suff : 4 <= pow p by lra.
        have ->: 4 = pow 2 by [].
        by apply: bpow_le ; lia.
      by lra.
    move=> hdl_b.
    case: (Rle_lt_dec dl (-u))=> dlu.
      have Fdhl: format (dh + dl).
        have ->: dh + dl = dh - (-dl) by ring.
        apply:sterbenz'=>//.
        + by rewrite /dh  /pih -xhmpih_exact //; 
             apply: generic_format_round; apply:generic_format_round.
        + by rewrite /dl; apply/generic_format_opp; apply:generic_format_round.
        rewrite dh_val; clear - dlu hdl_b upos; lra.
      have e20: e2 = 0 by rewrite /e2 /d  round_generic //; ring.
      by rewrite e20 Rplus_0_r; clear -upos h37; nra.
    apply :(Rle_trans _ _  _  (Rabs_triang _ _)).
    suff:Rabs e1 <= /2*(u *u) by lra.
    have->:  /2*(u *u) = /2 * pow (-p) * pow (-p) by rewrite /u; ring.
    apply:error_le_half_ulp'=>//.  
    case:(Rle_lt_dec (Rabs (xl - pil)) (pow (- p)))=>//.
    move/Rlt_le/rnd_p_le; rewrite round_generic /u.
      rewrite ZNE round_NE_abs -ZNE -/dl.
      move / Rabs_ge_inv; rewrite -/u; clear - upos dlu hdl_b ; nra.
    by apply:generic_format_bpow; rewrite /fexp; lia.
(* cas: Rabs (e1 + e2) <= 5 / 2 * (u * u) *)
  have h32:   th * y - pih  = (th*y -xh) + (xh - pih) by ring.
  have h40: d/y = x/y -th + e/y.
    apply: (Rmult_eq_reg_r y); last lra.
    rewrite /x /e /e1 /e2 /d /dh. 
    by field_simplify; try lra; rewrite (Rmult_comm y) pihlE.
  have h41a: Rabs (d/y) < 2*u.
    apply:(Rle_lt_trans _ ((4*u + 5*(u*u))/(2 + 4*u))); last first.
      apply:(Rmult_lt_reg_r (2 + 4 * u)); try lra.
      rewrite /Rdiv Rmult_assoc Rinv_l; last lra.
      clear - upos; nra.
    have->:  (4 * u + 5 * (u * u)) / (2 + 4 * u) = u + (u * u)/(2*(1 + 2*u)) + u/(1 + 2*u).
      field; lra.
    apply:(Rle_trans _  (u + (u * u)/(2*y)  + u/y)); last first.
      apply:Rplus_le_compat.
        apply:Rplus_le_compat_l.
        clear -upos y2 y1.
        rewrite /Rdiv ; apply:Rmult_le_compat_l; first nra.
        apply:Rinv_le; lra.
      rewrite /Rdiv ; apply:Rmult_le_compat_l; first lra.
      apply:Rinv_le; lra.
    rewrite h40; apply:(Rle_trans _ _  _  (Rabs_triang _ _)).
    apply:(Rle_trans _ ((u - (2* (u*u))/y + u/y )+  (5 / 2 * (u * u))/y)).
      apply:Rplus_le_compat.
        have->: x / y - th = xh/y - th + xl/y by rewrite /x; field.
        apply:(Rle_trans _ _  _  (Rabs_triang _ _)).
        apply:Rplus_le_compat.
          have->:xh / y - th = - (th - xh/y) by ring.
          rewrite Rabs_Ropp; clear -h34 ; nra.
        rewrite /Rdiv Rabs_mult (Rabs_pos_eq (/y)).
          apply:Rmult_le_compat_r=>//.
          apply/Rlt_le/Rinv_0_lt_compat; lra.
        apply/Rlt_le/Rinv_0_lt_compat; lra.
     rewrite /Rdiv /e  Rabs_mult (Rabs_pos_eq (/y)).
        apply:Rmult_le_compat_r=>//.
        apply/Rlt_le/Rinv_0_lt_compat; lra.
      apply/Rlt_le/Rinv_0_lt_compat; lra.
    field_simplify; lra.
  move/Rlt_le/rnd_p_le:  (h41a) .
  rewrite (round_generic _ _ _ (2*u)) //; last first.
    have-> : 2*u = pow (1 -p) by rewrite /u bpow_plus.
    apply:generic_format_bpow; rewrite /fexp; lia.
  move=> tlu.
  have e3ub: Rabs e3 <= u*u.
    rewrite /e3 /tl.
    have->:  u * u = /2 * pow (-p) * pow (1 -p).
      rewrite bpow_plus -/u /= IZR_Zpower_pos /= ;  field.
    apply:error_le_half_ulp'=>//.
    rewrite bpow_plus /= IZR_Zpower_pos /=  -/u; lra.
  rewrite h39g -/x.
  have:  Rabs ((th + tl - x / y)) <= 5/2* (u*u)/y + u*u.
    rewrite   thtlE; ring_simplify(x / y + e / y + e3 - x / y).
    apply:(Rle_trans _ _  _  (Rabs_triang _ _));apply: Rplus_le_compat; try lra.
    rewrite /Rdiv Rabs_mult (Rabs_pos_eq (/y)) /e; last lra.
    apply:Rmult_le_compat_r; lra.
  move=>haux.
  have xy0: 0 < x/y.
    apply: Rmult_lt_0_compat; lra.
  set xy := x/y.
  rewrite {1}/Rdiv Rabs_mult  (Rabs_pos_eq (/xy)); last first.
    rewrite /xy; apply/Rlt_le/Rinv_0_lt_compat; lra.
  have->: /xy = y/x by rewrite /xy; field; lra.
  apply:(Rmult_le_reg_r (x /y))=>//.
  rewrite Rmult_assoc.
  have->: (y / x) * (x / y) = 1 by field; lra.
  rewrite /xy Rmult_1_r.
  apply:(Rle_trans _ (5 / 2 * (u * u) / y + u * u))=>//.
  apply:(Rle_trans _ (7 / 2 * (u * u))).
    have->:  7 / 2 * (u * u) = 5/2 * (u * u) + u * u by field.
    apply:Rplus_le_compat_r.
    apply:(Rmult_le_reg_r y); try lra.
    rewrite /Rdiv Rmult_assoc Rinv_l ?Rmult_1_r; try lra.
    clear -upos y1.
    rewrite -[X in X <= _]Rmult_1_r.
    apply:Rmult_le_compat_l.
      nra.
    lra.
  clear -upos y1 hxy ypos.
  rewrite -[X in X <= _]Rmult_1_r.
  apply:Rmult_le_compat_l.
    nra.
  apply: (Rmult_le_reg_r y)=>//.
  rewrite /Rdiv Rmult_assoc Rinv_l;  lra.
(* x < y*)
have xhley:xh <= y.
  move/Rlt_le/rnd_p_le:(hxy).
  by rewrite /x -xE round_generic.
have thle1: th <= 1.
  rewrite /th -[X in _ <= X](round_generic two fexp (Znearest choice)).
    apply:round_le.
    clear - xh1 ypos xhley.
    apply:(Rmult_le_reg_r y); try lra.
    rewrite /Rdiv Rmult_assoc Rinv_l ?Rmult_1_l ?Rmult_1_r; lra.
  have ->: 1 = pow 0 by [].
  apply:generic_format_bpow; rewrite /fexp; lia.
case:  xhley => xhy; last first.
  have th1: th = 1.
    rewrite /th xhy /Rdiv Rinv_r ?round_generic //.
    have ->: 1 = pow 0 by [].
    apply:generic_format_bpow; rewrite /fexp; lia.
  have pihE: pih = xh by rewrite /pih th1 Rmult_1_l -xhy round_generic.
  have pil0: pil = 0.
    rewrite /pil pihE th1 xhy.
    by ring_simplify(1*y -y);rewrite round_0.
  have dxl: d = xl.
    rewrite /d /dh /dl pihE pil0 ? Rminus_0_r !round_generic //;  first ring.
    by ring_simplify (xh - xh + xl).
  pose eta := rnd_p (xl / y) - xl/y.
  have: zh + zl = x/y + eta.
    rewrite   h39g th1 /x Rdiv_plus_distr /tl dxl.
    have ->: xh/y = 1 by rewrite xhy; field.
    rewrite /eta; ring.
  have eta_ub: Rabs eta <= (u * u) * x/y.
    apply:(Rle_trans _ (u * (Rabs xl)/y)).
      rewrite /eta.
      suff ->:  u * Rabs xl / y =  / 2 * bpow two (- p + 1) * Rabs (xl/y).
        apply:relative_error_N_FLX ; lia.
      rewrite bpow_plus -/u /Rdiv Rabs_mult ?(Rabs_pos_eq (/y)); try lra.
      rewrite /= IZR_Zpower_pos /=; field; lra.
    have : Rabs xl <= u * x.
      suff->:  u * x = / 2 * pow (- p + 1) * Rabs x.
        have->:  xl = -(rnd_p (xh + xl ) - (xh + xl)) by rewrite -xE;ring.
        rewrite Rabs_Ropp /x.
        apply:relative_error_N_FLX; lia.
      rewrite Rabs_pos_eq //; last lra.
      rewrite bpow_plus -/u /= IZR_Zpower_pos /=; field.
    clear - upos ypos   yinvpos xpos.
    move/(Rmult_le_compat_r (u/y)); nra.
  move->.
  rewrite /x.
  have->: (xh + xl) / y + eta - (xh + xl) / y = eta by field.
  rewrite -/x /Rdiv Rabs_mult.
  have ->: / (x * / y) = y/x .
    field; split; lra.
  apply:(Rle_trans _ (( u * u * x / y)* Rabs (y / x))).
    apply:Rmult_le_compat_r=>//.
    by apply:Rabs_pos.
  have yx1: 1 < y/x.
    clear - xpos hxy.
    apply:(Rmult_lt_reg_r x)=>//.
    field_simplify; lra.
  rewrite Rabs_pos_eq; last lra.
  rewrite !Rmult_assoc.
  field_simplify.
    clear -upos ; nra.
  split; lra.
(* x < y *)
have xhyu: xh <= y - 2*u.
  move/(@succ_le_lt two fexp _ xh y Fxh Fy) :   xhy.
  rewrite succ_eq_pos   ?ulpxh; lra.
have: xh/y < 1-u/2.
  apply:(Rle_lt_trans _ (1- u/(2 -2*u))); last first.
    apply:(Rmult_lt_reg_r (2 - 2 * u)).
      suff : u < 1 by lra.
      rewrite /u ; have -> : 1 = pow 0 by [].
      apply:bpow_lt; lia.
    have->: (1 - u / (2 - 2 * u)) * (2 - 2 * u) = 2 - 2*u -u.
      field; lra.
    field_simplify.
    suff : 0 <  u ^ 2 by lra.
    clear -upos; nra.
  apply:(Rle_trans _ ( 1 - u/y)).
    apply:(Rmult_le_reg_r y); try lra.
    rewrite /Rdiv Rmult_minus_distr_r !Rmult_assoc Rinv_l; lra.
  clear - y2 y1 upos .
  suff :  /(2 - 2*u) <= /y by nra.
  apply:Rinv_le; lra.
move=> xhylt.
have: rnd_p (xh/y) <= 1-u.
  apply: round_N_le_midp.
    have xhE : 1 -  u = F2R (Float two (2 ^ p  -1 )%Z (-p)).
      rewrite /F2R /= plus_IZR /u (IZR_Zpower two) /=;last lia.  
      rewrite Rmult_plus_distr_r -bpow_plus.
      have ->: (p + -p = 0)%Z by ring.
       rewrite /=; ring.
    apply:(FLX_format_Rabs_Fnum p xhE).
    rewrite /= plus_IZR (IZR_Zpower two) ; last lia.
    rewrite opp_IZR Rabs_pos_eq; try  lra.
    suff : 1 <= pow p by lra.
    have ->: 1 = pow 0 by [].
    apply:bpow_le; lia.
  have u1: 0 <= 1 -u.
    suff : u <= 1 by lra.
    have ->: 1 = pow 0 by [].
    rewrite /u; apply:bpow_le; lia.
  rewrite succ_eq_pos //.
  have -> :  ulp radix2 fexp (1 - u) = u.
    rewrite ulp_neq_0 /cexp /fexp.
      rewrite (mag_unique_pos two (1-u)  0).
        rewrite bpow_plus /= /u; ring.
      rewrite /= IZR_Zpower_pos /=.
      split;  lra.
    lra.
  lra.
rewrite -/th => th1mu.
have haux: Rabs(th - xh/y) <= u/2 - /y* (u*u).
  by rewrite /th; apply:  l6_1_2=>//; lra.
have: Rabs( th*y - xh) <= u -2*(u*u).
  have->: th*y -xh = (th - xh/y)*y by field; lra.
  rewrite Rabs_mult (Rabs_pos_eq y) ;last lra.
  apply:(Rle_trans _ (u / 2 * y - u*u)).
    have->:  u / 2 * y - u * u = (u / 2 - / y * (u * u)) * y  by field; lra.

    apply:Rmult_le_compat_r; lra.
  have : y <= 2 * (1 -u) by lra.
  by move/(Rmult_le_compat_l (u/2)); lra.
move/Rabs_le_inv=> haux'.
have : xh -u + 2*(u*u) <= th*y <= xh + u - 2* (u*u) by lra.
have u2pos: 0 < u * u by clear -upos; nra.
move=> haux2.
have haux3: xh -u < th*y < xh + u by lra .
have:rnd_p (th * y) <= xh.
  apply:round_N_le_midp=>//.
  rewrite succ_eq_pos.
    rewrite ulpxh; lra.
  lra.
move=> haux4.
have: Rabs e <= 3/2*(u*u).
  case: xh1=> xh1.
  have xh1': 1 + 2*u <= xh.
    suff ->: 1 + 2*u = succ two  fexp  1.
      apply: succ_le_lt=> //.
      have ->: 1 = pow 0 by [].
      by apply:generic_format_bpow; rewrite /fexp ; lia.
    rewrite succ_eq_pos; try lra.
    by apply:Rplus_eq_compat_l; rewrite /u u_ulp1 ; field.
  have : xh <= rnd_p (th*y).
    apply:round_N_ge_midp=>//.
    rewrite notpow_pred=>//.
      rewrite ulpxh; lra.
    case:(is_pow_dec two  (xh ))=>// hpow.
    case:hpow=> exh.
    rewrite Rabs_pos_eq; last lra.
    move=> xe.
    move:xh1.
    have : xh < 2 by lra.
    rewrite xe.
    have->: 1 = pow 0 by [].
    have ->: 2 = pow 1 by [].
    move/lt_bpow=>exh1.
    move/lt_bpow; lia.
  move=> haux5.
    have pihE: pih = xh by rewrite /pih; lra.
    rewrite /e /e2 /d /dh /dl.
    rewrite pihE (Rminus_diag_eq xh) // ?Rplus_0_l round_round; last lia.
    rewrite Rminus_diag_eq  // Rplus_0_r; lra.
    have: rnd_p (1 - u) <= rnd_p (th * y).
    apply: round_le; rewrite xh1; lra.
  have Fomu: format (1-u).
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
  rewrite round_generic //.
  case.
    have Fpih: format (rnd_p (th * y)) by apply:generic_format_round.
    move/(@succ_le_lt two fexp _ _ _ Fomu Fpih).
    rewrite succ_eq_pos; last lra.
  have -> :  ulp radix2 fexp (1 - u) = u.
    rewrite ulp_neq_0 /cexp /fexp.
      rewrite (mag_unique_pos two (1-u)  0).
        rewrite bpow_plus /= /u; ring.
      rewrite /= IZR_Zpower_pos /=.
      split;  lra.
    lra.
    move=> *.
    have pih1: rnd_p (th * y) = 1 by lra.
    rewrite /e  /e2 /d /dh /dl /pih pih1 -xh1 (Rminus_diag_eq 1) // ?Rplus_0_l round_round; 
     last lia.
    rewrite Rminus_diag_eq // Rplus_0_r; lra.
  move=> pihlb.
  have : th*y <1.
    case:(Rlt_le_dec (th*y) 1) => // thy1.
    move/rnd_p_le:  thy1.
    rewrite round_generic; try lra.
    have->: 1 = pow 0 by [].
    apply:generic_format_bpow; rewrite /fexp; lia.
  move=> thy1.
  have pilub: Rabs pil <= u/2.
    have->: pil = -(pih -  th*y) by rewrite pihlE; ring.
    rewrite /pih Rabs_Ropp.
    have->: u / 2 =  / 2 * pow (- p) * pow 0.
      rewrite /u /=; field. 
    apply:error_le_half_ulp'; try lia; rewrite /= Rabs_pos_eq;  lra.
  have pillb: 2 * (u * u) <= pil.
    have->: pil = (th*y -xh) + (xh -pih) by rewrite   pihlE; ring.
    have ->:  2 * (u * u) = (- u + 2*(u*u)) + u by ring.
    apply:Rplus_le_compat; try lra.
    rewrite /pih  -pihlb; lra.
  have xllb: -u/2 <= xl.
    case: (Rle_lt_dec  (-u/2) xl)=>//.
    move/(Rplus_lt_compat_l xh)=> haux0.
    have: rnd_p (xh + xl) <= 1 - u.
      apply: round_N_le_midp=>//.
      rewrite succ_eq_pos.
        have -> :  ulp radix2 fexp (1 - u) = u.
          rewrite ulp_neq_0 /cexp /fexp.
            rewrite (mag_unique_pos two (1-u)  0).
              rewrite bpow_plus /= /u; ring.
            rewrite /= IZR_Zpower_pos /=.
            split;  lra.
          lra.
        lra.
      lra.
    rewrite -xE; lra.
  have [haux5 haux5']: -u <= xl - pil <= u -2*(u *u).
    move/Rabs_le_inv :  pilub=> haux1; split; try lra.
    move/Rabs_le_inv: xlu; lra.
  move/rnd_p_le :  (haux5'); move/rnd_p_le : (haux5).
  rewrite -/dl !round_generic; first last.
  + apply/generic_format_opp; rewrite /u; apply/generic_format_bpow; rewrite /fexp; lia.
  + have->:  (u - 2 * (u * u)) = (1 - 2*u)*(pow (-p)) by rewrite -/u ; ring.
    apply:formatS=>//.
    by rewrite xh1.
  move=> haux6 haux6'.
  have e1ub: Rabs e1 <= /2* (u*u).
    rewrite /e1 /dl.
    have->: /2*( u * u) = / 2 * pow (- p) * pow ( - p) by rewrite /u; ring.
    apply:error_le_half_ulp'; first lia.
    apply:Rabs_le.
    rewrite -/u; lra.
  have haux7: 0 <= dl + dh <= 2*u -2* (u*u).
    have ->: dh = u by rewrite /dh /pih -pihlb -xh1; ring.
    lra.
  have e2ub: Rabs e2 <= u * u.
    rewrite /e2/d.
    have->: u * u = /2 * pow (-p) * pow (1 -p).
      rewrite /u bpow_plus.
      have ->: pow 1 = 2 by [].
      field.
    apply:error_le_half_ulp'; first lia.
    rewrite bpow_plus; have ->: pow 1 = 2 by [].
    rewrite Rabs_pos_eq -/u;  lra.
  rewrite /e; apply:(Rle_trans _ _  _  (Rabs_triang _ _)); lra.
move=> h42b.
have: Rabs (d/y) < 2 *u.
  rewrite dE /x /Rdiv 4!Rmult_plus_distr_r.
  have->: (xh * / y + xl * / y + - (th * y) * / y + (e1 * / y + e2 * / y)) = 
          ((xh/y -th) + (xl/y)) + (e/y).
    rewrite /e; field; lra.
  apply:(Rle_lt_trans _ (Rabs (xh/y - th) + Rabs (xl/y) + Rabs (e/y))).
    apply/(Rle_trans _ _  _  (Rabs_triang _ _)).
    apply/Rplus_le_compat_r.
    by apply/(Rle_trans _ _  _  (Rabs_triang _ _)); apply/Rplus_le_compat_r; lra.
  have->: xh / y - th = - (th - xh/y) by ring.
  rewrite Rabs_Ropp.
  have xlyub:Rabs (xl / y) <= u/y.
    rewrite Rabs_mult (Rabs_pos_eq (/y)); try lra.
    rewrite /Rdiv; apply:Rmult_le_compat_r; lra.
  have eyub: Rabs (e / y) <= 3/2*(u*u)/y.
    rewrite Rabs_mult (Rabs_pos_eq (/y)); try lra.
     rewrite /Rdiv; apply:Rmult_le_compat_r; lra.
  apply:(Rle_lt_trans _  (u / 2 - / y * (u * u) + u / y + 3 / 2 * (u * u) / y)); try lra.
  have->: u / 2 - / y * (u * u) + u / y + 3 / 2 * (u * u) / y  = 
          u/2 + /2 * (u * u) / y + u/y by field.
  apply: (Rmult_lt_reg_r (2 *y /u)); try lra. 
    clear - upos y1.
    apply:(Rmult_lt_reg_r u) =>//.
    rewrite /Rdiv Rmult_assoc Rinv_l; lra.
  field_simplify; try lra.
  have->: (u ^ 2 + u * y + 2 * u) / u = u + y + 2 .
    field; try lra.
  lra.
move=> dy2u.
have tl2u: Rabs tl <= 2*u.
  rewrite /tl ZNE -round_NE_abs -ZNE.
  move/Rlt_le/rnd_p_le: dy2u.
  suff ->: rnd_p (2 * u) = 2 *u by [].
  rewrite round_generic //.
  have -> : 2 * u = pow (1- p)%Z.
    by rewrite bpow_plus /= IZR_Zpower_pos /u.
  apply : generic_format_bpow; rewrite /fexp; lia.
have e3ub: Rabs e3 <= u*u.
  rewrite /e3 /tl.
  have->: u*u=  / 2 * pow (- p) * pow (1 -p).
    rewrite /u bpow_plus /= IZR_Zpower_pos /=; field.
  apply:error_le_half_ulp'; first lia.
   rewrite  bpow_plus /= IZR_Zpower_pos /= -/u -/tl ; lra.
have: Rabs (zh + zl - x/y) <= 3/2*(u*u)/y + u*u.
  rewrite  h39g thtlE /x.
  ring_simplify((xh + xl) / y + e / y + e3 - (xh + xl) / y).
  apply/(Rle_trans _ _  _  (Rabs_triang _ _)); apply/Rplus_le_compat =>//.
  rewrite Rabs_mult (Rabs_pos_eq (/y)); last lra.
  apply:Rmult_le_compat_r; lra.
move=> haux0.
rewrite -/x.
have xy0: 0 < x/y by apply: Rmult_lt_0_compat; lra.
set xy := x/y.
rewrite {1}/Rdiv Rabs_mult  (Rabs_pos_eq (/xy)); last first.
  rewrite /xy; apply/Rlt_le/Rinv_0_lt_compat; lra.
have->: /xy = y/x by rewrite /xy; field; lra.
apply:(Rle_trans _  ((3 / 2 * (u * u) / y + u * u) * (y / x))).
  apply:Rmult_le_compat_r.
    apply/Rlt_le/ Rmult_lt_0_compat; try lra.
    apply:Rinv_0_lt_compat;lra.
  by rewrite /xy .
have->: (3 / 2 * (u * u) / y + u * u) * (y / x) = 3 / 2 * (u * u) / x + u * u * (y / x).
  field; split; lra.
have : 1 - u/2 <= x.
  rewrite /x.
  case:(Rle_lt_dec (1 - u / 2) (xh + xl))=>// hh.
  have: rnd_p (xh + xl ) <= (1- u).
    apply:round_N_le_midp.
      have xhE : 1 -  u = F2R (Float two (2 ^ p  -1 )%Z (-p)).
        rewrite /F2R /= plus_IZR /u (IZR_Zpower two) /=;last lia.  
        rewrite Rmult_plus_distr_r -bpow_plus.
        have ->: (p + -p = 0)%Z by ring.
        rewrite /=; ring.
      apply:(FLX_format_Rabs_Fnum p xhE).
      rewrite /= plus_IZR (IZR_Zpower two) ; last lia.
      rewrite opp_IZR Rabs_pos_eq; try  lra.
      suff : 1 <= pow p by lra.
      have ->: 1 = pow 0 by [].
      apply:bpow_le; lia.
    have u1: 0 <= 1 -u.
      suff : u <= 1 by lra.
      have ->: 1 = pow 0 by [].
      rewrite /u; apply:bpow_le; lia.
    rewrite succ_eq_pos //.
    have -> :  ulp radix2 fexp (1 - u) = u.
      rewrite ulp_neq_0 /cexp /fexp.
        rewrite (mag_unique_pos two (1-u)  0).
          rewrite bpow_plus /= /u; ring.
        rewrite /= IZR_Zpower_pos /=.
        split;  lra.
      lra.
    lra.
  rewrite -xE; lra.
move=> h0.
apply: (Rmult_le_reg_r (2 * x)); first lra.
have->:  (3 / 2 * (u * u) / x + u * u * (y / x)) * (2 * x) = 
         (3  + 2* y) * (u * u) by field; lra.
have->:  7 / 2 * (u * u) * (2 * x)=  7 * x *  (u * u)  by field.
by apply:Rmult_le_compat_r;lra.
Qed.
End Algo14.

Section Algo15.

(* Notation F2S_err a b := (F2Sum_err p choice a b). *)
Notation Fast2Sum := (Fast2Sum   p choice).
Notation Fast2Mult := (Fast2Mult p choice).
Notation F2P_prod a b  :=  (fst (Fast2Mult a b)).
Notation F2P_error a b  :=  (snd (Fast2Mult a b)).


Hypothesis Fast2Mult_correct: 
  forall a b, a * b =  F2P_prod a b +  F2P_error a b.

Notation F2P_errorE := (F2P_errorE Fast2Mult_correct).


Hypothesis TwoProdE : TwoProd = Fast2Mult. (* or Dekker's algorithm *)



Definition DWDivFP3 (xh xl y :R) :=
let th := rnd_p (xh/y) in
let (pih, pil ) := (TwoProd th y) in
let dh :=  xh  - pih in
let dt:= dh - pil in 
let d := rnd_p (dt + xl) in
let tl := rnd_p (d/y) in (Fast2Sum th tl).

Notation double_word xh xl := (double_word  p choice xh xl).


Fact  DWDivFP3_Asym_r xh xl y (yn0: y <> 0):  
  (DWDivFP3 xh xl (-y)) = pair_opp   (DWDivFP3 xh xl y).
Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
 rewrite /DWDivFP3 TwoProdE /=.
set th := rnd_p (xh/y).
have ->: rnd_p (xh / - y)  = - th.
  have ->: xh / - y = - (xh /y) by field.
  by rewrite ZNE round_NE_opp -ZNE /th.
have ->: - th * - y = th * y by ring.
set pih := rnd_p (th * y); set pil := rnd_p (th * y - pih); set dh := xh -pih.
set dt :=  dh - pil; set d := rnd_p (dt + xl).
have ->: d / - y = - (d/y) by field.
by rewrite ZNE round_NE_opp -ZNE Fast2Sum_asym.
Qed.

Fact  DWDivFP3_Asym_l xh xl y  (yn0: y <> 0): 
  (DWDivFP3 (-xh) (-xl)  y) = pair_opp (DWDivFP3 xh xl y).
Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
rewrite /DWDivFP3 TwoProdE /=.
set th := rnd_p (xh/y).
have ->: rnd_p ((-xh) /  y)  = - th.
  have ->: -xh / y = - (xh /y) by field.
  by rewrite ZNE round_NE_opp -ZNE /th.
have ->: - th * y = -(th * y) by ring.
rewrite ZNE round_NE_opp -ZNE.
set pih := rnd_p (th * y).
have->: (- (th * y) - - pih) = - ((th * y) - pih) by ring.
rewrite ZNE round_NE_opp -ZNE.
set pil := rnd_p (th * y - pih).
have->: (- xh - - pih - -pil + - xl) = - (xh - pih -pil + xl) by ring.
rewrite ZNE round_NE_opp -ZNE Ropp_div.
by rewrite ZNE round_NE_opp -ZNE  Fast2Sum_asym.
Qed.


Fact  DWDivFP3Sy xh xl y e (yn0: y <> 0):
  (DWDivFP3 xh xl   (y* pow e)) =  
     map_pair (fun x =>  x/ (pow e))  (DWDivFP3 xh xl y).
Proof.
rewrite /DWDivFP3 TwoProdE /=.
set th := rnd_p (xh/y).
have ->: rnd_p ((xh) /  ( y * pow e))  = th/ (pow e).
  have ->: xh / (y* pow e) = (xh /y) / (pow e).
    field; split=>//; move:(bpow_gt_0 two e); lra.
  have-> : xh / y / pow e = (xh/y) * (pow (-e)).
    apply: (Rmult_eq_reg_r (pow e)); last by move:(bpow_gt_0 two e); lra.
    rewrite Rmult_assoc -bpow_plus; ring_simplify (-e + e)%Z; rewrite /= Rmult_1_r; field; split=>//.
    by move:(bpow_gt_0 two e); lra.
  by rewrite round_bpow /th bpow_opp.
have->: (th / pow e * (y * pow e)) = th * y.
  field; move:(bpow_gt_0 two e); lra.
set pih := rnd_p (th * y).
set pil := rnd_p (th * y - pih).
set dh := xh -pih; set dt :=  dh - pil.
set d := rnd_p (dt + xl).
have->: d / (y * pow e) = (d/y) * (pow (-e)).
  rewrite bpow_opp; field; split =>//; move:(bpow_gt_0 two e); lra.
rewrite round_bpow.
rewrite /Rdiv -bpow_opp Fast2SumS //; apply:generic_format_round.
Qed.

Fact  DWDivFP3Sx xh xl y  e (yn0: y <> 0):
  (DWDivFP3 (xh* pow e) (xl* pow e) y) =
     map_pair (fun x =>  x* (pow e))  (DWDivFP3 xh xl y).
Proof.
rewrite /DWDivFP3 TwoProdE /=.
set th := rnd_p (xh/y).
have ->: rnd_p ((xh * pow e) / y )  = th* (pow e).
  have ->: xh * pow e / y  = (xh /y) *(pow e).
    by field.
  by rewrite /th round_bpow.
have->: (th  * pow e * y ) = th * y * pow e by ring.
rewrite round_bpow.
set pih := rnd_p (th * y).
have->: th * y * pow e - pih * pow e = (th * y - pih)* pow e by ring.
rewrite round_bpow.
set pil := rnd_p (th * y - pih).
have ->: (xh * pow e - pih * pow e - pil * pow e + xl * pow e) = 
(xh - pih -pil +xl)*pow e by ring.
rewrite round_bpow.
set rr:= (rnd_p (_ + _)).
have ->: (rr * pow e / y) = (rr/y)*(pow e)  by field.
 by rewrite round_bpow Fast2SumS //= ; apply:generic_format_round.
Qed.


(* Theorem 6.2 *)

Lemma DWDFP3_correct xh xl y (DWx: double_word xh xl) (Fy : format y) (Hp4: (4 <= p)%Z)(yn0 : y <> 0):
  let (zh, zl) := DWDivFP3 xh xl y in
  let xy := ((xh + xl) / y)%R in
  Rabs ((zh + zl - xy) / xy) <= 3*(u * u).
Proof.
have rn_sym:= (rnd_p_sym p _ (choiceP ZNE)).
case:(DWx)=> [[Fxh Fxl]] xE.
case:(is_pow_dec two y).
  move=>[ e ye].
  rewrite /DWDivFP3   TwoProdE.
  have rq : forall x,  rnd_p (x / y) = (rnd_p x) /y.
    move=>x ; rewrite /Rdiv.
    have: Rabs (/y) = pow (-e) by rewrite Rabs_Rinv // ye bpow_opp.
    rewrite -(Rabs_pos_eq (pow (-e))); last by  apply: bpow_ge_0.
    case/Rabs_eq_Rabs=> ->.
      by rewrite round_bpow.
    have ->: x * - pow (- e) = - (x * pow (- e)) by ring.
    rewrite ZNE round_NE_opp -ZNE  round_bpow; ring.
  rewrite (rq xh).
  have->: rnd_p xh = xh by rewrite round_generic.
  (* rewrite TwoProdE /=. *)
 rewrite /Fast2Mult.
  have->:  xh / y * y  = xh by field.
  have->: rnd_p xh = xh by rewrite round_generic.
  have ->: xh -xh = 0 by ring.
  rewrite round_0 Rminus_0_r Rplus_0_l . 
  have->: rnd_p xl = xl by rewrite round_generic.
  rewrite (rq xl).
  have->: rnd_p xl = xl by rewrite round_generic.
  case:(Req_dec xl 0)=> xl0.
    rewrite xl0.
    have ->: 0 / y = 0 by field.
    have Fxhy : format (xh /y).
      suff ->: xh / y = rnd_p (xh/y) by apply:generic_format_round.
      by rewrite rq round_generic.
    rewrite Fast2Sumf0 //.
    rewrite !Rplus_0_r Rabs0.
      rewrite /u ; move: (bpow_ge_0 two (-p)); nra.
    by ring_simplify  (xh / y - xh / y); rewrite /Rdiv Rmult_0_l.
  rewrite (surjective_pairing (Fast2Sum  _ _))
                 F2Sum_correct_cexp //=.
  + have ->: (xh / y + xl / y) = (xh + xl) /y by field.
    rewrite rq -xE.
    have->: ((xh / y + ((xh + xl) / y - xh / y) - (xh + xl) / y)) = 0 by ring.
    rewrite {1}/Rdiv Rmult_0_l Rabs_R0.
    rewrite /u ; move: (bpow_ge_0 two (-p)); nra.
  + have->: xh = rnd_p xh by rewrite round_generic.
    by rewrite -rq; apply: generic_format_round.
  + have->: xl = rnd_p xl by rewrite round_generic.
    by rewrite -rq; apply: generic_format_round.
  rewrite /cexp.
  apply/monotone_exp/mag_le_abs.
  move/Rinv_neq_0_compat:(  yn0 ); nra.
  rewrite /Rdiv !Rabs_mult; apply/Rmult_le_compat_r.
    by apply/Rabs_pos.
  apply:(Rle_trans _  (/2 * ulp two fexp xh)).
    by apply: (dw_ulp Hp1 DWx).
  apply: (Rle_trans _  (ulp two fexp xh)).
    suff: (0 <= ulp radix2 fexp xh) by lra.
    by apply:ulp_ge_0.
  apply: ulp_le_abs=>// xh0.
  have: rnd_p (xh + xl ) <> 0.
    by rewrite xh0 Rplus_0_l round_generic.
  by rewrite -xE xh0.
case:(Req_dec xh 0)=> xh0.
  have xl0: xl = 0.
    by move:xE; rewrite  xh0 Rplus_0_l round_generic.
move=> ynpow.
case E1: DWDivFP3 => [zh zl].
move=> xy.
rewrite /xy; clear xy.
move : (E1); rewrite /DWDivFP3 TwoProdE /=.
  rewrite xh0 xl0 /Rdiv !(Rmult_0_l, round_0, Rplus_0_l,  Rminus_0_l, Ropp_0).
  case=> <- <-.
  rewrite !(Rplus_0_r, round_0, Rminus_0_r, Rmult_0_l) Rabs0 //.
  nra.
move=> ynpow.
case E1:DWDivFP3=>[zh zl].
move=> xy.
rewrite /xy {xy Fxh Fxl xE}.
wlog ypos: y xh xl zh zl DWx Fy  E1   yn0 xh0 ynpow  / 0 <= y.
  move=>Hwlog.
  case:(Rle_lt_dec 0 y) => yle0; first by apply:Hwlog.
  have ->: (zh + zl - (xh + xl) / y) / ((xh + xl) / y) = 
            ((- zh + - zl - (xh + xl) / (- y)) / ((xh + xl) /( - y))).
    field.
    split =>//.
    move=> xhxl0; apply: xh0.
    case:(DWx) => [[Fxh Fxl] xE].
    by rewrite xE   xhxl0 round_0.
  apply:Hwlog=>//; try nra; first last.
  + move=> *; apply: ynpow.
    have ->: y = - (- y) by ring.
    by apply:is_pow_opp.
  + by rewrite DWDivFP3_Asym_r // E1.
  by apply: generic_format_opp.
have {} ypos : 0 < y by lra.
wlog [y1 y2]: y  zh zl  Fy yn0 ynpow  ypos E1/ 1 <= y <= 2-2*u.
  move=>Hwlog.
  case: (scale_generic_12 Fy ypos)=> ey Hys.
  have ->: (zh + zl - (xh + xl) / y) / ((xh + xl) / y) = 
         (zh / pow ey  + zl / pow ey - (xh  + xl) /( y * pow ey)) / ((xh + xl ) /( y * pow ey)).
    field; split ; first by move:(bpow_gt_0 two ey); lra.
    split=> //.
    move=> xhxl0; apply xh0.
    case:(DWx) => [[Fxh Fxl] xE].
    by rewrite xE   xhxl0 round_0.
  apply:Hwlog; last by rewrite /u.
  + by apply:formatS.
  + move: (bpow_gt_0 two ey); nra.
  + move=> [e he]; apply: ynpow.
    exists (e -ey)%Z.
    rewrite bpow_plus.
    move: he; rewrite Rabs_mult !Rabs_pos_eq; move:(bpow_gt_0 two ey); try nra.
    move=>*.
    apply:(Rmult_eq_reg_r  (pow ey)).
      rewrite Rmult_assoc -bpow_plus.
      by ring_simplify (-ey + ey)%Z; rewrite /= Rmult_1_r.
    by move:(bpow_gt_0 two ey); lra.
  + by move:(bpow_gt_0 two ey); nra.
  by rewrite DWDivFP3Sy // E1.
wlog xpos:  xh xl zh zl DWx   E1 xh0   / 0 <= xh.
  move=>Hwlog.
  case:(Rle_lt_dec 0 xh) => xhle0; first by apply:Hwlog.
  have ->: (zh + zl - (xh + xl) / y) / ((xh + xl) / y) = 
            ((- zh + - zl - (-xh + -xl) / y) / ((-xh + -xl) /y)).
    field.
    split =>//.
    suff: xh + xl <> 0 by lra.
    move=> xhxl0; apply: xh0.
    case:(DWx) => [[Fxh Fxl] xE].
    by rewrite xE   xhxl0 round_0.
  apply:Hwlog=>//; try nra.
    case:(DWx) => [[Fxh Fxl] xE].
    split; [split|idtac].
    + by apply:generic_format_opp.
    + by apply:generic_format_opp.
    have->:  (- xh + - xl) = - (xh + xl) by ring.
    by rewrite ZNE round_NE_opp -ZNE -xE.
  by rewrite DWDivFP3_Asym_l // E1.
have {xpos} xhpos : 0 < xh by lra.
wlog [xh1 xh2]: xh xl  zh zl  DWx {xh0} xhpos E1/ 1 <= xh <= 2-2*u.
  move=>Hwlog.
  case:(DWx) => [[Fxh Fxl] xE].
  case: (scale_generic_12 Fxh xhpos)=> exh Hxhs.
  have xhxl0: xh + xl <> 0 by move=> xhxl0; apply: xh0; rewrite xE  xhxl0 round_0.
  have ->: (zh + zl - (xh + xl) / y) / ((xh + xl) / y) = 
         (zh * pow exh  + zl * pow exh - (xh* pow exh   + xl* pow exh) /( y )) / ((xh  * (pow exh) + xl * (pow exh)) /( y )).
    field; split;  first by lra.
    by split=>//;rewrite -Rmult_plus_distr_r;  move:(bpow_gt_0 two exh); nra.
  apply:Hwlog=>//.
  + split; first by split ; apply:formatS.
    by rewrite   -Rmult_plus_distr_r round_bpow [in LHS]xE.
  + by move:(bpow_gt_0 two exh); lra.
  by rewrite DWDivFP3Sx // E1.
case:(DWx)=> [[Fxh Fxl]] xE.

have yinvpos: 0 < /y by apply: Rinv_0_lt_compat.
have {} y1: 1 + 2*u <= y.
  case:y1=>y1.
    suff ->: 1 + 2*u = succ two  fexp  1.
      apply: succ_le_lt=> //.
      have ->: 1 = pow 0 by [].
      by apply:generic_format_bpow; rewrite /fexp ; lia.
    rewrite succ_eq_pos; try lra.
    by apply:Rplus_eq_compat_l; rewrite /u u_ulp1 ; field.
  suff: is_pow radix2 y by [].
  by exists 0%Z; rewrite -y1 Rabs_pos_eq //=;  lra.
have xlu: Rabs xl <= u.
  suff <-:  / 2 * ulp radix2 fexp xh = u by apply:  (dw_ulp Hp1 DWx).
rewrite ulp_neq_0; last lra.
rewrite /cexp /u /fexp.
rewrite (mag_unique two xh 1).
rewrite bpow_plus /= IZR_Zpower_pos /= ; field.
rewrite bpow_plus /=  IZR_Zpower_pos /= Rabs_pos_eq ?Rmult_1_r ?Rinv_r; try lra.
move:(upos p); rewrite -/u; lra.
pose x := xh + xl.

have xpos: 0 < x by rewrite /x; move/Rabs_le_inv: xlu;lra.

have h30: 1/(2 - 2*u) <= xh/y <= (2 - 2*u) / (1 + 2*u).
  clear -  yn0    ypos  y2   xhpos  xh1  xh2    y1 Hp1; move:(upos p); rewrite -/u=> upos.
  have ult1: u < 1 by rewrite /u; apply:bpow_lt_1; lia.
  rewrite /Rdiv; split; apply: Rmult_le_compat; try lra.
  + apply/Rlt_le/Rinv_0_lt_compat; lra.
  + apply/Rinv_le; lra.
  + apply/Rlt_le/Rinv_0_lt_compat; lra.
   apply/Rinv_le; lra.
have h30a: 1/2 + u/2 < 1/(2 - 2*u).
  clear -  yn0    ypos  y2   xhpos  xh1  xh2    y1 Hp1; move:(upos p); rewrite -/u=> upos.
  have ult1: u < 1 by rewrite /u; apply:bpow_lt_1; lia.
  have->: 1 / 2 + u / 2 = (1 + u) /2 by field.
  have->:  (2 - 2 * u) =  (1 - u) *2 by field.
  rewrite /Rdiv Rinv_mult_distr; try lra.
  rewrite Rmult_1_l; apply:Rmult_lt_compat_r; try lra.
  apply:(Rmult_lt_reg_r (1 - u)); try lra.
  rewrite Rinv_l; try lra.
  have u2pos: 0 < u * u by apply:Rmult_lt_0_compat; lra.
  nra.
move:(upos p); rewrite -/u=> upos.
have h30b: (2 - 2*u)/(1 + 2 *u) < 2 - 5 *u.
  apply: (Rmult_lt_reg_r (1 + 2 *u));  try lra.
  rewrite /Rdiv Rmult_assoc Rinv_l ?Rmult_1_r; try lra.
  suff : 10 * u * u < u by lra.
   suff: u < 1/10  by clear -upos; nra.
  apply:(Rle_lt_trans _ (1/16)); try lra.
  have ->: 1/16 = pow (-4).
    rewrite /= IZR_Zpower_pos /=; field.
  rewrite /u; apply:bpow_le; lia.
have: 1/2 + u/2 < xh /y < 2 - 5*u by lra.
pose th := rnd_p (xh/y). 
move=> [hl hu].
have Fdmsu : format (2 - 6 * u).
  have->: 2 - 6*u = (1 - 3* u) * 2 by ring.
  have ->: 2 = pow 1 by [].
  apply:formatS=>//.
  have xhE : 1 - 3 * u = F2R (Float two (2^p -3)%Z (-p)).
    rewrite /F2R /= minus_IZR /u (IZR_Zpower two); last lia.
    by rewrite Rmult_minus_distr_r -bpow_plus Z.add_opp_diag_r.
  apply:(FLX_format_Rabs_Fnum p xhE).
  rewrite /= minus_IZR  (IZR_Zpower two); last lia.
  rewrite Rabs_pos_eq; try lra.
  suff : 4 <= pow p by lra.
  have ->: 4 = pow 2 by [].
  apply:bpow_le; lia.
have dmsu : 0 < 2 - 6 * u.
  suff : 3*u < 2 by lra.
  suff : u < /2 by nra.
  rewrite /u; have ->: /2 = pow (-1) by [].
  apply: bpow_lt ; lia.
have Fdpu : format (1/2 + u).
  have xhE : 1/2 + u = F2R (Float two (2 ^ (p -1) + 1)%Z (-p)).
    rewrite /F2R /= plus_IZR /u (IZR_Zpower two);last lia.  
    rewrite Rmult_plus_distr_r -bpow_plus Rmult_1_l.
    ring_simplify(p - 1 + - p)%Z.
    by have->: pow (- (1)) = /2 by []; field.
  apply:(FLX_format_Rabs_Fnum p  xhE).
  rewrite /= plus_IZR (IZR_Zpower two); last lia.
  rewrite Rabs_pos_eq; last first.
    by move:(bpow_ge_0 two (p -1)); lra.
  rewrite bpow_plus /= IZR_Zpower_pos  /=.
  suff : 2 <  pow p by lra.
  have ->: 2 = pow 1 by [].
  apply:bpow_lt; lia.
have h31b:1/2 + u <= rnd_p (xh/y).
  apply:round_N_ge_midp=>//.
  rewrite notpow_pred //; try lia.
    rewrite ulp_neq_0 /cexp /fexp ; last lra.
    rewrite (mag_unique two _ 0); last first.
      have ->:  (0 - 1)%Z = (-1)%Z by ring.
      have ->: pow (-1) = /2 by [].
      rewrite Rabs_pos_eq; last first.
        rewrite /u; move:(bpow_ge_0 two (-p)); lra.
      split; first lra.
      rewrite /=.
      suff: u < /2 by lra.
      rewrite /u; have ->: /2 = pow (-1) by [].
      apply:bpow_lt; lia.
    ring_simplify (0 -p)%Z.
    move:hl; rewrite /u; lra.
  case:(is_pow_dec two  (1 / 2 + u))=>// hpow.
  case:hpow=> e.
  rewrite Rabs_pos_eq.
    move=> xe.
    have : 1/2 < 1/2 + u by lra.
    have: 1/2 + u < 1 .
      suff: u < /2 by lra.
      rewrite /u ; have ->: /2 = pow (-1) by [].
      apply bpow_lt ; lia.
    rewrite xe.
    have {1}-> : 1 = pow 0 by [].
    move/lt_bpow=> e0.
    rewrite /Rdiv.
    have ->: /2 = pow (-1) by [].
    rewrite Rmult_1_l.
    move/lt_bpow=> e1.
    lia.
  rewrite /u; move:(bpow_ge_0 two (-p)); lra.
have h31a: rnd_p (xh/y) <= 2 - 6 * u.
  apply:round_N_le_midp=>//.
  rewrite succ_eq_pos; last lra.
  rewrite ulp_neq_0 /cexp /fexp ; last lra.
  rewrite (mag_unique two _ 1); last first.
    rewrite /= IZR_Zpower_pos /=  !Rmult_1_r Rabs_pos_eq; try lra.
    split; last  by  lra.
    suff: u <= /8 by lra.
    have ->: /8 = pow (-3) by [].
    rewrite /u ; apply:bpow_le; lia.
  ring_simplify (2 - 6 * u + (2 - 6 * u + pow (1 - p))).
  rewrite bpow_plus /= IZR_Zpower_pos /= -/u.
  lra.
move:(E1).
rewrite /DWDivFP3 TwoProdE /= -/th.
set  pih := rnd_p (th * y).
set pil := rnd_p(th *y - pih).
have pihlE : th * y = pih + pil.
  by rewrite [in LHS]Fast2Mult_correct /= /pil /pih.
set dh := xh -pih.

have Fdh: format dh.
  move:(xhmpih_exact Fxh  yn0).
  by rewrite -/th -/pih -/dh => <-; apply:generic_format_round.
set dt := dh -pil.
have dtE: dt = xh -th * y.

 rewrite -/th -/pih /dt /dh.
lra.
have Fdt: format dt.



by rewrite dtE /th; apply:div_error_FLX.
set d := rnd_p (dt + xl).
have dE : d = rnd_p (x - th*y).
  by rewrite /d dtE /x; congr rnd_p; ring.
pose e1 := d - (x - th*y).
pose tl := rnd_p (d/y).
pose e2 := tl - d/y.

have h32a: Rabs (th -xh/y) <= u - 2/y *(u *u).
  by rewrite /th; apply:l6_2=>//; lra.
move/(Rmult_le_compat_r  (Rabs y) _ _  (Rabs_pos y)):(h32a).
rewrite -Rabs_mult (Rabs_pos_eq y); last lra.
have ->:  ((th - xh / y) * y) = th*y -xh by field; lra.
rewrite Rmult_minus_distr_r.
have->:  2 / y * (u * u) * y = 2*(u*u) by field; lra.
move => h32b.
have h32c : Rabs (th*y -x) <= u* (y + 1) - 2*u*u.
have->: (th * y - x) = (th*y - xh) + (- xl) by rewrite /x; ring.
  apply/(Rle_trans _ _  _  (Rabs_triang _ _)).
rewrite Rabs_Ropp; lra.
have h32d: Rabs (th * y - x) < 3*u.
apply: (Rle_lt_trans _ (u * (y + 1) - 2 * u * u))=>//.
clear -upos y2; nra.
 
 


(* have h35: Rabs (th*y -xh) <= 2*u -4* (u * u). *)
(*   apply:(Rle_trans _ (u*y -2* (u *u))). *)
(*     have ->: (th * y - xh) = (th - xh / y)*y by field. *)
(*     rewrite Rabs_mult (Rabs_pos_eq y); last by  lra. *)
(*     have->:  u * y - 2 * (u * u) = ( u - 2 / y * (u * u)) * y by field; lra. *)
(*     apply:Rmult_le_compat_r; lra. *)
(*   clear - y1 y2 upos; nra. *)

have e1ub: Rabs e1 <= 2*u^2.
have ->: 2*u^2 = /2* pow (-p) * pow (2 -p).
rewrite bpow_plus /u.
have -> : pow 2 = 4 by [].
field.
rewrite /e1 dE.
apply:error_le_half_ulp' =>//.
apply: (Rle_trans _ (3*u)); last first.
rewrite bpow_plus /u; have -> : pow 2 = 4 by [].
rewrite -/u; lra.
have ->: (x - th * y)  = - (th*y -x) by ring.
rewrite Rabs_Ropp; lra.


have h32e: Rabs(d/y) < 2*u.

apply:(Rle_lt_trans _ (u + u/y)); last first.
suff : u/y < u by lra.
rewrite -[X in _ < X]Rmult_1_r -Rinv_1.
apply :Rmult_lt_compat_l =>//.
apply:Rinv_lt; lra.
have ->: u + u/y =  (u - 2 /y * (u * u)) + u/y + (2*u^2)/y by field; lra.

have ->: d/y = x/y -th + e1/y by rewrite /e1 ; field; lra.
have ->: (x / y - th + e1 / y ) = (xh / y - th) + (x/y - xh/y) + e1/y by ring.
 (apply/(Rle_trans _ _  _  (Rabs_triang _ _));
  try apply:Rplus_le_compat).
 (apply/(Rle_trans _ _  _  (Rabs_triang _ _));
  try apply:Rplus_le_compat).
        have ->:  (xh / y - th) = - (th - xh/y) by ring.
        by rewrite Rabs_Ropp.
      have ->: x/y - xh/y = xl/y by rewrite /x ; field ; lra.
      rewrite Rabs_mult (Rabs_pos_eq (/y)); try lra.
     apply:Rmult_le_compat_r ; lra.
    rewrite Rabs_mult (Rabs_pos_eq (/y)); try lra.
     apply:Rmult_le_compat_r ; lra.
 have tlub: Rabs tl <= 2*u.
rewrite /tl ZNE -round_NE_abs -ZNE.
suff -> : 2* u = rnd_p (2 * u) by apply: round_le; lra.
rewrite round_generic //.
change (format ((pow 1)* u)); rewrite /u -bpow_plus; apply:generic_format_bpow.
rewrite /fexp; lia.
have e2ub: Rabs e2 <= u^2.
have -> : u^2 = /2 * pow (-p) * (pow (1 -p)).
rewrite /u bpow_plus; have->:  pow 1 = 2 by [].
field.
rewrite /e2 /tl; apply: error_le_half_ulp'=>//.
rewrite bpow_plus; have ->: (pow 1) = 2 by [].
rewrite -/u; lra.
move=>E2.
have h39g: zh + zl = th + tl.
  move:E2;  rewrite (surjective_pairing (Fast2Sum  _ _))
                  F2Sum_correct_abs //=; try apply:generic_format_round.
    case => <- <-. rewrite /tl; ring.
rewrite -/tl /th.
apply:(Rle_trans _ (2 * u))=>//.

apply:(Rle_trans _ (1/2 + u))=>//.
suff : u <= /2 by lra.
change (pow (-p) <= pow (-1)).
apply: bpow_le; lia.
rewrite Rabs_pos_eq; lra.
have ->:  ((zh + zl - (xh + xl) / y) / ((xh + xl) / y))=
((th + tl) - x/y)/(x/y) by rewrite h39g /x.

have rele: ((th + tl) - x/y)/(x/y) = (e1/x + e2*y/x).
  rewrite /e1 /e2 /d.
field;  lra.
have yipos: 0 < /y by apply: Rinv_0_lt_compat. 

case (Rle_lt_dec y x)=>xy.
rewrite rele.

 apply/(Rle_trans _ _  _  (Rabs_triang _ _)).
have ->: 3* (u * u) = 2*u^2 + u^2 by ring.
apply:Rplus_le_compat.
rewrite Rabs_mult (Rabs_pos_eq (/x)).
rewrite -[X in _ <= X]Rmult_1_r.
apply: Rmult_le_compat =>//; first by apply: Rabs_pos; lra.
apply/Rlt_le/Rinv_0_lt_compat; lra.
rewrite -Rinv_1; apply:Rinv_le; lra.
apply/Rlt_le/Rinv_0_lt_compat; lra.
have -> : (e2 * y / x) = e2 * (y/x) by field; lra.


rewrite Rabs_mult.
rewrite -[X in _ <= X]Rmult_1_r.
apply: Rmult_le_compat=>//; try apply: Rabs_pos.

rewrite Rabs_pos_eq.


clear - yn0 ypos xy .
apply: (Rmult_le_reg_r x); try lra.
field_simplify; lra.
apply:Rmult_le_pos; try lra.

apply/Rlt_le/Rinv_0_lt_compat; lra.
have : rnd_p x <= rnd_p y by apply:round_le; lra.
rewrite {1}/x -xE round_generic //.
move=> xhy.
have th1: th <= 1.
rewrite /th.
have -> : 1 = rnd_p 1.

rewrite round_generic //.
change (format (pow 0)); apply: generic_format_bpow; rewrite /fexp; lia.
apply: round_le.
apply: (Rmult_le_reg_r y); try lra.
field_simplify; lra.
case:xhy => xhy; last first.
have the: th = 1.
rewrite /th xhy.
have->: y/y = 1.
field; lra.
rewrite round_generic //.
change (format (pow 0)); apply: generic_format_bpow; rewrite /fexp; lia.
have pihe: pih = xh.
by rewrite /pih  the -xhy Rmult_1_l round_generic.
have pile: pil = 0.

move :pihlE.
rewrite the pihe xhy ; lra.
have de: d= xl.
rewrite /d /dt /dh pihe pile.
have->:  (xh - xh - 0 + xl) = xl by ring.
by rewrite  round_generic.

  pose eta := (th + tl - x / y).
  have : Rabs eta <= u*(Rabs (xl /y)).
    rewrite /eta  /x xhy the /tl de.
    have ->: (1 + rnd_p (xl / y) - (y + xl) / y) =  rnd_p (xl / y) - xl/y.
      field; lra.
    set t := xl/y.
    have ->: u =   / 2 * pow  (- p + 1) .
      rewrite bpow_plus /u; have ->: pow 1 = 2 by [] ; field.
    apply:relative_error_N_FLX=>//; lia.
  rewrite Rabs_mult (Rabs_pos_eq (/y)); last lra.
  rewrite -/eta.
  move=> etaub.
  have hxl : Rabs xl <= u* x.
    have -> : xl = - (rnd_p x - x) by rewrite /x -xE; ring.
    rewrite Rabs_Ropp.

    case: (rnd_epsl Hp1 choice  x)=> e [eb rxe].
    apply:(Rle_trans _ ((Rabs e)*x)).
      rewrite rxe. 
      have  ->:  (x * (1 + e) - x)= e*x by ring.
      rewrite Rabs_mult (Rabs_pos_eq x);   lra.
    apply:Rmult_le_compat_r; rewrite /u; lra.
  rewrite Rabs_mult (Rabs_pos_eq (/(x/y))); 
    last by apply/Rlt_le/Rinv_0_lt_compat/Rmult_lt_0_compat=>//.
have h0: Rabs eta <= u^2 * (x/y).
apply:(Rle_trans _ (u * (Rabs xl * / y)))=>//.
apply: (Rle_trans _ (u *  (u * x )* /y)).
rewrite !Rmult_assoc.
apply: Rmult_le_compat_l; try lra.
rewrite -!Rmult_assoc.
apply: Rmult_le_compat_r =>//;  lra.
by apply:Req_le; field; lra.
apply: (Rle_trans _ (u^2)).
apply:(Rmult_le_reg_r (x/y)); first by apply:Rmult_lt_0_compat.
suff ->:   Rabs eta * / (x / y) * (x / y) = Rabs eta by [].
  field; lra.
clear -upos; nra.


(* xh < y  *)
have h0: Rabs (th - xh/y) <= u/2 -  /y *(u * u).
rewrite /th ; apply:  l6_1_2  =>//.
lra.
lra.
apply: (Rmult_lt_reg_r y); try lra.
field_simplify; lra.
 have :Rabs (th - xh / y) * y <= (u / 2 - / y * (u * u)) * y.
 apply/(Rmult_le_compat_r y); lra.
have->: (u / 2 - / y * (u * u)) * y = u/2*y -u^2 by field; lra.
have ->:  Rabs (th - xh / y) * y = Rabs (th*y -xh).
rewrite -[Y in _*Y]Rabs_pos_eq; last lra.
rewrite -Rabs_mult.
congr Rabs; field; lra.
move => h1.
have h2:  Rabs (th * y - xh) <= u  - u ^ 2.
apply:(Rle_trans _ ( u / 2 * y - u ^ 2))=>//; clear -upos y2; nra.
have h3:  Rabs (x - th * y ) <= 2*u - u ^ 2.
have ->:  (x - th * y ) = - (th*y -x) by ring.
rewrite Rabs_Ropp  /x.
have ->: (th * y - (xh + xl)) = ((th * y - xh) + (-xl)) by ring.

 apply/(Rle_trans _ _  _  (Rabs_triang _ _)).
rewrite Rabs_Ropp; lra.
have e1ub': Rabs e1 <= u^2.
rewrite /e1 dE.
have ->: u^2 =  / 2 * pow (- p) * pow (1 -p).
rewrite bpow_plus /u; have->: pow 1 = 2 by [].
field.


apply:error_le_half_ulp'=>//.
rewrite bpow_plus ; have->: pow 1 = 2 by [].
rewrite -/u.
have u2pos: 0 < u^2 by clear -upos; nra.
lra.


 rewrite rele.
case (Rlt_le_dec x (1-u/2)).

case: (Rle_lt_dec (1- (u/2) ) (xh +xl)) => xlu2 ; last first.


 have is_pow1: is_pow two 1 by exists 0%Z;rewrite Rabs_pos_eq //;lra. 
 have F1: format 1 by apply:is_pow_generic ; try lra. 

have : rnd_p (xh + xl) <= 1-u.
rewrite pred_1 //.
apply:round_N_le_midp=>//.

apply: generic_format_pred => //.
rewrite  succ_pred //.
rewrite- pred_1 -/u //;lra.
rewrite -xE; lra.
rewrite /x ; lra.

move=> xlb.
have xi: /x  <= /(1 -u/2).

apply:Rinv_le =>//.
suff : u < 2 by lra.
change (pow (-p) < pow 1); apply: bpow_lt; lia.
have xipos : 0< /x by apply:Rinv_0_lt_compat .


(* have ->:  (e1 / x + e2 * y / x) = (e1 + e2 *y) /x by field; lra. *)
(* rewrite Rabs_mult (Rabs_pos_eq (/x)); last lra. *)


(* apply : (Rmult_le_reg_r x)=>//. *)
(* rewrite Rmult_assoc Rinv_l ?Rmult_1_r; last lra. *)





(*  apply/(Rle_trans _ _  _  (Rabs_triang _ _)). *)


have h4 : Rabs (e1 /x) <= u^2* (/(1 -u/2)).
rewrite Rabs_mult ; apply: Rmult_le_compat =>// ; try apply: Rabs_pos.
rewrite Rabs_pos_eq //; lra.
have h5:  Rabs (e2 * y / x) <= u^2 * (2 - 2*u) * (/(1-u/2)).
rewrite !Rabs_mult  (Rabs_pos_eq y) ?(Rabs_pos_eq (/x)) ; try lra. 
apply:(Rle_trans _ (u^2 * (2 -2*u) * /(1-u/2))).
apply:Rmult_le_compat=>//; try lra.
apply:Rmult_le_pos; try lra.
apply:Rabs_pos.
apply:Rmult_le_compat=>//; try lra.

apply:Rabs_pos.
lra.
apply:(Rle_trans _ (u ^ 2 * (3 - 2 * u) * / (1 - u / 2))).

apply/(Rle_trans _ _  _  (Rabs_triang _ _)).


lra.
have->: 3 * (u * u) = u^2 *3 by  ring.
rewrite Rmult_assoc.
apply:Rmult_le_compat_l.
clear -upos; nra.
apply:(Rmult_le_reg_r (1 - u/2)).
suff : u < 2 by lra.
change (pow (-p) < pow 1); apply: bpow_lt; lia.
rewrite Rmult_assoc Rinv_l ?Rmult_1_r; try lra.
Qed.


End Algo15.

End Div.
