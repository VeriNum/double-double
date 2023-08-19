(* Copyright (c) ENS de Lyon and Inria. All rights reserved. *)

(* Require Import ROmega.*)
Require Import Reals Psatz ZArith.
From Flocq Require Import Core Relative Sterbenz Operations.
Require Import mathcomp.ssreflect.ssreflect.


Set Implicit Arguments.

Section Aux.

Local Notation two := radix2 (only parsing).
Local Notation pow e := (bpow two e).
Open Scope R_scope.

Variables p  : Z.
Hypothesis Hp : Z.lt 1 p. 

Local Instance p_gt_0 : Prec_gt_0 p.
now apply Z.lt_trans with (2 := Hp).
Qed.


Section MoreFlocq.
Theorem Rabs_0  x (x0 : x = 0) : Rabs x = 0.
Proof. by rewrite x0 Rabs_R0. Qed.

Variable beta:radix.
Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).

Definition is_pow  x :=  exists e : Z, Rabs x = bpow beta e.

Theorem is_pow_dec x : {is_pow  x} + {~ is_pow  x}.
Proof.
case:(Req_EM_T x 0)=>[-> |xn0].
  right; move=> [n ]; rewrite Rabs_R0.
  move:(bpow_gt_0 beta n); lra.
have  [e E]:= mag beta x.
move:(E xn0).
case; case/Rle_lt_or_eq_dec.
  right => [[n Hn]].
  move:b a; rewrite Hn=>/lt_bpow a /lt_bpow b; lia.
by move=>*; left ; exists (e -1)%Z.
Qed.

Theorem is_pow_opp  : forall x : R, is_pow   x -> is_pow  (- x).
Proof. by move=> x [ex]; rewrite -Rabs_Ropp => xe; exists ex.  Qed.

Theorem is_pow_generic x : is_pow x -> format  x.
Proof.
case=> e ex.
case:(Rle_lt_dec 0 x)=> x0.
  rewrite Rabs_pos_eq // in ex; rewrite ex.
  by apply:generic_format_bpow; rewrite /fexp; lia.
rewrite -Rabs_Ropp Rabs_pos_eq in ex; last lra.
rewrite -(Ropp_involutive x); apply:generic_format_opp.
by rewrite ex; apply:generic_format_bpow; rewrite /fexp; lia.
Qed.

Theorem POSpow_ln_beta :
  forall x : R, is_pow  x -> (0 < x)%R ->
    x = (bpow beta (mag beta x - 1)).
Proof.
move=> x [e Bx] Px.
rewrite Rabs_pos_eq in Bx; last lra.
by rewrite Bx mag_bpow; ring_simplify (e + 1 - 1)%Z.
Qed.

(* pred_pos*)

Theorem POSpow_pred :
  forall (x : R),  is_pow  x -> (0 < x)%R ->
  ( pred beta fexp x = x - ulp beta fexp  (x / IZR beta) )%R.
Proof.
move=> x  Bx Px.
have Fx: format x by apply: is_pow_generic.
have B'x:=  POSpow_ln_beta Bx Px.
rewrite /pred /ulp /succ Req_bool_false; last first.
 apply/Rmult_integral_contrapositive_currified; first lra.
 apply/Rinv_neq_0_compat; move:(radix_pos beta); lra.
rewrite Rle_bool_false; last lra.
case:Bx=> e Bx; rewrite Rabs_pos_eq in Bx; last  lra.
have He := mag_bpow beta  e.
rewrite !Ropp_involutive /pred_pos  Req_bool_true /cexp // /Rdiv.
have->: / IZR beta = bpow beta (-1).
rewrite /= IZR_Zpower_pos  /powerRZ /=; field; move :(radix_pos beta); lra.
rewrite mag_mult_bpow; ring_simplify (mag beta x + -1)%Z=>//; lra.
Qed.


Theorem notpow_pred :
  forall (x : R), format   x -> ~ is_pow x ->
  ( pred beta fexp x = x - ulp beta fexp x )%R.
Proof.
move =>x Fx NBx.
case(Req_bool_spec x 0)=>[ ->| H0].
  have ulp0 :  ulp beta fexp 0 = 0 by rewrite ulp_FLX_0.
  rewrite -{1}ulp0 pred_ulp_0 ulp0; ring.
rewrite /pred /succ.
case: (Rle_bool_spec 0 (-x))=> hx.
  by rewrite  Ropp_plus_distr !Ropp_involutive ulp_opp.
rewrite !Ropp_involutive /pred_pos Req_bool_false //.
move=>hxpow; apply: NBx.
exists (mag beta x - 1)%Z.  rewrite  {1}hxpow Rabs_pos_eq //; apply:bpow_ge_0.
Qed.

Notation DN x := (round beta fexp Zfloor x).
Notation UP x := (round beta fexp Zceil x).

(* move ? *)
Theorem ulp_pos : forall x, (x <> 0%R) ->(0 < ulp beta fexp x)%R.
Proof.
now intros x xneq0; rewrite ulp_neq_0; trivial; apply bpow_gt_0.
Qed.

(* move ?*)
Theorem round_DN_UP_le :
  forall x, ( round beta fexp Zfloor x <= x <= round beta fexp Zceil x )%R.
Proof.
move=>x; split; rewrite /round /F2R /=.
  apply:(Rle_trans _ (scaled_mantissa beta fexp x * bpow beta (cexp beta fexp x))%R).
    apply:Rmult_le_compat_r; first exact:bpow_ge_0.
    by apply: Zfloor_lb.
  by rewrite scaled_mantissa_mult_bpow; apply Rle_refl.
apply:( Rle_trans _ (scaled_mantissa beta fexp x * bpow beta (cexp beta fexp x))%R).
  by rewrite scaled_mantissa_mult_bpow; apply Rle_refl.
apply Rmult_le_compat_r; first exact:bpow_ge_0.
by  apply:Zceil_ub.
Qed.

Theorem round_DN_UP_generic :
  forall x,
    generic_format beta fexp x ->
    round beta fexp Zfloor x = round beta fexp Zceil x.
Proof.
move=>x Fx; rewrite /round scaled_mantissa_generic //.
by rewrite Zfloor_IZR Zceil_IZR.
Qed.


End  MoreFlocq.

Section Preliminaries.

Theorem bpow_lt_1 : forall beta n, (0 < n)%Z -> bpow beta (-n) < 1.
Proof. move=> beta n Hn. by apply:( bpow_lt _ _ 0); lia. Qed.

Let u := pow (-p).

Variable choice : Z -> bool.

Local Notation fexp := (FLX_exp p).

Local Notation format := (generic_format two fexp).
Local Notation cexp := (cexp two fexp).
Local Notation mant := (scaled_mantissa two fexp).
Local Notation rnd_p := (round two fexp (Znearest choice)).
Local Notation ulp := (ulp two fexp).

Lemma u_ulp1: u = (/2 * (ulp 1)).
Proof.
rewrite /ulp Req_bool_false; last by lra.
by rewrite /cexp /u (mag_bpow two 0)  Zplus_0_l /fexp bpow_plus bpow_1 /=; lra.
Qed.

Lemma upos: 0 < u.
Proof.
move: (bpow_gt_0 two (-p)); rewrite /u; lra.
Qed.

(* Lemma 1.1 *)
(* a simplifier *)


Lemma error_le_half_ulp' (t:R) (k:Z):  ((Rabs t) <= pow k)%R -> 
                       (Rabs ((rnd_p t) - t)) <= /2 * u  * (pow k).
Proof.
have rge0: 0 <=  / 2 * u * pow k.
  by rewrite  /u Rmult_assoc -bpow_plus; move:(bpow_ge_0 two (- p + k)); lra.
case:(Req_dec t 0)=>[-> |t0].
  by rewrite round_0 Rminus_0_r Rabs_R0. 
case=>Rteq.
  apply: (Rle_trans _  (/2 * Ulp.ulp two fexp t)); first exact:error_le_half_ulp.
  rewrite Rmult_assoc; apply:Rmult_le_compat_l; first lra.
  rewrite /u ulp_neq_0 // /cexp /fexp Rmult_comm bpow_plus.
  apply:Rmult_le_compat_r; first exact: bpow_ge_0.
  by apply/bpow_le /mag_le_bpow=>//.
  rewrite round_generic; last  by apply:is_pow_generic; exists k.
  rewrite Rabs_0 // ; ring.
Qed.


(* Lemma 1.2 *)
Lemma sterbenz' x y (Fx: format x) (Fy : format y):
  ( x/2 <= y <= 2*x)%R  -> format  (x - y).
Proof.
move=> hxy; replace (x - y)%R with (- (y - x))%R by ring.
by apply:generic_format_opp; apply:sterbenz.
Qed.


Lemma scale_12  x  (xpos:  0 < x):(exists e, 1 <= x * pow e < 2 ).
Proof.
have xn0: x <> 0 by lra.
case: (mag two x)=>ex /(_ xn0).
rewrite  Rabs_pos_eq;( try lra) => [[hex1 hex2]].
exists ( 1 - ex)%Z.
split.
  apply:(Rmult_le_reg_r (pow (ex -1))); first by apply: bpow_gt_0.
  rewrite Rmult_assoc -bpow_plus.
  ring_simplify (1 - ex + (ex - 1))%Z.
  have ->: pow 0 = 1 by [].
  lra.
apply:(Rmult_lt_reg_r (pow (ex -1))); first by apply: bpow_gt_0.
rewrite Rmult_assoc -bpow_plus.
ring_simplify (1 - ex + (ex - 1))%Z.
rewrite bpow_plus.
change (x * 1 < 2 * ((pow ex) * (/2))); lra.
Qed.

Lemma rel_error_u t (tn0 : t <> 0) : Rabs ((rnd_p t - t) /t ) <= u/(1+u).
Proof.
rewrite Rabs_mult; apply/(Rmult_le_reg_r (Rabs t)); first by apply/Rabs_pos_lt. 

rewrite Rmult_assoc -Rabs_mult Rinv_l // (Rabs_pos_eq 1); last lra.
have ->: u = (u_ro two p).
rewrite /u /u_ro bpow_plus.
have ->: pow 1 = 2 by [].
field.
rewrite Rmult_1_r.

by apply/relative_error_N_FLX'; lia.
Qed.


(* Lemma 1.3 part 1 *)
Lemma rnd_epsl (t:R) : exists (e1:R) , ((Rabs e1) <= u)%R /\ 
                                  (rnd_p t) = (t * (1 + e1))%R.
Proof.
case : (relative_error_N_FLX_ex two p p_gt_0  choice t)=> e1 [he1 he1q].
by exists e1; split=>//; move:he1;  rewrite /u  bpow_plus  bpow_1 /=; lra.
Qed.


(* Lemma 1.3 part 2*)
(* move, tester s'il est utilisé *)

Lemma rnd_epsr (t:R) : 
  exists (e2:R) , ((Rabs e2) <= u)%R /\ (rnd_p t) = (t / (1 + e2))%R.
Proof.
have hpow1 : (/2 * pow (- p + 1) =  (pow (-p)))%R.
  by rewrite bpow_plus bpow_1 /=; field.
case (Req_dec (rnd_p t) 0%R)=> rt0.
  exists u; split.
    by rewrite Rabs_pos_eq; try lra; apply: bpow_ge_0.
  rewrite rt0; suff-> : t = 0 by lra.
  move:rt0; apply/eq_0_round_0_FLX.
exists ((t - (rnd_p t))%R / (rnd_p t))%R; split; try lra.
  rewrite /Rdiv Rabs_mult Rabs_Rinv // Rabs_minus_sym.
  have hh := (Rabs_pos_lt (rnd_p t) rt0).
  apply:(Rmult_le_reg_r (Rabs (rnd_p t)))=>//.
 have h := (relative_error_N_FLX_round two p p_gt_0  choice t).
  rewrite  hpow1 -/u in h.
  field_simplify;  lra.
field; split=>//;ring_simplify( rnd_p t + (t - rnd_p t)).
by move=>t0 ; apply: rt0; rewrite t0 round_0.
Qed.

(* move *)
Lemma round_round x: rnd_p (rnd_p x )= rnd_p x.
Proof. by rewrite round_generic //; apply:generic_format_round. Qed.

(* a generaliser, et bouger *)
(* Hypothesis ZNE : choice = fun n => negb (Z.even n). *)
Lemma r1pu  (ZNE : choice = fun n => negb (Z.even n)): rnd_p (1 + u) = 1.
Proof.
rewrite /round  /ulp /scaled_mantissa /cexp /fexp /= /F2R /=.
have->:  (mag radix2 (1 + u)  = 1%Z :> Z).
  apply:mag_unique_pos.
  rewrite /= /u ; move:(bpow_ge_0 two (-p)); split;first lra.
  rewrite IZR_Zpower_pos /=.
  suff:pow (-p) < 1 by lra.
  by apply : bpow_lt_1; lia.
have h1e: 1 = (IZR (Zpower radix2 (p - 1)) * bpow radix2 (1 - p)).
  by rewrite IZR_Zpower -?bpow_plus;[ ring_simplify (p - 1 + (1 - p))%Z | lia].
rewrite [RHS] h1e; congr (_ *_); congr IZR.
rewrite /u Rmult_plus_distr_r Rmult_1_l  -bpow_plus; ring_simplify (- p + - (1 - p))%Z.
have->: ((- (1 - p))= p -1)%Z by ring.
rewrite -IZR_Zpower /=;[| lia].
rewrite ZNE /Znearest; set z := Zfloor _.
have ->: z=  Zpower radix2 (p - 1).
  rewrite /z; rewrite IZR_Zpower_pos /=; apply: Zfloor_imp; rewrite plus_IZR /=; lra.
rewrite Rcompare_Eq /=; first by rewrite Z.even_pow //=; lia.
rewrite IZR_Zpower_pos /=; ring.
Qed.

Lemma r1pugE x (ZNE : choice = fun n => negb (Z.even n)): 
    0 <= x <= u->  rnd_p (1 + x) = 1.
Proof.
move=> [hxl hxu]; apply:Rle_antisym.
  rewrite -[X in _ <= X]r1pu //; apply:round_le; lra.
have: rnd_p (1 + 0 ) <= rnd_p (1 +x) by apply:round_le; lra.
rewrite round_generic; first lra.
rewrite Rplus_0_r; change (format (pow (0))).
apply:generic_format_bpow; rewrite /fexp; lia.
Qed.

Lemma r1mu2 (ZNE : choice = fun n => negb (Z.even n)): rnd_p (1 - u /2) = 1.
Proof.
rewrite /round  /ulp /scaled_mantissa /cexp /fexp /= /F2R /=.
have->:  (mag radix2 (1 - u /2)  = 0%Z :> Z).
  apply:mag_unique_pos;rewrite /= /u; split.
    rewrite IZR_Zpower_pos /=.
    suff:pow (-p ) < 1 by  lra.
    by apply : bpow_lt_1; lia.
  move:(bpow_gt_0 two (-p)); lra.
rewrite Z.sub_0_l Z.opp_involutive.
have h1e: 1 = (IZR (Zpower radix2 p ) * bpow radix2 ( - p)).
  rewrite IZR_Zpower -?bpow_plus ?Z.add_opp_diag_r //=; lia.
rewrite [RHS] h1e; congr (_ *_); congr IZR.
rewrite /u Rmult_plus_distr_r Rmult_1_l.   
have ->: -(pow (- p) / 2) * pow p = -(pow (-1)).
  rewrite /Rdiv; have->: /2 = pow (-1) by [].
  by rewrite Ropp_mult_distr_l_reverse -!bpow_plus; ring_simplify(- p + -1 + p)%Z.
rewrite -IZR_Zpower /=;[| lia]; rewrite ZNE /Znearest;  set z := Zfloor _.
have ->: z=  (Zpower radix2 (p)  - 1)%Z.
  rewrite /z; apply: Zfloor_imp; rewrite !plus_IZR !IZR_Zpower_pos /=;  lra.
rewrite Rcompare_Eq /=; last by rewrite plus_IZR IZR_Zpower_pos /=; field.
rewrite -Zodd_even_bool {1}Z.sub_1_r Z.odd_pred Z.even_pow /=; try lia.
apply:Zceil_imp ; rewrite plus_IZR IZR_Zpower_pos/= ;split;lra.
Qed.

Lemma r1mu2_2 (ZNE : choice = fun n => negb (Z.even n)): 
                  rnd_p (2 * (1 - u)) = (2 - pow (1 - p)).
Proof.
rewrite /round  /ulp /scaled_mantissa /cexp /fexp /= /F2R /=.
have D:  (mag radix2 (1 - u)  = 0%Z :> Z).
  apply:mag_unique_pos;rewrite /= /u; split.
    rewrite IZR_Zpower_pos /=. 
    suff:pow (-p) <= /2; try lra.
    replace (/2) with (pow (-1)) by (simpl; lra).
    apply bpow_le. apply Z.opp_le_mono. 
    rewrite !Z.opp_involutive; simpl; lia. 
    apply Rminus_lt; field_simplify. 
    replace 0 with (-0) by nra.
    apply Ropp_lt_contravar.
    apply bpow_gt_0. 
change 2 with (bpow radix2 1).
replace (pow 1 * (1 - u )) with
  ((1 - u ) * pow 1) by nra.
rewrite mag_mult_bpow.
rewrite D Z.add_0_l.
have h1e: (2 - pow (1 - p)) = (IZR (Zpower radix2 p - 1) * bpow radix2 (1 - p)).
  change 2 with (bpow radix2 1). Search (IZR ( _ - _)).
  rewrite minus_IZR IZR_Zpower ?bpow_plus; try lia. field_simplify. 
  rewrite Rplus_comm. replace (pow 1 + - pow 1 * pow (- p)) with
      (pow 1  - pow 1 * pow (- p)) by nra. f_equal.  rewrite -!bpow_plus.  
  ring_simplify (1 + - p + p)%Z => //.
rewrite [RHS] h1e; congr (_ *_); congr IZR.
rewrite /u Rmult_plus_distr_r Rmult_1_l.   
have ->: -(pow (- p)) * pow 1 = -(pow (-p + 1)).
   by rewrite Ropp_mult_distr_l_reverse -!bpow_plus; ring_simplify(- p + -1 + 1)%Z.
 ring_simplify((pow 1 + - pow (- p + 1)) * pow (- (1 - p))). rewrite -!bpow_plus.
 ring_simplify (- p + 1 +- (1-p))%Z. ring_simplify(1 + - (1 - p))%Z.
simpl.
rewrite -IZR_Zpower /=;[| lia]; rewrite ZNE /Znearest;  set z := Zfloor _.
have ->: z=  (Zpower radix2 (p)  - 1)%Z. subst z.
replace (IZR ( 2 ^ p) -1) with (IZR (2^p - 1)).
rewrite Zfloor_IZR => //. rewrite minus_IZR => //.
rewrite Rcompare_Lt /=; try lia ; last rewrite plus_IZR  /=; field_simplify; lra.
rewrite /u. 
apply Rgt_not_eq.
apply Rgt_minus.
have Hp1 : ( -1 > -p)%Z  by lia.
apply Rlt_gt.
apply bpow_lt_1; lia. 
Qed.

Lemma r1pug x : 0 <= x < u->  rnd_p (1 + x) = 1.
Proof.
have F1 : format 1.
  change (format (pow 0)); apply:generic_format_bpow; rewrite /fexp; lia.
move=> [[hxl|<-] hxu]; last by rewrite Rplus_0_r round_generic.
have ulp1:= u_ulp1.
rewrite round_N_eq_DN ?round_DN_plus_eps_pos //; try lra.
rewrite round_UP_plus_eps_pos //; lra.
Qed.
Lemma r1pu2: rnd_p (1 + u /2) = 1.
Proof. by apply: r1pug; rewrite /u; move:(bpow_gt_0 two (-p)); lra. Qed.



(* FLX.v *)
Lemma cexp_bpow : forall x e, x <> R0 -> cexp (x * pow e) = (cexp x + e)%Z.
Proof. by move=> x e xn0; rewrite /cexp mag_mult_bpow // /FLX_exp; lia. Qed.
(* FLX.v *)
Lemma  mant_bpow x e : mant (x * pow e) = mant x.
Proof. 
case: (Req_dec x 0) => [->|Zx]; first by rewrite Rmult_0_l. 
rewrite /scaled_mantissa cexp_bpow // Rmult_assoc -bpow_plus.
by ring_simplify (e + - (cexp x + e))%Z.
Qed.
(* FLX.v *)

Lemma  round_bpow  x e:  rnd_p (x * pow e) = (rnd_p x * pow e)%R.
Proof.
case: (Req_dec x 0) => [->|Zx]; first by rewrite Rmult_0_l round_0 Rmult_0_l.
by rewrite /round /F2R /= mant_bpow  cexp_bpow // bpow_plus Rmult_assoc.
Qed.



Lemma  round_bpowG  x e rnd  (vrnd : Valid_rnd rnd ):  (round two fexp rnd  (x * pow e) = 
                              (  round two fexp rnd x) * pow e)%R.
Proof.
case: (Req_dec x 0) => [->|Zx].
 by rewrite Rmult_0_l  round_0 Rmult_0_l.
by rewrite /round /F2R /= mant_bpow  cexp_bpow // bpow_plus Rmult_assoc.
Qed.


Lemma rbpowpu (ZNE : choice = fun n => negb (Z.even n)) x :  
0 < x -> (is_pow two x) -> rnd_p (x + (/2 * (ulp x))) = x.
Proof.
move=> xpos  [xpow]; rewrite Rabs_pos_eq; [move=> xe| lra].
rewrite  xe ulp_bpow {2}/fexp /= !bpow_plus /= IZR_Zpower_pos /= Rmult_1_r.
field_simplify (/ 2 * (pow xpow * 2 * pow (- p))).
have->: (pow xpow + pow xpow * pow (- p)) = (1 + pow(-p))*(pow xpow)  by field.
rewrite round_bpow -/u r1pu //; ring.
Qed.


Lemma rbpowpuW   (ZNE : choice = fun n => negb (Z.even n)) x e:  
0 < x -> 0 <= e <= (/2 * (ulp x))->
                     (is_pow two x) -> rnd_p (x + e) = x.
Proof.
move=> xpos [el eu] xispow; move : (xispow) => [xpow]; rewrite Rabs_pos_eq; [move=> xe| lra].
have: rnd_p (x + e) <= rnd_p (x + (/2 * (ulp x))).
  apply/round_le; lra.
rewrite rbpowpu // => hrxe.
apply:Rle_antisym =>//.
have {1}->: x = rnd_p x.
  rewrite round_generic // xe;   apply:generic_format_bpow; rewrite /fexp; lia.
apply:round_le; lra.
Qed.

Hypothesis choice_sym: forall x, choice x  = negb (choice (- (x + 1))).

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

Lemma error_le_half_ulp_W (ZNE : choice = fun n => negb (Z.even n))
(t:R) (k:Z) e:  0 <= e <= /2 * u  * (pow k)->((Rabs t) <= pow k + e)%R -> 
                       (Rabs ((rnd_p t) - t)) <= /2 * u  * (pow k).
Proof.
move=>[e0 eu].
wlog tpos: t / 0 <= t.
  move=> hwlog.
  case:(Rle_lt_dec 0 t) =>[hto | /Rlt_le ht0]; first by apply: hwlog.
  rewrite -Rabs_Ropp.
  have ->:  Rabs (rnd_p t - t) = Rabs (rnd_p (-t) - (-t)).
    rewrite rnd_p_sym  -Rabs_Ropp Ropp_minus_distr; congr Rabs; ring.
  apply: hwlog; lra.
have : rnd_p 0 <= rnd_p t by apply:round_le.
rewrite round_0 => rt0.
case : (Rle_lt_dec (Rabs t) (pow k)).
  by move=> *; apply:  error_le_half_ulp'.
move=> pkrt rtpke.
have he: Rabs (rnd_p t) = pow k; first apply:Rle_antisym.
+ suff ->:  pow k = rnd_p (pow k + e).
    by rewrite -rnd_p_abs  //; apply: round_le.
  rewrite rbpowpuW //; try apply: bpow_gt_0.
    rewrite ulp_bpow /fexp; rewrite !bpow_plus /= IZR_Zpower_pos /=; split; try lra.
    move:eu; rewrite /u ; lra.
  exists k; rewrite Rabs_pos_eq //;apply/bpow_ge_0.
+ have: rnd_p (pow k) <= rnd_p (Rabs t) by apply/round_le/Rlt_le.
  rewrite round_generic; last by   apply:generic_format_bpow; rewrite /fexp; lia.
  by rewrite ZNE round_NE_abs -ZNE.
rewrite Rabs_pos_eq // in he; rewrite he.
rewrite Rabs_pos_eq // in pkrt.
rewrite Rabs_pos_eq // in rtpke.
rewrite -Rabs_Ropp Rabs_pos_eq; lra.
Qed.


End Preliminaries.

End Aux.
