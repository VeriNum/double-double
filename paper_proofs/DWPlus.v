
(* Copyright (c  Inria. All rights reserved. *)


Require Import Psatz Reals ZArith.

From Flocq Require Import Core Relative Sterbenz Operations.

Require Import mathcomp.ssreflect.ssreflect.
Require Import Bayleyaux.


From Flocq Require Import Pff2Flocq.



Require Import F2Sum (* TwoSum.*).


Set Implicit Arguments.

Section DWPlus.

Local Notation two := radix2 (only parsing).
Local Notation pow e := (bpow two e).
Fact twole3: (two <= 3)%Z. Proof. by rewrite /=; lia. Qed.


Variables p  : Z.
Hypothesis Hp : Z.lt 1 p.


Local Instance p_gt_0 : Prec_gt_0 p.
by apply: (Z.lt_trans _  1 _ _ Hp). Qed.

Let u := pow (-p).



Local Notation fexp := (FLX_exp p).

Local Notation format := (generic_format two fexp).
Local Notation cexp := (cexp two fexp).
Local Notation mant := (scaled_mantissa two fexp).


Fact formatS x (Fx : format x)
 exp: format (x * pow exp).
Proof.
case/FLX_format_generic: Fx=> fx xE fnumx.
apply/generic_format_FLX.
apply: (FLX_spec  _ _ _ (Float two (Fnum fx) ((Fexp fx) + exp)%Z)); 
   rewrite ?xE /F2R //= bpow_plus ; ring.
Qed.


Variable choice : Z -> bool.
Local Notation rnd_p := (round two fexp (Znearest choice)).

Lemma rbpowpuW':
   forall x e : R,
   0 < x -> format x ->
   0 <= e < / 2 * ulp radix2 (FLX_exp p) x ->
   round radix2 (FLX_exp p) (Znearest choice) (x + e) = x.
Proof.
move=> x e xpos Fx eb .
case:(Req_dec e 0)=>e0.
  by rewrite e0 Rplus_0_r round_generic.
have dE: round two fexp Zfloor (x + e) = x.
  by apply: round_DN_plus_eps_pos =>//;  lra.
rewrite -{2}dE; apply:round_N_eq_DN; rewrite round_UP_DN_ulp.
  rewrite dE. 
  suff: e <  (ulp radix2 fexp (x + e)) / 2 by lra.
  apply: (Rlt_le_trans _ (/ 2 * ulp radix2 fexp x)); try lra.
  suff:  ulp radix2 fexp x <= ulp radix2 fexp (x + e) by lra.
  by apply:ulp_le; rewrite !Rabs_pos_eq; lra.
case : (generic_format_EM two fexp (x+e))=>// Fxe.
by move:dE; rewrite round_generic //; lra.
Qed.

Hypothesis ZNE : choice = fun n => negb (Z.even n).
Local Notation r1pu  := (r1pu  Hp ZNE).
Local Notation r1mu2 := (r1mu2  Hp ZNE).
Local Notation r1pu2 := (r1pu2  Hp choice).



Open Scope R_scope.
 
Fact ulp_pow_aux  a:  ulp radix2 fexp a / 2 = ulp radix2 fexp (a/ IZR radix2).
Proof.
case:(Req_dec a 0)=> a0; first by rewrite a0 /Rdiv !(ulp_FLX_0, Rmult_0_l).
have->: a / IZR radix2 = a * pow (-1) by [].
rewrite !ulp_neq_0 =>//; first  by rewrite cexp_bpow // bpow_plus.
apply/Rmult_integral_contrapositive_currified =>//.
have: 0 <  pow (-1) by apply bpow_gt_0.
lra.
Qed.


(* Lemma 2.1 *)
Lemma roundN_plus_ulp  a b (Fa : format a) (Fb : format b): 
      ( (a + b) <> 0) ->
        (Rmax ((ulp two fexp a)/2) ((ulp two fexp b)/ 2)) <= Rabs (rnd_p (a + b)).
Proof.
move=> sn0.
have rsn0: rnd_p (a + b) <> 0.
  by apply:round_neq_0_negligible_exp=>//; apply/negligible_exp_FLX.
rewrite !ulp_pow_aux.
apply/ Rmax_lub; try  apply/ Plus_error.round_plus_ge_ulp=>//.
by rewrite Rplus_comm; apply:Plus_error.round_plus_ge_ulp; rewrite ?(Rplus_comm b).
Qed.


Definition double_word xh xl :=  ((format xh) /\ (format xl)) /\ 
                                 ( xh = rnd_p (xh + xl)%R).

Lemma dw_ulp xh xl: double_word xh xl -> Rabs xl <= /2 * ulp two fexp xh.
Proof.
case=>[[Fxh Fxl] xhe].
have -> : xl = - (rnd_p (xh + xl)  - (xh + xl)) by rewrite -xhe; ring.
rewrite Rabs_Ropp; apply:(Rle_trans _  (/ 2 * ulp two fexp (rnd_p (xh +xl)))).
  by apply: error_le_half_ulp_round.
by rewrite -xhe; lra.
Qed.


Lemma rulp2p x xl (Fx: format x):  ~(is_pow two x) -> 
               Rabs  xl < /2 * (ulp two fexp x) -> rnd_p (x + xl) = x.
Proof.
move=> xpow xlb.
wlog xpos: x Fx  xpow xl xlb / 0 <= x.
  move=> Hwlog.
  case:(Rle_lt_dec 0 x) => x0; first by apply:Hwlog.
  suff:  -rnd_p (x + xl) = - x by lra.
  rewrite ZNE -round_NE_opp -ZNE Ropp_plus_distr.
  apply: Hwlog; last lra.
  + by apply:generic_format_opp.
  + move=> [e xe]; apply: xpow.
    by exists e; rewrite Rabs_Ropp in xe.
  + by rewrite Rabs_Ropp ulp_opp.
move:xlb  => /Rabs_lt_inv xlub.
have [h1 h2] :  x - / 2 * ulp radix2 fexp x < x +xl <
                         x + / 2 * ulp radix2 fexp x by lra.
apply:Rle_antisym.
  apply: round_N_le_midp =>//.
  rewrite succ_eq_pos; lra.
apply:round_N_ge_midp=>//.
by rewrite notpow_pred=>//; lra.
Qed.

Fact generic_is_pow x: is_pow two  x -> format x.
Proof.
move=> [e ]  .
case: (Rle_dec 0 x) => x0.
  by rewrite Rabs_pos_eq // => ->; apply : generic_format_bpow ; rewrite /fexp; lia.
rewrite -Rabs_Ropp  Rabs_pos_eq; try lra; move => xe.
have ->: x = -pow e by lra.
apply/generic_format_opp /generic_format_bpow; rewrite /fexp;lia.
Qed.


Lemma rxpu2pow x xl :  (is_pow two x)-> Rabs  xl <=  /4 * (ulp two fexp x) -> rnd_p (x + xl) = x.
Proof.
move=> xpow  xlb.
wlog xpos: x xpow xl xlb / 0 <= x.
  move=> Hwlog.
  case:(Rle_lt_dec 0 x) => x0.
    apply:Hwlog=>//.
  suff:  -rnd_p (x + xl) = - x by lra.
  rewrite ZNE -round_NE_opp -ZNE Ropp_plus_distr.
  apply: Hwlog; try lra.
    case: xpow => e xe; exists e; by rewrite Rabs_Ropp.
  by rewrite Rabs_Ropp ulp_opp.
have Fx:= ( generic_is_pow xpow).
have xer: x = rnd_p x  by rewrite round_generic.
case: xpos => x0; last first.
case:xpow => e xe.
move:xe; rewrite -x0 Rabs_R0; move:(bpow_gt_0 two e); lra.
case:(Rle_lt_dec 0 xl)=> xl0.
apply:Rle_antisym.
  apply:round_N_le_midp =>//.
  rewrite /succ  Rle_bool_true; try lra.
  case/Rabs_le_inv : xlb=> h1 h2.
  suff : 0 < ulp radix2 fexp x by lra.
  apply: ulp_pos; lra.
rewrite {1} xer; apply/round_le; lra.
rewrite -Rabs_Ropp Rabs_pos_eq // in xlb; last by lra.
 have: x -  / 4 * ulp radix2 fexp x  <= x + xl  by lra.
move/(round_le  radix2 fexp (Znearest choice)).
have ->:  rnd_p (x - / 4 * ulp radix2 fexp x) = x.
case:(xpow)=> e xe.
rewrite Rabs_pos_eq // in xe; try lra.
  rewrite xe ulp_bpow.
  have ->: (fexp (e + 1) = e +1  -p)%Z by rewrite /fexp.
  have ->: pow e - / 4 * pow (e + 1 - p) = (1 - /4 * pow (1 - p)) * pow e.
    rewrite !bpow_plus; field.
  rewrite round_bpow  !bpow_plus /= IZR_Zpower_pos /=.
  have ->:  / 4 * (2 * 1 * pow (- p)) =  pow (- p) / 2 by field.
  by rewrite r1mu2; ring.
move=> xub.
apply: Rle_antisym=>//.
rewrite [X in _ <= X ] xer; apply: round_le ; lra.
Qed.

Section TwoF2Sum.

Fact choiceP: (forall x : Z, choice x = negb (choice (- (x + 1))%Z)).
Proof.
move=>x.
by rewrite ZNE Bool.negb_involutive Z.even_opp Z.add_1_r Z.even_succ Z.negb_even.
Qed.


Definition TwoSum (a b : R) :=
let s := rnd_p (a + b) in
let a' := rnd_p (s - b) in
let b' := rnd_p (s - a') in
let da := rnd_p (a - a') in
let db := rnd_p (b - b') in (rnd_p (a+b), (rnd_p (da + db))).

Hypothesis Hp3: Z.le 3 p.

Notation ubemin x := ( mag two  x - p)%Z.

Fact Rle_pmabs emin x:  (emin <= ubemin x)%Z -> x <> 0 ->  pow (emin + p - 1) <= Rabs x.
Proof.
move=> hemin xn0.
apply:(Rle_trans _ (pow  ((mag two x) - 1))).
  apply:bpow_le; lia.
by apply: bpow_mag_le.
Qed.

Definition TwoSum_err a b := snd (TwoSum a b).
Definition TwoSum_sum a b := fst (TwoSum a b).
Lemma  TwoSum_correct  a b (Fa : format a) (Fb : format b):  
                            TwoSum_err a b  = a + b  -  TwoSum_sum  a b.
Proof.
pose s :=  rnd_p (a + b).
pose  a' := rnd_p (s - b).
pose  b' := rnd_p (s - a').
pose   da := rnd_p (a - a').
pose  db := rnd_p (b - b').

pose emin := (Z.min 0 (Z.min (ubemin a) (Z.min (ubemin b) 
                      (Z.min (ubemin (a + b)) (Z.min  (ubemin (s - b)) 
                      (Z.min (ubemin (s - a')) (Z.min (ubemin (b - b')) 
                      (Z.min (ubemin (a - a')) (Z.min (ubemin (b + da))
                      (Z.min (ubemin da)  (ubemin (da + db)))))))))))).

rewrite /TwoSum_err /TwoSum_sum.
case: (Req_dec a 0)=>[->| an0].
  rewrite /= Rplus_0_l  Rminus_0_l (round_generic _ _ _ b) //  Rminus_diag_eq //.
  rewrite round_0 Rminus_0_r Ropp_0 round_0 Rplus_0_l (round_generic _ _ _ b) // Rminus_diag_eq //.
  by rewrite !round_0.
case: (Req_dec b 0)=>[->| bn0].
  rewrite /=  Rplus_0_r Rminus_0_r !(round_generic _ _ _ a) // Rminus_diag_eq //.
  by rewrite round_0  Rminus_0_r  round_0 Rplus_0_r round_0.
case:(Req_dec (a + b) 0)=>[ab0|abn0].
  rewrite /= ab0 round_0 Rminus_0_r Rminus_0_l.
  rewrite ZNE round_NE_opp -ZNE Rminus_0_l Ropp_involutive !(round_generic _ _ _ b) //.
  rewrite  (Rminus_diag_eq b) // round_0 Rplus_0_r round_round; last by move:Hp; lia.
  by rewrite /Rminus Ropp_involutive ab0 round_0.
case:(Req_dec (s -  b) 0)=>[sb0|sbn0].
  rewrite /= sb0 round_0 ?Rminus_0_r ?Rminus_0_l.
  rewrite  round_round -/s;last by move:Hp; lia.
  have->: b - s = 0 by lra.
  rewrite round_0 Rplus_0_r round_round -/s;last by move:Hp; lia.
  rewrite round_generic //; lra.
  rewrite /= -/s -/a'.
have rabn0: rnd_p (a + b) <> 0 by move=> rab0; apply: abn0; apply/eq_0_round_0_FLX: rab0.

rewrite (Rplus_comm  a b).
have: b + a =  round radix2 (FLT_exp emin p) (Znearest choice) (b + a) +
   round radix2 (FLT_exp emin p) (Znearest choice)
     (round radix2 (FLT_exp emin p) (Znearest choice)
        (b -
         round radix2 (FLT_exp emin p) (Znearest choice)
           (round radix2 (FLT_exp emin p) (Znearest choice) (b + a) -
            round radix2 (FLT_exp emin p) (Znearest choice)
              (round radix2 (FLT_exp emin p) (Znearest choice) (b + a) - b))) +
      round radix2 (FLT_exp emin p) (Znearest choice)
        (a -
         round radix2 (FLT_exp emin p) (Znearest choice)
           (round radix2 (FLT_exp emin p) (Znearest choice) (b + a) - b))).
  rewrite -{1}(TwoSum_correct emin p choice Hp) //; try exact:choiceP.
  + by repeat (apply: Z.le_min_l || apply: (Z.le_trans _ _ _ (Z.le_min_r _ _))).
  + apply: generic_format_FLT_FLX =>//; apply: Rle_pmabs=>//.
    by repeat (apply: Z.le_min_l || apply: (Z.le_trans _ _ _ (Z.le_min_r _ _))).
  apply: generic_format_FLT_FLX =>//; apply: Rle_pmabs =>//.
  by repeat (apply: Z.le_min_l || apply: (Z.le_trans _ _ _ (Z.le_min_r _ _))).
rewrite (Rplus_comm b a) ; move=> hba.
rewrite  -/s [X in _ = X - s] hba.
rewrite round_FLT_FLX; last by apply: Rle_pmabs =>//;
  repeat (apply: Z.le_min_l || apply: (Z.le_trans _ _ _ (Z.le_min_r _ _))).
rewrite -/s.
rewrite (round_FLT_FLX _ _ _ _ (s - b)); last by apply: Rle_pmabs;
  repeat (apply: Z.le_min_l || apply: (Z.le_trans _ _ _ (Z.le_min_r _ _))).
ring_simplify;rewrite -/a'.
case:(Req_dec (a -  a') 0)=>[da0|dan0].
  rewrite da0 !round_0 Rplus_0_l Rplus_0_r round_round; last by move:Hp.
  rewrite [RHS]round_generic; last by apply: generic_format_round.
  case: (Req_dec (s -  a') 0)=>[b'0|b'n0].
    rewrite b'0 !round_0 Rminus_0_r round_FLT_FLX //; apply: Rle_pmabs =>//.
    by repeat (apply: Z.le_min_l || apply: (Z.le_trans _ _ _ (Z.le_min_r _ _))).
  rewrite (round_FLT_FLX _ _ _ _ (s - a')); last by apply: Rle_pmabs;
    repeat (apply: Z.le_min_l || apply: (Z.le_trans _ _ _ (Z.le_min_r _ _))).
  rewrite -/b';case: (Req_dec (b -  b') 0)=>[db0|dbn0].
    by rewrite db0 !round_0.
  by rewrite round_FLT_FLX //; apply: Rle_pmabs ; 
     repeat (apply: Z.le_min_l || apply: (Z.le_trans _ _ _ (Z.le_min_r _ _))).
rewrite (round_FLT_FLX _ _ _ _ (a - a')); last by apply: Rle_pmabs;
  repeat (apply: Z.le_min_l || apply: (Z.le_trans _ _ _ (Z.le_min_r _ _))).
rewrite -/da; case: (Req_dec (s -  a') 0)=>[->|b'n0].
  rewrite !round_0 Rminus_0_r !(round_generic _ _ _  b) //.
    case:  (Req_dec  (b + da) 0)=> [bda0|bdan0].
      by rewrite  Rplus_comm bda0 !round_0.
    by rewrite Rplus_comm round_FLT_FLX //; apply: Rle_pmabs;
       repeat (apply: Z.le_min_l || apply: (Z.le_trans _ _ _ (Z.le_min_r _ _))).
  by apply: generic_format_FLT_FLX =>//; apply: Rle_pmabs;
    repeat (apply: Z.le_min_l || apply: (Z.le_trans _ _ _ (Z.le_min_r _ _))).
rewrite (round_FLT_FLX _ _ _ _ (s - a')); last by apply: Rle_pmabs;
  repeat (apply: Z.le_min_l || apply: (Z.le_trans _ _ _ (Z.le_min_r _ _))).
rewrite -/b'; case: (Req_dec (b -  b') 0)=>[->|dbn0].
  rewrite !round_0 Rplus_0_r  Rplus_0_l round_FLT_FLX //.
  apply: Rle_pmabs =>//.
    by repeat (apply: Z.le_min_l || apply: (Z.le_trans _ _ _ (Z.le_min_r _ _))).
  by rewrite /da => rda0; apply/dan0; apply/  eq_0_round_0_FLX: rda0.
rewrite (round_FLT_FLX  _ _ _ _ (b -  b'))//; last by apply: Rle_pmabs;
  repeat (apply: Z.le_min_l || apply: (Z.le_trans _ _ _ (Z.le_min_r _ _))).
rewrite -/db (Rplus_comm db); case: (Req_dec (da + db) 0)=>[->|dabn0].
  by rewrite !round_0.
rewrite round_FLT_FLX //; apply: Rle_pmabs=>//;
  repeat (apply: Z.le_min_l || apply: (Z.le_trans _ _ _ (Z.le_min_r _ _))); lia.
Qed.


Fact TwoSum_sumE a b : TwoSum_sum a b = rnd_p (a + b).
Proof. by []. Qed.

Fact TwoSumC (a b : R) (Fa : format a) (Fb : format b): 
   (TwoSum  a b =  TwoSum b a).
Proof.
  apply:  injective_projections.
    by rewrite /= Rplus_comm.
have  TwoSum_errE x y :  snd (TwoSum x y) = TwoSum_err x y  by [].
by rewrite !TwoSum_errE !TwoSum_correct // !TwoSum_sumE Rplus_comm.
Qed.



  
Fact TwoSum_errC (a b : R) (Fa : format a) (Fb : format b):
(TwoSum_err a b =  TwoSum_err b a).
Proof. by rewrite /TwoSum_err TwoSumC. Qed.

Fact TwoSum_asym (a b : R): TwoSum (-a) (-b) = pair_opp (TwoSum a b).
Proof.
  apply:  injective_projections.
    by rewrite /= -Ropp_plus_distr  ZNE round_NE_opp.
    have h x y:  - x - - y = - (x - y) by ring.
 by rewrite /= ZNE !(=^~Ropp_plus_distr, round_NE_opp, h) -ZNE.
Qed.
  
Lemma TwoSum_err_bound (a b : R) (Fa: format a) (Fb : format b): 
    Rabs (TwoSum_err a b)  <= /2 * ulp two fexp (a + b).
Proof.
  rewrite  TwoSum_correct //=.
have->: (a + b - rnd_p (a + b)) = - (rnd_p (a + b) - (a + b)) by ring.
by rewrite Rabs_Ropp; apply: error_le_half_ulp.
Qed.


Lemma DW_TwoSum a b (Fa : format a) (Fb: format b): double_word (TwoSum_sum a b) (TwoSum_err a b).
Proof.
  split;[split; apply:generic_format_round|].
  rewrite TwoSum_correct //= TwoSum_sumE;congr round; ring.
Qed.



End TwoF2Sum.


Notation  F2Sum a b := (Fast2Sum p choice a b).

Notation  F2Sum_sum a b  := (fst (F2Sum a b)).
Notation  F2Sum_err a b  := (snd (F2Sum a b)).

Section DWPlusFP_Pre.

Variables xh xl y: R.
Notation  x := (xh + xl)%R.

Notation  sh := (TwoSum_sum xh y).
Notation  sl :=  (TwoSum_err xh y).
Notation  v := (rnd_p (xl + sl)).

Notation zh :=   (F2Sum_sum sh v).
Notation zl := (F2Sum_err sh v).
Hypothesis Fy : format y.

Definition DWPlusFP := (F2Sum  sh v).

Definition  relative_errorDWFP := (Rabs (((zh + zl) - (x  + y))/ (x  + y))).
Definition errorDWFP := (x + y) - (zh + zl).

Fact rel_errorE: relative_errorDWFP = Rabs errorDWFP * (Rabs (/( x + y))).
Proof.
rewrite /relative_errorDWFP /errorDWFP /Rdiv !Rabs_mult -Ropp_minus_distr Rabs_Ropp //.
Qed.

Notation e := (sl + xl -v).

Lemma errorDWFPe_abs (Fxh: format xh) (Fxl : format xl) :(Rabs v <= Rabs sh) 
                ->errorDWFP  =  e.
Proof.
move=> *.
have Fsh: format sh by apply: generic_format_round.
have Fv: format v by apply: generic_format_round.
rewrite /errorDWFP F2Sum_correct_abs //.
  rewrite TwoSum_correct //=; ring.
by apply/rnd_p_sym/choiceP.
Qed.

Lemma rel_errorDWFPe_abs (Fxh: format xh) (Fxl : format xl):  (Rabs v <= Rabs sh) 
                ->relative_errorDWFP  =  Rabs( e /(x + y)).
Proof.
move=> *.
rewrite /relative_errorDWFP -errorDWFPe_abs // -1?Rabs_Ropp /Rdiv ?Ropp_mult_distr_l.
congr Rabs;congr Rmult; rewrite /errorDWFP; ring.
Qed.

Fact null_case_pre : (xh + y ) = 0 -> (sh  = 0 /\ sl  = 0).
Proof.
move=> xhy0; rewrite /TwoSum_sum /TwoSum_err /TwoSum xhy0 !round_0 /=; split=>//.
rewrite!Rminus_0_l ZNE round_NE_opp -ZNE Ropp_involutive. 
rewrite !(round_generic _ _ _ _ Fy)  /Rminus !Ropp_involutive Rplus_opp_r.
by rewrite xhy0 !(round_0, Rplus_0_r).
Qed.


Fact Rabs0 x (x0: x = 0): Rabs x = 0. 
Proof. by rewrite x0 Rabs_R0. Qed.

Hypothesis xDW: double_word xh xl.

Fact Fxh : format xh. Proof. by case:xDW;case. Qed.
Fact Fxl : format xl. Proof. by case:xDW;case. Qed.
Fact Fsh : format sh. Proof. apply: generic_format_round. Qed.
Fact Fsl : format sl . Proof. apply: generic_format_round. Qed.
Fact Fv : format v. Proof. apply: generic_format_round. Qed.


Fact null_sl (sl0: sl = 0):  errorDWFP = 0.
Proof.
case: xDW=> [[Fxh Fxl]] xE.
have Fsh:= Fsh;  have Fv:= Fv;  have Fx := Fxl.
have vE: v = xl by rewrite sl0 Rplus_0_r round_generic.
have xhye : (xh + y) = rnd_p (xh + y).
  by move:(TwoSum_correct Fxh Fy); rewrite sl0 TwoSum_sumE; lra.
case:(Req_dec xl 0)=> xl0.
  by rewrite /errorDWFP  vE  xl0 Fast2Sumf0 //= TwoSum_sumE -xhye; ring.
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


Fact null_sl_rel (sl0: sl = 0):  relative_errorDWFP = 0.
Proof.
by rewrite rel_errorE null_sl // Rabs_R0 Rmult_0_l.
Qed.

Fact null_case_rel : (xh + y ) = 0 -> relative_errorDWFP = 0.
Proof. by case/null_case_pre=>_ /null_sl_rel. Qed.

Fact null_xh(xh0: xh = 0): errorDWFP = 0.
Proof.
  apply:null_sl; case: xDW; case=> Fxh Fxl _.
  rewrite  TwoSum_correct //= TwoSum_sumE  xh0 Rplus_0_l round_generic //; ring.
Qed.

Fact null_xh_rel (xh0: xh = 0): relative_errorDWFP = 0.
Proof.
  apply:null_sl_rel; case: xDW; case=> Fxh Fxl _.
  rewrite  TwoSum_correct //= TwoSum_sumE  xh0 Rplus_0_l round_generic //; ring.
Qed.

Fact null_case_s (s0:xh + y  = 0 ):  errorDWFP   = 0 /\ (Fast2Sum_correct  p choice sh  v ).
Proof.
case:xDW =>[[Fxh Fxl] _].
rewrite /errorDWFP.
case:(null_case_pre s0)=> -> ->.
rewrite  /Fast2Sum_correct Rplus_0_r round_generic // Fast2Sum0f //=.
lra.
Qed.

End  DWPlusFP_Pre.


Section DWPlusFP.

Hypothesis Hp3: (3 <= p)%Z.

Notation  sh xh y:= (TwoSum_sum xh y). 
Notation  sl xh y:=  (TwoSum_err xh y). 
Notation  v xh y xl:= (rnd_p (xl + (sl xh y))). 



Fact vAsym  xh y xl :
  v  (-xh) (-y) (-xl) = -(v  xh y  xl).
Proof.
  by rewrite /TwoSum_err !TwoSum_asym /pair_opp 
    -Ropp_plus_distr ZNE round_NE_opp -ZNE.
Qed.

Fact vC y xh xl (Fxh: format xh) (Fy: format y) : v  xh y xl = v  y xh xl.
Proof. by rewrite TwoSum_errC. Qed.


Fact relative_error_DWFPC  xh xl y  (Fxh : format xh)(Fy : format y):
  (relative_errorDWFP  xh xl y) =  (relative_errorDWFP   y xl xh).
Proof.
rewrite /relative_errorDWFP.
have <-: (y + xl + xh) = (xh + xl + y) by ring.
by rewrite /TwoSum_sum TwoSumC // vC.
Qed.

Fact error_DWFPC  xh xl y (Fxh : format xh)(Fy : format y):
  (errorDWFP  xh xl y ) =  (errorDWFP  y xl xh).
Proof.
rewrite /errorDWFP.
have <-: (y + xl + xh) = (xh + xl + y) by ring.
by rewrite /TwoSum_sum TwoSumC // vC.
Qed.

Fact error_DWFAsym   xh xl y  (Fxh : format xh)  (Fy : format y):
 (errorDWFP  (-xh)  (-xl )  (-y))=  - (errorDWFP  xh  xl y).
Proof.
  rewrite /errorDWFP /TwoSum_sum TwoSum_asym // vAsym Fast2Sum_asym // /pair_opp.
  rewrite /=; ring.
by apply/rnd_p_sym/choiceP.
Qed.

Fact TwoSum_errS  x y  exp (Fx : format x) (Fy : format y):
  let e := pow exp in 
  TwoSum_err (x * e)  (y * e)  = (TwoSum_err  x y   ) * e.
Proof.
by rewrite /TwoSum_err /= 
   !(=^~ Rmult_plus_distr_r, round_bpow, =^~ Rmult_minus_distr_r).
Qed.

Fact TwoSumS  x y  exp (Fx : format x) (Fy : format y):
  TwoSum (x * pow exp )  (y * (pow exp ))  =
  (fst (TwoSum x y   ) * pow exp, (snd (TwoSum x y))* pow exp).
by  rewrite /TwoSum /= 
    !(=^~ Rmult_plus_distr_r, round_bpow, =^~ Rmult_minus_distr_r).
Qed.

Fact vS y xh xl exp (Fy : format y) (Fxh : format xh):
let e := pow exp in 
v  (xh * e)  (y * e) (xl * e)  = (v  xh y  xl) * e.
Proof.
  by rewrite /= (TwoSum_errS exp) //  -Rmult_plus_distr_r round_bpow .
Qed.

Fact relative_error_DWFPS xh xl y exp (Fy : format y) (Fxh : format xh): 
  xh + xl + y <> 0 -> let e := pow exp in 
  (relative_errorDWFP   (xh*e)  (xl* e)  (y*e)) =  (relative_errorDWFP  xh  xl y).
Proof.
move=> xyn0 /=.
rewrite /relative_errorDWFP =>// ; try apply:formatS =>//.
congr Rabs.
rewrite vS // !(=^~ Rmult_plus_distr_r, round_bpow, =^~ Rmult_minus_distr_r).
rewrite /TwoSum_sum TwoSumS //  Fast2SumS //=; try apply:generic_format_round.
field.
split=>//; move:(bpow_gt_0 two  exp); lra.
Qed.

Lemma scale_generic_12  x (Fx: format x) (xpos:  0 < x):(exists e, 1 <= x * pow e <= 2 - 2 * u).
Proof.
have xn0: x <> 0 by lra.  
case: (mag two x)=>ex /(_ xn0).
rewrite  Rabs_pos_eq;( try lra) => [[hex1 hex2]].
have h := (id_p_ulp_le_bpow two fexp x ex xpos Fx hex2).
have hpow := (bpow_gt_0 two (ex -1)).
exists (-(ex -1))%Z.
rewrite bpow_opp;split; apply:(Rmult_le_reg_r ((pow (ex - 1)%Z)))=>//.
  by field_simplify; try lra.
rewrite Rmult_assoc.
have-> : (/ pow (ex - 1) * pow (ex - 1))=1 by field; lra.
rewrite Rmult_1_r bpow_plus bpow_opp /=.
have -> : (2 - 2 * u) * (pow ex * / 2)= (1-u)*(pow ex) by field.
suff : u * (pow ex) = ulp radix2 fexp x by lra.
rewrite /ulp Req_bool_false // /cexp (mag_unique two x ex).
  by rewrite /fexp bpow_plus /u Rmult_comm.
by rewrite Rabs_pos_eq; lra.
Qed.

Lemma equlpcexp y x :  ulp two fexp y = ulp two fexp x -> cexp x = cexp y.
Proof.
case:(Req_dec y 0);[move ->;rewrite ulp_FLX_0 | move /(ulp_neq_0 two fexp)->];
  case:(Req_dec x 0)=>[-> //| /(ulp_neq_0 two fexp) ->].
    by  move: (bpow_gt_0 two (cexp x)); lra.
  by rewrite ulp_FLX_0 => h;  move: (bpow_gt_0 two (cexp y)); lra.
by move => h; apply: (bpow_inj two).
Qed.

Theorem FLX_mant_le :
 forall x, format x -> (Z.abs (Ztrunc (mant x)) <= two ^p - 1)%Z.
Proof.
move=> x Fx.
apply: Zlt_succ_le; rewrite -Z.add_1_r.
have ->: (radix2 ^ p - 1 + 1 = radix2 ^ p)%Z by ring.
apply: lt_IZR;rewrite abs_IZR IZR_Zpower; last by move:Hp; lia.
move:(scaled_mantissa_lt_bpow  two fexp x).
rewrite -scaled_mantissa_generic // /cexp/fexp.
by ring_simplify (mag radix2 x - (mag radix2 x - p))%Z.
Qed.

Lemma FLX_format_Rabs_Fnum  (x : R) (fx : float two):
  x = F2R fx -> Rabs (IZR (Fnum fx)) < pow p ->
   format  x.
Proof.
case:fx => fn fe ->; rewrite /F2R /= =>h.
apply:generic_format_F2R =>/not_0_IZR Mxyn0.
rewrite /F2R /= /cexp /fexp mag_mult_bpow //.
have mlpb := (mag_le_bpow two _ p Mxyn0 h).
lia.
Qed.
Lemma FLX_format_Rabs_Fnumf  (fx : float radix2):
  (Rabs (IZR (Fnum fx)) < pow p )%R->
   format  (F2R fx).
Proof.
move=>hFnum; by apply:FLX_format_Rabs_Fnum.
Qed.

Theorem Z2R_beta_even_div_two :
  forall b, Z.even b = true -> (IZR b / 2) = IZR (Z.div b 2).
Proof.
move=> b evenb.
case: (Zeven_ex b) => b2 be. 
rewrite be evenb Zplus_0_r Zmult_comm Z.div_mul; last lia.
rewrite mult_IZR ; field.
Qed.
(* a bouger dans bayleyaux et a enlever de DWTimesFP*)

(* From Flocq Require Import Plus_error. *)

(* Lemma ex_mul z k : (pow k)  <= Rabs z  -> format z ->   *)
(*    exists (mz:Z), z = IZR mz * (2 * (pow (- p))  * (pow k)). *)
(* Proof. *)
(* move=>  hle Fz. *)
(* case:(ex_shift two fexp z (1 -p + k)) =>//. *)
(*   rewrite /cexp /fexp. *)
(*   suff:( 1 + k <= mag radix2 z)%Z by lia. *)
(*   by apply:mag_ge_bpow; ring_simplify (1 + k -1)%Z. *)
(* move=>mz zE; by exists mz; rewrite zE !bpow_plus. *)
(* Qed. *)
Notation ulp := (ulp two fexp).

Definition sign x := if  (Rlt_bool x 0) then  (-1) else 1.

Lemma format_bpow e: format (pow e).
Proof. apply/generic_format_bpow; rewrite /fexp;lia. Qed.


(* particular case where (y, xl) may not be a double*)
Lemma part_case_ulp  xh xl  y (DWx: double_word xh xl) (Fy : format y) (xh0: xh <> 0) 
                     (xhy : xh + y <> 0):
  ulp y = ulp  xh -> Rabs xl = (ulp  xh) /2 ->
  errorDWFP xh xl y  = 0 /\ (Fast2Sum_correct  p choice (sh xh y) (v xh y xl)).
Proof.
move=>  ulpe xlE.
have Fsh:= Fsh;  have Fv:= Fv;  have Fx := Fxl.
case:(DWx)=> [[Fxh Fxl] _].
have cexpE:= (equlpcexp _ _ ulpe).
have pcexpE:  (pow (cexp xh)) = ulp xh by rewrite ulp_neq_0.
move:(refl_equal (xh + y)) (refl_equal xh) (refl_equal y).
rewrite {2 4}Fxh {2 4}Fy cexpE -F2R_plus  Fplus_same_exp.
set Mxh := Ztrunc (mant xh).
set  My := Ztrunc (mant y).
rewrite /F2R /==> sE xhE yE.
have hmxh:= (FLX_mant_le Fxh).
have hmy:= (FLX_mant_le Fy).
rewrite -/Mxh -/My in  hmxh hmy.
move/IZR_le: (hmxh) ; move/IZR_le :(hmy);  rewrite !abs_IZR minus_IZR IZR_Zpower; 
 last lia.
move=> Rmxh  Rmy.
have shE: sh xh y  = rnd_p (IZR (Mxh + My))*(ulp xh).
  by rewrite TwoSum_sumE sE   round_bpow  - cexpE pcexpE .
have slE: sl xh y = (IZR (Mxh + My) - rnd_p (IZR (Mxh + My)))* ulp xh.
  rewrite TwoSum_correct //  shE sE -cexpE   pcexpE; ring.  
have xlsE: xl = (sign xl) * /2 * ulp xh.
  move:xlE.
  case : (Rlt_dec xl 0)=> xl0.
    rewrite /sign  Rlt_bool_true  ?Rabs_left; lra.
  rewrite /sign  Rlt_bool_false  ?Rabs_right; lra.

have  v'E: (xl + sl xh y)= (IZR (Mxh + My) - rnd_p (IZR (Mxh + My))
                      + (sign xl) * /2) * ulp xh.
  rewrite  slE {1}xlsE ; ring.
have vE : v xh y xl = rnd_p ((IZR (Mxh + My) - rnd_p (IZR (Mxh + My))
                      + (sign xl) * /2)) * ulp xh.
  by rewrite  v'E ulp_neq_0  // -round_bpow.
(*ici*)
have Fsxl: format (sign xl  * /2).
  change (format (sign xl  * (pow (-1)))); apply:formatS.
  rewrite /sign; case(Rlt_bool xl 0); try apply/generic_format_opp;
  change (format (pow 0)); apply/generic_format_bpow; rewrite /fexp;lia.

have F1m_2:   format (- / 2).
  by  apply/generic_format_opp; change (format (pow (-1))); apply/format_bpow.
have F1_2:    format ( / 2).
  by change (format (pow (-1))); apply/format_bpow.
have F3: format 3.
  apply:(@ FLX_format_Rabs_Fnum _ (Float two 3 0)).
  rewrite /F2R //=; ring.
  rewrite /=; apply:(Rlt_le_trans _ (pow 2)).
    rewrite Rabs_pos_eq; last lra.
    by change (3 < 4); lra.
  by apply:bpow_le; lia.
pose v' := xl + sl xh y.
have v'E':  v' = /2 * ulp xh \/ v'= -(/2) * ulp xh \/
 (v' = 3/2 * ulp xh  /\ pow p <= Rabs  (IZR (Mxh + My)))
\/ (v' = -(3/2) * ulp xh  /\ pow p <= Rabs  (IZR (Mxh + My))).
  rewrite /v' v'E.
  case: (Rle_lt_dec  (Rabs (IZR (Mxh + My))) (pow p -1))=> hMs.
    rewrite (round_generic _ _ _ (IZR _)).
      have-> : (IZR (Mxh + My) - IZR (Mxh + My) + sign xl * / 2) = 
                 sign xl * / 2  by ring.
      rewrite /sign; case(Rlt_bool xl 0).
         by right; left; field.
      by left; field. 
(*   format (IZR (Mxh + My)) *)
    pose fs := (Float two (Mxh + My) 0).
    have fsE : IZR (Mxh + My) = F2R fs by rewrite /fs /F2R /= Rmult_1_r.
    by apply: (FLX_format_Rabs_Fnum fsE); rewrite /fs /=; lra.

(* cas  pow p - 1 < Rabs (IZR (Mxh + My)) *)
  have hMs': pow p <=  Rabs (IZR (Mxh + My)).
    rewrite -abs_IZR -IZR_Zpower; last lia.
    apply/IZR_le.
    suff: (radix2 ^ p  -1 < Z.abs (Mxh + My))%Z by lia.
    by apply/ lt_IZR; rewrite abs_IZR minus_IZR IZR_Zpower; last lia.
  case:(Zeven_odd_dec   (Mxh + My))=> [/Zeven_bool_iff Heven | /Zodd_bool_iff  Hodd].
 (* a factoriser *)
   rewrite (round_generic _ _  _ (IZR (Mxh + My))).
      have->: (IZR (Mxh + My) - IZR (Mxh + My) + sign xl * / 2) = 
                 sign xl * / 2  by ring.
      rewrite /sign; case(Rlt_bool xl 0).
        by right; left; field.
      by left; field. 
(*   format (IZR (Mxh + My)) *)
    pose fs := (Float two ((Mxh + My)/2)%Z 1).
    have fsE : IZR (Mxh + My) = F2R fs.
      rewrite /fs /F2R /= -Z2R_beta_even_div_two //   IZR_Zpower_pos /= ; field.
    apply: (FLX_format_Rabs_Fnum fsE); rewrite /fs /=.
    rewrite  -Z2R_beta_even_div_two //  Rabs_mult (Rabs_pos_eq (/2)); last lra.
    suff:Rabs (IZR (Mxh + My)) < 2* pow p by lra.
    rewrite plus_IZR;  apply:(Rle_lt_trans _ _ _ (Rabs_triang _ _)); lra.
(* cas odd *)
  case: (Zeven_ex (Mxh + My))=>M  Me.
  have {} ME : (Mxh + My)%Z = (2 * M + 1)%Z.
    by rewrite Me; rewrite Zeven.Zeven_odd_bool Hodd.
  rewrite ME.
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
    ring_simplify(1 + p - 1)%Z.
    split=>//.
    rewrite bpow_plus; 
    rewrite plus_IZR; apply:(Rle_lt_trans _ _ _ (Rabs_triang _ _)).
     have ->: pow 1 = 2 by [];  lra.
  have cexpf :  (cexp (IZR (2 * M + 1)) = 1)%Z.
    rewrite /cexp /fexp (mag_unique _ _  (1 +p)); first ring.
    split.
      have->:  (1 + p - 1 = p)%Z by ring.
      by rewrite -ME.
    rewrite -ME plus_IZR bpow_plus; apply:(Rle_lt_trans _ _ _ (Rabs_triang _ _)).
    by have ->: pow 1 = 2 by []; lra.
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

  case:(round_DN_or_UP two fexp (Znearest choice) (IZR (2 * M + 1))); 
     rewrite ?rDN ?rUP => ->; rewrite ?Z.mul_add_distr_l !plus_IZR /sign; 
     case (Rlt_bool xl 0).
     + have->:  (IZR (2 * M) + 1 - IZR (2 * M) + -1 * / 2) = /2 by field.
       by left.
     + have->: (IZR (2 * M) + 1 - IZR (2 * M) + 1 * / 2) = 3* /2 by field.
       by right; right; left;  rewrite -plus_IZR  -ME. 
     + have ->: (IZR (2 * M) + 1 - (IZR (2 * M) + IZR (2 * 1)) + -1 * / 2) = 
             -(3 */2) by rewrite Zmult_1_r; field.
       by right; right; right; rewrite -plus_IZR  -ME.  
  have ->: (IZR (2 * M) + 1 - (IZR (2 * M) + IZR (2 * 1)) + 1 * / 2)= -/2 
   by  rewrite Zmult_1_r; field.
  by right; left.
have Fv': format v'.
  by case: v'E'; [move =>-> |case ; [move => ->|case ;[ case ; move=> -> h| 
   case=> -> h]]]; rewrite - pcexpE; apply/formatS=>//; try apply/generic_format_opp; 
    change (format (3 * (pow (-1)))); apply/formatS.
have Mpos:   (1 <= Z.abs (Mxh + My))%Z.
  suff: ((Mxh + My) <> 0)%Z by lia.
  move => hm0; rewrite hm0 Rmult_0_l in sE; lra.
move/IZR_le:(Mpos); rewrite abs_IZR=> Mge1.

have:Fast2Sum_correct p choice (sh xh y) (v xh y xl).
  apply: F2Sum_correct_abs =>//; try (apply/rnd_p_sym/choiceP).
  rewrite round_generic // -/v'.
  move:(v'E' ); case; [move =>-> |case ; [move => ->|case ;[ case ; move=> -> h| 
   case=> -> h]]];
  rewrite shE 2!Rabs_mult; (try apply: Rmult_le_compat_r;   try exact: Rabs_pos);
  rewrite ZNE -!round_NE_abs -ZNE.
  + apply:(Rle_trans _ 1); first by rewrite Rabs_pos_eq;  lra.
    have ->: 1 = rnd_p 1.
      by rewrite round_generic //; change (format (pow 0)); apply:format_bpow.
    by apply/round_le. 
  + apply:(Rle_trans _ 1); first by rewrite Rabs_Ropp Rabs_pos_eq;  lra.
    have ->: 1 = rnd_p 1.
      by rewrite round_generic //; change (format (pow 0)); apply:format_bpow.
    by apply/round_le.
  + apply:(Rle_trans _ (pow p)).
      rewrite Rabs_pos_eq; try lra; apply(Rle_trans _ 4);first lra.
      change(pow 2 <= pow p); apply/bpow_le; lia.
    have ->: pow p = rnd_p (pow p) by rewrite round_generic //; apply/format_bpow.
    by apply/round_le.
  + apply:(Rle_trans _ (pow p)).
      rewrite Rabs_Ropp Rabs_pos_eq; try lra; apply(Rle_trans _ 4);first lra.
      change(pow 2 <= pow p); apply/bpow_le; lia.
    have ->: pow p = rnd_p (pow p) by rewrite round_generic //; apply/format_bpow.
    by apply/round_le.  
split =>//. 
rewrite /errorDWFP H; ring_simplify.
suff->: rnd_p (xl + sl xh y) = (xl + sl xh y); ring_simplify.
  rewrite TwoSum_correct//; ring.
by rewrite round_generic.
Qed.

(* particular case where (y, xl) may not be a double*)
(* added by AK 8/16/2023 *)
Lemma part_case_ulps  xh xl  y (DWx: double_word xh xl) (Fy : format y) (xh0: xh <> 0) 
                     (xhy : xh + y <> 0):
  ulp y = ulp  xh -> Rabs xl = (ulp  xh) /2 ->
  Rabs (rnd_p (xl + sl xh y)) <= Rabs ( (sh xh y)).
Proof.
move=>  ulpe xlE.
have Fsh:= Fsh;  have Fv:= Fv;  have Fx := Fxl.
case:(DWx)=> [[Fxh Fxl] _].
have cexpE:= (equlpcexp _ _ ulpe).
have pcexpE:  (pow (cexp xh)) = ulp xh by rewrite ulp_neq_0.
move:(refl_equal (xh + y)) (refl_equal xh) (refl_equal y).
rewrite {2 4}Fxh {2 4}Fy cexpE -F2R_plus  Fplus_same_exp.
set Mxh := Ztrunc (mant xh).
set  My := Ztrunc (mant y).
rewrite /F2R /==> sE xhE yE.
have hmxh:= (FLX_mant_le Fxh).
have hmy:= (FLX_mant_le Fy).
rewrite -/Mxh -/My in  hmxh hmy.
move/IZR_le: (hmxh) ; move/IZR_le :(hmy);  rewrite !abs_IZR minus_IZR IZR_Zpower; 
 last lia.
move=> Rmxh  Rmy.
have shE: sh xh y  = rnd_p (IZR (Mxh + My))*(ulp xh).
  by rewrite TwoSum_sumE sE   round_bpow  - cexpE pcexpE .
have slE: sl xh y = (IZR (Mxh + My) - rnd_p (IZR (Mxh + My)))* ulp xh.
  rewrite TwoSum_correct //  shE sE -cexpE   pcexpE; ring.  
have xlsE: xl = (sign xl) * /2 * ulp xh.
  move:xlE.
  case : (Rlt_dec xl 0)=> xl0.
    rewrite /sign  Rlt_bool_true  ?Rabs_left; lra.
  rewrite /sign  Rlt_bool_false  ?Rabs_right; lra.

have  v'E: (xl + sl xh y)= (IZR (Mxh + My) - rnd_p (IZR (Mxh + My))
                      + (sign xl) * /2) * ulp xh.
  rewrite  slE {1}xlsE ; ring.
have vE : v xh y xl = rnd_p ((IZR (Mxh + My) - rnd_p (IZR (Mxh + My))
                      + (sign xl) * /2)) * ulp xh.
  by rewrite  v'E ulp_neq_0  // -round_bpow.
(*ici*)
have Fsxl: format (sign xl  * /2).
  change (format (sign xl  * (pow (-1)))); apply:formatS.
  rewrite /sign; case(Rlt_bool xl 0); try apply/generic_format_opp;
  change (format (pow 0)); apply/generic_format_bpow; rewrite /fexp;lia.


have F1m_2:   format (- / 2).
  by  apply/generic_format_opp; change (format (pow (-1))); apply/format_bpow.
have F1_2:    format ( / 2).
  by change (format (pow (-1))); apply/format_bpow.
have F3: format 3.
  apply:(@ FLX_format_Rabs_Fnum _ (Float two 3 0)).
  rewrite /F2R //=; ring.
  rewrite /=; apply:(Rlt_le_trans _ (pow 2)).
    rewrite Rabs_pos_eq; last lra.
    by change (3 < 4); lra.
  by apply:bpow_le; lia.
pose v' := xl + sl xh y.
have v'E':  v' = /2 * ulp xh \/ v'= -(/2) * ulp xh \/
 (v' = 3/2 * ulp xh  /\ pow p - 1 <= Rabs (rnd_p (IZR (Mxh + My))))
\/ (v' = -(3/2) * ulp xh  /\ pow p - 2 <= Rabs (rnd_p (IZR (Mxh + My)))).
  rewrite /v' v'E.

 case: (Rle_lt_dec  (Rabs (IZR (Mxh + My))) (pow p - 1 ))=> hMs.
    rewrite (round_generic _ _ _ (IZR _)).
      have-> : (IZR (Mxh + My) - IZR (Mxh + My) + sign xl * / 2) = 
                 sign xl * / 2  by ring.
      rewrite /sign; case(Rlt_bool xl 0).
         by right; left; field.
      by left; field. 
(*   format (IZR (Mxh + My)) *)
    pose fs := (Float two (Mxh + My) 0).
    have fsE : IZR (Mxh + My) = F2R fs by rewrite /fs /F2R /= Rmult_1_r.
    by apply: (FLX_format_Rabs_Fnum fsE); rewrite /fs /=; lra.

(* cas  pow p - 1 < Rabs (IZR (Mxh + My)) *)
  have hMs': pow p <=  Rabs (IZR (Mxh + My)).
    rewrite -abs_IZR -IZR_Zpower; last lia.
    apply/IZR_le.
    suff: (radix2 ^ p  -1 < Z.abs (Mxh + My))%Z by lia.
    by apply/ lt_IZR; rewrite abs_IZR minus_IZR IZR_Zpower; last lia.
  case:(Zeven_odd_dec   (Mxh + My))=> [/Zeven_bool_iff Heven | /Zodd_bool_iff  Hodd].
 (* a factoriser *)
   rewrite (round_generic _ _  _ (IZR (Mxh + My))).
      have->: (IZR (Mxh + My) - IZR (Mxh + My) + sign xl * / 2) = 
                 sign xl * / 2  by ring.
      rewrite /sign; case(Rlt_bool xl 0).
        by right; left; field.
      by left; field. 
(*   format (IZR (Mxh + My)) *)
    pose fs := (Float two ((Mxh + My)/2)%Z 1).
    have fsE : IZR (Mxh + My) = F2R fs.
      rewrite /fs /F2R /= -Z2R_beta_even_div_two //   IZR_Zpower_pos /= ; field.
    apply: (FLX_format_Rabs_Fnum fsE); rewrite /fs /=.
    rewrite  -Z2R_beta_even_div_two //  Rabs_mult (Rabs_pos_eq (/2)); last lra.
    suff:Rabs (IZR (Mxh + My)) < 2* pow p by lra.
    rewrite plus_IZR;  apply:(Rle_lt_trans _ _ _ (Rabs_triang _ _)); lra.
(* cas odd *)
  case: (Zeven_ex (Mxh + My))=>M  Me.
  have {} ME : (Mxh + My)%Z = (2 * M + 1)%Z.
    by rewrite Me; rewrite Zeven.Zeven_odd_bool Hodd.
  rewrite ME.
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
    ring_simplify(1 + p - 1)%Z.
    split=>//.
    rewrite bpow_plus; 
    rewrite plus_IZR; apply:(Rle_lt_trans _ _ _ (Rabs_triang _ _)).
     have ->: pow 1 = 2 by [];  lra.
  have cexpf :  (cexp (IZR (2 * M + 1)) = 1)%Z.
    rewrite /cexp /fexp (mag_unique _ _  (1 +p)); first ring.
    split.
      have->:  (1 + p - 1 = p)%Z by ring.
      by rewrite -ME.
    rewrite -ME plus_IZR bpow_plus; apply:(Rle_lt_trans _ _ _ (Rabs_triang _ _)).
    by have ->: pow 1 = 2 by []; lra.
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

  case:(round_DN_or_UP two fexp (Znearest choice) (IZR (2 * M + 1))); 
     rewrite ?rDN ?rUP => ->; rewrite ?Z.mul_add_distr_l !plus_IZR /sign;
     case (Rlt_bool xl 0).
     + have->:  (IZR (2 * M) + 1 - IZR (2 * M) + -1 * / 2) = /2 by field.
       by left.
     + have->: (IZR (2 * M) + 1 - IZR (2 * M) + 1 * / 2) = 3* /2 by field.
       right; right; left; split => //.
        have Hp': pow p <= Rabs (IZR(2*M) + 1).
        refine (Rle_trans _ _ _ _ _ ).  apply hMs'. rewrite ME.
rewrite -plus_IZR ; nra.
        have : pow p <= Rabs (IZR(2*M)) + 1 ; try nra.
              refine (Rle_trans _ _ _ Hp' _ ).  
              refine (Rle_trans _ _ _ (Rabs_triang _ _ ) _ ); rewrite Rabs_R1; nra. 
     + have ->: (IZR (2 * M) + 1 - (IZR (2 * M) + IZR (2 * 1)) + -1 * / 2) = 
             -(3 */2) by rewrite Zmult_1_r; field.
       right; right; right; split => //.

rewrite -plus_IZR Zmult_1_r.
{ 
destruct (Rlt_or_le (IZR (2 * M + 2)) 0).
have Hn:  (IZR (2*M+1) < 0).
refine (Rlt_trans  _ _ _ _ H); lra.
apply Rabs_left in H => //. rewrite H.
rewrite plus_IZR. field_simplify.
have : (pow p  <= -IZR (2 * M)); try nra.
refine (Rle_trans  _ _ _ hMs' _).
rewrite ME.
apply Rabs_left in Hn => //. rewrite Hn; nra.


rewrite Rabs_pos_eq => //.
refine (Rle_trans  _ (pow p) _ _ _); try nra.

destruct (Rlt_or_le (IZR (2 * M + 1)) 0).

refine (Rle_trans  _ _ _ hMs' _); try nra.
rewrite ME.
apply Rabs_le; split; try nra.

destruct (Rlt_or_le (IZR (2 * M + 1)) 0).
apply Rge_le.
refine (Rge_trans _ 0 _ _ _ ); try nra.


refine (Rle_trans  _ (IZR (2 * M)) _ _ _); try nra.
rewrite -opp_IZR. 
apply IZR_le. rewrite Z.opp_add_distr => //. 
Search (IZR _ <= IZR _).

apply Rlt_le. 
Search (_ <= _ <= _ -> Rabs _ <= _).
rewrite ME.
destruct (Rlt_or_le (IZR (2 * M + 1)) 0).
apply Rabs_left in H0 => //. rewrite H0. 
refine (Rle_trans  _ _ _ _ _); apply Rlt_le. 
apply H0.
try nra.
rewrite Rabs_pos_eq => //; try nra.

Search ( _ <= _ - _)%R.
refine (Rle_lt_trans  _ _ _ _ _).

have Hu : forall a b, Rabs (a + b) = Rabs a + Rabs b \/ Rabs (a+b) = Rabs a - Rabs b.
intros.
destruct (Rlt_or_le (a+b) 0).
right.
assert (Rabs (a + b) = - (a + b)) by
apply Rabs_left in H => //. rewrite H0.
destruct (Rlt_or_le b 0).
destruct (Rlt_or_le a 0).


        have Hp': pow p <= Rabs (IZR(2*M) + 2).
        refine (Rle_trans _ _ _ _ _ ).  apply hMs'. rewrite ME.
rewrite -plus_IZR ; nra.
        have : pow p <= Rabs (IZR(2*M)) + 2 ; try nra.
              refine (Rle_trans _ _ _ Hp' _ ).  
              refine (Rle_trans _ _ _ (Rabs_triang _ _ ) _ ); rewrite Rabs_R1; nra. 




        have Hp': pow p <= Rabs (IZR(2*M) + 1).
        refine (Rle_trans _ _ _ _ _ ).  apply hMs'. rewrite ME.
rewrite -plus_IZR ; nra.
refine (Rle_trans _ (pow p) _ _ _). lra.
refine (Rle_trans _ _ _ Hp' _). 
replace (IZR (2 * M) + IZR (2 * 1)) with (IZR (2 * M +2)). 
     case (Req_dec (IZR M) 0); move => H0.
rewrite plus_IZR !mult_IZR H0 Rmult_0_r !Rplus_0_l !Rabs_pos_eq; nra.

assert (0 < IZR M \/ IZR M < 0). lra. destruct H.
rewrite plus_IZR !mult_IZR  !Rabs_pos_eq; nra.

        have : pow p <= Rabs (IZR(2*M)) + 1 ; try nra.
              refine (Rle_trans _ _ _ Hp' _ ).  
              refine (Rle_trans _ _ _ (Rabs_triang _ _ ) _ ); rewrite Rabs_R1; nra. 


       by right; right; right; rewrite -plus_IZR  -ME.  
  have ->: (IZR (2 * M) + 1 - (IZR (2 * M) + IZR (2 * 1)) + 1 * / 2)= -/2 
   by  rewrite Zmult_1_r; field.
  by right; left.
have Fv': format v'.
  by case: v'E'; [move =>-> |case ; [move => ->|case ;[ case ; move=> -> h| 
   case=> -> h]]]; rewrite - pcexpE; apply/formatS=>//; try apply/generic_format_opp; 
    change (format (3 * (pow (-1)))); apply/formatS.
have Mpos:   (1 <= Z.abs (Mxh + My))%Z.
  suff: ((Mxh + My) <> 0)%Z by lia.
  move => hm0; rewrite hm0 Rmult_0_l in sE; lra.
move/IZR_le:(Mpos); rewrite abs_IZR=> Mge1.


suff->: rnd_p (xl + sl xh y) = (xl + sl xh y); ring_simplify.

pose proof DW_TwoSum Fxh Fy.
unfold double_word in H.


2: by rewrite round_generic. 
fold v'.
destruct v'E'. 
{ rewrite H0.
refine (Rle_trans _ _ _ _ (roundN_plus_ulp _ _ _) ) => //.
rewrite Rabs_pos_eq.
refine (Rle_trans _  _ _ (Rmax_l _ (ulp y / 2)) _).
apply Rle_max_compat_r; nra.
apply Rmult_le_pos; [nra| apply ulp_ge_0]. } 
destruct H0.
{ rewrite H0.
refine (Rle_trans _ _ _ _ (roundN_plus_ulp _ _ _) ) => //.
refine (Rle_trans _  (Rabs ( / 2 * ulp xh)) _ _ _).
apply Req_le.
replace (-/2*ulp xh) with (-(/2*ulp xh)) by nra.
rewrite Rabs_Ropp => //.
rewrite Rabs_pos_eq.
refine (Rle_trans _  _ _ (Rmax_l _ (ulp y / 2)) _).
apply Rle_max_compat_r; nra.
apply Rmult_le_pos; [nra| apply ulp_ge_0]. } 
destruct H0.
{ destruct H0 as (A & B).
rewrite shE. 
rewrite A Rabs_mult.
Search (round _ _ _ IZR.
eapply Rle_trans.
2: rewrite Rabs_mult.
2: 
apply Rmult_le_compat_r. 
apply Rle_refl. 
apply Rabs_pos.
eapply Rle_trans.
2: apply B.
eapply Rle_trans.
2: apply bpow_le.
2: apply Hp3.
rewrite Rabs_pos_eq.
simpl. nra. nra. 


admit. }  (* formatS *) admit. 


Admitted.


Fact  FLX_round_N_eq0  (x : R): rnd_p  x = 0 -> x = 0.
Proof.
move=> rnd0.
case:(Req_dec x 0 )=> // xn0.
suff: rnd_p x <> 0 by [].
by apply: round_neq_0_negligible_exp => //; rewrite negligible_exp_FLX.
Qed.

(* Lemma  boundDWFP_ge_0: 0 <= (pow (1 - 2*p)%Z) /(1 - (pow (1 -p)%Z)). *)
(* Proof. *)
(* have ppow := bpow_gt_0 two (1 -2*p). *)
(* have ppo1 :  pow (1 - p) < 1. *)
(*   have -> : (1 - p = -(p -1))%Z by ring. *)
(*   apply:(bpow_lt_1  two). *)
(*   by lia. *)
(*  have ppo11 : 0 < (1 - pow (1 -  p)) by lra. *)
(* rewrite /Rdiv. *)
(* apply: Rmult_le_pos; try lra. *)
(* by apply: Rlt_le; apply: Rinv_0_lt_compat. *)
(* Qed. *)



Fact  DWPlusFP_Asym( xh xl y:R):

  (DWPlusFP   (-xh) (-xl)(-y) ) =  pair_opp  (DWPlusFP  xh xl y).
Proof.
  by rewrite /DWPlusFP /TwoSum_sum  TwoSum_asym vAsym /pair_opp [LHS]/= Fast2Sum_asym; try apply/rnd_p_sym/choiceP.
Qed.

Fact  DWPlusFPS  xh xl y e (Fxh :format xh) (Fy: format y):

    (DWPlusFP    (xh* pow e) (xl* pow e) (y * pow e)) =
    (fst (DWPlusFP  xh xl y)  * pow e, (snd (DWPlusFP  xh xl y) * pow e)).
Proof.
rewrite /DWPlusFP /TwoSum_sum TwoSumS // vS //  [LHS]/=   Fast2SumS //; 
 by  apply:generic_format_round.             
Qed.

Fact DWPlusFP0f xh xl y  (DWx: double_word xh xl) (Fy : format y) : xh = 0 -> 
                                            DWPlusFP xh xl y = (y,0).
Proof.
move=> xh0; rewrite xh0 /DWPlusFP /=.
case:(DWx)=>[[Fxh Fxl] xE].
have xl0: xl = 0 by move:xE;  rewrite xh0 Rplus_0_l round_generic.
rewrite xl0 TwoSum_correct // ; last apply:generic_format_0.
rewrite 
  TwoSum_sumE Rplus_0_l round_generic //.
have ->: y - y = 0 by ring.
by rewrite Rplus_0_r round_0 Fast2Sumf0.
Qed.


Fact  DWPlusFPC  xh xl y  (Fxh :format xh) (Fy: format y):
    (DWPlusFP    xh xl y) =(DWPlusFP    y xl xh).
Proof.
   rewrite /DWPlusFP vC //.
have ->: (sh y xh) = sh xh y by rewrite TwoSum_sumE Rplus_comm.
by [].
Qed.

Fact F2Sum_correct_DW' a b : Fast2Sum_correct  p choice a b -> 
                 double_word (fst (Fast2Sum p choice a b)) (snd (Fast2Sum p choice a b)).
Proof.
move => h.
by case:(F2Sum_correct_DW _ h) =>// F1 [F2 hE].
Qed.

Fact DW_sym a b : double_word a b -> double_word (-a) (-b).
Proof.
move=>[[Fa Fb] abE]; split; [split|]; try apply:generic_format_opp=>//.
have ->: (- a + - b) = - (a + b) by ring.
by rewrite {1}abE ZNE round_NE_opp; ring.
Qed.

Fact DW_S a b e : double_word a b -> double_word (a* (pow e)) (b* (pow e)).
Proof.
move=>[[Fa Fb] abE]; split; [split|]; try apply:formatS => //.
by rewrite -Rmult_plus_distr_r round_bpow {1}abE.
Qed.




Lemma pred_1 : 1 -u = pred two fexp 1.
Proof.
have is_pow1: is_pow two 1 by exists 0%Z;rewrite Rabs_pos_eq //;lra.
have F1: format 1 by apply:is_pow_generic ; try lra.
rewrite POSpow_pred //; last lra.
congr Rminus.
have -> : (1 / IZR radix2) = 1/2 by [].
rewrite /Rdiv; have->: /2 = pow (-1) by [].
rewrite ulp_FLX_exact_shift.
rewrite /u u_ulp1; have ->: pow (-1) = /2 by [].
ring.
Qed.

Lemma  rulp2p' x y xl: Rabs xl <= /2  * ulp x -> ulp x < ulp y ->  
                       x <> 0 -> y <> 0 -> format y ->
                       rnd_p (y + xl) = y.
Proof.
move=> rxlu uxuy xn0 yn0 Fy.
have h: Rabs xl <= / 4 * ulp y.
  apply:(Rle_trans _ (/ 2 * ulp x))=>//.
  suff: ulp x <= / 2 * ulp y by lra.
  move: uxuy;  rewrite !ulp_neq_0 //.
  move/lt_bpow/Zlt_le_succ; rewrite -Z.add_1_r.
  move/(bpow_le two); rewrite bpow_plus.
  have ->: pow 1 = 2 by [].
  lra.
case:(is_pow_dec two y)=> hy.
  by rewrite rxpu2pow.
by rewrite rulp2p //; lra.
Qed.

(* rewrite relative_error_DWFPC //DWPlusFPC // ; split; case:  (Hwlog xh y)=>//; try lra. *)
Notation  DWFP_Plus_correct  xh xl y :=  (relative_errorDWFP xh xl y<= 2 * u^2 /\
    (double_word (fst (DWPlusFP xh xl y) )(snd (DWPlusFP xh xl y)))).

Theorem  DWPlusFP_correct ( xh xl y  : R) 
         (Fy : format y) 
         (DWx: double_word xh xl): 
 DWFP_Plus_correct  xh xl y.
         (* (relative_errorDWFP xh xl y)<= 2*u^2 /\ *)
         (* (double_word (fst (DWPlusFP xh xl y) )(snd (DWPlusFP xh xl y) )). *)
Proof.
have rn_sym:= (rnd_p_sym _ _ choiceP).
have boundDWFP_ge_0 : 0 <= 2*u^2 by rewrite /u; move: (bpow_ge_0 two (-p)); nra.
case:(DWx) =>[[Fxh Fxl] xE].
case:(Req_dec xh 0)=> hxh0.
   split; first by rewrite ?null_xh_rel.
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
    move=>h. move /bpow_inj => h2.
    have {} h2:  ((ey + 1 ) = mag radix2 xh )%Z. by lia.
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



Lemma DWPlusFP_baux (Hp4: (4 <= p)%Z): (pow (1 - 2*p)%Z) /(1 - (pow (1 - p)%Z)) 
                     <= 2*u^2 + 5*u^3.
Proof.  
clear  - Hp4.
have hlt1: pow(1 -p) <1.
  have ->: (1 - p = -(p -1))%Z by ring.
  apply:bpow_lt_1; lia.
apply:(Rmult_le_reg_r ((1 - pow (1 - p)))); first lra.
rewrite /Rdiv Rmult_assoc Rinv_l ?Rmult_1_r; last lra.
have ->:  pow (1 - 2 * p)  =  2 * u ^ 2.
  have-> : ((1 - 2 * p) = 1 + -p + -p)%Z by ring.
  rewrite !bpow_plus -/u; have ->: 2 = pow 1 by [].
  by ring.
have ->: pow (1 - p) = 2 * u.
  have ->: 2 = pow 1 by [].
 by rewrite bpow_plus /u.
ring_simplify.
suff: 0<= (1  - 10 * u) * u^3 by lra.
(* clear - Hp4. *)
have upos : 0 < u by apply:bpow_gt_0.
apply: Rmult_le_pos; last nra.
suff: u <= /10 by lra.
apply:(Rle_trans _ (/16)); try lra.
change (pow (-p) <= pow (-4)); apply/bpow_le; lia.
Qed.

Theorem  DWPlusFP_bound ( xh xl y  : R) 
         (Fy : format y) 
         (DWx: double_word xh xl): 
         (relative_errorDWFP xh xl y)<= 2*u^2 .
Proof.
by case:(DWPlusFP_correct Fy DWx).
Qed.







End DWPlusFP.


Section DWPlusDW_Pre.
Hypothesis Hp3 : (3 <= p)%Z.


Variables xh xl yh yl : R.
Notation  x := (xh + xl)%R.
Notation  y := (yh + yl).


Notation  sh := (TwoSum_sum xh yh).
Notation  sl :=  (TwoSum_err xh yh).
Notation  th := (TwoSum_sum xl yl).
Notation  tl :=  (TwoSum_err xl yl).
Notation c := (rnd_p (sl + th)).
Notation vh := (F2Sum_sum sh c).
Notation vl :=  (F2Sum_err sh c).
Notation w := (rnd_p (tl + vl)).
Notation zh :=  (F2Sum_sum vh w).
Notation zl :=  (F2Sum_err vh w).
Hypothesis xDW: double_word xh xl.
Hypothesis yDW: double_word yh yl.

Notation Fxh := (Fxh xDW).
Notation Fxl := (Fxl xDW).
Fact Fyh : format yh. Proof. by case:yDW;case. Qed.
Fact Fyl : format yl. Proof. by case:yDW;case. Qed.
Notation Fsh := (Fsh yh xh).
Notation Fsl := (Fsl yh xh).
Fact Fth : format th. Proof. by apply: generic_format_round. Qed.
Fact Ftl : format tl. Proof. by apply: generic_format_round. Qed.
Fact Fc : format c. Proof. apply: generic_format_round. Qed.
Fact Fvh : format vh. Proof. by apply: generic_format_round. Qed.
Fact Fvl : format vl. Proof. by apply: generic_format_round. Qed.
Fact Fw : format w. Proof. apply: generic_format_round. Qed.
Fact Fzh : format zh. Proof. by apply: generic_format_round. Qed.
Fact Fzl : format zl. Proof. by apply: generic_format_round. Qed.

Notation e1 := ((sl + th) - c).
Notation e2 := ((tl + vl) - w).


Fact errorDWDWe_abs: (Rabs c <= Rabs sh) -> (Rabs w <= Rabs vh)
                -> (x + y) - (zh + zl)= e1 + e2.
Proof.
have Fsh: format sh by apply: generic_format_round. 
have Fvh := Fvh; have Fw := Fw;  have Fc := Fc.
have Fxh:= Fxh;  have Fyh := Fyh;  have Fxl := Fxl; have Fyl := Fyl.
have rn_sym:= (rnd_p_sym _ _ choiceP).
move=>*;  rewrite (@F2Sum_correct_abs   _ Hp  choice  _ _ vh w) // (@F2Sum_correct_abs  _ _ choice _ _ sh c) //.
have->: x + y = xh + yh + (xl + yl) by ring.
have {1}-> : xh + yh = sh + sl.
  rewrite TwoSum_correct //= /sh /=;    ring.
have {1}->: xl + yl = th + tl.
   rewrite  TwoSum_correct  //= /th  /=  ;ring.
lra.
Qed.


Definition relative_errorDWDW := (Rabs (((zh + zl) - (x  + y))/ (x  + y))).
Definition errorDWDW := (x + y) - (zh + zl).


Lemma rel_errorDWDWe_abs: (Rabs c <= Rabs sh) -> (Rabs w <= Rabs vh)
                ->relative_errorDWDW  =  Rabs((e1 + e2)/(x + y)).
Proof.
move=> *.
rewrite /relative_errorDWDW -errorDWDWe_abs //.
have ->: (zh + zl - (x + y)) / (x + y) = -((x + y - (zh + zl)) / (x + y)) by lra.
by rewrite Rabs_Ropp.
Qed.


Lemma  boundDWDW_ge_0: 0 <= (3 * u^2) / (1 - 4 * u).
Proof.
have nump: 0 <= 3 * u ^ 2 by move:(pow2_ge_0 u); lra.
have denpos: 0 < (1 - 4 * u).
  suff: 4*u < 1 by lra.
  have ->:  4 = pow 2 by [].
  rewrite -bpow_plus.
  have ->: ((2 + - p) = - (p - 2))%Z by lia.
  apply:(bpow_lt_1 two).
  by move: Hp3; lia.
by apply:Rmult_le_pos =>//; move/Rinv_0_lt_compat:  denpos; lra.
Qed.

Lemma relative_errorDWDWxh0 : xh = 0 -> relative_errorDWDW= 0.
Proof.
have Fxh:= Fxh. have Fyh := Fyh. have Fxl := Fxl. have Fyl := Fyl.
move=> xh0.
have she: sh = yh.
   by rewrite  xh0 TwoSum_sumE Rplus_0_l round_generic //.
have sl0: sl = 0.
  rewrite TwoSum_correct //= TwoSum_sumE   xh0 Rplus_0_l round_generic //;
    ring.
have xl0: xl = 0.
  by case:xDW=> _; rewrite xh0 Rplus_0_l round_generic //.
have the: th = yl.
   by rewrite  xl0 TwoSum_sumE   Rplus_0_l round_generic //.
have e10:  e1 = 0 by rewrite sl0 the Rplus_0_l round_generic //; ring.
have tl0: tl = 0 by rewrite  TwoSum_correct  //=  TwoSum_sumE xl0 Rplus_0_l
    round_generic // ;  ring.
have e20:  e2 = 0.
  rewrite tl0 sl0 xh0 !Rplus_0_l the round_generic //. 
  rewrite !round_generic //; first by ring.
  by apply:generic_format_round.
rewrite /relative_errorDWDW Rabs0//.
suff-> : (zh + zl - (x + y))= 0 by lra.
have -> : x = 0 by rewrite xh0 xl0 ;ring. 
rewrite Rplus_0_l.
have ce : c = yl by rewrite sl0 the Rplus_0_l round_generic.
have vhe: vh = yh  by rewrite ce she; case: yDW => _ {2}->.
have vle: vl = yl.
  rewrite  ce she.
  case: yDW => _ yhE.
    by rewrite /Fast2Sum /F2SumFLX.Fast2Sum -yhE /= (Rminus_diag_eq yh) // round_0 Rminus_0_r round_generic.
have we : w = yl  by rewrite tl0 vle Rplus_0_l round_generic.
rewrite vhe we  /Fast2Sum /=.
case: yDW => _ <-.
by rewrite (Rminus_diag_eq yh) // round_0 Rminus_0_r round_generic //;ring.
Qed.

Notation relative_error_DWFP :=   (relative_errorDWFP  xh yh yl).

Hypothesis  xyn0 : xh + xl + (yh + yl) <> 0.
Hypothesis   xhy : Rabs yh <= Rabs xh.
Hypothesis   s0 : xh + yh <> 0.
Hypothesis  x0 : xh <> 0.
Hypothesis  xhpos : 0 < xh.
Hypothesis  xh1 : 1 <= xh.
Hypothesis  xh2 : xh <= 2 - 2 * u.
Notation ulp := (ulp two fexp).

Theorem  DWPlusDW_relerr_bound_pre : (double_word zh zl) /\
    relative_errorDWDW <=  (3 * u^2) / (1 - 4 * u).
Proof.
have rn_sym:= (rnd_p_sym _ _ choiceP).
have upos : 0 < u by apply:bpow_gt_0.
have ulpxh: ulp xh = 2 * u.
  have->: 2 = pow 1 by [].
  rewrite ulp_neq_0 // /cexp /fexp  bpow_plus /u (mag_unique_pos _ _ 1) //= IZR_Zpower_pos /=; lra.
have xlu: Rabs xl <= u.
  move:(dw_ulp xDW);rewrite  -/ulp ulpxh; lra.
have ylu: Rabs yl <= u. 
  apply:(Rle_trans _ (/ 2 * (ulp yh))); first by apply:(dw_ulp yDW).
  apply:(Rle_trans _ (/ 2 * (ulp xh))); try lra.
  by apply:Rmult_le_compat_l; try lra; apply:ulp_le.
have shn0: rnd_p (xh + yh) <> 0.
  by move=> sh0; apply s0; apply: (FLX_round_N_eq0  sh0).
case:(xDW)=>[[Fxh Fxl] hx].  
case:(yDW)=>[[Fyh Fyl] hy].
(* xh is a multiple of 2u *)
  move:(Fxh); rewrite /generic_format.
set fx:= {| Fnum := Ztrunc (mant xh); Fexp := cexp xh |}.
rewrite /fx /F2R /cexp (mag_unique_pos _ _ 1); last first.
  have ->: (1 -1)%Z = 0%Z by ring.
  by move: xh2; rewrite /u; move: (bpow_gt_0 two (-p)); rewrite /= IZR_Zpower_pos /=; lra.
  move => xhe.
  have {} xhe: xh = IZR ( Ztrunc (mant xh)) * pow (1 -p) by [].
  have {} xhe : xh = IZR ( Ztrunc (mant xh)) * (2 * u) .
    by rewrite {1}xhe  bpow_plus /= -/u -Rmult_assoc.
  move:xhy; 
    rewrite (Rabs_pos_eq xh ); last lra.
  move=> xhy'.
  
case/Rabs_le_inv: (xhy')=> xhyh yhxh.
(* set sh := (rnd_p (xh + yh)); set sl := (TwoSum_err xh yh). *)
(* pose th :=  (rnd_p( xl + yl)). *)
(* pose tl :=  (TwoSum_err xl yl). *)
have thu: Rabs th <= 2 * u.
  rewrite   TwoSum_sumE ZNE -round_NE_abs -ZNE.
  have -> : 2 * u = rnd_p (pow 1 * u).
    rewrite round_generic // /u -bpow_plus; apply: generic_format_bpow.
    rewrite /fexp; move : Hp; lia.
  apply: round_le; apply:(Rle_trans _ (Rabs xl + Rabs yl)) => /=; first by apply:Rabs_triang.
  rewrite IZR_Zpower_pos /=; lra.
have tlu2: Rabs tl <= u * u.
  rewrite  TwoSum_correct  //=  -Rabs_Ropp Ropp_minus_distr.
  apply:(Rle_trans _ (/ 2 * pow (- p) * pow (1 -p))).
    apply: error_le_half_ulp'; first exact Hp.
     apply:(Rle_trans _ (Rabs xl + Rabs yl)); first by apply:Rabs_triang.
     rewrite bpow_plus /= -/u IZR_Zpower_pos /=; lra.
  rewrite bpow_plus /= /u IZR_Zpower_pos /=; lra.
case: (Rle_lt_dec yh (-xh/2) )=> hyx.
  have she:  sh = xh + yh.
    rewrite  TwoSum_sumE  round_generic //.
    have ->:  (xh + yh ) = (xh - (- yh)) by ring.
    apply: sterbenz'; (try apply:generic_format_opp) =>//.
    by split; lra.
  have sl0: sl = 0 by  rewrite TwoSum_correct //  she; ring.  (* rewrite sl0 Rplus_0_l (round_round Hp). *)
  (* set  c := (rnd_p (sl + th)). *)
  have ce: c = th 
    by rewrite  sl0 Rplus_0_l round_generic /th // ; apply:  generic_format_round.
(* need boolean comparison here ... *)
  pose sigma := if  Rle_dec yh (-1) is left _ then 2%Z else 1%Z.
  have sigmae: sigma = 1%Z \/ sigma = 2%Z.
    by rewrite /sigma; case:(Rle_dec yh (-1)); [right|left].
  have sigma2: yh <= -1 -> IZR sigma = 2.
      by move=> hy1 ; rewrite /sigma; case:(Rle_dec yh (-1)).        
  have sigma1: ~ yh <= -1 -> IZR sigma = 1.
      by move=> hy1 ; rewrite /sigma; case:(Rle_dec yh (-1)).      
  have lnb_yh: (pow (mag radix2 yh)) = IZR sigma.
    case:(Rle_dec yh (-1))=> hy1; [rewrite sigma2 //|rewrite sigma1 //].
    rewrite(mag_unique two yh 1) //= ; first last.
      by rewrite  Rabs_left1 /= ?IZR_Zpower_pos /=; try lra; split;lra. 
    rewrite(mag_unique two yh 0) //=.
    by rewrite  Rabs_left1 /= ?IZR_Zpower_pos /=; try lra; split;lra.
  have ylusig: Rabs yl <= IZR sigma /2 * u.
    move:(dw_ulp yDW).
    rewrite /u u_ulp1 !ulp_neq_0; try lra; rewrite /cexp /fexp.
    rewrite !bpow_plus /= lnb_yh.
    by rewrite /sigma (mag_unique_pos two 1 1)/= IZR_Zpower_pos /=;lra.
  have h6_1 : -xh < yh <= (1 - IZR sigma) + xh/2 * (IZR sigma -2).
    by case:(Rle_dec yh (-1))=> hy1; [rewrite sigma2 //|rewrite sigma1 //]; lra.
  have spos: 0 < xh+yh  by lra.
  have h6_2: xh+yh  <= 1 + IZR sigma * (xh/2 -1)<= 1 - IZR sigma * u.
    by case:(Rle_dec yh (-1))=> hy1; [rewrite sigma2 //|rewrite sigma1 //]; lra.
  have xh_mul_su: exists z, xh = IZR z * (IZR sigma * u).
    case:sigmae=> ->.
      exists ((Fnum fx) * 2)%Z.
      rewrite xhe mult_IZR /= /mant; ring.
    by exists (Fnum fx); rewrite xhe /= /mant; ring.      
(* yh is a multiple of sigma*u *)  
  have yh_mul_su: exists z, yh = IZR z * (IZR sigma * u).
    move:(Fyh); rewrite /generic_format.
    set fy:= {| Fnum := Ztrunc (mant yh); Fexp := cexp yh |}.
    rewrite /F2R  => yhe.
    have fye: Fexp fy = (mag two yh  - p)%Z by rewrite /fy /= /cexp /fexp.
    exists (Fnum fy).
    rewrite yhe fye bpow_plus -/u.
    suff -> : (pow (mag radix2 yh)) = IZR sigma by ring.
    case:(Rle_dec yh (-1))=> hy1; [rewrite sigma2 //|rewrite sigma1 //].
      rewrite(mag_unique two yh 1) //= ; first last.
      by rewrite  Rabs_left1 /= ?IZR_Zpower_pos /=; try lra; split;lra.
    rewrite(mag_unique two yh 0) //=; first last.
    by rewrite  Rabs_left1 /= ?IZR_Zpower_pos /= ; try lra; split;lra.
  have h6: IZR sigma * u <= sh <= 1 - IZR sigma * u. (* 6 *)
    split;try  lra.
    move:spos; rewrite she.
    case: xh_mul_su => xz ->; case: yh_mul_su => yz ->.
    have -> : IZR xz * (IZR sigma * u) + IZR yz * (IZR sigma * u) = (IZR xz +  IZR yz) * (IZR sigma * u) by ring.
    have supos:0 < (IZR sigma * u) by case:  sigmae => -> /=  ; lra.
    move=> hpos.
    suff h1: 1 <= (IZR xz + IZR yz).
      rewrite -{1} (Rmult_1_l (IZR sigma * u)).
      by apply: Rmult_le_compat_r; lra.
    have hinv: 0< /(IZR sigma * u) by apply: Rinv_0_lt_compat.
    move:(Rmult_lt_0_compat _ (/(IZR sigma * u)) hpos hinv).
    rewrite Rmult_assoc Rinv_r;try lra.
    rewrite Rmult_1_r -plus_IZR.
    (* have ->: 0 = IZR 0 by [].*)
    change 1 with (IZR 1).
    by move/lt_IZR => ?; apply: IZR_le; lia.
  have sle: Rabs (xl + yl) <= (1 + IZR sigma / 2) * u.
    apply:(Rle_trans _  (Rabs xl + Rabs yl)).
      by apply: Rabs_triang.
    rewrite /=; lra.
  have thle:Rabs th <= (1 + IZR sigma/2) * u.
    apply:abs_round_le_generic =>//.
    have ->: (1 + IZR sigma / 2) * u = (2 + IZR sigma ) * pow (-1 -p).
      by rewrite /u bpow_plus /= IZR_Zpower_pos /= ; lra.
    apply:formatS.
    case: sigmae=> ->; [apply: (generic_format_F2R' _ _ _ (Float _  (2 + 1)  (0))) |
      apply: (generic_format_F2R' _ _ _ (Float _  (2 + 2)  (0)))]; rewrite /F2R /=; try lra;
      move=> _; rewrite /= /cexp /fexp.
      rewrite (mag_unique_pos two (2 + 1) 2); first by lia.
      rewrite /= ?IZR_Zpower_pos /=;  lra.
    rewrite (mag_unique_pos two (2 + 2) 3); first by lia.
    by rewrite /= ?IZR_Zpower_pos /=; lra.
  have Fsh: format sh by apply : generic_format_round.
  case: (Req_dec (rnd_p (xl + yl))  0)=>[th0|th0].
    have xlyl0: xl + yl = 0 by move/ FLX_round_N_eq0: th0.
    have tl0: tl = 0 .
    by rewrite TwoSum_correct // TwoSum_sumE th0 xlyl0 ; ring.
    rewrite /relative_errorDWDW.
    suff zE: (zh + zl - (x + y)) = 0. 
    rewrite zE Rabs_mult Rabs0 // Rmult_0_l; split; last by    exact:  boundDWDW_ge_0.  
    split; [split; apply:generic_format_round|].
      have-> : zh+zl = x + y by lra.
 rewrite sl0 !(Rplus_0_l, Rminus_0_r, th0, round_round) // Fast2Sumf0 //= Rplus_0_r tl0 round_0 Rplus_0_r (round_generic _ _ _ sh) //.
suff->: x + y = xh + yh by [].
lra.

     rewrite sl0 !(Rplus_0_l, Rminus_0_r, th0, round_round) // Fast2Sumf0 //= Rplus_0_r tl0 round_0 Rplus_0_r (round_generic _ _ _ sh) //

             ( Rminus_diag_eq sh)// round_0 Rminus_0_r round_0 she;lra.


  have {} th0 : th <> 0 by rewrite /th  //.
  case:h6 => h61 h62.
  have hcexp :(cexp th <= cexp sh)%Z.
    have: Rabs th < bpow two  (-p + sigma ).
      rewrite bpow_plus -/u /=.
      apply:(Rle_lt_trans _ ((1 + IZR sigma / 2) * u))=>//.
      by case:sigmae=> ->; rewrite  /= IZR_Zpower_pos /=; lra.
    move/mag_le_bpow.
    move/(_ th0)=> h1.
    move: h61.
    have -> : IZR sigma = pow (sigma - 1)%Z.
      by  case:sigmae=> ->.
    rewrite -(Rabs_pos_eq sh) /u; try lra.
    rewrite -bpow_plus.
    have -> : (sigma - 1 + - p)%Z = (-p + sigma -1)%Z by ring.
    move/mag_ge_bpow=> h2.
    by rewrite /cexp /fexp Rabs_pos_eq; try lra; try lia.
  have h1: vh + vl = sh + c.
    rewrite  F2Sum_correct_cexp //=; try apply: generic_format_round.
      ring.
    by rewrite ce.
  have h2: vh + vl = x + y -tl.
    rewrite h1 she ce  TwoSum_correct  // ; ring.
  have: Rabs (sh + th) <= 1 + u/2.
    apply: (Rle_trans _ (Rabs sh + Rabs th)).
      exact: Rabs_triang.
    by rewrite Rabs_pos_eq ; lra.
  move=> hst.
  have vh1: Rabs vh <= 1.
    rewrite /vh ZNE -round_NE_abs -ZNE ce.
    rewrite -[X in _ <= X] r1pu2.
    by apply:round_le.
  have hvl: Rabs vl <= u/2.
    case: (Rle_lt_dec (Rabs (sh + th)) 1).
      have ->: 1 = pow 0 by [].
      move/(error_le_half_ulp' Hp choice).
      have ->: (rnd_p (sh + th) - (sh + th)) = - vl.
      move: h1 ; rewrite /= ce; lra.
      
      by rewrite Rabs_Ropp /u /=; lra.
    move/Rlt_le=> h3.
    have: rnd_p 1 <= rnd_p (Rabs (sh + th)).
      by apply:round_le.
    rewrite ZNE round_NE_abs  -ZNE.
    have <-: 1 = rnd_p 1.
      rewrite round_generic //.
      change 1 with (pow 0%Z).
      apply:generic_format_bpow.
      by rewrite Zplus_0_l /fexp; move:Hp; lia.
    have-> :  (rnd_p (sh + th))= vh by rewrite /vh  ce.
    move=> h4.
    have : Rabs vh = 1 by lra.
    move=> hvh1.
    case/Rabs_le_inv: hst.
    case/Rabs_ge_inv: h3.
      move=> g1 g2 _.
      move:hvh1.
      rewrite -{1}(Rabs_pos_eq 1); try lra.
      case/ Rabs_eq_Rabs.
        suff: vh <= 0 by lra.
        rewrite /vh  ce.
        have ->: 0 = rnd_p 0 by rewrite round_0.
        by apply:round_le; lra.
      move=> v1.
      have ->: vl = sh + th -vh.
      rewrite -{2}ce; lra.
      rewrite v1.
      by apply: Rabs_le; lra.
    move=> g1 _ g2.
    move:hvh1.
    rewrite -{1}(Rabs_pos_eq 1); try lra.
    case/ Rabs_eq_Rabs; last first.
      suff: 0<= vh  by lra.
      rewrite   ce.
      have ->: 0 = rnd_p 0 by rewrite round_0.
      by apply:round_le; lra.
    move=> v1.
    have ->: vl = sh + th -vh by rewrite -{2}ce ; lra.
    rewrite v1.
    by apply: Rabs_le;lra.
  have h8_1:  Rabs e2 <= /2 * (ulp (tl + vl)).
    rewrite -Rabs_Ropp.
    have->: - (tl + vl - rnd_p (tl + vl))= ( rnd_p (tl + vl) - (tl + vl)) by ring.
    by apply: error_le_half_ulp.
  have h8 : Rabs e2 <= (u^2)/2.
    apply:(Rle_trans _ (/2 * ( ulp (tl + vl)))) =>//.
    suff: ulp (tl + vl) <= u ^ 2 by lra.
    rewrite -ulp_abs -/ulp.
    apply:(Rle_trans _ (ulp (Rabs tl + Rabs vl))).
      by apply:ulp_le_pos; try apply:Rabs_pos; apply: Rabs_triang.
    apply:(Rle_trans _ (ulp  (u^2 + u/2))).
      apply:ulp_le_pos; try apply:Rabs_pos; try lra.
      by move:(Rabs_pos tl) (Rabs_pos vl); lra.
    suff : ulp  (u ^ 2 + u / 2) <= u ^ 2 by lra.
    rewrite  ulp_neq_0.
      rewrite /cexp /fexp.
      set ln:= ((mag radix2 (u ^ 2 + u / 2)))%Z.
      rewrite /u bpow_plus /=.
      suff->:  pow ln = pow (- p) by lra.
      move:(mag_unique_pos two (u^2 + u/2) (-p)).
      rewrite /ln => -> //.
      split.
        suff:  pow (- p - 1) =  u / 2 by move:(pow2_ge_0 u); lra.
        by rewrite bpow_plus /u .
      rewrite /u /Rdiv.
      have->: /2 = pow (-1) by [].
      have->:  pow (- p) ^ 2 + pow (- p) * pow (-1) =  pow (- p) * (pow (- p) + (pow (-1))) 
        by ring.
      have: (pow (- p) + pow (-1)) < 1.
        apply:(Rmult_lt_reg_l  (pow (p))).
          by apply:bpow_gt_0.
        rewrite Rmult_plus_distr_l -!bpow_plus.
        apply:(Rlt_le_trans _ (pow (p -1) + pow (p -1))).
          rewrite  /Zminus /=.
          apply:Rplus_lt_compat_r.
          apply:bpow_lt.
          by move:Hp; lia.
        rewrite -double.
        have ->: 2 = pow 1 by [].
        rewrite -bpow_plus.
        ring_simplify.
        have->: (1 + (p -1))%Z = p by ring.
        by lra.
      by move/(Rmult_lt_compat_l (pow (-p))_ _  (bpow_gt_0 two (-p))); lra.
    rewrite /Rdiv /u /=.
    have->: /2 = pow (-1) by [].
    rewrite Rmult_1_r -!bpow_plus.
    by move: (bpow_gt_0 two (- p + - p) ) (bpow_gt_0 two (- p + -1)); lra.
(* 0 <= x + y *)
  have xypos: 0 <= x + y.
    case:(Rle_lt_dec 0 (x + y))=>// hxy.
    have {} hxy: x <= -y by lra.
    have: rnd_p (xh + xl) <= rnd_p(- (yh + yl)) by apply: round_le.
    by rewrite -hx ZNE round_NE_opp -ZNE -hy; lra.
  have:  Rabs e2 <= /2 * ulp ( /2 *ulp (xl + yl) + /2* ulp ((x + y) + /2* ulp (xl + yl))).
    apply:(Rle_trans _  (/ 2 * ulp (tl + vl)))=>//.
    apply: Rmult_le_compat_l; try lra.
    apply: ulp_le.
    rewrite [X in _ <= X]Rabs_pos_eq; last first.
      rewrite -(Rplus_0_l 0); apply: Rplus_le_compat;
        by rewrite -(Rmult_0_r (/2)); apply: Rmult_le_compat; try lra; apply: ulp_ge_0.
    apply:(Rle_trans _ ((Rabs tl)+ Rabs vl)); try apply: Rabs_triang.
    apply:Rplus_le_compat.
      by rewrite /tl; apply: TwoSum_err_bound.
      have Fth: format th by apply : generic_format_round.
      have: Rabs (F2Sum_err sh th )  <= /2 * (ulp  (sh  + th)).
      rewrite F2Sum_correct_cexp /Fast2Sum //=.
      rewrite -Ropp_minus_distr Rabs_Ropp;  apply: error_le_half_ulp.
    have shth: sh + th = x + y + -tl.
      by rewrite she  TwoSum_correct  //; ring.
    rewrite -{1}ce shth.
    move/(Rle_trans _ _ (/ 2 * ulp (x + y + / 2 * ulp (xl + yl)))).
    apply.
    apply:Rmult_le_compat_l; try lra.
    apply:ulp_le.
    apply:(Rle_trans _ ((Rabs (x + y))+ (Rabs (-tl)))) ; first by apply:Rabs_triang.
    rewrite [X in _ <= X] Rabs_pos_eq.
      apply:Rplus_le_compat.
        by rewrite Rabs_pos_eq //; lra.
      by rewrite Rabs_Ropp /tl; apply: TwoSum_err_bound.
    rewrite -(Rplus_0_l 0); apply:Rplus_le_compat=>//.
    move:(ulp_ge_0 two fexp (xl + yl)).
    by rewrite /ulp; lra.
  move => h9.
  have husigma: ulp (IZR sigma * u) = 2 * IZR sigma * u^2.
    rewrite  ulp_neq_0.
      rewrite /cexp /fexp bpow_plus -/u.
      rewrite /= Rmult_1_r -Rmult_assoc.
      apply: Rmult_eq_compat_r.
      case:sigmae => -> /=.
        rewrite Rmult_1_l  (mag_unique_pos two u (-p +1)%Z).
          by rewrite /u bpow_plus /= ?IZR_Zpower_pos /= ; lra.
        rewrite /u; split.
          by apply: bpow_le; lia.
        by apply: bpow_lt; lia.
      rewrite (mag_unique_pos two (2 * u) (-p +2)%Z).
        by rewrite /u bpow_plus /= IZR_Zpower_pos /= ; lra.
      rewrite /u !bpow_plus /=; split.
        rewrite ?IZR_Zpower_pos /=; lra.
      by rewrite -/u IZR_Zpower_pos /=; lra.
    by case:sigmae => -> /=; lra.
  case: (Req_dec (sh + th) 0)=> shth0.
    have vh0: vh = 0 by rewrite   ce /=  shth0 round_0.
    rewrite /relative_errorDWDW vh0 Fast2Sum0f //= ce   shth0; 
      last apply:generic_format_round.
    rewrite  !(Rminus_0_r, Rplus_0_l, round_round, round_0) -/th // Rabs0.
      split; last by apply:boundDWDW_ge_0.
      have Ftl: format tl by apply:generic_format_round.
      rewrite Rminus_0_l ZNE round_NE_opp -ZNE (round_generic _ _ _ (sh)) //.
      have-> : th - - sh = 0 by lra.
      rewrite round_0 Rplus_0_r round_generic //.
      split;[split|] => //; try apply:generic_format_0.
      by rewrite Rplus_0_r round_generic.
    rewrite Rminus_0_l Rplus_0_r (round_generic _ _ _ (-sh)).
    have->: th - - sh = 0 by lra.
    rewrite round_0 Rplus_0_r round_generic; try apply:generic_format_round.
      rewrite TwoSum_correct //.
      suff->: (xl + yl - th - (xh + xl + (yh + yl))) = 0.
      by rewrite /Rdiv Rmult_0_l.
    have->: (xl + yl - th) = tl by rewrite  TwoSum_correct.
      rewrite  TwoSum_correct //.
      ring_simplify.
        by move:shth0; rewrite she /th; lra.
    by apply/generic_format_opp/generic_format_round.        
  have: Rabs vh >= (IZR sigma)* u ^2.
    have <-: /2* ulp (IZR sigma * u)=  IZR sigma * u^2  by lra.
    rewrite   ce.
    apply:(Rge_trans _  (Rmax ((ulp  sh)/2)   ((ulp th)/ 2))).
      apply/Rle_ge/roundN_plus_ulp=>//.
      by rewrite /th; apply:generic_format_round.
    apply:(Rge_trans _  (ulp sh / 2)).
    apply/Rle_ge/ Rmax_l.
    suff: ulp sh >= ulp (IZR sigma * u) by lra.
    apply/Rle_ge/ulp_le_pos=>//.
    by case:sigmae=> -> /=; lra.
  move=> hvhge.
  have vh0: vh <> 0.
    move=>vh0; apply: shth0.
    move:vh0; rewrite /vh  ce.
    by move/FLX_round_N_eq0.
(* page 10 *)
  have u20: 0 < u ^ 2 by apply: pow_lt.
  have hf2S: Rabs w <= Rabs vh.
    case/Rge_le: hvhge => hvhe; last first.
      have:Rabs (vl + tl) <= (IZR sigma ) * u ^ 3 + u ^2.
        apply:(Rle_trans _ (Rabs vl + Rabs tl)); first  by apply: Rabs_triang.
        apply: Rplus_le_compat=>//.
          apply:(Rle_trans _ (/ 2 * ulp vh)).
            rewrite  ce.
            rewrite F2Sum_correct_cexp // ; try apply:generic_format_round.
            have->:(sh + th - rnd_p (sh + th)) = - (rnd_p (sh + th) - (sh + th)) by ring.
            by rewrite Rabs_Ropp; apply: error_le_half_ulp_round.
          have ulpvh:/2* ulp vh <= (Rabs vh) * u.
            rewrite ulp_neq_0/cexp /fexp //.
            rewrite  bpow_plus -/u -Rmult_assoc.
            apply: Rmult_le_compat_r; try lra.
            have ->: /2 = pow (-1) by [].
            rewrite Rmult_comm -bpow_plus /=.
            by apply: bpow_mag_le.
          rewrite -hvhe in   ulpvh.
          lra.
        rewrite /= ; lra.
      move=> htlvl.
      have: Rabs w <= IZR  sigma * u ^2.
        rewrite /w ZNE -round_NE_abs -ZNE.
        apply:(Rle_trans _ (rnd_p(IZR sigma * u ^ 3 + u ^ 2))).
          apply:round_le=>//.
          by rewrite Rplus_comm.
        have sigmapow: IZR sigma = pow (sigma -1)%Z.
          by case:sigmae => -> /=.
        rewrite sigmapow.
        have ->: (pow (sigma - 1) * u ^ 3 + u ^ 2) =  
                 pow (sigma - 1) * u ^ 2 *(u + pow (1 - sigma)).
          ring_simplify.
          suff ->: pow (sigma - 1) * u ^ 2 * pow (1 - sigma) = u ^2 by ring.
          set uu := u^2.
          rewrite (Rmult_comm _ uu) Rmult_assoc -bpow_plus.
          have ->: (sigma - 1 + (1 - sigma))%Z = 0%Z by ring.
          by rewrite /=; ring.
        rewrite /u.
        have ->: pow (sigma - 1) * u ^ 2 = pow (sigma -1 -2 *p).
          rewrite /u !bpow_plus.
          suff->:  pow (- p) ^ 2 = pow (- (2 * p)) by [].
          rewrite [_^_]/=.
          rewrite Rmult_1_r -bpow_plus.
          congr bpow.
          by ring.
        rewrite Rmult_comm round_bpow.
        rewrite -[X in _<= X]Rmult_1_l.
        apply:Rmult_le_compat_r.
          by apply:bpow_ge_0.
        case:sigmae => ->.
          have-> : (1 -1 )%Z= 0%Z by ring.
          rewrite -/u /=.
          by rewrite  Rplus_comm  r1pu; lra.
        have ->: 1 = rnd_p 1.
          rewrite round_generic //.
          have->: 1 = pow 0 by [].
          apply:generic_format_bpow.
          by rewrite /fexp; move:Hp; lia.
        apply:  round_le.
        rewrite /= IZR_Zpower_pos /= Rmult_1_r.
        suff h: pow (-1) <= /2 .
          have ->: 1 = /2 + /2 by lra.
          apply:Rplus_le_compat_r =>//.
          have ->: /2 =  pow (-1) by [].
          apply: bpow_le.
          by move:Hp; lia.
        have ->: /2 =  pow (-1) by [].
        apply: bpow_le.
        lia.
      lra.
    have su2pow: (IZR sigma * u ^ 2) =  pow (sigma - 1 - p - p).
          have ->: IZR sigma = pow (sigma -1).
        by case:sigmae => ->.
        have ->: 2%nat = (1 + 1)%nat by [].
        by rewrite pow_add pow_1 /u -!bpow_plus; congr bpow; ring.
    have ulpsu2: ulp (IZR sigma * u ^ 2)= 2* u * (IZR sigma * u ^ 2).

      rewrite su2pow  ulp_bpow /fexp.
      have ->: 2* u = pow (1 -p).
        have ->: 2 = pow 1 by [].
        by rewrite /u bpow_plus.
      by rewrite -bpow_plus; congr bpow; ring.
    have: succ two fexp ( IZR sigma * u ^ 2 ) <= Rabs vh.
      apply: succ_le_lt=>//. 
        by rewrite  su2pow; apply:generic_format_bpow; rewrite /fexp; move:Hp; lia.
      by apply/generic_format_abs/generic_format_round.
    rewrite succ_eq_pos; first last.
      by rewrite su2pow; apply:bpow_ge_0.
    rewrite su2pow   ulp_bpow.
    have ->:   pow (sigma - 1 - p - p) + pow (fexp (sigma - 1 - p - p + 1)) = 
               (IZR sigma * u ^ 2)*(1 + 2*u).
      rewrite /fexp -su2pow.
      have->:  pow (sigma - 1 - p - p + 1 - p)=  (IZR sigma * u ^ 2)* (2 *u).
        have -> : 2 * u = pow (1 -p).
          by rewrite /u bpow_plus.
        rewrite  su2pow -bpow_plus.
        by congr bpow ; ring.
      by ring.
    move=>h.
    have: (IZR sigma * u ^ 2/(1-u)) <= Rabs vh.
      apply:(Rle_trans _ (IZR sigma * u ^ 2 * (1 + 2 * u)))=>//.
      rewrite /Rdiv.
      apply:Rmult_le_compat_l.
        by rewrite  su2pow; apply bpow_ge_0. 
      apply:(Rmult_le_reg_l (1 -u)).
        by rewrite /u; move : (bpow_lt_1 two p_gt_0); lra.
      rewrite Rinv_r; last by rewrite /u; move : (bpow_lt_1 two p_gt_0); lra.
      have->:  (1 - u) * (1 + 2 * u) = 1 +  u * (1 - 2 * u) by ring.
      suff : 0 <= u * (1 - 2 *u) by lra.
      have ->: 0 = u * 0 by ring.
      by apply: Rmult_le_compat_l; lra.
    move=>g.
    have : u * Rabs vh +  IZR sigma * u ^ 2 <= Rabs vh.
      have gg:0 <= 1 -u by move:(@bpow_lt_1 two (-p)); lra.
      move/(Rmult_le_compat_r (1 -u) _ _ gg):g; rewrite /Rdiv.
      rewrite Rmult_assoc Rinv_l.
        lra.
      by move:(@bpow_lt_1 two (-p)); lra.
    move=> hh.
    have:Rabs vl + Rabs tl <= Rabs vh.
      apply:(Rle_trans _ (u * Rabs vh + IZR sigma * u ^ 2))=>//.
      apply:Rplus_le_compat; last by case:sigmae => -> /=; lra.
      rewrite  ce  F2Sum_correct_cexp //; try apply:generic_format_round.
      have ->: sh + th - rnd_p (sh + th) = - ( rnd_p( sh+ th) - ( sh + th)) by ring.
      rewrite  Rabs_Ropp.
      apply:(Rle_trans _ (/ 2 * bpow two (- p + 1) * Rabs vh)).
        rewrite  ce; apply: relative_error_N_FLX_round.
        by move:Hp; lia.
      by rewrite   bpow_plus -/u /= IZR_Zpower_pos /= -{2}ce; lra.
    move/(round_le radix2 fexp (Znearest choice)).
    rewrite ZNE round_NE_abs -ZNE.
    rewrite [X in _ <= Rabs X]round_generic; last apply:generic_format_round.
    apply/(Rle_trans (Rabs w)).
    rewrite /w  ZNE -round_NE_abs -ZNE //.
    by apply/round_le; rewrite Rplus_comm; apply:Rabs_triang.
  case:(Req_dec w 0)=>w0.
    have Fvh : format vh by apply:generic_format_round.
    rewrite /relative_errorDWDW w0 Fast2Sumf0 /=; last by apply:generic_format_round.
    rewrite Rplus_0_r Rabs0.
       split; last by  exact: boundDWDW_ge_0.
       split;[split|]; try apply:generic_format_round; try apply:generic_format_0.
       by rewrite Rplus_0_r round_round.
    suff->: vh - (xh + xl + (yh + yl)) = 0 by rewrite /Rdiv Rmult_0_l.
    have->:  (xh + xl + (yh + yl)) = xh+yh +(xl +yl) by ring.
    rewrite -she.
    have ->: xl + yl= th + tl by rewrite  TwoSum_correct //; ring.
    have ->: vh = sh + th - vl.
      rewrite  ce F2Sum_correct_cexp //=; try apply:generic_format_round.
    ring.
    have: vl + tl = 0 by move/FLX_round_N_eq0 : w0; lra.
    by lra.
  rewrite  /relative_errorDWDW  F2Sum_correct_cexp //; try apply:generic_format_round; 
   last by rewrite ce.
  have f2sc: (Fast2Sum_correct p choice vh w).
   by  apply:F2Sum_correct_abs=> //; try apply:generic_format_round.
  have->: (sh + c - vh) = vl by lra.
  split; first by apply F2Sum_correct_DW'.
  rewrite   f2sc.
  set fs:= F2Sum_sum _ _.
  have->: fs + (vh + w - fs)= vh + w by ring.
  have->: (vh + w - (xh + xl + (yh + yl))) = -e2.
    have ->: vh = sh + th - vl by lra.
    have->:  (xh + xl + (yh + yl)) = xh+yh +(xl +yl) by ring.
    rewrite -she /e2; ring_simplify.
    by rewrite  (TwoSum_correct Fxl Fyl); ring.
  have ->: - e2 / (xh + xl + (yh + yl)) = - (e2 /(xh + xl + (yh + yl))) 
    by rewrite /Rdiv; ring.
  rewrite Rabs_Ropp /Rdiv Rabs_mult.
  case:  (xh_mul_su) => xhm xhem.
  case:  (yh_mul_su) => yhm yhem.
  have xhyh_msu: xh + yh = IZR (xhm + yhm) * (IZR sigma * u).
    by rewrite   xhem  yhem plus_IZR; ring.
  have xhyh_msu0: (xhm + yhm <> 0)%Z.
    move=> xhyhm0.
    by move: xhyh_msu; rewrite xhyhm0 /=; lra.
  have xhyhm1: (1 <= xhm + yhm)%Z.
    suff: (0 <  xhm + yhm)%Z by lia.
    have : 0< xh + yh by lra.
    rewrite xhyh_msu -(Rmult_0_l (IZR sigma * u)).
    have h: 0<IZR sigma * u by case:sigmae => -> /=; lra.
    move/(Rmult_lt_reg_r _ _ _ h).
    by move/lt_IZR.
  have : (IZR sigma * u) <= xh + yh.
    move/IZR_le: xhyhm1 =>/= xhyhm1.
    rewrite xhyh_msu; case:sigmae => -> /=.
      by apply:Rmult_le_compat; lra.
    have{1}->: (2 * u) = 1 * (2 * u) by ring.
    by apply:Rmult_le_compat=>//; lra.
  move=> h.
  have : Rabs (xl + yl) <= 3/2*(xh+yh).
    apply:(Rle_trans _ ((1 + IZR sigma / 2) * u)) =>//.
    apply:(Rle_trans _ (3/2 * ( IZR sigma * u))); last by  lra.
    by case:sigmae => -> /=; lra.
  move/Rabs_le_inv=>   [hxlyl hxlylsup].
  case:(Rle_lt_dec (xl + yl) (- /2 * (xh + yh))) =>   hxlylsup2.
    have: vh = sh +th.
      rewrite  ce /=.
      have ->:  (sh + th ) = (sh - (- th)) by ring.
      rewrite round_generic=>//.
      apply: sterbenz'; (try apply:generic_format_opp) =>//.
(* th generic ... gu up *)
        by apply:generic_format_round.
      split.
        have: rnd_p (xl + yl) <= rnd_p (- / 2 * (xh + yh)) by apply:round_le.
        have -> : rnd_p (- / 2 * (xh + yh))  = - /2 * rnd_p (xh + yh).
          rewrite Ropp_mult_distr_l_reverse ZNE round_NE_opp -ZNE.
          have ->: /2 = pow (-1) by [].
          by rewrite  Rmult_comm round_bpow; ring.
       by rewrite !TwoSum_sumE; lra.
      have hl: -(2 * (xh + yh)) <= xl + yl.
        by apply:(Rle_trans _ (- (3 / 2 * (xh + yh)))); lra.
      have: rnd_p(- (2 * (xh + yh))) <= rnd_p( xl + yl) by apply:round_le.
      rewrite  ZNE round_NE_opp -ZNE.
      have ->: 2 = pow (1) by [].
      by rewrite  Rmult_comm round_bpow /= !TwoSum_sumE ; lra.
    move=> vhe; have vl0: vl = 0.
      rewrite  ce F2Sum_correct_cexp //; try apply: generic_format_round.
      rewrite /= -{1}vhe  -{2}ce /=; ring.
    rewrite vl0 Rplus_0_r.  
    have ->:  rnd_p tl = tl by rewrite round_generic //; apply: generic_format_round.
    rewrite  Rabs0; last by ring.
    by rewrite Rmult_0_l;move=>*; apply : boundDWDW_ge_0 .
  (* move=> hrel; *) apply:(Rle_trans _ (2* u^2)); last first.
    have h4u: 0 < 1 - 4 * u.
      have->: 4 = pow 2 by [].
      rewrite -bpow_plus.
      have -> : (2 + -p = - (p -2))%Z by ring.
      suff : (pow (- (p -2))) < 1 by lra.
      by apply: bpow_lt_1; move :Hp3; lia.
    apply: (Rmult_le_reg_l ((1 - 4 * u))) =>//.
    rewrite [X in _ <= X] Rmult_comm [X in _ <= X]Rmult_assoc Rinv_l; last by  lra.
    rewrite -Rmult_assoc Rmult_1_r.
    apply:Rmult_le_compat_r; last by lra.
    by rewrite /u /= Rmult_1_r -bpow_plus; apply : bpow_ge_0.
  have xy0: 0 < x + y by  lra.
  rewrite -/x -/y Rabs_Rinv ; try lra; rewrite (Rabs_pos_eq (x + y)); try lra.
   apply:(Rmult_le_reg_r (x + y)); rewrite // Rmult_assoc Rinv_l; last by lra.
   rewrite Rmult_1_r.
  have: Rabs (xl + yl) < Rabs (x + y).
    rewrite (Rabs_pos_eq (x + y)) //.
    by apply: Rabs_lt; lra.
  move/Rlt_le/(ulp_le two fexp)=>hulp.
  have: /2* (ulp ((x + y) + /2*ulp (xl +yl))) <= ulp (x + y).
    have ulpxy: ulp (x + y) <= Rabs(x + y) * pow (1 -p) by apply: ulp_FLX_le.
    have : /2* ulp (x + y) <= /2 * Rabs(x + y) * pow (1 -p) by lra.
    rewrite bpow_plus /= IZR_Zpower_pos /=  => ulpxy2.
    have:  /2* ulp (x + y) <=  Rabs(x + y).
      apply:(Rle_trans _  (Rabs (x + y) * pow (- p))); try lra.
      rewrite -[X in _<= X] Rmult_1_r.
      apply:Rmult_le_compat_l; try apply:Rabs_pos.
      by apply/Rlt_le/bpow_lt_1;  lia.
    rewrite Rabs_pos_eq // => h11.
    have h21: x + y + / 2 * ulp (xl + yl) <=  x + y + / 2 * ulp (x + y) by  lra.
    have h22:  x + y + / 2 * ulp (xl + yl) <= x + y + (x + y) by lra.
    have: ulp  (x + y + / 2 * ulp (xl + yl) ) <= ulp (x + y + (x + y)).
      apply/ulp_le.
      rewrite !Rabs_pos_eq; try lra.
      by move:(ulp_ge_0 two fexp (xl + yl)); lra.
    have->: (x + y + (x + y)) = 2 * (x + y) by ring.
    have->:  ulp (2 * (x + y))= 2 *ulp(x + y).
      rewrite !ulp_neq_0 //; last by  lra.
      rewrite Rmult_comm.
      have->: 2 = pow 1 by [].
      rewrite cexp_bpow  // bpow_plus /=; lra.
    move=> h3.
    rewrite Rmult_1_r; apply/(Rmult_le_reg_l 2); lra.
  move=> h4.
  apply:(Rle_trans _ (/2* ulp (3/2*ulp(x+y)))).
    apply:(Rle_trans _ 
     (/ 2 * ulp (/ 2 * ulp (xl + yl) + / 2 * ulp (x + y + / 2 * ulp (xl + yl))))) =>//.
    apply:Rmult_le_compat_l; try lra.
    apply:ulp_le_pos.
      suff: 0<= ulp (xl + yl) + ulp (x + y + / 2 * ulp (xl + yl)) by lra.
      rewrite -(Rplus_0_r 0).
      by apply/Rplus_le_compat; apply:ulp_ge_0.
    apply: (Rle_trans _  (/ 2 * ulp (xl + yl) +   ulp (x + y))).
      lra.
    apply:(Rle_trans _  (/ 2 * ulp (x + y) + ulp (x + y))); try lra.
(* move out *)
  have ulp32: forall r, ulp (3/2* (ulp r)) = ulp (ulp r).
    move=>r.
    case:(Req_dec r 0)=>[->|hr0].
      by rewrite  ulp_FLX_0  Rmult_0_r ulp_FLX_0.
    case:(mag two r)=> ulpr /(_ hr0) hulpr  /=.
    rewrite(ulp_neq_0 _ _ r) // /cexp (mag_unique _ _ ulpr) // {2 4}/fexp.
    rewrite   ( ulp_neq_0  two fexp (pow (ulpr - p))); last by move:(bpow_gt_0 two (ulpr -p)); lra.
    rewrite /= /cexp (mag_unique_pos _ _ (ulpr -p +1)); last first.
      by split;[apply: bpow_le |apply: bpow_lt] ; lia.
    rewrite  ulp_neq_0 /cexp /fexp.
      congr bpow.
      suff ->: (mag radix2 (3 / 2 * pow (ulpr - p)))%Z = (ulpr - p + 1)%Z :> Z by ring.
      apply:mag_unique_pos.
      split.
        ring_simplify((ulpr - p + 1 - 1)%Z); 
         rewrite -[X in X <= _]Rmult_1_l; apply:Rmult_le_compat.
        + exact Rle_0_1.
        + apply:bpow_ge_0.
        + lra.
        exact: Req_le.
      rewrite [X in _ < X]bpow_plus /=  Rmult_comm.
      apply:Rmult_lt_compat_l; first by apply: bpow_gt_0.
      rewrite IZR_Zpower_pos /=;lra.
    apply:Rmult_integral_contrapositive_currified; try lra.
    by move:(bpow_gt_0 two (ulpr -p)); lra.
  rewrite ulp32.
  move:(@ulp_FLX_le two p p_gt_0 (x + y)).
  move/(ulp_le_pos two fexp).
  move/(_ (ulp_ge_0 two fexp (x + y))).
  rewrite -/ulp =>h0.
  apply:(Rle_trans _  (ulp (Rabs (x + y) * pow ( - p)))).
    rewrite Rmult_comm.
    apply:(Rmult_le_reg_r 2); first by lra.
    rewrite Rmult_assoc Rinv_l ?Rmult_1_r.
      suff->:  (ulp (Rabs (x + y) * pow (- p)) * 2) = (ulp (Rabs (x + y) * pow (1 - p))) by [].
      rewrite !ulp_neq_0 /cexp /fexp.
      + rewrite !bpow_plus /= !mag_mult_bpow.
          rewrite -! bpow_plus.
          have ->: 2 * pow (- p) = pow (1 -p) by rewrite bpow_plus /=.
          rewrite !mag_mult_bpow.
            set l := (mag _ _).
            have ->: 2 = pow 1 by [].
            by rewrite -bpow_plus; congr bpow; ring.
          by rewrite Rabs_pos_eq;lra.
        by rewrite Rabs_pos_eq;lra.
      + rewrite Rabs_pos_eq; try lra.
        apply:Rmult_integral_contrapositive_currified; try lra.
        by move:(bpow_gt_0 two (1 -p)); lra.
      apply:Rmult_integral_contrapositive_currified; try lra.
        by rewrite Rabs_pos_eq;lra.
      by move:(bpow_gt_0 two (-p)); lra.
    lra.
  apply:(Rle_trans _ (Rabs(x+y) * pow (-p) * (pow (1 -p)))).
    rewrite {1}Rabs_pos_eq; try lra.
    rewrite /ulp; move:(@ulp_FLX_le two p p_gt_0 ((x + y) * pow (- p))).
    rewrite !Rabs_pos_eq // -(Rmult_0_r 0).
    apply:Rmult_le_compat; try lra.
    by apply:bpow_ge_0.
  rewrite Rabs_pos_eq; try lra.
  rewrite /u !bpow_plus /=.
  rewrite Rmult_assoc.
  suff ->:  pow (- p) * (2 * pow (- p)) =  2 * (pow (- p) * (pow (- p) * 1)) by lra.
  ring.

(* cas 2 : -xh/2 < yh <= xh *)
have : xh/2 < xh + yh <= 2*xh by lra.
case =>/Rlt_le /(round_le two fexp (Znearest choice))   hd hu0.
move/(round_le two fexp (Znearest choice)):(hu0) => hu.
move: hd hu.
have ->: rnd_p (2*xh) = 2* rnd_p xh.
have->: 2 = pow 1 by [].
rewrite Rmult_comm round_bpow; ring.
have ->:   rnd_p (xh / 2) = rnd_p xh /2.
rewrite /Rdiv.
have -> : /2 = pow (-1) by [].
by rewrite  round_bpow.
rewrite (round_generic _ _ _ xh) // => hd hu.
have: /2 < xh + yh by lra.
case:(Rle_lt_dec (xh + yh) (2 - 4*u))=> hu' hd'.
  pose sigma := if  Rle_dec (xh + yh)  (1 -2 *u) is left _ then 1%Z else 2%Z.
  have sigmae: sigma = 1%Z \/ sigma = 2%Z.
    by rewrite /sigma; case:Rle_dec;[left|right].
  have sigma1: xh + yh <= 1 - 2*u  -> IZR sigma = 1.
    by rewrite  /sigma; case:Rle_dec.
  have sigma2: ~ (xh + yh) <= 1 - 2*u -> IZR sigma = 2.
    by rewrite  /sigma; case:Rle_dec.
  have sigmapow: IZR sigma = pow (sigma -1)%Z.
    by case:sigmae => -> /=. 
  have hF1m2u: format (1 - 2 * u).
    rewrite /u  u_ulp1 -Rmult_assoc Rinv_r ?Rmult_1_l; try lra.
    rewrite ulp_neq_0; last lra.
    rewrite /u. 
    apply:(@FLX_format_Rabs_Fnum _ (Float two (2^p -2)%Z (-p)%Z)).
      rewrite /F2R  /= minus_IZR (IZR_Zpower two); last lia.
      rewrite Rmult_minus_distr_r -(bpow_plus _ p); congr Rminus; first by rewrite Z.add_opp_diag_r.
      rewrite /cexp /fexp bpow_plus; congr Rmult.
      suff->: ((mag radix2 1) = 1%Z :>Z) by rewrite /= IZR_Zpower_pos.
      apply:mag_unique_pos; rewrite /=  IZR_Zpower_pos /=; lra.
    rewrite /=  minus_IZR (IZR_Zpower two) ?Rabs_pos_eq; move:(bpow_ge_0 two p); try lra; try lia.
    suff : (pow 1 ) <= pow p by rewrite /= IZR_Zpower_pos /=; lra.
    apply:bpow_le; lia.
  have h11_1: IZR sigma /2 * ( 1 - 2 * u) <= sh <= IZR sigma * ( 1 - 2 * u).
    rewrite /sigma; case:Rle_dec => /=.
      move/( round_le two fexp (Znearest choice)).
      rewrite [X in _<=X] round_generic // => hu''.
      by rewrite Rmult_1_l  TwoSum_sumE ; split;lra.
    move/Rnot_le_lt/Rlt_le /(round_le two fexp (Znearest choice)).
    rewrite round_generic// => hu''; split.
      rewrite /Rdiv Rinv_r ?Rmult_1_l ?TwoSum_sumE ; lra.
    move /(round_le two fexp (Znearest choice)): (hu').
    rewrite [X in _<=X]round_generic ?TwoSum_sumE; first lra.
    have->: (2 - 4 * u) = 2 * (1 - 2*u) by ring.
    have->: (2 * (1 - 2 * u))= (1 - 2 * u) * (pow 1) by rewrite /= IZR_Zpower_pos; ring.
    by apply:formatS.
  have h11_2: Rabs sl <= IZR sigma / 2 * u.
    apply:(Rle_trans _ (/2* ulp sh)).
      rewrite  TwoSum_correct  // -Rabs_Ropp Ropp_minus_distr /ulp.
      by  apply: error_le_half_ulp_round.
    have shpos: 0 <= sh.
      have : 0 <= xh + yh by lra.
      by move/( round_le two fexp (Znearest choice)); rewrite round_0.
    suff : ulp sh <= IZR sigma * u by lra.
    have : sh <= IZR sigma * (1 - 2 * u) by lra.
    move/(ulp_le_pos two fexp  _ _ shpos).
    rewrite -/ulp.
    suff ->: ulp (IZR sigma * (1 - 2 * u)) = IZR sigma * u by [].
    rewrite ulp_neq_0.
      rewrite /cexp /fexp bpow_plus {3} /u.
      congr (_ *_).
      rewrite sigmapow.
      congr bpow.
      rewrite /= ; apply:  mag_unique_pos.
      set ps := pow (sigma -1).
      rewrite bpow_plus /= -/ps.
      have h2u: 0 < 2 * u by lra.
      split; last first.
        rewrite -[X in _ < X]Rmult_1_r; apply: Rmult_lt_compat_l; try lra.
        by rewrite /ps; apply: bpow_gt_0.
      apply:Rmult_le_compat_l.
        by rewrite /ps; apply: bpow_ge_0.
      suff:  4 * u <= 1 by rewrite IZR_Zpower_pos /=;lra.
      have->: 4 = pow 2 by [].
      rewrite /u -bpow_plus.
      have->: 1 = pow 0 by [].
      apply: bpow_le.
      move:Hp3; lia.
    apply:Rmult_integral_contrapositive_currified; lra.
(* try to factorize keeping sigma *)
  have h12_0: Rabs yl <= IZR sigma /2 *u.
    rewrite /sigma; case :Rle_dec=> hxhyhle.
      have yhboubds: -xh/2 < yh < 0 by split;  lra.
      have ylyh:Rabs yl <= /2*ulp yh by apply: dw_ulp. 
      apply:(Rle_trans  _(/ 2 * ulp yh)) =>//=.
      suff: ulp yh <= u by lra.
      rewrite ulp_neq_0 ; try lra; rewrite /cexp /fexp.
      rewrite bpow_plus /u.
      apply:(Rmult_le_reg_r (pow p)).
        exact : bpow_gt_0.
      rewrite Rmult_assoc -bpow_plus.
      ring_simplify (- p + p)%Z=>//=.
      rewrite Rmult_1_r.
      have -> : 1 = pow 0 by [].
      apply: bpow_le.
      apply:mag_le_bpow.
        lra.
      rewrite /=  -Rabs_Ropp Rabs_pos_eq /=; lra.
    have yhboubds: Rabs yh <= 2 -2 *u by lra.
    apply:(Rle_trans  _(/ 2 * ulp yh)) =>//=.
      by apply: dw_ulp.
    suff: ulp yh <= 2*  u by lra.
    case:(Req_dec yh 0)=>[->| hyh0].
      by rewrite ulp_FLX_0; lra.
    rewrite ulp_neq_0 ; try lra; rewrite /cexp /fexp.
    rewrite bpow_plus /u.
    apply:Rmult_le_compat_r.
      by apply:bpow_ge_0.
    have->:2 = pow 1 by [].
    apply: bpow_le.
    apply:mag_le_bpow=>//.
    rewrite /= IZR_Zpower_pos /=;  lra.
  have h12_00: Rabs (xl + yl) <= (1 + (IZR sigma)/2) *u.
    apply:(Rle_trans _ (Rabs xl + Rabs  yl)); first  exact: Rabs_triang; lra.
(* ! duplication *)
  have h12_1: Rabs th <= (1 + (IZR sigma)/2)*u.
    move/(round_le two fexp (Znearest choice)): (h12_00).
    rewrite ZNE round_NE_abs -ZNE.
    rewrite [X in _ <= X] round_generic.
      by rewrite /th .
    rewrite /u; apply:formatS.
    case:sigmae => -> /=.
      apply: (@FLX_format_Rabs_Fnum _ (Float two 3 (-1))).
        rewrite /F2R /= IZR_Zpower_pos /= ; field.
      rewrite /=; rewrite Rabs_pos_eq; try lra.
      apply:(Rlt_le_trans _ (pow 2)); first by rewrite /= IZR_Zpower_pos /= ; lra.
      apply:bpow_le; move : Hp; lia.
    have->: 1 + 2/2 = pow 1 by rewrite /= IZR_Zpower_pos /= ; field.
    apply:generic_format_bpow; rewrite /fexp; move:Hp;lia.
  have h13_0: Rabs (sl + th) <= (1 + IZR sigma ) *u.
    apply:(Rle_trans _ (Rabs sl + Rabs th)); first by apply:Rabs_triang.
    lra.
  move/(round_le two fexp (Znearest choice)):(h13_0).
  rewrite ZNE round_NE_abs -ZNE.
  rewrite [X in _ <= X]round_generic; last first.
    rewrite /u; apply:formatS.
    pose s1 := (1+sigma)%Z.
    apply: (@FLX_format_Rabs_Fnum _ (Float two s1 0)).
      rewrite /F2R /= /s1 plus_IZR /=; ring.
    rewrite /= /s1; case:sigmae => -> /=; rewrite Rabs_pos_eq; try lra.
      have -> : 2 = pow 1 by [].
      apply:bpow_lt; move :Hp; lia.
    apply:(Rlt_le_trans _ 4); first lra.
    have ->: 4 = pow 2 by [].
    apply:bpow_le;  lia.
  move=> h13_1.
  have h13_2:  Rabs e1 <= IZR sigma * u ^2.
    rewrite  -Rabs_Ropp Ropp_minus_distr.   
    apply:(Rle_trans _ (/ 2 * pow (- p) * pow (sigma -p))).
      apply: error_le_half_ulp'; first exact: Hp.
      move: h13_0.
      rewrite sigmapow !bpow_plus /= /u=> *.
      apply:(Rle_trans _ ((1 + pow sigma * / 2) * pow (- p))_ )=>//.
      apply:Rmult_le_compat_r; first by apply:bpow_ge_0.
      suff : 2 <= pow sigma by lra.
      have->:2= pow 1 by [].
      apply : bpow_le; move:Hp; lia.
    by rewrite sigmapow !bpow_plus /= /u IZR_Zpower_pos /= ; lra.
  have Fsh : format sh by apply:generic_format_round.
  have Fc: format c by  apply:generic_format_round.
  have hcsh: Rabs c <= Rabs sh.
    apply:(Rle_trans _ ((1 + IZR sigma) * u))=>//.
    apply:(Rle_trans _ (/2)).
      apply:(Rmult_le_reg_l 2); try lra.
      rewrite Rinv_r /u; try lra.
      case:sigmae => -> /=.
        have ->: 1 + 1 = 2 by [].
        have ->: 1 = pow 0 by [].
        have->: 2 = pow 1 by [].
        rewrite -!bpow_plus; apply: bpow_le; move:Hp;lia.
      apply:(Rle_trans _ (8 * pow (-p))).
        rewrite -Rmult_assoc; apply: Rmult_le_compat_r; try lra.
        exact: bpow_ge_0.
      have ->: 8 = pow 3 by [].
      have {1}->: 1 = pow 0 by [].
      rewrite -bpow_plus; apply:bpow_le; move:Hp3; lia.
    have->: /2 =  (pow (-1)) by [].
    have ->: (pow (-1)) = rnd_p (pow (-1)).
      rewrite round_generic //; apply: generic_format_bpow.
      rewrite /fexp; move:Hp; lia.
    rewrite TwoSum_sumE ZNE -round_NE_abs -ZNE.
    apply: round_le.
    rewrite /= Rabs_pos_eq ?IZR_Zpower_pos /=; lra.
     move:(eq_refl relative_errorDWDW).
    rewrite {-1}/relative_errorDWDW F2Sum_correct_abs //.
  have h14_0: Rabs (sh + c ) <= IZR sigma.
    apply:(Rle_trans _ ((Rabs sh ) + (Rabs c))); first by exact:Rabs_triang.
    apply:(Rle_trans _ ( (IZR sigma) * (1 - 2 * u) + (1 + IZR sigma) * u)).
      apply:Rplus_le_compat=>//.
      rewrite Rabs_pos_eq; lra.
    by case:sigmae => -> /=; lra.
  have h14_1: Rabs vh <= IZR sigma.
    rewrite sigmapow.
    have <-:  rnd_p (pow (sigma - 1)) = (pow (sigma - 1)).
      rewrite round_generic //; apply:generic_format_bpow.
      rewrite /fexp /=.
      case:sigmae => ->; move:Hp; lia.
    rewrite /vh   ZNE -round_NE_abs -ZNE.
    apply: round_le.
    by rewrite -sigmapow.
  have f2sc_shc: Fast2Sum_correct  p choice sh c by apply: F2Sum_correct_abs.
  have h14_2: Rabs vl <= (IZR sigma)/2 * u.
    rewrite   f2sc_shc -Rabs_Ropp Ropp_minus_distr.   
    have->: IZR sigma / 2 * u = / 2 * pow (- p) * pow (sigma -1) 
     by rewrite /u sigmapow; field.
    apply: error_le_half_ulp'; first exact: Hp.
    by rewrite -sigmapow.
  have h15_0: Rabs (tl + vl) <= u^2 + (IZR sigma)/2 * u.
    apply:(Rle_trans _ ((Rabs tl) + (Rabs vl))); first by apply:Rabs_triang.
    lra.
  have vlE: (sh + c - vh) = vl by rewrite   f2sc_shc .
  rewrite vlE.
  have h15_1: Rabs w <=  (IZR sigma)/2 * u +  u^2.
    have: rnd_p (Rabs (tl + vl)) <= rnd_p (u^2 + (IZR sigma)/2 * u) by apply:round_le.
    rewrite ZNE round_NE_abs -ZNE /w.
    move/(Rle_trans (Rabs (rnd_p (tl + vl)))  (rnd_p (u ^ 2 + IZR sigma / 2 * u))   
                      (IZR sigma / 2 * u + u ^ 2)).
    apply.
    rewrite Rplus_comm.
    have ->: ( IZR sigma / 2 * u + u ^ 2) = ( IZR sigma / 2  + u) * u by ring.
    rewrite round_bpow.
    apply:Rmult_le_compat_r.
      exact: bpow_ge_0.
    case:sigmae=> -> /=; last first.
      rewrite /Rdiv Rinv_r ?r1pu; move:(bpow_ge_0 two (-p)); lra.
    have->: 1/2 + u = ((pow (-1))* (1 + 2 * u)) by rewrite /= IZR_Zpower_pos /=;  field.
    rewrite Rmult_comm round_bpow.
    apply:Rmult_le_compat_r.
      exact: bpow_ge_0.
    rewrite round_generic; try lra.
    rewrite /u u_ulp1 -Rmult_assoc Rinv_r ?Rmult_1_l; try lra.
    apply:generic_format_succ_aux1; try lra.
    apply:(generic_format_bpow _ _ 0); rewrite /fexp; move:Hp; lia.
  have h15_2: Rabs e2 <= (IZR sigma) / 2 * u ^2.
    rewrite  -Rabs_Ropp Ropp_minus_distr.  
    have ->:  IZR sigma / 2 * u ^ 2 =  / 2 * pow (- p) * pow (sigma - 1 - p).
      rewrite sigmapow !bpow_plus /u; field.
    apply: error_le_half_ulp'; first exact : Hp.
    apply:(Rle_trans _ (IZR sigma / 2 * u + u ^ 2)); first  lra.
    rewrite bpow_plus -sigmapow -/u /=.
    suff : u * u  <= /2 * (IZR sigma * u) by lra.
    have->: /2 = pow (-1) by [].
    rewrite -Rmult_assoc.
    apply:Rmult_le_compat_r; try lra.
    rewrite /u sigmapow - bpow_plus; apply: bpow_le.
    case:sigmae => -> /=; move : Hp; lia.
  have h16_0 : (IZR sigma)/2 - u * (2* (IZR sigma)  + 1) <= sh + c.
    by case/Rabs_le_inv:   h13_1; lra.
  have h16_1: rnd_p (IZR sigma / 2 - u * (2 * IZR sigma + 1)) <=  
               rnd_p (sh + c) by apply:round_le.
  have h16_2: (IZR sigma / 2 - u * (2 * IZR sigma + 1)) <= Rabs vh.
    apply: Rabs_ge.
    right.
    suff <-: rnd_p (IZR sigma / 2 - u * (2 * IZR sigma + 1)) = 
               IZR sigma / 2 - u * (2 * IZR sigma + 1) by rewrite /= ;lra.
    rewrite round_generic //.
    case:sigmae => -> /=; last first.
      have -> : 2 / 2 - u * (4 + 1) = (pow p  - 5) * (pow (- p)).
        rewrite Rmult_minus_distr_r -bpow_plus.
        rewrite Z.add_opp_diag_r -/u /Rdiv Rinv_r /=; lra.
      apply:(@FLX_format_Rabs_Fnum  ((pow p - 5) * pow (- p)) 
              (Float two ((two ^ p) - 5)%Z (-p)%Z));
        rewrite /F2R /= minus_IZR /= (IZR_Zpower two p) //.
      + move:Hp; lia.
      + rewrite Rabs_pos_eq ; try lra.
        apply: (Rle_trans _ (pow p - pow 3)).
          suff: pow 3  <= pow p by  lra.
          apply:bpow_le; move : Hp3; lia.
        suff: 5 <= pow 3 by lra.
        by rewrite /= IZR_Zpower_pos /= ; lra.
      lia.
    apply:(@FLX_format_Rabs_Fnum ((1 / 2 - u * (2 * 1 + 1))) 
            (Float two ((two ^ p) - 6)%Z (- p -1)%Z));
      rewrite /F2R minus_IZR  (IZR_Zpower two p) //.
    + set p6:= (pow p - IZR 6).
      set pp:= (-2 * p - 1)%Z.
      rewrite /= /p6 /pp !bpow_plus.
      have ->:  1 / 2 - u * (2 * 1 + 1) = /2 * (1 - 6 * u) by field.
      apply:(Rmult_eq_reg_l 2); try lra; rewrite  -Rmult_assoc Rinv_r; 
        try lra; rewrite Rmult_1_l.
      rewrite /u [IZR _]/= ; ring_simplify.
      have ->:2 = pow 1 by [].
      rewrite -!bpow_plus.
      ring_simplify  (1 + - p + p + - (1))%Z.
      rewrite -/u /= IZR_Zpower_pos /=  ; field.
    + lia.
    + rewrite Rabs_pos_eq.
         rewrite /=;  lra.
      rewrite /=.
      suff : 8 <= pow p by lra.
      have ->: 8 = pow 3 by [].
      apply: bpow_le; move: Hp3; lia.
     lia.
  have h16_3: Rabs w <= Rabs vh.
    apply:(Rle_trans _ (IZR sigma / 2 * u + u ^ 2))=>//.
    apply:(Rle_trans _   (IZR sigma / 2 - u * (2 * IZR sigma + 1))) =>//.
    suff: u * (7 +  (pow (2 - sigma))* u ) <= 1.
      case:sigmae => -> /=; rewrite ?IZR_Zpower_pos /=; lra.
    apply: (Rmult_le_reg_l (pow p)); first exact:bpow_gt_0.
    rewrite Rmult_1_r -!Rmult_assoc /u -bpow_plus Z.add_opp_diag_r   Rmult_1_l.
    apply:(Rle_trans _ (pow 3)).
      rewrite - bpow_plus.
      suff: pow (2 - sigma + - p) <= 1 by  rewrite /= IZR_Zpower_pos /= ;lra.
      have->: 1 = pow 0 by [].
      apply:bpow_le; move:Hp; lia.
    apply:bpow_le; move:Hp3; lia.
  move => hrel; rewrite -hrel. 
  have f2sc: (Fast2Sum_correct  p choice vh (rnd_p (tl + (sh + c - vh)))).
   by apply: F2Sum_correct_abs=>//; try apply:generic_format_round; rewrite vlE.
  have -> : relative_errorDWDW = Rabs((e1 + e2)/(x + y)).
    exact: rel_errorDWDWe_abs.
  split;   first by apply:F2Sum_correct_DW'; rewrite vlE in f2sc.

  have h16_4: Rabs (e1 + e2) <= 3 * (IZR sigma)/2 * u ^2.
    apply:(Rle_trans _ (Rabs e1 + Rabs e2)); first by  apply: Rabs_triang.
    lra.
  have h16_5: (xh - u) + (yh - (IZR sigma) * u /2) <= x + y.
    suff: (- u <= xl) /\ (-(IZR sigma) *u/2 <=  yl) by lra.
    split.
      by case/Rabs_le_inv:  xlu.
    by case/Rabs_le_inv:  h12_0; lra.
  have hs2: (sigma = 2)%Z -> 1 -4*u < x + y.
    move:  h16_5.
    rewrite /sigma;  case:( Rle_dec (xh + yh) (1 - 2 * u)) =>//=.
    move/Rnot_le_lt.
    lra.
  have hs1: (sigma = 1)%Z -> 1/2 -3*u/2 < x + y.
    move:  h16_5.
    rewrite /sigma; case:( Rle_dec (xh + yh) (1 - 2 * u)) =>//=; lra.
  move:   h16_4 hs2 hs1; rewrite /sigma.
  case:  (Rle_dec (xh + yh) (1 - 2 * u))=>//=.
    move=> g1 g2 _ /(_ (eq_refl 1%Z))g3.
    rewrite /Rdiv Rabs_mult.
    apply:(Rle_trans _ ((3/2*u*u)*/(/2 -3*u/2))).
      apply: Rmult_le_compat; try apply: Rabs_pos; try lra.
      rewrite Rabs_Rinv; try lra.
      rewrite Rabs_pos_eq; try lra.
      apply: Rinv_le;  lra.
    field_simplify.
    + rewrite /Rdiv; apply:Rmult_le_compat_l.
      move:(pow2_ge_0 u); lra.
    + apply:Rle_Rinv.
      - suff : 4*u <1 by lra.
        have ->: 1 = pow 0 by [].
        have->:4 = pow 2 by [].
        rewrite /u -bpow_plus; apply: bpow_lt; move:Hp3; lia.
      - suff : 3*u <1 by lra.
        apply:(Rlt_trans _ (pow (2 -p))).
          rewrite bpow_plus /= -/u IZR_Zpower_pos /= ; lra.
      - have ->:1 = pow 0 by [].
        apply: bpow_lt.
        move: Hp3;lia.
      - lra.
    + suff : 4*u <1 by lra.
      have ->: 1 = pow 0 by [].
      have->:4 = pow 2 by [].
      rewrite /u -bpow_plus; apply: bpow_lt; move:Hp3; lia.
    suff : 3*u <1 by lra.
    apply:(Rlt_trans _ (pow (2 -p))).
      rewrite bpow_plus /= -/u IZR_Zpower_pos /=; lra.
    have ->:1 = pow 0 by [].
    apply: bpow_lt.
    move: Hp3;lia.
  move/Rnot_le_lt.
  move=> g1 g2 /(_ (eq_refl 2%Z))g3 _ .
  have h1m4u: 0< (1 - 4 * u ).
    suff : 4*u <1 by lra.
    have ->: 1 = pow 0 by [].
    have->:4 = pow 2 by [].
    rewrite /u -bpow_plus; apply: bpow_lt; move:Hp3; lia.
  have xypos: 0 < x+y.
  apply:(Rlt_trans _ (1 - 4 * u ))=>//.
  rewrite /Rdiv Rabs_mult.
  apply: Rmult_le_compat; try apply: Rabs_pos; try lra.
  rewrite Rabs_Rinv; try lra.
  rewrite Rabs_pos_eq; try lra.
  apply: Rinv_le; lra.

have F4u: format (2 -4 * u).
  apply:(@FLX_format_Rabs_Fnum  (2 - 4 * u)( (Float two (two ^ (p) - 2)%Z (- p +1)%Z))).
    rewrite /F2R /= minus_IZR /= (IZR_Zpower two (p)) //.
      rewrite /u Rmult_minus_distr_r  -bpow_plus.
      congr Rminus.
        have->: 2 = pow 1 by [].
        congr bpow; ring.
      rewrite bpow_plus /= IZR_Zpower_pos /=; ring.
    move:Hp; lia.
  rewrite /F2R /= minus_IZR /= (IZR_Zpower two (p )) //.
    rewrite Rabs_pos_eq; try lra.
    suff: pow 1 <= pow p by rewrite /= IZR_Zpower_pos /=;lra.
    apply:bpow_le; move:Hp; lia.
  lia.
have shd: 2 - 4 * u <= sh.
  rewrite -[X in X <= _](round_generic two fexp (Znearest choice))=>//.
  by apply:round_le; lra.
have hu'': sh <= 4 - 4*u.
  rewrite -[X in _ <= X](round_generic two fexp (Znearest choice))=>//.
    apply:round_le; lra.
  apply:(@FLX_format_Rabs_Fnum (4 - 4 * u)( (Float two (two ^ (p) - 1)%Z (- p +2)%Z))).
    rewrite /F2R /= minus_IZR /= (IZR_Zpower two (p)) //.
      rewrite !bpow_plus /=.
      ring_simplify.
      rewrite/u Rplus_comm IZR_Zpower_pos /=; congr (_ + _); try ring.
      rewrite Rmult_1_r  -bpow_plus /= Z.add_opp_diag_r /= ; ring.
    lia.
  rewrite /F2R /= minus_IZR /= (IZR_Zpower two (p )) //.
    rewrite Rabs_pos_eq; try lra.
    suff: pow 0  <= pow p by rewrite /=;lra.
    apply:bpow_le; move:Hp;lia.
   move:Hp;lia.
have slu: Rabs sl <= 2*u.
  rewrite TwoSum_correct // -Rabs_Ropp Ropp_minus_distr .
  have->: 2 * u = / 2 * pow (- p) * pow 2 by  rewrite /u /= IZR_Zpower_pos /=; field.
  apply:(error_le_half_ulp' Hp choice (xh + yh) 2).
  move:  hu'';  rewrite /= IZR_Zpower_pos /=  /sh Rabs_pos_eq; lra.
have thle: th + tl = xl + yl by rewrite  TwoSum_correct //; ring.
have h17_0: Rabs (xl + yl) <= 2 * u.
  apply:(Rle_trans _ (Rabs xl + Rabs  yl)); first  exact: Rabs_triang; lra.
have h17_1 : Rabs th <= 2 * u.
  rewrite  TwoSum_sumE ZNE -round_NE_abs -ZNE.
  have -> : 2 * u = rnd_p (pow 1 * u).
    rewrite round_generic // /u -bpow_plus; apply: generic_format_bpow.
    rewrite /fexp; move : Hp; lia.
  by apply: round_le.
have h17_2: Rabs (sl + th)  <= 4 * u.
  apply:(Rle_trans _ (Rabs sl + Rabs th)); first apply:Rabs_triang; lra.
have cu: Rabs c <= 4 * u.
  have ->: 4 * u = rnd_p ( pow 2 * u) .
    rewrite round_generic -bpow_plus //;  apply : generic_format_bpow; rewrite /fexp;  lia.
  by rewrite /c /= ZNE -round_NE_abs -ZNE; apply: round_le.
have e1u: Rabs e1 <= 2 * u * u.
  rewrite /e1 /c  -Rabs_Ropp Ropp_minus_distr.   
  apply:(Rle_trans _ (/ 2 * pow (- p) * pow (  -p + 2))).
    apply: error_le_half_ulp'; first exact: Hp.
    by rewrite bpow_plus /= -/u Rmult_comm.
  rewrite /u bpow_plus /= IZR_Zpower_pos /=; lra.
pose vh := (rnd_p ( sh + c)).
pose vl :=  (F2Sum_err sh c).
have clesh: Rabs c <= Rabs sh.
  rewrite (Rabs_pos_eq sh); last first.
    apply:(Rle_trans _ (2 - 4 * u)) =>//.
    apply: Rle_0_minus.
    suff : pow 2 * u <= pow 1 by [].
    rewrite /u -bpow_plus; apply: bpow_le; move:Hp; lia.
  apply/(Rle_trans _ (4 * u) )=>//.
  apply:(Rle_trans _ (2 - 4 * u))=>//.
  suff: (pow 3 * u <= pow 1) by  rewrite /= ?IZR_Zpower_pos /=; lra.
  rewrite /u -bpow_plus; apply: bpow_le; move:Hp3; lia.
have hl4: vh + vl = sh + c.
  rewrite /vh /vl  F2Sum_correct_abs //=; try apply:generic_format_round; try ring.
have shcu: sh + c  <= 4.
  case/Rabs_le_inv: cu; lra.
have vhu : vh <= 4.
  rewrite -(round_generic two fexp (Znearest choice ) 4).
    by apply: round_le.
  have -> : 4 = pow 2 by [].
  apply: generic_format_bpow; rewrite /fexp; move:Hp; lia.
have vlu: Rabs vl <= 2 * u.
  have ->: vl = sh + c - rnd_p (sh + c)  by move: hl4; rewrite /vh ; lra.
  have -> : 2 * u = /2 * u * pow 2 by rewrite /= IZR_Zpower_pos /=; field.
  rewrite -Rabs_Ropp Ropp_minus_distr; apply:error_le_half_ulp'.
    exact Hp.
  rewrite Rabs_pos_eq //.
  apply:(Rle_trans _ (2 - 8 * u)).
    suff: pow 3 * u <= pow 1 by rewrite /= ?IZR_Zpower_pos /=; lra.
    rewrite /u -bpow_plus; apply: bpow_le.
    lia.
  case/Rabs_le_inv: cu; lra.
have tlvlu: Rabs (tl + vl) <= 2 * u + u * u.
  apply:(Rle_trans _ (Rabs tl + Rabs vl)); first apply:Rabs_triang; lra.
pose  w := (rnd_p (tl + vl)).
pose  e2 := ((tl + vl) - w).
have ulpw: ulp (2 * u ) = pow (-p -p + 2).
  rewrite ulp_neq_0 /cexp /fexp.
    rewrite bpow_plus /u.
    have->:2 = pow 1 by []. 
    rewrite -!bpow_plus mag_bpow.
    congr bpow; ring.
  lra.
have e2u: Rabs e2 <= u * u.
  rewrite /e2 /w -Rabs_Ropp Ropp_minus_distr.
  case:(Rlt_le_dec   (Rabs (tl + vl)) (2 * u))=> tlvlu'.
    have -> : u * u = /2 * (pow (-p))* (pow (-p + 1)) by rewrite /u bpow_plus /= IZR_Zpower_pos /= ; field.
    apply:error_le_half_ulp'.
      exact Hp.
    rewrite bpow_plus /= -/u IZR_Zpower_pos /= ; lra.
  have we :Rabs  w = 2 * u.
    apply: Rle_antisym; last first.
      have ->: 2 * u = rnd_p (pow 1 * pow (-p)).
        rewrite round_generic //.
        rewrite -bpow_plus ; apply:generic_format_bpow; rewrite /fexp; move:Hp; lia.
      rewrite /w ZNE -round_NE_abs -ZNE.
      by apply:round_le; rewrite  -/u.
    rewrite /w ZNE -round_NE_abs -ZNE.
    suff ->:  2 * u = rnd_p (2 * u + u * u).
      by apply:round_le; rewrite  -/u.
    have -> : (2 * u + u * u) = (1 + u/2) * (pow (1 -p)) by rewrite bpow_plus -/u /= IZR_Zpower_pos /= ; field.
     by rewrite round_bpow r1pu2 bpow_plus -/u /= IZR_Zpower_pos /= ; ring.
  case :(Rle_lt_dec 0  (tl + vl)) => tlvl0.
    apply:Rabs_le.
    move/(round_le two fexp (Znearest choice)):  (tlvl0).
    rewrite round_0 -/w=>*.
    rewrite Rabs_pos_eq // in we.
    rewrite we.
    rewrite Rabs_pos_eq // in tlvlu'   tlvlu.
    lra.
  move/Rlt_le/(round_le two fexp (Znearest choice)):  (tlvl0).
  rewrite round_0 -/w=>*.
  rewrite -Rabs_Ropp Rabs_pos_eq in  we; try lra.
  apply:Rabs_le.
  have h: Rabs (tl + vl) = -(tl + vl) by rewrite -Rabs_Ropp Rabs_pos_eq; lra.
  move:  tlvlu tlvlu'; rewrite h.
  lra.
have vhd : 2 - 8 * u <= vh.
  suff <- : rnd_p (2 - 8 * u) = (2 - 8 * u).
    apply: round_le.
    case/Rabs_le_inv: cu.
    lra.
  rewrite round_generic //.
  apply:(@FLX_format_Rabs_Fnum  (2 - 8 * u)( (Float two (two ^ (p) - 4)%Z (- p +1)%Z))).
    rewrite /F2R /= minus_IZR /= (IZR_Zpower two (p)) //.
      rewrite !bpow_plus /=.
      ring_simplify.
      rewrite/u Rplus_comm IZR_Zpower_pos /=; congr (_ + _); try ring.
      rewrite Rmult_1_r  -bpow_plus /= Z.add_opp_diag_r /=  ; ring.
    lia.
  rewrite /F2R /= minus_IZR /= (IZR_Zpower two (p )) //.
    rewrite Rabs_pos_eq; try lra.
    suff: pow 2  <= pow p by rewrite /= IZR_Zpower_pos /= ;lra.
    apply:bpow_le; move:Hp;lia.
   move:Hp;lia.
have wu: Rabs w <= 2 * u.
  suff ->:  2 * u = rnd_p (2 * u + u * u).
    rewrite /w ZNE -round_NE_abs -ZNE.
    by apply:round_le; rewrite  -/u.
  (* a remonter: duplication *)
  have -> : (2 * u + u * u) = (1 + u/2) * (pow (1 -p)) by rewrite bpow_plus -/u /= IZR_Zpower_pos /=; field.
  by rewrite round_bpow r1pu2 bpow_plus -/u /= IZR_Zpower_pos /= ; ring.
(* pose zh :=  (rnd_p (vh +  w)). *)
(* pose  zl :=  (F2Sum_err vh w). *)
have wlevh: Rabs w <= Rabs vh.
  apply:(Rle_trans _ (2 * u)) =>//.
  apply:(Rle_trans _ (2 - 8 * u)).
    suff: 10 * u <= 2  by lra.
    apply:(Rle_trans _ (16 * u)); try lra.
    have ->: 16 = pow 4 by [].
    have ->: 2 = pow 1 by [].
    rewrite -bpow_plus; apply: bpow_le; move: Hp3; lia.
  rewrite Rabs_pos_eq //.
  apply:(Rle_trans _ (2 - 8 * u))=>//.
  suff: 8 * u <= 2 by lra.
  have ->: 8 = pow 3  by [].
  have ->: 2 = pow 1 by [].
  rewrite -bpow_plus; apply: bpow_le;  lia.
have f2sc: Fast2Sum_correct  p choice vh w.
  apply:  F2Sum_correct_abs =>//; try apply: generic_format_round.
split; first by apply:  F2Sum_correct_DW'.
have fstE A (a b : A) : fst (a, b) = a  by []. 
have hl6: zh + zl = vh + w. 
  rewrite   f2sc fstE ; ring.
have -> : relative_errorDWDW  = Rabs((e1 + e2)/(x + y)).
  by apply: rel_errorDWDWe_abs.
rewrite /Rdiv Rabs_mult Rabs_Rinv //.
have:   Rabs (e1 + e2) <= 3 * u * u.
  apply:(Rle_trans _ (Rabs e1 + Rabs e2)); first apply: Rabs_triang; lra.
have xyd: (xh - u) + (yh - u) <= x + y.
  apply:Rplus_le_compat.
    case/Rabs_le_inv: xlu; lra.
  case/Rabs_le_inv: ylu; lra.
have xyd': 2 - 6 *u < x + y.
  apply:(Rlt_le_trans _ (xh - u + (yh - u)))=>//.
  lra.
move=>*; apply: Rmult_le_compat =>//=; try apply:Rabs_pos; try lra.
  by apply/Rlt_le/Rinv_0_lt_compat/Rabs_pos_lt.
have xypos: 0 < x + y.
  apply:(Rlt_trans _ (2 - 6  * u)) =>//.
  suff: 6 * u < 2 by lra.
  apply:(Rlt_trans _ ((pow 3) * (pow (-p)))) ; first by rewrite -/u /= IZR_Zpower_pos /= ;lra.
  rewrite -bpow_plus.
  have ->: 2 = pow 1 by [].
  apply:bpow_lt; move: Hp3; lia.
rewrite Rabs_pos_eq; try lra.
apply: Rinv_le.
  suff : (pow 2 ) * pow (-p) < 1 by rewrite /= -/u IZR_Zpower_pos /=; lra.
  have ->: 1 = pow 0 by [].
  rewrite -bpow_plus; apply: bpow_lt; move: Hp3; lia.
apply:(Rle_trans _ (2 - 6 * u)); try lra.
Qed.

End  DWPlusDW_Pre.

Section DWPlusDW.

Hypothesis Hp3 : (3 <= p)%Z.
Notation rndp_generic := (round_generic two fexp (Znearest choice)).
Notation ulp := (ulp two fexp).


Lemma error_le_x: forall x,  Rabs (rnd_p x - x) <= Rabs (rnd_p x).
Proof.
move => x.
apply:(Rle_trans _ (/ 2 * ulp (rnd_p x))).
apply:error_le_half_ulp_round.
case:(Req_dec (rnd_p x) 0)=> r0.
  by rewrite r0 ulp_FLX_0 Rabs_R0; lra.
apply:(Rle_trans _ (ulp (rnd_p x))).
  by move:(ulp_ge_0 two fexp (rnd_p x)); lra.
apply:ulp_le_abs =>//; apply:generic_format_round.
Qed.


Fact rel_errorDWDW_Sym (xh xl yh yl: R) 
              (Fxh: format xh) (Fyh: format yh) (Fxl: format xl)(Fyl: format yl)
 (sn0: xh + xl + (yh + yl) <> 0):
  (relative_errorDWDW (-xh) (-xl) (-yh) (-yl) ) =  
                           (relative_errorDWDW xh xl yh yl ).
Proof.
have rn_sym:= (rnd_p_sym p _ choiceP).
congr Rabs.
rewrite   /TwoSum_sum /TwoSum_err !TwoSum_asym //.
have rnd_opp a b: rnd_p (-a + -b) = - (rnd_p (a + b)).
  have ->: (-a + -b )= -(a + b) by ring.
  by rewrite ZNE round_NE_opp .
  rewrite !(rnd_opp, Fast2Sum_asym) -?ZNE //=.
  field.
by split; lra.
Qed.

Fact DW_asym xh xl: double_word xh xl -> double_word (-xh ) (-xl).
Proof.
case=>[[Fxh Fxl] xe]; split;[split; try apply:generic_format_opp|]=>//.
have -> : (- xh + - xl) = -(xh + xl) by ring.
by rewrite {1} xe ZNE round_NE_opp.
Qed.



Fact relative_errorDWDWC  xh xl yh yl (Fxh: format xh) (Fyh: format yh)
            (Fxl: format xl) (Fyl: format yl):
  (relative_errorDWDW  yh yl  xh xl ) =  (relative_errorDWDW  xh  xl yh yl ).
Proof.

  have TwoSumCh :=  (TwoSumC Fxh Fyh).
   have TwoSumCl :=  (TwoSumC Fxl Fyl).
   (* case : (TwoSumC Fxl Fyl)=> TwoSum_sumCl TwoSum_errCl. *)
rewrite /relative_errorDWDW /TwoSum_sum /TwoSum_err TwoSumCh TwoSumCl.
by have ->: (yh  + yl + ( xh + xl)) = (xh + xl + (yh + yl)) by ring.
Qed.

Fact relative_errorDWDWS  xh xl yh yl  exp (Fyh : format yh) (Fxh : format xh) (Fxl: format xl) (Fyl: format yl): 
  xh + xl + yh + yl  <> 0 -> let e := pow exp in 
  (relative_errorDWDW   (xh*e)  (xl* e) (yh * e) (yl *e)  ) =  (relative_errorDWDW  xh  xl yh yl).
Proof.
  move=> xyn0 /=.
  
rewrite /relative_errorDWDW.  congr Rabs. rewrite /TwoSum_sum /TwoSum_err !TwoSumS //= !(=^~ Rmult_plus_distr_r, round_bpow, =^~ Rmult_minus_distr_r).

field.
 split =>//; move:(bpow_gt_0 two exp); lra.
Qed.

(* Notation TwoSum_sum a b := (rnd_p (a + b)). *)


Theorem  DWPlusDW_relerr_bound (xh xl yh yl: R) 
         (DWx: double_word xh xl)(DWy: double_word yh yl)  (xyn0: (xh+xl + (yh + yl) <> 0)): 
         (relative_errorDWDW xh xl yh yl )<=  (3 * u^2) / (1 - 4 * u).
Proof.
(* pose ulp:= (ulp two fexp). *)
wlog xhy : xh xl yh yl  DWx DWy xyn0 /  Rabs yh <= Rabs xh.
  move=> Hwlog.
  case:(Rle_lt_dec (Rabs yh) (Rabs xh) )=> absyxh.
    by apply: Hwlog =>//.
  case:(DWx)=>[[Fxh Fxl] hx].
  case:(DWy)=>[[Fyh Fyl] hy].
  by rewrite relative_errorDWDWC //;  apply:Hwlog =>//; try lra.
case:(DWx)=>[[Fxh Fxl] hx].
case:(DWy)=>[[Fyh Fyl] hy].
pose x := xh + xl.
pose y := yh + yl.
have F0:= (generic_format_0 two fexp).
case:(Req_dec xh 0)=> x0.
  suff -> : relative_errorDWDW xh xl yh yl = 0 by apply: boundDWDW_ge_0.
  have xl0: xl = 0.
    move: (dw_ulp DWx).
    rewrite x0 ulp_FLX_0 Rmult_0_r => absle0.
    have abs0 : Rabs xl = 0 by move:(Rabs_pos xl); lra.
      by case:(Req_dec xl 0)=>// /Rabs_no_R0;lra. 
  by rewrite relative_errorDWDWxh0.  
have TwoSum_sumE' a b : fst (TwoSum a b ) = rnd_p (a+b) by [].
case:(Req_dec (xh + yh) 0)=> s0.
  suff -> : relative_errorDWDW xh xl yh yl = 0  by apply: boundDWDW_ge_0.
  rewrite /relative_errorDWDW TwoSum_correct // !(TwoSum_sumE, s0, TwoSum_sumE',
  round_0, Rminus_0_r,Rplus_0_l).
  rewrite (round_round Hp).
  set r := (rnd_p (xl + yl)).
  have Fr : format r by apply:generic_format_round.
  rewrite Fast2Sum0f //=.
  rewrite Rplus_0_r.
  have ->: (rnd_p (TwoSum_err xl yl)) =  (TwoSum_err xl yl) by rewrite (round_round Hp).
  rewrite Rabs0 // /Rdiv. 
  set num := (_ + _ - _).
  suff ->:  num = 0 by ring.
  rewrite /num .
  have->:  (r + TwoSum_err xl yl) = xl + yl.
    by rewrite TwoSum_correct // TwoSum_sumE   /r; ring.
    rewrite -/r (Rminus_diag_eq r)// round_0 Rminus_0_r round_generic //.
   rewrite  TwoSum_correct //= TwoSum_sumE /r. 
   lra.
  by rewrite /TwoSum_err ; apply:generic_format_round.
clear Fxh Fxl hx x Fyh Fyl hy y.
wlog xhpos:  xh xl DWx yh yl DWy xyn0 xhy x0 s0 / 0 <  xh.
  move=> Hwlog.
  case: (Rle_lt_dec 0 xh)=> xh0.
    apply:Hwlog => //; lra.
  case:(DWx)=>[[Fxh Fxl] hx].
  case:(DWy)=>[[Fyh Fyl] hy].
  rewrite -rel_errorDWDW_Sym =>//.
  apply: Hwlog; try lra; try apply: DW_asym => //.
  by rewrite !Rabs_Ropp.
wlog [xh1 xh2]:  xh xl yh yl DWx DWy xyn0 xhy s0 x0 xhpos
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
    + rewrite -!Rmult_plus_distr_r.
      by apply: Rmult_integral_contrapositive_currified; lra.
    + rewrite !Rabs_mult  (Rabs_pos_eq (pow _)); try lra.
      by apply: Rmult_le_compat_r ; lra.
  rewrite -!Rmult_plus_distr_r.
  by apply: Rmult_integral_contrapositive_currified; lra.
by  case:( DWPlusDW_relerr_bound_pre Hp3 DWx DWy).
Qed.

End  DWPlusDW.


End DWPlus.


 
