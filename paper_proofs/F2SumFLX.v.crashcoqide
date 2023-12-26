(* Copyright (c)  Inria. All rights reserved. *)
Require Import Reals  Psatz.
From Flocq Require Import Core Plus_error Relative Sterbenz Operations.
Require Import F2SumFLT.

Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.


Section Fast2Sum.
Variable beta: radix.
Local Notation pow e := (bpow beta e).
Local Open Scope Z_scope.

Variables p  : Z.
Hypothesis Hp : Z.lt 1 p. 

Local Instance p_gt_0 : Prec_gt_0 p.
Proof. by apply:(Z.lt_trans _ 1). Qed.

Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation ce := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).

Variable choice : Z -> bool.


Local Notation rnd_p := (round beta fexp (Znearest choice)).
Hypothesis rnd_p_sym : forall x, (rnd_p (-x) = - rnd_p (x))%R.


Theorem cexp_bpow  x e (xne0: x <> R0):  ce (x * pow e) = ce x + e.
Proof. rewrite /ce mag_mult_bpow // /FLX_exp; ring. Qed.

Theorem mant_bpow x e : mant (x * pow e) = mant x.
Proof.
case: (Req_dec x 0) => [->|Zx]; first by rewrite Rmult_0_l.
rewrite /scaled_mantissa cexp_bpow // Rmult_assoc -bpow_plus.
by ring_simplify (e + - (ce x + e)).
Qed.


Theorem round_bpow  x e:  rnd_p (x * pow e) = (rnd_p x * pow e)%R.
Proof.
case: (Req_dec x 0) => [->|Zx] ; first by rewrite Rmult_0_l round_0 Rmult_0_l.
by rewrite /round /F2R /= mant_bpow  cexp_bpow // bpow_plus Rmult_assoc.
Qed.


(* (* to move .... MoreFLXFlocq *) *)

(* cf FLX_format *)
Theorem FLX_mant_le  x (Fx: format x): Z.abs (Ztrunc (mant x)) <= beta^p - 1.
Proof.
suff :  (Z.abs (Ztrunc (mant x)) < beta ^ p)%Z by lia.
apply: lt_IZR; rewrite abs_IZR - scaled_mantissa_generic //.
rewrite IZR_Zpower; last lia.
have ->:  pow p = pow (mag beta x - ce x) by rewrite /ce /fexp; congr bpow; ring.
exact : scaled_mantissa_lt_bpow.
Qed.


Definition pair_opp (p: R*R):= ((-(fst p))%R, (- (snd p))%R).

Section F2Sum.

Variables a b   : R.
Hypothesis Fa : format a.
Hypothesis Fb : format b.
Notation  s := (rnd_p (a + b)).
Notation  z := (rnd_p (s - a)).
Notation t := (rnd_p (b - z)).
Hypothesis Hb3 : beta <= 3.

Variable fa : float beta.
Hypothesis exp_le:  (a = F2R fa) /\ (ce b  <= Fexp fa).

Notation ubemin x := ( mag beta  x - p)%Z.

Fact Rle_pmabs emin x:  (emin <= ubemin x)%Z -> x <> 0%R ->  (pow (emin + p - 1) <= Rabs x)%R.
Proof.
move=> hemin xn0.
apply:(Rle_trans _ (pow  ((mag beta x) - 1))).
  apply:bpow_le; lia.
by apply: bpow_mag_le.
Qed.


Definition  emin :=  (Z.min (ubemin a)
                           (Z.min (ubemin b)
                           (Z.min (ubemin s)
                           (Z.min (ubemin (a + b))
                           (Z.min  (ubemin z)
                           (Z.min (ubemin (s - a))
                           (Z.min (ubemin (b - z))(ubemin t)))))))).



Fact getnum_fa:  exists  (fa : float beta), 
                 (a = F2R fa) /\  (Z.abs (Fnum fa) <= beta^p - 1)
                /\ (ce b  <= Fexp fa).
Proof.
case:exp_le => h1 h2.
case:(Z_lt_le_dec  ( ce a ) (ce b))=> h;  last first.
  rewrite Fa.
  set f'a := (Float beta _ _).
  exists f'a; split=>//; rewrite /fa /=; split =>//.
  by apply:FLX_mant_le.
exists fa; split=>//; split =>//.
move:h1; rewrite  Fa /F2R /=.
have -> : (Fexp fa) = ((Fexp fa) - (ce a)) + ce a by ring.
rewrite bpow_plus -Rmult_assoc.
move/Rmult_eq_reg_r.
have hh: pow (ce a) <> 0%R by move:(bpow_gt_0 beta (ce a)); lra.
move/(_ hh)=> h1.
apply:(Z.le_trans _ (Z.abs (Ztrunc (mant a)))); last by apply:FLX_mant_le.
apply:le_IZR.
rewrite !abs_IZR  h1 Rabs_mult // -[X in (X <= _)%R]Rmult_1_r.
apply:Rmult_le_compat_l; first by apply: Rabs_pos.
rewrite Rabs_pos_eq ; last by apply:bpow_ge_0.
change ( pow 0 <= pow (Fexp fa - ce a))%R.
by apply:bpow_le; lia.
Qed.


(* Hypothesis ZNE : choice = fun n => negb (Z.even n). *)

Theorem Fast2Sum_correct_proof_aux : t = (a + b - s)%R.
Proof.

case:getnum_fa=>// fa' [fa'E [h1 h2]].
case:(Req_dec a 0)=>a0.
  rewrite a0 !Rplus_0_l Rminus_0_r !round_generic //.
  have ->: (b - b = 0)%R by ring.
  by apply/generic_format_0.
have emin_a: (pow (emin + p - 1) <= Rabs a)%R.
  apply:Rle_pmabs=>//.
  by repeat (apply: Z.le_min_l || apply: (Z.le_trans _ _ _ (Z.le_min_r _ _))). 
case:(Req_dec b 0)=>b0.
   rewrite b0 !Rplus_0_r (round_generic _ _ _ a) //.
  have ->: (a - a = 0)%R by ring.
  by rewrite round_0 Rminus_0_r round_0 //.
have emin_b: (pow (emin + p - 1) <= Rabs b)%R.
  apply:Rle_pmabs=>//.
  by repeat (apply: Z.le_min_l || apply: (Z.le_trans _ _ _ (Z.le_min_r _ _))). 
case:(Req_dec (a+b) 0)=>ab0.
  rewrite  ab0 round_0 Rminus_0_l Rminus_0_r.
  rewrite  rnd_p_sym (round_generic _ _ _ a) //.
  have-> : (b - - a = a + b)%R by ring.
  by rewrite ab0 round_0.
have emin_apb: (pow (emin + p - 1) <= Rabs (a+b))%R.
  apply:Rle_pmabs=>//.
  by repeat (apply: Z.le_min_l || apply: (Z.le_trans _ _ _ (Z.le_min_r _ _))). 
case:(Req_dec (s - a) 0)=>sma0.
 rewrite  sma0 round_0 Rminus_0_r round_generic //; lra.
have emin_sma: (pow (emin + p - 1) <= Rabs (s-a))%R.
  apply:Rle_pmabs=>//.
  by repeat (apply: Z.le_min_l || apply: (Z.le_trans _ _ _ (Z.le_min_r _ _))). 
case:(Req_dec (b - z) 0)=>bmz0.
  (* pose emin := (Z.min (ubemin a)  *)
  (* (Z.min (ubemin b) (Z.min (ubemin (a + b))   (ubemin (s -a))))). *)
  rewrite bmz0 round_0 -!(round_FLT_FLX _ emin)//.
  have ->: (0%R = round beta (FLT_exp emin p) (Znearest choice) (b -z))%R.
    by rewrite bmz0 round_0.
  rewrite -!(round_FLT_FLX _ emin) //.
    apply Fast2Sum_correct_proof_flt with (fa := fa')=>//.
    + by rewrite /Prec_gt_0; lia.
    + by apply:generic_format_FLT_FLX.
    + by apply:generic_format_FLT_FLX.
    split=>//; split=>//.
    by rewrite cexp_FLT_FLX.
  by rewrite (round_FLT_FLX _ emin).
have emin_bmz: (pow (emin + p - 1) <= Rabs (b -z))%R.
  apply:Rle_pmabs=>//.
  by repeat (apply: Z.le_min_l || apply: (Z.le_trans _ _ _ (Z.le_min_r _ _))). 
rewrite -!(round_FLT_FLX _ emin)//.
+ apply Fast2Sum_correct_proof_flt with (fa := fa')=>//.
  - rewrite / Prec_gt_0; lia.
  - by apply:generic_format_FLT_FLX.
  - by apply:generic_format_FLT_FLX.
  split=>//; split=>//.
  by rewrite cexp_FLT_FLX.
+ by rewrite !(round_FLT_FLX _ emin).
+ by rewrite !(round_FLT_FLX _ emin).
+ by rewrite !(round_FLT_FLX _ emin).
Qed.



Definition Fast2Sum := (s, t).


Definition  Fast2Sum_correct  := 
   let s := fst Fast2Sum  in let t := snd Fast2Sum  in t = (a+b -s)%R.
End F2Sum.



Fact Fast2Sum0f b (Fb:format b): (Fast2Sum 0 b ) = (b,0%R).
Proof. 
rewrite /Fast2Sum !(Rplus_0_l, Rminus_0_r, round_0) !round_generic //;
  ring_simplify(b-b)%R=>//.
by apply:generic_format_0.
Qed.

 Fact Fast2Sumf0 a (Fa:format a): (Fast2Sum a 0 ) = (a,0%R).
 Proof. 
by rewrite /Fast2Sum !(Rplus_0_r, Rminus_0_l, round_0) !round_generic //;
  ring_simplify(a-a)%R; rewrite ?Ropp_0 // ;
  apply:generic_format_0.
Qed.

Hypothesis ZNE : choice = fun n => negb (Z.even n).
 
 Fact Fast2Sum_asym a b : Fast2Sum (-a) (-b) = pair_opp (Fast2Sum a b).
 Proof.
rewrite /Fast2Sum /pair_opp/=.
rewrite -!Ropp_plus_distr ZNE round_NE_opp -ZNE.
rewrite -2!Ropp_minus_distr Ropp_involutive -Ropp_minus_distr.
set rab := rnd_p (a + b).
have->: (-rab - - a = - (rab - a))%R  by ring.
rewrite  ZNE !round_NE_opp -ZNE.
by have->: ((- rnd_p (rab - a) - - b) = (b - rnd_p (rab - a)))%R by ring.
Qed.
 
Fact Fast2SumS  x y  e (Fx : format x) (Fy : format y):
   Fast2Sum (x * pow e)  (y * pow e)  = ((fst (Fast2Sum x y) * pow e)%R,
                                (snd (Fast2Sum x y) * pow e)%R).
Proof.
rewrite /= /Fast2Sum.
by rewrite /= !(=^~ Rmult_plus_distr_r, round_bpow, =^~ Rmult_minus_distr_r).
Qed.

Hypothesis Hb3 : beta <= 3.

Notation ubemin x := ( mag beta  x - p)%Z.

Theorem F2Sum_correct_proof a b (Fa : format a) (Fb : format b) :
     (exists (fa:float beta), a = F2R fa /\ ce b <= Fexp fa )->
Fast2Sum_correct  a b.
Proof.
case=> fa [faE hle].
case:(@getnum_fa a b Fa fa)=>// fa' [fa'E [h1 h2]].
rewrite /Fast2Sum_correct /=.
by rewrite   (@Fast2Sum_correct_proof_aux _ _ Fa Fb Hb3 fa').
Qed.

Theorem F2Sum_correct_cexp a b (Fa : format a) (Fb : format b) : 
                ce b <= ce a  -> Fast2Sum_correct  a b.
Proof.
move=> cexp_le.


move:(Fa); rewrite /generic_format.
set Ma := Ztrunc _.
set fa := Float beta _ _.
move=> afE.
apply: (@Fast2Sum_correct_proof_aux _ _ _ _ _ fa)=>//.
Qed.

Theorem F2Sum_correct_abs a b (Fa : format a) (Fb : format b) :
   (Rabs b <= Rabs a)%R  -> Fast2Sum_correct  a b. 
Proof.
move=> abs_le.
move:(Fa); rewrite /generic_format.
set Ma := Ztrunc _.
set fa := Float beta _ _.
move=> afE.
case:(Req_dec b 0)=> [->|b0].         
rewrite /Fast2Sum_correct Fast2Sumf0 //=; ring.
apply:F2Sum_correct_cexp=>//.
by apply/FLX_exp_monotone/mag_le_abs.
Qed.

Theorem  F2Sum_correct_DW a b : Fast2Sum_correct  a b ->
let s := fst (Fast2Sum a b) in let t := snd (Fast2Sum a b) in 
     (format s /\format t) /\ s = rnd_p (s + t).
Proof.  
rewrite  /Fast2Sum_correct.
case H: (Fast2Sum a b) => [s t] /=.
move: H; rewrite /Fast2Sum; case=> sE tE H.
split;first by split; rewrite -?sE -?tE; apply:generic_format_round.
by have -> : (s + t = a+b)%R;  lra.
Qed.

End Fast2Sum.
