(* Copyright (c)  Inria. All rights reserved. *)
From Stdlib Require Import Reals Psatz.
From Flocq Require Import Core Plus_error Relative Sterbenz Operations.
From Flocq Require Import  Round.
Require Import mathcomp.ssreflect.ssreflect.
Require Import F2SumFLX.
Set Implicit Arguments.


Section Fast2Sum2.




Local Notation pow e := (bpow radix2 e).
Local Open Scope Z_scope.

Variables p  : Z.
Hypothesis Hp : Z.lt 1 p.

Local Instance p_gt_0 : Prec_gt_0 p.
Proof. by apply:(Z.lt_trans _ 1). Qed.

Notation fexp := (FLX_exp p).
Notation format := (generic_format radix2 fexp).
Notation ce := (cexp radix2 fexp).

Variable choice : Z -> bool.

Local Notation rnd_p := (round radix2 fexp (Znearest choice)).

Definition pair_opp (p: R*R):= ((-(fst p))%R, (- (snd p))%R).


Definition  Fast2Sum := (F2SumFLX.Fast2Sum radix2 p choice).



Definition  Fast2Sum_correct a b  := 
   let s := fst (Fast2Sum a b) in let t := snd (Fast2Sum a b) in t = (a+b -s)%R.

Fact Fast2Sum0f b (Fb:format b): (Fast2Sum 0 b ) = (b,0%R).
Proof. 
rewrite /Fast2Sum /F2SumFLX.Fast2Sum   !(Rplus_0_l, Rminus_0_r, round_0) !round_generic //;
  ring_simplify(b-b)%R=>//.
by apply:generic_format_0.
Qed.

 Fact Fast2Sumf0 a (Fa:format a): (Fast2Sum a 0 ) = (a,0%R).
 Proof. 
by rewrite /Fast2Sum  /F2SumFLX.Fast2Sum  !(Rplus_0_r, Rminus_0_l, round_0) !round_generic //;
  ring_simplify(a-a)%R; rewrite ?Ropp_0 // ;
  apply:generic_format_0.
Qed.



Hypothesis rnd_p_sym : forall x, (rnd_p (-x) = - (rnd_p x))%R.

Fact Fast2Sum0 a  b (Fa: format a) : (b = -a)%R
      -> (Fast2Sum a b) = (0%R,0%R).
Proof.
move->.
rewrite /Fast2Sum /F2SumFLX.Fast2Sum .
have ->: (a +  -a = 0)%R by ring.
rewrite round_0 Rminus_0_l rnd_p_sym (round_generic _ _ _ a) //.
ring_simplify (-a - - a)%R.
by rewrite round_0.
Qed.
 
 Fact Fast2Sum_asym a b : Fast2Sum (-a) (-b) = pair_opp (Fast2Sum a b).
 Proof.
rewrite /Fast2Sum /F2SumFLX.Fast2Sum   /pair_opp/=.
rewrite -!Ropp_plus_distr rnd_p_sym.
rewrite -2!Ropp_minus_distr Ropp_involutive -Ropp_minus_distr.
set rab := rnd_p (a + b).
have->: (-rab - - a = - (rab - a))%R  by ring.
rewrite  !rnd_p_sym.
by have->: ((- rnd_p (rab - a) - - b) = (b - rnd_p (rab - a)))%R by ring.
Qed.
 
Fact Fast2SumS  x y  e (Fx : format x) (Fy : format y):
   Fast2Sum (x * pow e)  (y * pow e)  = ((fst (Fast2Sum x y) * pow e)%R,
                                (snd (Fast2Sum x y) * pow e)%R).
Proof.
rewrite /= /Fast2Sum /F2SumFLX.Fast2Sum .
by rewrite /= !(=^~ Rmult_plus_distr_r, round_bpow, =^~ Rmult_minus_distr_r).
Qed.

Hypothesis Hb3 : radix2 <= 3.

Theorem F2Sum_correct_proof a b (Fa : format a) (Fb : format b) :
     (exists (fa:float radix2), a = F2R fa /\ ce b <= Fexp fa )->
Fast2Sum_correct  a b.
Proof.
case=> fa [faE hle].
case:(@getnum_fa _ _ Hp a b Fa fa)=>// fa' [fa'E [h1 h2]].
by apply Fast2Sum_correct_proof_aux with (fa := fa').
Qed.


Theorem F2Sum_correct_cexp a b (Fa : format a) (Fb : format b) : 
                ce b <= ce a  -> Fast2Sum_correct  a b.
Proof.
move=> cexp_le.


move:(Fa); rewrite /generic_format.
set Ma := Ztrunc _.
set fa := Float radix2 _ _.
move=> afE.
by apply Fast2Sum_correct_proof_aux with (fa := fa).
Qed.

Theorem F2Sum_correct_abs a b (Fa : format a) (Fb : format b) :
   (Rabs b <= Rabs a)%R  -> Fast2Sum_correct  a b. 
Proof.
move=> abs_le.
move:(Fa); rewrite /generic_format.
set Ma := Ztrunc _.
set fa := Float radix2 _ _.
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
split; first by split; rewrite -?sE -?tE; apply:generic_format_round.
by have -> : (s + t = a+b)%R;  lra.
Qed.

End Fast2Sum2.
