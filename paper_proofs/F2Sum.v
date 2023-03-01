(* Copyright (c)  Inria. All rights reserved. *)
Require Import Reals  Psatz.
From Flocq Require Import Core Plus_error Relative Sterbenz Operations.
From Flocq Require Import  Round.
Require Import mathcomp.ssreflect.ssreflect.
Require Import F2SumFLX.
Set Implicit Arguments.


Section Fast2Sum2.




(* (* Variable beta: radix. *) *)
Local Notation pow e := (bpow radix2 e).
Local Open Scope Z_scope.

Variables p  : Z.
Hypothesis Hp : Z.lt 1 p.

Local Instance p_gt_0 : Prec_gt_0 p.
Proof. by apply:(Z.lt_trans _ 1). Qed.

Notation fexp := (FLX_exp p).
Notation format := (generic_format radix2 fexp).
Notation ce := (cexp radix2 fexp).
(* Local Notation mant := (scaled_mantissa radix2 fexp). *)

Variable choice : Z -> bool.

Local Notation rnd_p := (round radix2 fexp (Znearest choice)).

(* Notation cexp_bpow := (cexp_bpow radix2). *)
(* Notation mant_bpow := (mant_bpow radix2). *)
(* Notation round_bpow := (round_bpow radix2). *)
(* (* Theorem cexp_bpow  x e (xne0: x <> R0):  ce (x * pow e) = ce x + e. *) *)
(* (* Proof. rewrite /ce mag_mult_bpow // /FLX_exp; ring. Qed. *) *)

(* (* Theorem mant_bpow x e : mant (x * pow e) = mant x. *) *)
(* (* Proof. *) *)
(* (* case: (Req_dec x 0) => [->|Zx]; first by rewrite Rmult_0_l.  *) *)
(* (* rewrite /scaled_mantissa cexp_bpow // Rmult_assoc -bpow_plus. *) *)
(* (* by ring_simplify (e + - (ce x + e)). *) *)
(* (* Qed. *) *)


(* (* Theorem round_bpow  x e:  rnd_p (x * pow e) = (rnd_p x * pow e)%R. *) *)
(* (* Proof. *) *)
(* (* case: (Req_dec x 0) => [->|Zx] ; first by rewrite Rmult_0_l round_0 Rmult_0_l. *) *)
(* (* by rewrite /round /F2R /= mant_bpow  cexp_bpow // bpow_plus Rmult_assoc. *) *)
(* (* Qed. *) *)


(* (* to move .... MoreFLXFlocq *) *)

(* (* cf FLX_format *) *)
(* (* Theorem FLX_mant_le  x (Fx: format x): Z.abs (Ztrunc (mant x)) <= radix2^p - 1. *) *)
(* (* Proof. *) *)
(* (* suff :  (Z.abs (Ztrunc (mant x)) < radix2 ^ p)%Z by lia. *) *)
(* (* apply: lt_IZR; rewrite abs_IZR - scaled_mantissa_generic //. *) *)
(* (* rewrite IZR_Zpower; last lia. *) *)
(* (* have ->:  pow p = pow (mag radix2 x - ce x) by rewrite /ce /fexp; congr bpow; ring. *) *)
(* (* exact : scaled_mantissa_lt_bpow. *) *)
(* (* Qed. *) *)

(* (* move ??*)  *)
(* Theorem FLX_Rabs_le x (Fx: format x) : (Rabs x <= (pow p - 1) * pow (ce x))%R. *)
(* Proof. *)
(* move:(Fx). *)
(* rewrite /generic_format =>xE. *)
(* rewrite {1}xE /F2R /= Rabs_mult (Rabs_pos_eq (pow _)); last exact: bpow_ge_0. *)
(* apply:Rmult_le_compat_r; first exact: bpow_ge_0. *)
(* move/IZR_le: (FLX_mant_le Hp Fx); rewrite -abs_IZR minus_IZR (IZR_Zpower radix2) //; lia. *)
(* Qed. *)

(* Theorem F_Rabs_le x (Fx: format x): exists (fx : float radix2),   *)
(*       x = F2R fx /\  (Rabs x <= (pow p - 1) * pow (Fexp fx))%R. *)
(* Proof. *)
(* case/FLX_format_generic:(Fx)=> f  xf hnum. *)
(* exists f; split=>//. *)
(* rewrite xf  /F2R /= Rabs_mult. *)
(* apply:Rmult_le_compat; try  apply:Rabs_pos; last  by  rewrite (Rabs_pos_eq (pow _)); try lra; exact : bpow_ge_0. *)
(* have : Z.abs (Fnum f) <= radix2 ^ p -1 by lia. *)
(* move/IZR_le; rewrite abs_IZR minus_IZR IZR_Zpower //; lia. *)
(* Qed. *)


(* Fact Znearest_scale : *)
(*   forall  f m n, (1 <= f)%R -> *)
(*   IZR (Znearest choice (m * f)) = (IZR n * f)%R -> Znearest choice m = n. *)
(* Proof. *)
(* move=>  f m n [Hf|Hf1]; last by  rewrite -Hf1 !Rmult_1_r; exact: eq_IZR. *)
(* move=>H; apply: Znearest_imp. *)
(* move: (Znearest_half choice (m * f)). *)
(* rewrite H -Rmult_minus_distr_r Rabs_mult  (Rabs_pos_eq f); last lra. *)
(* move=>H'. *)
(* apply:(Rmult_lt_reg_r f); first lra; apply:(Rle_lt_trans _ (/2))=>//. *)
(* rewrite -{1}(Rmult_1_r (/2)); apply/Rmult_lt_compat_l =>//. *)
(* apply/Rinv_0_lt_compat; lra. *)
(* Qed. *)


(* Fact mant_N_e : forall x m, x <> R0 -> *)
(*   x = (rnd_p (pow (ce x) * m)) -> mant x = IZR (Znearest choice m). *)
(* Proof. *)
(* move=> x m Zx Hx. *)
(* case:(Req_dec m 0) => Zm. *)
(*   by elim: Zx; rewrite  Hx Zm Rmult_0_r round_0. *)
(* rewrite Rmult_comm in Hx. *)
(* case: (mag_round radix2 fexp (Znearest choice) (m * pow (ce x)));  *)
(*       rewrite -Hx // => Er. *)
(* (* general case: x is  in the same slice as m * pow (ce x) *) *)
(*   rewrite /scaled_mantissa {1}Hx /round /F2R /= /scaled_mantissa {2 4}/ce -Er. *)
(*   by rewrite  2!Rmult_assoc -bpow_plus Zplus_opp_r !Rmult_1_r. *)
(* (* is_pow x *) *)
(* rewrite Zmax_left -cexp_abs in Er; last by rewrite /fexp; lia. *)
(* rewrite cexp_abs in Er. *)
(* have: (mag radix2 (Rabs x) = mag radix2 (pow (mag radix2 (m * pow (ce x)))) :>Z)  *)
(*  by rewrite Er. *)
(* rewrite  mag_bpow mag_abs=> Er'. *)
(* have {Er} Er:  x = cond_Ropp (Rlt_bool x 0) (pow (mag radix2 (m * pow (ce x)))). *)
(*   rewrite -[LHS](cond_Ropp_involutive (Rlt_bool x 0)). *)
(*   by congr  cond_Ropp; rewrite (cond_Ropp_Rlt_bool x). *)
(* rewrite /scaled_mantissa. *)
(* rewrite {1} Er - cond_Ropp_mult_l - bpow_plus. *)
(* have: (cond_Ropp (Rlt_bool x 0) (pow (mag radix2 (m * pow (ce x)) + - ce x)) * *)
(*   pow (ce x + - ce (m * pow (ce x))) = *)
(*   IZR (Znearest choice (m * pow (ce x + - ce (m * pow (ce x))))))%R. *)
(*   apply:(Rmult_eq_reg_r (pow (ce (m * pow (ce x))))); last first. *)
(*     by apply: Rgt_not_eq; apply bpow_gt_0. *)
(*   rewrite - 2!cond_Ropp_mult_l - 2!bpow_plus. *)
(*   ring_simplify (mag radix2 (m * pow (ce x)) + - ce x + *)
(*     (ce x + - ce (m * pow (ce x))) + ce (m * pow (ce x))). *)
(*   by rewrite bpow_plus - Rmult_assoc -Er //. *)
(* rewrite -IZR_Zpower;  last by rewrite {3}/cexp {3}/fexp Er'; lia. *)
(* rewrite  -IZR_cond_Zopp. *)
(* set zx := (cond_Zopp _ _)=> H. *)
(* have H' := (sym_eq H). *)
(* rewrite (@Znearest_scale ( pow (ce x + - ce (m * pow (ce x)))) m zx) //. *)
(* apply:(bpow_le radix2 0); apply Zle_minus_le_0; rewrite /cexp {1 4}/ fexp -/(ce x) Er'; lia. *)
(* Qed. *)

(* Theorem mant_N x m:  *)
(*   x = (rnd_p (pow (ce x) * m)) -> Ztrunc (mant x) = Znearest choice m. *)
(* Proof.  *)
(* case:(Req_dec x 0) => [Zx|Zx]; last first. *)
(*   move=> H; apply: eq_IZR. *)
(*   rewrite -scaled_mantissa_generic ; first by  apply mant_N_e. *)
(*   by rewrite H; apply: generic_format_round. *)
(* move=>h. *)
(* have {h}h: rnd_p (pow (ce x) * m) = 0%R by lra. *)
(* have :(pow (ce x) * m)%R = 0%R by apply:  (eq_0_round_0_FLX _ _ _ _   h). *)
(* case/Rmult_integral=>[|->]; first last. *)
(*   rewrite Zx scaled_mantissa_0; change R0 with (IZR 0). *)
(*   by rewrite (Zrnd_IZR (Znearest _)) Zrnd_IZR. *)
(* by move :(bpow_gt_0 radix2 (ce x)); lra. *)
(* Qed. *)

(* (* cf generic_format_FLX *) *)

(* Lemma FLX_format_Rabs_Fnum (x : R) (fx : float radix2): *)
(*   x = F2R fx -> (Rabs (IZR (Fnum fx)) < pow p )%R-> *)
(*    format  x. *)
(* Proof. *)
(* move=>xe fxnlt; apply/generic_format_FLX /(FLX_spec _ _ _ fx)=>//. *)
(* apply/lt_IZR; rewrite IZR_Zpower ?abs_IZR //; lia. *)
(* Qed. *)

(* Lemma FLX_format_Rabs_Fnumf  (fx : float radix2): *)
(*   (Rabs (IZR (Fnum fx)) < pow p )%R-> *)
(*    format  (F2R fx). *)
(* Proof. *)
(* move=>hFnum; by apply:FLX_format_Rabs_Fnum. *)
(* Qed. *)

Definition pair_opp (p: R*R):= ((-(fst p))%R, (- (snd p))%R).

(* Section F2Sum. *)

(* Variables a b   : R. *)
(* Hypothesis Fa : format a. *)
(* Hypothesis Fb : format b. *)
(* Notation  s := (rnd_p (a + b)). *)
(* Notation  z := (rnd_p (s - a)). *)
(* Notation t := (rnd_p (b - z)). *)
(* Hypothesis Hb3 : radix2 <= 3. *)

(* Variable fa : float radix2. *)
(* Hypothesis exp_le:  (a = F2R fa) /\ (ce b  <= Fexp fa). *)



(* Fact getnum_fa:  exists  (fa : float radix2), (a = F2R fa) /\  (Z.abs (Fnum fa) <= radix2^p - 1)   *)
(*                 /\ (ce b  <= Fexp fa). *)

(* case:exp_le => h1 h2. *)
(* case:(Z_lt_le_dec  ( ce a ) (ce b))=> h;  last first. *)
(* rewrite Fa. *)
(* set f'a := (Float radix2 _ _). *)

(* exists f'a. *)
(* split=>//. *)
(* rewrite /fa /=; split =>//. *)
(* by apply:FLX_mant_le. *)


(* exists fa. *)
(* split=>//; split =>//. *)
(* move:h1; rewrite  Fa /F2R /=. *)
(* have -> : (Fexp fa) = ((Fexp fa) - (ce a)) + ce a by ring. *)
(* rewrite bpow_plus -Rmult_assoc. *)
(* Search (_ = _)%R (_ * _ = _*_)%R. *)

(* move/Rmult_eq_reg_r. *)

(* have hh: pow (ce a) <> 0%R by move:(bpow_gt_0 radix2 (ce a)); lra. *)
(* move/(_ hh)=> h1. *)

(* apply:(Z.le_trans _ (Z.abs (Ztrunc (mant a)))); last first. *)
(* by apply:FLX_mant_le. *)
(* apply:le_IZR. *)
(* rewrite !abs_IZR. *)
(* rewrite h1 Rabs_mult. *)
(* rewrite -[X in (X <= _)%R]Rmult_1_r. *)
(* apply:Rmult_le_compat_l; first by apply: Rabs_pos. *)
(* rewrite Rabs_pos_eq ; last by apply:bpow_ge_0. *)
(* change ( pow 0 <= pow (Fexp fa - ce a))%R. *)
(* apply:bpow_le. *)
(* lia. *)
(* Qed. *)

(* Section F2Sum_aux. *)
(* Hypothesis num_le: (Z.abs (Fnum fa) <= radix2^p - 1). *)


(* Fact F2Sexp_aux (sn0: (s <> 0)%R): (ce s  <= 1 + Fexp fa)%Z. *)
(* Proof. *)
(* case:exp_le => [faE  cebfa]. *)

(* pose ea := Fexp fa. *)
(* move:(Fb); rewrite /generic_format /F2R [X in _ = X]/=;  set Mb := Ztrunc _; move => bfE. *)
(* have Habs: (Rabs (a + b) <= (pow p - 1) * pow (1 +ea))%R. *)
(*   apply :(Rle_trans _ _  _  (Rabs_triang _ _)). *)
(*   rewrite faE bfE  /F2R !Rabs_mult !(Rabs_pos_eq (pow _)); try apply: bpow_ge_0. *)
(*   rewrite Zplus_comm bpow_plus. *)
(*   have ->: pow 1 = IZR (1 + (radix2 -1)). *)
(*     rewrite plus_IZR minus_IZR /=. *)
(*     by rewrite IZR_Zpower_pos /=; ring. *)
(*   rewrite plus_IZR -Rmult_assoc Rmult_plus_distr_l Rmult_1_r. *)
(*   apply: Rplus_le_compat. *)
(*     rewrite /ea; apply: Rmult_le_compat_r; first apply: bpow_ge_0. *)
(*     by move/IZR_le : num_le; rewrite abs_IZR minus_IZR IZR_Zpower //; lia. *)
(*   rewrite Rmult_assoc. *)
(*   apply: Rmult_le_compat;  [apply:Rabs_pos|apply: bpow_ge_0| idtac|idtac]; last first. *)
(*     rewrite -[X in (X <= _)%R]Rmult_1_r; apply:Rmult_le_compat. *)
(*     + by apply: bpow_ge_0. *)
(*     + by lra. *)
(*     + by  rewrite /ea; apply:bpow_le. *)
(*     apply:IZR_le. *)
(*     by move: (radix_gt_1 radix2); lia. *)
(*   by move/IZR_le:(FLX_mant_le Fb); rewrite /Mb abs_IZR minus_IZR IZR_Zpower //; lia. *)
(* have Ffx: (format ((pow p - 1) * pow (1 +ea))). *)
(*   apply:generic_format_FLX. *)
(*   apply:( FLX_spec radix2 p _ (Float radix2 (radix2^p-1) (1 + ea))). *)
(*     set exp := ( (1 + _)). *)
(*     by rewrite /F2R /=; apply:Rmult_eq_compat_r; rewrite minus_IZR (IZR_Zpower radix2) //; lia. *)
(*   rewrite /= Z.abs_eq;  lia. *)
(* have Hle: (Rabs s <= (pow p - 1) * pow (1 + ea))%R. *)
(*   by  apply: abs_round_le_generic. *)
(* have Hlt: (Rabs s < pow (p + (1 + ea)))%R. *)
(*   apply (Rle_lt_trans _ _ _  Hle). *)
(*   rewrite (bpow_plus _ p). *)
(*   by apply Rmult_lt_compat_r; try lra;  apply bpow_gt_0. *)
(* rewrite {1}/ce {1}/FLX_exp. *)
(* apply( Zplus_le_reg_l _ _ p); ring_simplify. *)
(* apply:mag_le_bpow =>//; rewrite -/ea.  *)
(* by have <- : (p + (1 + ea)) = (p + ea + 1) by ring. *)
(* Qed. *)

(* Fact sma_exact : (z = s - a)%R. *)
(* Proof. *)
(* case:exp_le => [faE cebfa]. *)
(* have fa_num:= num_le. *)

(* pose ea := Fexp fa. *)
(* pose eb := ce b. *)
(* pose  es := ce s. *)
(* pose  mb := mant b. *)
(* pose  ms := mant s. *)
(* pose  Ma := Fnum fa. *)
(* pose  Mb := Ztrunc mb. *)
(* pose  Ms := Ztrunc ms. *)
(* have {faE} faE : (a = F2R (Float radix2  Ma  ea))%R.  by rewrite faE  /Ma /ea; case : fa. *)
(* have faE' : (a = IZR Ma * pow ea)%R by rewrite /F2R. *)
(* rewrite round_generic //. *)
(* case:(Req_dec s R0)=>[->|Zs]; first by rewrite Rminus_0_l; apply: generic_format_opp. *)
(* have Zab: ((a + b)%R <> R0) by move=> K; apply: Zs; rewrite  K round_0. *)
(* have valid_fexp := (@FLX_exp_valid _ p_gt_0). *)
(* have mon_fexp := FLX_exp_monotone p. *)
(* have L := (@error_le_half_ulp_round  radix2 fexp  valid_fexp mon_fexp  choice (a + b)%R). *)
(* rewrite ulp_neq_0 // in  L. *)
(* have Fs : (format s) by  apply :generic_format_round.  *)
(* have Ha := fa_num. *)
(* have Hb := FLX_mant_le Fb. *)
(* have Hs := FLX_mant_le Fs. *)
(* rewrite -/Ma -/mb -/Mb -/ms -/Ms in Ha Hb Hs. *)
(* have {Ha} Ha := IZR_le _ _ Ha. *)
(* have {Hb} Hb := IZR_le _ _ Hb. *)
(* have {Hs} Hs := IZR_le _ _ Hs. *)
(* rewrite !abs_IZR !minus_IZR !IZR_Zpower //= in Ha Hb Hs; last lia. *)
(* have  [Ha1 Ha2] := Rabs_le_inv _ _ Ha. *)
(* have  [Hb1 Hb2] := Rabs_le_inv _ _ Hb. *)
(* have  [Hs1 Hs2] := Rabs_le_inv _ _ Hs. *)
(* have /= Hp0 :( pow 0 <= pow p)%R  by apply: bpow_le ; lia. *)
(* have haux := (F2Sexp_aux Zs). *)
(* have [H1|H2]:  (es = ea + 1 \/ (es <= ea)%Z) by rewrite /es /ea; lia. *)
(* (* 1. *) *)
(*   pose delta := (Zminus ea  eb). *)
(*   pose mu := (Ms * radix2 - Ma). *)
(*   have: Zabs mu <= Zabs Mb + 1. *)
(*     suff h: (IZR Mb* pow (-delta) - IZR radix2/2 <= IZR mu <= IZR  Mb* pow (-delta) + IZR radix2/2)%R. *)
(*       have {h} h: ( - (IZR radix2 / 2) <= IZR mu -(IZR Mb * pow (- delta)) <= *)
(*         IZR radix2 / 2)%R by lra. *)
(*       have {h} h: (Rabs (IZR mu - IZR Mb * pow (- delta)) <= IZR radix2 / 2)%R by  apply:Rabs_le. *)
(*       have {h} h :  (Rabs (IZR mu) - Rabs (IZR Mb * pow (- delta)) <= IZR radix2 / 2)%R. *)
(*         by apply:(Rle_trans _ _ _ (Rabs_triang_inv  (IZR mu) (IZR Mb * pow (- delta)))). *)
(*       have {h} h:(Rabs (IZR mu) <= Rabs (IZR Mb * pow (- delta))+ IZR radix2 / 2)%R by lra. *)
(*       have {h} h:(Rabs (IZR mu) <= Rabs (IZR Mb) + IZR radix2 / 2)%R. *)
(*         suff:  (Rabs (IZR Mb * pow (- delta)) <=  Rabs (IZR Mb))%R  by lra. *)
(*         rewrite Rabs_mult (Rabs_pos_eq (pow _)); last by apply: bpow_ge_0. *)
(*         rewrite -[X in (_ <= X)%R]Rmult_1_r. *)
(*         apply:Rmult_le_compat_l; first by apply:Rabs_pos. *)
(*         change ( (pow (- delta) <=  pow 0)%R). *)
(*         apply:bpow_le. *)
(*         by rewrite /delta /ea /eb; lia. *)
(*       have ht:  (Rabs (IZR Mb) + IZR radix2 / 2 <Rabs (IZR Mb) +  (IZR 2))%R. *)
(*         apply:Rplus_lt_compat_l. *)
(*         suff: (IZR radix2 < 4)%R by lra. *)
(*         apply:IZR_lt; lia. *)
(*       have {ht}ht: (Rabs (IZR mu) < Rabs (IZR Mb) + 2)%R by lra. *)
(*       rewrite  - !abs_IZR in ht. *)
(*       move :ht. *)
(*       have ->: (IZR (Z.abs Mb) + 2 = IZR( (Z.abs Mb) + 2) )%R by rewrite plus_IZR. *)
(*       move/lt_IZR => ht. *)
(*       lia. *)
(*     move: L. *)
(*     have {1}->: s = (IZR Ms * pow es)%R by rewrite Fs /F2R /= -/ms -/Ms -/es. *)
(*     rewrite -/es  faE'. *)
(*     have ->: b = (IZR Mb * pow eb)%R by rewrite Fb /F2R /= -/mb -/Mb -/eb. *)
(*     move/Rabs_le_inv. *)
(*     have->: pow es = (pow ea * pow 1)%R by rewrite H1 bpow_plus. *)
(*     set dem := (/2)%R. *)
(*     have->:  (dem* (pow ea * pow 1) = (pow 1 * dem ) *pow ea)%R by ring. *)
(*     have->: pow 1 = IZR radix2 by rewrite -IZR_Zpower // Z.pow_1_r. *)
(*     have->: (pow eb = pow (eb - ea) * pow ea)%R. *)
(*       rewrite (bpow_plus radix2 eb) Rmult_assoc -bpow_plus. *)
(*       have->: -ea + ea = 0 by ring. *)
(*       by rewrite Rmult_1_r. *)
(*     have ->:  (- (IZR radix2 * dem * pow ea) = - (IZR radix2 * dem) * pow ea)%R by ring. *)
(*     have ->: ( IZR Ms * (pow ea * IZR radix2) -  *)
(*              (IZR Ma * pow ea + IZR Mb * (pow (eb - ea) * pow ea)) =  *)
(*           ( IZR Ms * IZR radix2 -  *)
(*              IZR Ma  -  IZR Mb * (pow (eb - ea))) * pow ea)%R by ring. *)
(*     move=> h. *)
(*     have h1: (- (IZR radix2 * dem)  <=  (IZR Ms * IZR radix2 - IZR Ma - IZR Mb * pow (eb - ea)))%R. *)
(*     apply:(Rmult_le_reg_r (pow ea)); first apply:bpow_gt_0. *)
(*       lra. *)
(*     have h2: ((IZR Ms * IZR radix2 - IZR Ma - IZR Mb * pow (eb - ea)) <= (IZR radix2 * dem))%R. *)
(*       apply:(Rmult_le_reg_r (pow ea)); first apply:bpow_gt_0. *)
(*       lra. *)
(*     rewrite /Rdiv -/dem /delta /mu. *)
(*     have->: (- (ea - eb)) = eb -ea  by ring. *)
(*     rewrite minus_IZR mult_IZR. *)
(*     lra. *)
(*   have Mbub: Z.abs Mb <= radix2 ^ p -1. *)
(*     apply/Z.abs_le. *)
(*     by split; apply:le_IZR ; rewrite ?opp_IZR minus_IZR IZR_Zpower //; lia. *)
(*   have: format s by apply:generic_format_round. *)
(*   move ->; rewrite   /F2R /= -/ms -/Ms -/es. *)
(*   case:exp_le=> -> *. *)
(*   rewrite /F2R H1 bpow_plus -/ea bpow_1. *)
(*   have->:  ((IZR Ms * (pow ea * IZR radix2) - IZR (Fnum fa) * pow ea) =   *)
(*          ((IZR Ms  * IZR radix2) - IZR (Fnum fa)) * pow ea)%R by ring. *)
(*   rewrite -mult_IZR -minus_IZR. *)
(*   have: Z.abs mu <= radix2 ^ p by lia. *)
(*   rewrite -/Ma -/mu. *)
(*   case/Z_le_lt_eq_dec; last first. *)
(*     rewrite - (Z.abs_eq (radix2 ^ p)); last by apply:Z.pow_nonneg;  move:(radix_gt_0 radix2); lia. *)
(*     case/Z.abs_eq_cases=> ->. *)
(*       rewrite IZR_Zpower -?bpow_plus; try lia; apply:generic_format_bpow; rewrite /fexp; lia. *)
(*     have-> : (IZR (- radix2 ^ p) * pow ea= - (IZR ( radix2 ^ p) * pow ea))%R by rewrite opp_IZR; ring. *)
(*     apply/generic_format_opp. *)
(*     rewrite IZR_Zpower -?bpow_plus; try lia; apply:generic_format_bpow; rewrite /fexp; lia. *)
(*   move=>h. *)
(*   pose fx := Float radix2 (Ms * radix2 - Fnum fa) ea. *)
(*   apply: (FLX_format_Rabs_Fnumf fx). *)
(*   move/IZR_lt: h. *)
(*   by rewrite /fx /F2R /= -/mu -abs_IZR IZR_Zpower //;  lia. *)
(* (* 2. es <= ea *) *)
(* pose d1 := ea - eb. (* delta_1 *) *)
(* have HA: (a + b = F2R (Float radix2 (radix2^d1 * Ma + Mb) eb))%R. *)
(*   rewrite  faE Fb  -/mb -/Ma -/Mb -/ea -/eb. *)
(*   by rewrite (@F2R_change_exp radix2 eb Ma ea) // -F2R_plus Fplus_same_exp Zmult_comm. *)
(* case: (Zle_or_lt es eb) => [Hle|Hlt]. *)
(* (* Hle : es <= eb *) *)
(*   have sExact: (s = a + b)%R. *)
(*     rewrite round_generic //. *)
(*     pose f:= Float radix2  (radix2 ^ d1 * Ma + Mb) eb. *)
(*     apply:(generic_format_F2R' _ _ _ f ). *)
(*       by rewrite HA /f. *)
(*     move=> h0. *)
(*     apply:(Z.le_trans _ (ce s)). *)
(*       apply: cexp_round_ge. *)
(*       by apply/round_neq_0_negligible_exp ; first apply/negligible_exp_FLX. *)
(*     by rewrite -/es /f /=. *)
(*   by rewrite sExact; ring_simplify (a + b - a)%R. *)
(* (* Hlt : eb < es *) *)
(* have sDef : s = rnd_p (IZR Ma * pow ea + IZR Mb * pow eb). *)
(*   by replace  (IZR Ma * pow ea)%R with a; replace  (IZR Mb * pow eb)%R with b. *)
(* pose d2 := es - eb. *)
(* move: HA. *)
(* have -> :  eb = ((-d2) + es) by rewrite /d2;ring. *)
(* rewrite /F2R /= bpow_plus=> HA. *)
(* have: (a + b)%R =  ((IZR Ma * pow ( d1 -d2) + IZR Mb  * (pow (- d2))) * pow es)%R. *)
(*   rewrite HA plus_IZR mult_IZR (IZR_Zpower radix2); last by rewrite /d1; lia. *)
(*   rewrite (bpow_plus _ d1); ring. *)
(* move=> haux0. *)
(* rewrite  {2}faE /F2R /= -/Ma -/ea. *)
(* have :  s = rnd_p (pow es * (IZR Ma * pow (d1 - d2) + IZR Mb * pow (- d2)))  by rewrite haux0;congr round; ring. *)
(* move : HA ; set x := (IZR Ma * pow (d1 - d2) + IZR Mb * pow (- d2))%R. *)
(* move=> HA H0s. *)
(* have Hls := (mant_N H0s). *)
(* have Habs := (Znearest_half choice x). *)
(* rewrite -/ms -/Ms in Hls. *)
(* have -> :  (IZR Ma * pow ea)%R = a by []. *)
(* rewrite Fs {3}faE' -/es -/ea. *)
(* have -> :  ea =  (d1 - d2 + es) by rewrite /d1 /d2; lia. *)
(* rewrite /F2R /= -/ms  -/Ms -/Ma. *)
(* rewrite  bpow_plus  -Rmult_assoc -Rmult_minus_distr_r -IZR_Zpower; last first. *)
(*   by rewrite /d1 /d2; lia. *)
(* rewrite - mult_IZR - minus_IZR /es -ulp_neq_0 //. *)
(* set fnum := Ms -  _. *)
(* rewrite ulp_neq_0 //. *)
(* apply: (@FLX_format_Rabs_Fnum  _ (Float radix2 fnum (ce s)))=>//. *)
(* rewrite /fnum minus_IZR mult_IZR IZR_Zpower; last  by rewrite /d1 /d2; lia. *)
(* rewrite -Hls /x in Habs. *)
(* have {Habs} [_x x_]:=  Rabs_le_inv _ _ Habs. *)
(* have PPmd2:=  bpow_gt_0 radix2 (- d2). *)
(* have PPd2:=  bpow_gt_0 radix2 d2. *)
(* have radix2posZ: 1 < radix2 by exact: radix_gt_1.  *)
(* have radix2pos: (0 < IZR radix2)%R by apply/IZR_lt; lia. *)
(* have  [_D2 D2_]:  (0 < IZR radix2  * pow (- d2) <= 1)%R. *)
(*   split; first by apply: Rmult_lt_0_compat. *)
(*   have hd2: (1 <= d2) by rewrite /d2; lia. *)
(*   rewrite bpow_opp. *)
(*   apply:(Rmult_le_reg_r (pow d2))=>//. *)
(*   rewrite Rmult_assoc Rinv_l ?Rmult_1_l ?Rmult_1_r; try lra. *)
(*   have ->: IZR radix2 = pow 1. *)
(*     rewrite /= IZR_Zpower_pos /=; ring. *)
(*   by apply bpow_le. *)
(* set (Pd1m2 := pow (d1 - d2)) in *. *)
(* set (Pmd2 := pow (-d2)) in *. *)
(*   have : (-(pow p - 1) * 1 <= -(pow p - 1) * (IZR radix2 * Pmd2) <= IZR Mb * (IZR radix2 * Pmd2))%R. *)
(*     split; [|apply Rmult_le_compat_r; lra]. *)
(*     rewrite !Ropp_mult_distr_l_reverse. *)
(*     apply: Ropp_le_contravar. *)
(*     by apply Rmult_le_compat; lra. *)
(* have : (IZR Mb * (IZR radix2  * Pmd2) <= (pow p - 1) * (IZR radix2  * Pmd2) <= (pow p - 1) * 1)%R. *)
(*   by split; [apply Rmult_le_compat_r|apply Rmult_le_compat]; lra. *)
(*   have: 2 = radix2 \/ 3 = radix2 by lia. *)
(*  case=> <-=> *; apply: Rabs_lt; split; lra. *)
(* Qed. *)


(* Theorem Fast2Sum_correct_proof_aux : t = (a + b - s)%R. *)
(* Proof. *)
(* rewrite  sma_exact /s. *)
(* have -> :  (b - (rnd_p (a + b) - a))%R = (-(rnd_p (a + b) - (a + b)))%R by ring. *)
(* rewrite round_generic. *)
(*   by have ->: (a + b - rnd_p (a + b))%R = (-(rnd_p (a + b) - (a + b)))%R by ring. *)
(* by apply:  generic_format_opp; apply: plus_error. *)

(* Qed. *)
(* End F2Sum_aux. *)


Definition  Fast2Sum := (F2SumFLX.Fast2Sum radix2 p choice).


(* End F2Sum. *)

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



(* Hypothesis ZNE : choice = fun n => negb (Z.even n). *)
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
