Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs common DDModels.
Require Import Bayleyaux DWPlus.

(* for choice functions : choice = fun x0 : Z => negb (Z.even x0) *)
Require Import Logic.FunctionalExtensionality.

Require Import mathcomp.ssreflect.ssreflect.

Set Bullet Behavior "Strict Subproofs".

Section DWDefLemmas.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 

Notation fexp :=
  (SpecFloat.fexp (fprec t) (femax t)).
Notation format :=
  (Generic_fmt.generic_format Zaux.radix2 fexp).
Notation emin := (SpecFloat.emin (fprec t) (femax t)).
Notation double_word := (DD.DDModels.double_word).
Notation radix2 := Zaux.radix2.

Lemma double_word_0 (xh xl : ftype t) : 
  double_word xh xl -> 
  FT2R xh = 0 ->  
  FT2R xl = 0.
Proof.
rewrite /double_word.
intros DWx H0. rewrite H0 in DWx.
rewrite DWx Rplus_0_l /rounded 
  Generic_fmt.round_generic => //; auto with dd_base.
Qed.

Fact dw_ulp xh xl: 
  double_word xh xl -> Rabs (FT2R xl) <= /2 * ulp (@FT2R t xh).
Proof.
unfold double_word; intros.
assert (FT2R xl = - (rounded t (FT2R xh + FT2R xl) 
  - (FT2R xh + FT2R xl))).
{ rewrite -H; nra. } 
rewrite H0 Rabs_Ropp.
eapply Rle_trans.
apply Ulp.error_le_half_ulp_round.
apply FLT.FLT_exp_valid.
apply (fprec_gt_0 t).
apply FLT.FLT_exp_monotone.
fold choice.
rewrite {2}H; unfold rounded.
now apply Req_le.
Qed.

Lemma double_word_underflow (xh xl: ftype t) : 
  double_word xh xl -> 
  Rabs (FT2R xh + FT2R xl) < 
      bpow radix2 (emin + fprec t - 1) -> 
  FT2R xl = 0.
Proof.
rewrite /double_word. intros DWx Hr. move: DWx. 
rewrite /rounded Generic_fmt.round_generic; [ nra|
  apply Plus_error.FLT_format_plus_small => //].
1,2: rewrite -B2R_float_of_ftype; 
  apply Binary.generic_format_B2R.
eapply Rle_trans.
apply Rlt_le, Hr.
apply bpow_le; rewrite /emin; lia.
Qed.

Lemma rbpowpuW':
   forall (x e : ftype t),
   0 < FT2R x -> 
   0 <= FT2R e < / 2 * ulp (FT2R x) ->
   rounded t (FT2R x + FT2R e) = FT2R x.
Proof.
intros x e Hx He.
assert (Hfx: format (FT2R x)) by 
  (rewrite <- B2R_float_of_ftype;
apply Binary.generic_format_B2R).
assert 
  (Generic_fmt.Valid_exp (SpecFloat.fexp (fprec t) (femax t))).
{ apply BinarySingleNaN.fexp_correct. unfold FLX.Prec_gt_0.
pose proof fprec_gt_one t; lia. } 
destruct (Req_dec (FT2R e) 0) as [e0 | e0].
{ rewrite e0 Rplus_0_r /rounded.
apply Generic_fmt.round_generic. 
apply BinarySingleNaN.valid_rnd_round_mode.
rewrite -B2R_float_of_ftype.
apply Binary.generic_format_B2R. } 
assert (Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) 
              Zfloor (FT2R x + FT2R e) = FT2R x) as dE.
apply Ulp.round_DN_plus_eps_pos ; auto;  try lra. 
rewrite -{2}dE . 
eapply Ulp.round_N_eq_DN; auto. 
 rewrite Ulp.round_UP_DN_ulp. rewrite dE.
  assert (FT2R e <  (ulp (FT2R x + FT2R e)) / 2); try lra.
  refine (Rlt_le_trans _  (/ 2 * ulp (FT2R x)) _ _ _); try lra.
  assert (ulp ( FT2R x) <= ulp  (FT2R x + FT2R e)); try lra. 
  apply Ulp.ulp_le; try rewrite !Rabs_pos_eq; try lra; auto. 
apply Binary.fexp_monotone.
destruct (Generic_fmt.generic_format_EM 
  Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) (FT2R x + FT2R e)); auto.
revert dE. rewrite Generic_fmt.round_generic; simpl; auto. try lra. 
Qed.


Notation is_pow := (is_pow Zaux.radix2).


Theorem POSpow_ln_beta :
  forall x : R, is_pow x -> (0 < x)%R ->
    x = (bpow Zaux.radix2 (mag Zaux.radix2 x - 1)).
Proof.
intros x [e Bx] H1.
rewrite Rabs_pos_eq in Bx; last lra.
rewrite Bx mag_bpow; ring_simplify (e + 1 - 1)%Z. auto.
Qed.

Fact dw_le xh xl: FT2R xh <> 0 -> 
  double_word xh xl -> Rabs (FT2R xl) <= Rabs (@FT2R t xh).
Proof.
intros. 
apply dw_ulp in X.
refine (Rle_trans _ _ _ X _).
refine (Rle_trans _ _ _ _ 
  (Ulp.ulp_le_abs Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
         _ H _)).
refine (Rle_trans _ _ _ (Rmult_le_compat _ 1 _ _ _ _ _ _) _); try nra.
apply Ulp.ulp_ge_0.
apply Rle_refl. nra.
rewrite -B2R_float_of_ftype.
apply Binary.generic_format_B2R.
Qed.


End DWDefLemmas.

Section UlpLemmas.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 

Theorem ulps_eq : 
  (* assuming no underflow, ulp of val is equal in different (Flocq) formats *)
  forall x, x <>0 -> bpow Zaux.radix2 (@emin t + fprec t - 1) <= Rabs x -> 
  ulp x = Ulp.ulp Zaux.radix2 (FLX.FLX_exp (fprec t )) x.
Proof.
intros.
unfold ulp.
destruct (Req_dec x 0) as [Hx|Hx]; subst; 
 apply Req_bool_false in H. 
{ remember (Req_bool 0 0) as HU;
  destruct HU; subst.
  rewrite H in HeqHU; discriminate.
  rewrite <- (@FLT.cexp_FLT_FLX Zaux.radix2 (@emin t)); auto. }
rewrite H. 
rewrite <- (@FLT.cexp_FLT_FLX Zaux.radix2 (@emin t)); auto.
Qed.

End UlpLemmas.
