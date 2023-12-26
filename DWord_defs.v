Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs common DDModels.
Require Import Bayleyaux DWPlus.

(* for choice functions : choice = fun x0 : Z => negb (Z.even x0) *)
Require Import Logic.FunctionalExtensionality.


Set Bullet Behavior "Strict Subproofs".

Section DefLemmas.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 

Notation fexp :=
(SpecFloat.fexp (fprec t) (femax t)).
Notation format :=
(Generic_fmt.generic_format Zaux.radix2 fexp).
Notation emin := (SpecFloat.emin (fprec t) (femax t)).
Notation double_word := (DD.DDModels.double_word).

Fact dw_ulp xh xl: 
  double_word xh xl -> Rabs (FT2R xl) <= /2 * ulp (@FT2R t xh).
Proof.
unfold double_word; intros.
assert (FT2R xl = - (rounded t (FT2R xh + FT2R xl) 
  - (FT2R xh + FT2R xl))).
{ rewrite <-H; nra. } 
rewrite H0, Rabs_Ropp.
eapply Rle_trans.
apply Ulp.error_le_half_ulp_round.
apply FLT.FLT_exp_valid.
apply (fprec_gt_0 t).
apply FLT.FLT_exp_monotone.
fold choice.
rewrite H at 2; unfold rounded.
now apply Req_le.
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
{ rewrite e0, Rplus_0_r. unfold rounded.
apply Generic_fmt.round_generic. 
apply BinarySingleNaN.valid_rnd_round_mode.
rewrite <- B2R_float_of_ftype.
apply Binary.generic_format_B2R. } 
assert (Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t)) 
              Zfloor (FT2R x + FT2R e) = FT2R x) as dE.
apply Ulp.round_DN_plus_eps_pos ; auto;  try lra. 
rewrite <- dE at 2. 
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
apply Generic_fmt.valid_rnd_DN.
Qed.

(* Definition is_pow  x :=  exists e : Z, Rabs x = bpow Zaux.radix2 e. *) 
Notation is_pow := (is_pow Zaux.radix2).

Theorem POSpow_ln_beta :
  forall x : R, is_pow x -> (0 < x)%R ->
    x = (bpow Zaux.radix2 (mag Zaux.radix2 x - 1)).
Proof.
intros x [e Bx] H1.
rewrite Rabs_pos_eq in Bx; last lra.
rewrite Bx, mag_bpow; ring_simplify (e + 1 - 1)%Z. auto.
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
rewrite <- B2R_float_of_ftype.
apply Binary.generic_format_B2R.
Qed.


Theorem ulps_eq : 
  (* assuming no underflow, ulp of val is equal in different (Flocq) formats *)
  forall x, x <>0 -> bpow Zaux.radix2 (emin + fprec t - 1) <= Rabs x -> 
  ulp x = Ulp.ulp Zaux.radix2 (FLX.FLX_exp (fprec t )) x.
Proof.
intros.
unfold ulp.
destruct (Req_dec x 0) as [Hx|Hx]; subst; 
 apply Req_bool_false in H. 
{ remember (Req_bool 0 0) as HU;
  destruct HU; subst.
  rewrite H in HeqHU; discriminate.
  rewrite <- (@FLT.cexp_FLT_FLX Zaux.radix2 emin); auto. }
rewrite H. 
rewrite <- (@FLT.cexp_FLT_FLX Zaux.radix2 emin); auto.
Qed.


Theorem is_double_word :
  forall (xh xl : ftype t)
  (NO_UF1 : bpow Zaux.radix2 (emin + fprec t - 1) <= Rabs (FT2R xh + FT2R xl))
  (NO_UF2 : 
  (FT2R xh) <> 0 -> bpow Zaux.radix2 (emin + fprec t - 1) <= Rabs (FT2R xh)),
  (is_pow (FT2R xh) -> 
  Rabs (FT2R xl) <= / 4 * ulp (FT2R xh)) ->
  (~ is_pow (FT2R xh) -> 
  Rabs (FT2R xl) <= / 2 * ulp (FT2R xh)) ->
  rounded t (FT2R xh + FT2R xl) = FT2R xh.
Proof.
intros ? ? ? ? HP HNP.
assert ( choice = (fun n : Z => negb (Z.even n))) as HCH.
apply functional_extensionality; unfold choice. simpl; auto.
pose proof (fprec_gt_one t) as HPrec.
destruct (Req_dec (FT2R xh) 0) as [Hx|Hx]; subst.
{  assert (FT2R xl = 0). rewrite Hx in HNP, NO_UF1.
replace ulp with 
  (Ulp.ulp Zaux.radix2 (FLT.FLT_exp emin (fprec t))) in HNP
  by f_equal.
rewrite FLT.ulp_FLT_0 in HNP.
exfalso.
assert (bpow Zaux.radix2 (emin + fprec t - 1)  
  </ 2 * bpow Zaux.radix2 emin) as H0.
{  rewrite Rplus_0_l in NO_UF1.
refine (Rle_lt_trans _ (Rabs (FT2R xl)) _ _ _);
 [apply NO_UF1| ].
assert (~ is_pow 0 -> Rabs (FT2R xl) < / 2 * bpow Zaux.radix2 emin).
intros.
(specialize (HNP H)).
apply lesseq_less_or_eq in HNP; destruct HNP; auto.
{ exfalso. rewrite H0 in NO_UF1.
replace (/2) with (bpow Zaux.radix2 (-1)) in NO_UF1
  by (simpl; lra).
rewrite <- bpow_plus in NO_UF1.
apply le_bpow in NO_UF1.
pose proof (fprec_gt_one t); lia. } clear HNP.
apply H. 
unfold is_pow. red; intros HE; 
  destruct HE as (x & Hx'). rewrite Rabs_R0 in Hx'. 
pose proof bpow_gt_0 Zaux.radix2 x; nra. } 
replace (/2) with (bpow Zaux.radix2 (-1)) in H0
  by (simpl; lra).
rewrite <- bpow_plus in H0.
apply bpow_lt_bpow in H0.
pose proof (fprec_gt_one t); lia.
unfold FLX.Prec_gt_0; lia.
rewrite Hx, H, Rplus_0_l.
apply Generic_fmt.round_0, 
  BinarySingleNaN.valid_rnd_round_mode. }
specialize (NO_UF2 Hx).
destruct (is_pow_dec Zaux.radix2 (FT2R xh)) as [HA|HA]; 
  [clear HNP; specialize (HP HA)| clear HP; specialize (HNP HA)].
- pose proof rxpu2pow (fprec_gt_one t) HCH (FT2R xl) HA as H1.
rewrite <- H1 at 2. apply FLT.round_FLT_FLX; auto.
revert HP. cbv [ulp].
pose proof FLX.negligible_exp_FLX (fprec t). 
remember (Req_bool ((FT2R xh)) 0) as HU;
  destruct HU; subst;
remember (Ulp.negligible_exp fexp) as HU;
  destruct HU; subst;
remember (Ulp.negligible_exp (FLX.FLX_exp (fprec t))) as HU;
  destruct HU; subst; try discriminate; auto.
{ exfalso. apply Req_bool_false in Hx. rewrite Hx in HeqHU; 
  discriminate. }   
all: rewrite <- (@FLT.cexp_FLT_FLX Zaux.radix2 emin); auto.
- apply lesseq_less_or_eq in HNP; destruct HNP as [HNP|].
{ pose proof (@rulp2p _ (fprec_gt_one t) _ HCH (FT2R xh) (FT2R xl)).
rewrite <- H at 2; auto. apply FLT.round_FLT_FLX; auto.
apply (@FLT.generic_format_FLX_FLT Zaux.radix2 emin).
rewrite <- B2R_float_of_ftype. apply Binary.generic_format_B2R.
revert HNP. cbv [ulp].
pose proof FLX.negligible_exp_FLX (fprec t). 
remember (Req_bool ((FT2R xh)) 0) as HU;
  destruct HU; subst;
remember (Ulp.negligible_exp fexp) as HU;
  destruct HU; subst;
remember (Ulp.negligible_exp (FLX.FLX_exp (fprec t))) as HU;
  destruct HU; subst; try discriminate; auto.
{ exfalso. apply Req_bool_false in Hx. rewrite Hx in HeqHU; 
  discriminate. }
all: rewrite <- (@FLT.cexp_FLT_FLX Zaux.radix2 emin); auto. }
Search bpow Ulp.ulp.
Search is_pow.
(* pose proof (@rulp2p' _ (fprec_gt_one t) _ HCH 
  (FT2R xl) (FT2R xh) (FT2R xl)) as H0.
rewrite <- H0 at 2; auto. apply FLT.round_FLT_FLX; auto. 

Search (
Generic_fmt.round _ _
  _ (_ + _) = _).

destruct (Rle_or_lt (FT2R xl) 0).
destruct (Rle_or_lt (FT2R xh) 0).
apply Rabs_left1 in H1, H2.
rewrite H in H1.
rewrite H,  ulps_eq. 
Search (Ulp.ulp _ _ (Ulp.ulp _ _ _ )).

 <- H1.
replace (Rabs (FT2R xl)) with (- FT2R xl).
refine (Rle_trans _ 0 _ _ _ ); try nra.

apply Rabs_left1 in H1. rewrite H1.

rewrite H, ulps_eq.
apply Rmult_le_compat_l, Ulp.ulp_le; try nra. admit. admit.
rewrite H.
Search (Ulp.ulp _ _ _<= Ulp.ulp _ _ _ ).

rewrite <- FLT.round_FLT_FLX; auto.
Search (
Generic_fmt.round _ _
  _ (_ + _) = _).

rewrite H.  *)

Admitted.

Theorem double_word_implies : 
  forall (xh xl : ftype t)
  (NO_UF1 : bpow Zaux.radix2 (emin + fprec t - 1) <= Rabs (FT2R xh + FT2R xl))
  (NO_UF2 : 
  (FT2R xh) <> 0 -> bpow Zaux.radix2 (emin + fprec t - 1) <= Rabs (FT2R xh)),
  double_word xh xl -> 
  (~ is_pow (FT2R xh) -> 
  Rabs (FT2R xl) <= / 2 * ulp (FT2R xh)) /\
  (is_pow (FT2R xh) -> 
  Rabs (FT2R xl) <= / 4 * ulp (FT2R xh)) .
Proof.
intros ? ? ? ? HD; split; [intro HP | intro HNP].
- apply dw_ulp; auto.
- revert HD; unfold double_word; intros.
assert (FT2R xl = - (rounded t (FT2R xh + FT2R xl) 
  - (FT2R xh + FT2R xl))) as H0.
{ rewrite <-HD; nra. }
destruct (Req_dec (FT2R xh) 0) as [Hx|Hx]; subst.
+ rewrite Hx, Rplus_0_l in HD. 
symmetry in HD. 
exfalso. destruct HNP as (e & He).
rewrite Hx, Rabs_R0 in He. 
pose proof bpow_gt_0 Zaux.radix2 e; nra.
+
destruct (Rle_or_lt (FT2R xl) 0).
destruct (Rle_or_lt (FT2R xh) 0).
{
apply Rabs_left1 in H.
apply Rabs_le; split.
Search ( _ <= _ <= _ -> Rabs _<= _).
(* rewrite H.
assert (is_pow (- FT2R xh)) as HNP2 by admit.
replace (/4 * ulp (FT2R xh)) with 
  (/2 * ulp (-FT2R xh /2)).
assert (ulp (- FT2R xh / 2) = 
  - FT2R xh - Ulp.pred Zaux.radix2 fexp (-FT2R xh)).
pose proof
POSpow_pred (fprec_gt_one t) HNP2.
simpl in H2.
admit.
rewrite H2.
Search (Generic_fmt.round _ _ _ _ - _ = _).


Search Ulp.ulp bpow.
 rewrite H1 in H.
apply Ropp_lt_contravar in H.
rewrite Ropp_involutive in H.
exfalso.
assert (rounded t (FT2R xh) = rounded t (FT2R xh + FT2R xl)) by admit.
assert ( rounded t (FT2R xh) <= rounded t (FT2R xh - (/ 4 * ulp (FT2R xh)))).
rewrite H3 at 1.
apply Generic_fmt.round_le. admit. admit.
apply Rplus_le_compat_l; nra. clear H3.
Search Ulp.pred.
assert (is_pow (- FT2R xh)) as HNP2 by admit.
assert (
FT2R xh =
     - Ulp.pred Zaux.radix2 (FLX.FLX_exp (fprec t)) (- FT2R xh) -
     Ulp.ulp Zaux.radix2 (FLX.FLX_exp (fprec t)) (- FT2R xh / IZR (Zaux.radix_val Zaux.radix2))).
pose proof
POSpow_pred (fprec_gt_one t) HNP2.
admit.(* 
rewrite H3 in H4 at 2. *)

rewrite <- Round_NE.round_NE_opp in HD.
Search (Generic_fmt.round _ _ _ (- _)).
admit.
assert (is_pow (- FT2R xh)) as HNP2 by admit.
pose proof
POSpow_pred (fprec_gt_one t) HNP2. (FT2R xh).
Search Ulp.pred.
Search (Generic_fmt.round _ _ _ ( _ + _) = _).
assert 
assert (FT2R xh + FT2R xl < FT2R xh - /4 * ulp (FT2R xh)) by lra.
assert (FT2R xh - / 4 * ulp (FT2R xh) <= FT2R xh ).
admit.
assert (FT2R xh + FT2R xl < FT2R xh ) by nra.
Search Ulp.pred Ulp.ulp.
Search ( Generic_fmt.round _ _ _  _ < _).

Search (Generic_fmt.round _ _ _ ( _ + _) = _).

Search (  _ < - _).
assert ( FT2R xl < 
Search (Rabs _ = - _).


exfalso.
destruct HNP as (e & He).
revert H. 
rewrite <- Ulp.ulp_abs, He, ulps_eq; auto.
rewrite (Ulp.ulp_bpow Zaux.radix2 (FLX.FLX_exp (fprec t)) e).
Search (Generic_fmt.round _ _ _ ( _ + _) = _).


destruct HNP as (e & He).
assert ((FT2R xh /2) = rounded t ((FT2R xh/2) + FT2R xl)).
Search bpow Binary.B2R.
admit.
replace (/ 4 * ulp (FT2R xh)) with (/ 2 * ulp (FT2R xh/2)).
pose proof dw_ulp. admit.
Search Ulp.ulp bpow.
replace (FT2R xh / 2) with (FT2R xh * bpow Zaux.radix2 (-1)).
rewrite !ulps_eq, FLX.ulp_FLX_exact_shift; auto.
simpl; field_simplify; try nra. admit. admit.

specialize (NO_UF2 Hx).
rewrite H0, Rabs_Ropp.
destruct HNP as (e & He).
rewrite <- Ulp.ulp_abs, He.
rewrite ulps_eq.
rewrite (Ulp.ulp_bpow Zaux.radix2 (FLX.FLX_exp (fprec t)) e).
unfold FLX.FLX_exp.
replace (e + 1 - fprec t)%Z with (e - fprec t + 1)%Z by lia.
Search (bpow _ (_ + _) = _).
rewrite bpow_plus_1.
eapply Rle_trans. Search is_pow Generic_fmt.round. 
Search Generic_fmt.round Ulp.ulp.
Search bpow Generic_fmt.round Ulp.ulp.
apply Ulp.error_le_half_ulp_round.
apply FLT.FLT_exp_valid.
apply (fprec_gt_0 t).
apply FLT.FLT_exp_monotone.
fold choice.
Search bpow Ulp.ulp.
rewrite HD at 2; unfold rounded.

now apply Req_le. *)


Admitted.

End DefLemmas.
