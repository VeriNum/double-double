(* This file contains the floating-point functional models in IEEE-754
  format for the 2Sum and Fast2Mult implementations.*)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs common.

Section Format.
Context {t : type}.

Definition emin := SpecFloat.emin (fprec t) (femax t).
Fact emin_le_0 : (emin <= 0)%Z. 
Proof. pose proof @fprec_lb t; pose proof @femax_lb t; 
unfold emin, SpecFloat.emin; lia. Qed.

Definition choice:= fun x0 : Z => negb (Z.even x0).
Fact choiceP (x : Z) : choice x = negb (choice (- (x + 1))%Z).
Proof. unfold choice; rewrite Z.even_opp, Z.even_add; 
destruct (Z.even x); auto. Qed.

End Format.


Section TwoSumModel.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Definition TwoSumF (a b : ftype t) :=
let s  := BPLUS a b in
let a' := BMINUS s b in
let b' := BMINUS s a' in
let da := BMINUS a a' in
let db := BMINUS b b' in (BPLUS a b, BPLUS da db).

Definition TwoSumF_err (a b : ftype t) := snd (TwoSumF a b).
Definition TwoSumF_sum (a b : ftype t) := fst (TwoSumF a b).

End TwoSumModel.

Section FastTwoSumModel.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Definition Fast2Sum (a b : ftype t) :=
let s := BPLUS a b in
let z := BMINUS s a in 
let t := BMINUS b z in (s, t).

Definition Fast2Sum_err (a b : ftype t) := snd (Fast2Sum a b).
Definition Fast2Sum_sum (a b : ftype t) := fst (Fast2Sum a b).

End FastTwoSumModel.


Section Fast2MultModel.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

(** Algorithm 3 : Fast2Mult *)
Definition Fast2Mult (a b : ftype t) :=
let m := BMULT a b in
let p := BFMA a b (BOPP m) in (m, p).

Definition Fast2Mult_err (a b : ftype t) := snd (Fast2Mult a b).
Definition Fast2Mult_mul (a b : ftype t) := fst (Fast2Mult a b).

End Fast2MultModel.


Section DWord.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

(** Definition 1.4 *) 
Definition double_word : ftype t -> ftype t -> Type :=
  fun xh xl => FT2R xh = rounded t (FT2R xh + FT2R xl).

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 

Fact dw_ulp xh xl: 
  double_word xh xl -> Rabs (FT2R xl) <= /2 * ulp (FT2R xh).
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



Notation fexp :=
(SpecFloat.fexp (fprec t) (femax t)).
Notation format :=
(Generic_fmt.generic_format Zaux.radix2 fexp).

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


Definition is_pow  x :=  exists e : Z, Rabs x = bpow Zaux.radix2 e.

Theorem POSpow_ln_beta :
  forall x : R, is_pow  x -> (0 < x)%R ->
    x = (bpow Zaux.radix2 (mag Zaux.radix2 x - 1)).
Proof.
intros x [e Bx] H1.
rewrite Rabs_pos_eq in Bx; last lra.
rewrite Bx, mag_bpow; ring_simplify (e + 1 - 1)%Z. auto.
Qed.


Fact dw_le xh xl: FT2R xh <> 0 -> 
  double_word xh xl -> Rabs (FT2R xl) <= Rabs (FT2R xh).
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

End DWord.

Section DWops.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

(** Algorithm 4 : Addition of DW number and FP number *)
Definition DWPlusFP (xh xl y : ftype t) := 
let (sh, sl) := TwoSumF xh y in
let v:= BPLUS xl sl in
let (zh, zl) := Fast2Sum sh v in (zh, zl).

(** Algorithm 5 : Addition of two DW numbers *)
Definition SloppyDWPlusDW (xh xl yh yl : ftype t) := 
let (sh, sl) := TwoSumF xh yh in
let v:= BPLUS xl yl in
let w:= BPLUS sl v in
let (zh, zl) := Fast2Sum sh w in (zh, zl).

(** Algorithm 6 : Addition of two DW numbers *)
Definition AccurateDWPlusDW (xh xl yh yl : ftype t) := 
let (sh, sl) := TwoSumF xh yh in
let (th, tl) := TwoSumF xl yl in
let c:= BPLUS sl th in
let (vh, vl) := Fast2Sum sh c in 
let w:= BPLUS tl vl in
let (zh, zl) := Fast2Sum vh w in (zh, zl).

(** Algorithm 7 : Multiplication of a DW number by a FP number *)
Definition DWTimesFP1 (xh xl y : ftype t) := 
let (ch, cl1) := Fast2Mult xh y in
let cl2 := BMULT xl y in
let (th, tl1) := Fast2Sum ch cl2 in 
let tl2 := BMULT tl1 cl1 in
let (zh, zl) := Fast2Sum th tl2 in (zh, zl).

(** Algorithm 8 : Multiplication of a DW number by a FP number *)
Definition DWTimesFP2 (xh xl y : ftype t) := 
let (ch, cl1) := Fast2Mult xh y in
let cl2 := BMULT xl y in
let cl3 := BPLUS cl1 cl2 in
let (zh, zl) := Fast2Sum ch cl3 in (zh, zl).

(** Algorithm 9 : Multiplication of a DW number by a FP number*)
Definition DWTimesFP3 (xh xl y : ftype t) := 
let (ch, cl1) := Fast2Mult xh y in
let cl3 := BFMA xl y cl1 in
let (zh, zl) := Fast2Sum ch cl3 in (zh, zl).

(** Algorithm 10 : Multiplication of a DW number by a DW number*)
Definition DWTimesDW1 (xh xl yh yl : ftype t) := 
let (ch, cl1) := Fast2Mult xh yh in
let tl1 := BMULT xh yl in
let tl2 := BMULT xl yh in
let cl2 := BPLUS tl1 tl2 in
let cl3 := BPLUS cl1 cl2 in 
let (zh, zl) := Fast2Sum ch cl3 in (zh, zl).

(** Algorithm 11 : Multiplication of a DW number by a DW number*)
Definition DWTimesDW2 (xh xl yh yl : ftype t) := 
let (ch, cl1) := Fast2Mult xh yh in
let tl        := BMULT xh yl in
let cl2       := BFMA  xl yh tl in
let cl3       := BPLUS cl1 cl2 in
let (zh,zl)   := Fast2Sum ch cl3 in (zh, zl).

(** Algorithm 12 : Multiplication of a DW number by a DW number *)
Definition DWTimesDW3 (xh xl yh yl : ftype t) := 
let (ch, cl1) := Fast2Mult xh yh in
let tl0 := BMULT xl yl in 
let tl1 := BFMA xh yl tl0 in
let cl2 := BFMA xl yh tl1 in
let cl3 := BPLUS cl1 cl2 in
let (zh, zl) := Fast2Sum ch cl3 in (zh, zl).

(** Algorithm 13 : Division of a DW number by a FP number*)
Definition DWDivFP1 := True.

(** Algorithm 14 : Division of a DW number by a FP number*)
Definition DWDivFP2 := True.

(** Algorithm 15 : Division of a DW number by a FP number*)
Definition DWDivFP3 := True.

(** Algorithm 16 : Division of a DW number by a DW number*)
Definition DWDivDW1 := True.

(** Algorithm 17 : Division of a DW number by a DW number*)
Definition DWDivDW2 := True.

(** Algorithm 18 : Division of a DW number by a DW number*)
Definition DWDivDW3 := True.

End DWops.

