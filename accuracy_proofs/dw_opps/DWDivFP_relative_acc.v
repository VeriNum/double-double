(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Relative and mixed accuracy results for [DWDivFP]. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common FLT_helpers.
Require Import DWTimesFP DWDivFP DDConds DWord_defs Fast2Mult_acc Fast2Sum_acc
               Fast2Sum_acc_helpers.
Require Import DWPlusFP_relative_acc_helpers DWTimesFP_relative_acc DW_acc_lemmas.
From Flocq Require Import Pff2Flocq Core.
From Flocq Require Import Mult_error FLT Div_sqrt_error Plus_error.
From Flocq Require Relative Sterbenz.

Require Import mathcomp.ssreflect.ssreflect.

Set Bullet Behavior "Strict Subproofs".

Local Lemma abst_round_step (W u E B R0 K M : R) :
  0 <= u -> u <= /16 -> 0 <= E -> 0 <= B -> 0 <= W ->
  0 <= K -> K <= 16 -> 0 <= M -> M <= 8 ->
  B <= K*W + M*E ->
  R0 <= B + B*u + /2*E ->
  R0 <= (K+1)*W + (M+1)*E.
Proof. intros; nra. Qed.

Local Lemma abst_pih_err (X u E B R0 : R) :
  0 <= X -> 0 <= u -> u <= /16 -> 0 <= E -> 0 <= B ->
  B <= X + X*u ->
  R0 <= B*u + /2*E ->
  R0 <= X*u*2 + E.
Proof.
intros HX Hu Hu16 HE HB Hthy Hr.
assert (Hxu : 0 <= X*u) by (apply Rmult_le_pos; assumption).
assert (HBu : B*u <= X*u + X*u).
{ apply Rle_trans with ((X + X*u)*u).
  - apply Rmult_le_compat_r; [exact Hu | exact Hthy].
  - replace ((X + X*u)*u) with (X*u + X*u*u) by ring.
    apply Rplus_le_compat_l.
    rewrite -{2}(Rmult_1_r (X*u)); apply Rmult_le_compat_l; [exact Hxu | lra]. }
lra.
Qed.

Local Lemma abst_xl (X u E V UL : R) :
  0 <= E -> V <= /2*UL -> UL <= X*(2*u) + E -> V <= X*u + E.
Proof. intros; nra. Qed.

Local Lemma abst_lt_Om (V Om X W E c0 c1 c2 : R) :
  0 <= c0 -> c0 <= 1 -> 0 <= c1 -> c1 <= 10 -> 0 <= c2 -> c2 <= 7 ->
  32 <= Om -> X <= /4*Om -> W <= /64*Om -> E <= 1 -> 0 <= X -> 0 <= W -> 0 <= E ->
  V <= c0*X + c1*W + c2*E ->
  V < Om.
Proof. intros; nra. Qed.

Local Lemma abst_fin (RV UV Om X W E c0 c1 c2 : R) :
  0 <= c0 -> c0 <= 1 -> 0 <= c1 -> c1 <= 10 -> 0 <= c2 -> c2 <= 7 ->
  32 <= Om -> X <= /4*Om -> W <= /64*Om -> E <= 1 -> 0 <= X -> 0 <= W -> 0 <= E ->
  RV <= c0*X + c1*W + c2*E ->
  UV <= /16*Om ->
  RV + UV < Om.
Proof. intros; nra. Qed.

Local Lemma abst_H1 (L Om Y u : R) :
  0 <= Om -> 0 <= Y -> 0 <= u -> u <= /16 ->
  L <= (/4*Om*Y)*u*10 ->
  L <= 5/32*Om*Y.
Proof.
intros HOm HY Hu Hu16 HL.
apply Rle_trans with ((/4*Om*Y)*u*10); [exact HL|].
assert (HP : 0 <= /4*Om*Y) by (repeat apply Rmult_le_pos; lra).
apply Rle_trans with ((/4*Om*Y)*(/16)*10).
- apply Rmult_le_compat_r; [lra|].
  apply Rmult_le_compat_l; [exact HP | exact Hu16].
- apply Req_le; field.
Qed.

Local Lemma abst_dy_lt (V Om : R) : 32 <= Om -> V <= 5/32*Om + 7 -> V < Om.
Proof. intros; lra. Qed.

Local Lemma abst_fin_dy (RV UV Om : R) :
  32 <= Om -> RV <= 5/32*Om + 7 -> UV <= /16*Om -> RV + UV < Om.
Proof. intros; lra. Qed.

Local Lemma abst_fst_sum (S Q1 Q2 Om u E : R) :
  0 <= u -> u <= /16 -> 0 <= E -> E <= 1 -> 32 <= Om ->
  0 <= Q1 -> Q1 <= /4*Om -> 0 <= Q2 -> Q2 <= 5/32*Om + 7 ->
  S <= (Q1 + Q1*u + /2*E) + (Q2 + Q2*u + /2*E) ->
  S < Om.
Proof. intros; nra. Qed.

Local Lemma abst_fst_fin (S UV Q1 Q2 Om u E : R) :
  0 <= u -> u <= /16 -> 0 <= E -> E <= 1 -> 32 <= Om ->
  0 <= Q1 -> Q1 <= /4*Om -> 0 <= Q2 -> Q2 <= 5/32*Om + 7 ->
  S <= (Q1 + Q1*u + /2*E) + (Q2 + Q2*u + /2*E) ->
  UV <= /16*Om ->
  S + UV < Om.
Proof. intros; nra. Qed.

Local Lemma abst_th_half (X u E Om : R) :
  0<=X -> X<=/4*Om -> 0<=u -> u<=/16 -> 0<=E -> E<=1 -> 32<=Om ->
  X + X*u + /2*E <= /2*Om.
Proof.
intros. assert (X*u <= /4*Om*/16)
  by (apply Rle_trans with (/4*Om*u);
      [apply Rmult_le_compat_r|apply Rmult_le_compat_l]; nra). nra.
Qed.

Local Lemma abst_tl_half (Q u E Om : R) :
  0<=Q -> Q<=5/32*Om+7 -> 0<=u -> u<=/16 -> 0<=E -> E<=1 -> 32<=Om ->
  Q + Q*u + /2*E <= /2*Om.
Proof.
intros. assert (Q*u <= (5/32*Om+7)*/16)
  by (apply Rle_trans with ((5/32*Om+7)*u);
      [apply Rmult_le_compat_r|apply Rmult_le_compat_l]; nra). nra.
Qed.

Local Lemma abst_z (D U1 U2 Tl Om : R) :
  32<=Om -> U1<=/16*Om -> Tl<=/2*Om -> U2<=/16*Om -> D <= U1+Tl -> D+U2 < Om.
Proof. intros; lra. Qed.

Local Lemma abst_snd (D U1 U2 U3 Om : R) :
  32<=Om -> U1<=/16*Om -> U2<=/16*Om -> U3<=/16*Om -> D <= U1+U2 -> D+U3 < Om.
Proof. intros; lra. Qed.

Local Lemma abst_pih_close (X u : R) :
  0 <= X -> 0 <= u -> u <= /16 -> u * (X + u * X) + u * X <= /2 * X.
Proof.
intros HX Hu Hu16.
assert (HuX : 0 <= u * X) by (apply Rmult_le_pos; assumption).
assert (H1 : u * X <= /16 * X) by (apply Rmult_le_compat_r; [ exact HX | exact Hu16 ]).
assert (H2 : u * (u * X) <= /16 * (u * X)) by (apply Rmult_le_compat_r; [ exact HuX | exact Hu16 ]).
nra.
Qed.

Local Lemma abst_revtri (A B C : R) : A - B <= C -> A - C <= B.
Proof. lra. Qed.

Local Lemma abst_prod_lb (P R X B2 : R) :
  R <= X * / 2 -> X - R <= P -> B2 <= X -> / 2 * B2 <= P.
Proof. lra. Qed.

Opaque DWTimesFP.TwoProd.
Arguments DWTimesFP.TwoProd : simpl never.

Section CorrectDWDivFP.
  Context {NANS: Nans} {t : type} {STD: is_standard t}.

  Variables (xh xl y : ftype t).

  Hypothesis FIN : is_finite_p (DWDivFP xh xl y).

  Ltac prove_finite :=
    move: FIN;
    rewrite /DWDivFP/is_finite_p //=;
    move => [] //=;
    subexpr_finite => //
  .

  Let th  := BDIV xh y.
  Let pih := fst (Fast2Mult th y).
  Let pil := snd (Fast2Mult th y).
  Let dh  := BMINUS xh pih.
  Let dt  := BMINUS dh pil.
  Let d   := BPLUS dt xl.

  Fact FINth : is_finite th = true.
  Proof. prove_finite. Qed.

  Fact FINxh : is_finite xh = true.
  Proof. prove_finite. Qed.

  Fact FINpih : is_finite (BMULT th y) = true.
  Proof. prove_finite. Qed.

  Fact FINtl : is_finite (BDIV d y) = true.
  Proof. prove_finite. Qed.

End CorrectDWDivFP.

Section BridgeDWDivFP.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (common.emin (t:=t)).
Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Notation rnd_p := (round radix2 (FLX_exp (fprec t)) (Znearest choice)).

Variables (xh xl y : ftype t).

Hypothesis FIN : is_finite_p (DWDivFP xh xl y).
Hypothesis Hp4 : (4 <= fprec t)%Z.
Hypothesis Hyne : FT2R y <> 0.

Notation th := (BDIV xh y).
Notation pih := (BMULT th y).
Notation pil := (Fast2Mult_err th y).
Notation dh := (BMINUS xh pih).
Notation dt := (BMINUS dh pil).
Notation d  := (BPLUS dt xl).

Hypothesis UF_th   : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xh / FT2R y).
Hypothesis UF_prod : bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R th * FT2R y).

Hypothesis UF_tl   : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R d / FT2R y).

Lemma bridge_th :
  round radix2 (FLX_exp (fprec t)) (Znearest choice) (FT2R xh / FT2R y)
    = FT2R (BDIV xh y).
Proof.
rewrite -(BDIV_round_correct t xh y Hyne (FINth xh xl y FIN)).
by rewrite round_FLT_FLX //; exact UF_th.
Qed.

Lemma Fxh_flx : generic_format radix2 (FLX_exp (fprec t)) (FT2R xh).
Proof.
apply (generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t)).
apply generic_format_FLT_FT2R.
Qed.

Lemma Fy_flx : generic_format radix2 (FLX_exp (fprec t)) (FT2R y).
Proof.
apply (generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t)).
apply generic_format_FLT_FT2R.
Qed.

Lemma Fbdiv_flx : generic_format radix2 (FLX_exp (fprec t)) (FT2R (BDIV xh y)).
Proof.
apply (generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t)).
apply generic_format_FLT_FT2R.
Qed.

Lemma FIN_d :
  is_finite (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                           (Fast2Mult_err (BDIV xh y) y)) xl) = true.
Proof. exact (BDIV_finite_e t _ y (FINtl xh xl y FIN)). Qed.

Lemma FIN_dt :
  is_finite (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                    (Fast2Mult_err (BDIV xh y) y)) = true.
Proof. exact (proj1 (BPLUS_finite_e t _ xl FIN_d)). Qed.

Lemma FIN_dh : is_finite (BMINUS xh (BMULT (BDIV xh y) y)) = true.
Proof. exact (proj1 (BMINUS_finite_e t _ _ FIN_dt)). Qed.

Lemma bridge_prod :
  DWTimesFP.Fast2Mult (fprec t) choice (FT2R (BDIV xh y)) (FT2R y)
    = F2Rp (Fast2Mult (BDIV xh y) y).
Proof.
exact (DWTimesFP_relative_acc.Fast2Mult_correct_weak (BDIV xh y) y (FINpih xh xl y FIN)
         (fun _ => UF_prod)).
Qed.

Lemma bridge_pih :
  round radix2 (FLX_exp (fprec t)) (Znearest choice) (FT2R (BDIV xh y) * FT2R y)
    = FT2R (BMULT (BDIV xh y) y).
Proof.
have H := f_equal (@fst R R) bridge_prod.
rewrite /DWTimesFP.Fast2Mult /F2Rp /Fast2Mult /= in H. exact H.
Qed.

Lemma bridge_pil :
  round radix2 (FLX_exp (fprec t)) (Znearest choice)
    (FT2R (BDIV xh y) * FT2R y
     - round radix2 (FLX_exp (fprec t)) (Znearest choice) (FT2R (BDIV xh y) * FT2R y))
    = FT2R (Fast2Mult_err (BDIV xh y) y).
Proof.
have H := f_equal (@snd R R) bridge_prod.
rewrite /DWTimesFP.Fast2Mult /F2Rp /= in H. exact H.
Qed.

Lemma prodExact :
  FT2R (BMULT (BDIV xh y) y) + FT2R (Fast2Mult_err (BDIV xh y) y)
    = FT2R (BDIV xh y) * FT2R y.
Proof.
rewrite -bridge_pih -bridge_pil.
have Hg : generic_format radix2 (FLX_exp (fprec t))
   (FT2R (BDIV xh y) * FT2R y
    - round radix2 (FLX_exp (fprec t)) (Znearest choice) (FT2R (BDIV xh y) * FT2R y)).
{ rewrite -Ropp_minus_distr; apply: generic_format_opp.
  apply: (mult_error_FLX radix2 (fprec t) (Znearest choice)
           (FT2R (BDIV xh y)) (FT2R y)); [ exact Fbdiv_flx | exact Fy_flx ]. }
rewrite (round_generic radix2 (FLX_exp (fprec t)) (Znearest choice) _ Hg); ring.
Qed.

Lemma pih_close_xh :
  Rabs (FT2R (BMULT (BDIV xh y) y) - FT2R xh) <= / 2 * Rabs (FT2R xh).
Proof.
set u := bpow radix2 (- fprec t).
have upos : 0 <= u by apply bpow_ge_0.
have Hu16 : u <= /16.
{ rewrite /u. have -> : (/ 16 = bpow radix2 (-4))%R by (simpl; lra).
  apply bpow_le; lia. }
have Hxpos : 0 <= Rabs (FT2R xh) by apply Rabs_pos.
have Hyabs : 0 <= Rabs (FT2R y) by apply Rabs_pos.
have Hth  : FT2R (BDIV xh y) = rnd_p (FT2R xh / FT2R y) by rewrite bridge_th.
have Hpih : FT2R (BMULT (BDIV xh y) y) = rnd_p (FT2R (BDIV xh y) * FT2R y)
  by rewrite bridge_pih.
have Hxhy : FT2R xh / FT2R y * FT2R y = FT2R xh by (field; exact Hyne).
have Heq2u : (/2 * bpow radix2 (- fprec t + 1) = u)%R.
{ rewrite /u. have -> : (- fprec t + 1 = 1 + - fprec t)%Z by lia.
  rewrite bpow_plus. have -> : bpow radix2 1 = 2%R by reflexivity. lra. }

have Hrel1 : Rabs (rnd_p (FT2R xh / FT2R y) - FT2R xh / FT2R y)
             <= /2 * bpow radix2 (- fprec t + 1) * Rabs (FT2R xh / FT2R y)
  by apply: Relative.relative_error_N_FLX; lia.
rewrite Heq2u -Hth in Hrel1.
have HthyX : Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh) <= u * Rabs (FT2R xh).
{ have Hid : FT2R (BDIV xh y) * FT2R y - FT2R xh
            = (FT2R (BDIV xh y) - FT2R xh / FT2R y) * FT2R y
    by (field; exact Hyne).
  rewrite Hid Rabs_mult.
  apply Rle_trans with (u * Rabs (FT2R xh / FT2R y) * Rabs (FT2R y)).
  { apply Rmult_le_compat_r; [exact Hyabs | exact Hrel1]. }
  rewrite Rmult_assoc -Rabs_mult Hxhy. apply Req_le; ring. }

have HthyBnd : Rabs (FT2R (BDIV xh y) * FT2R y) <= Rabs (FT2R xh) + u * Rabs (FT2R xh).
{ apply Rle_trans with (Rabs (FT2R xh) + Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh)).
  - rewrite Rplus_comm. apply Rcomplements.Rle_minus_l.
    exact (Rabs_triang_inv (FT2R (BDIV xh y) * FT2R y) (FT2R xh)).
  - apply Rplus_le_compat_l. exact HthyX. }

have Hrel2 : Rabs (rnd_p (FT2R (BDIV xh y) * FT2R y) - FT2R (BDIV xh y) * FT2R y)
             <= /2 * bpow radix2 (- fprec t + 1) * Rabs (FT2R (BDIV xh y) * FT2R y)
  by apply: Relative.relative_error_N_FLX; lia.
rewrite Heq2u -Hpih in Hrel2.
have Hpih2 : Rabs (FT2R (BMULT (BDIV xh y) y) - FT2R (BDIV xh y) * FT2R y)
           <= u * (Rabs (FT2R xh) + u * Rabs (FT2R xh)).
{ apply Rle_trans with (u * Rabs (FT2R (BDIV xh y) * FT2R y)); [ exact Hrel2 |].
  apply Rmult_le_compat_l; [ exact upos | exact HthyBnd ]. }

apply Rle_trans with (Rabs (FT2R (BMULT (BDIV xh y) y) - FT2R (BDIV xh y) * FT2R y)
                      + Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh)).
- have -> : FT2R (BMULT (BDIV xh y) y) - FT2R xh
          = (FT2R (BMULT (BDIV xh y) y) - FT2R (BDIV xh y) * FT2R y)
          + (FT2R (BDIV xh y) * FT2R y - FT2R xh) by ring.
  apply Rabs_triang.
- eapply Rle_trans; [ apply Rplus_le_compat; [ exact Hpih2 | exact HthyX ] |].
  exact (abst_pih_close (Rabs (FT2R xh)) u Hxpos upos Hu16).
Qed.

Lemma bridge_dh :
  FT2R xh - FT2R (BMULT (BDIV xh y) y) = FT2R (BMINUS xh (BMULT (BDIV xh y) y)).
Proof.
have Hclose := pih_close_xh.
have FX : generic_format radix2 (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
            (FT2R xh) by apply generic_format_FLT_FT2R.
have FP : generic_format radix2 (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
            (FT2R (BMULT (BDIV xh y) y)) by apply generic_format_FLT_FT2R.
have HgFLT : generic_format radix2 (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
               (FT2R xh - FT2R (BMULT (BDIV xh y) y)).
{ have HXP := Rabs_le_inv (FT2R (BMULT (BDIV xh y) y) - FT2R xh)
                          (/2 * Rabs (FT2R xh)) Hclose.
  destruct (Rcase_abs (FT2R xh)) as [HX0|HX0].
  - have HrX : Rabs (FT2R xh) = - FT2R xh by (rewrite Rabs_left //).
    rewrite HrX in HXP.
    have Hopp : FT2R xh - FT2R (BMULT (BDIV xh y) y)
              = - ((- FT2R xh) - (- FT2R (BMULT (BDIV xh y) y))) by ring.
    rewrite Hopp. apply generic_format_opp.
    apply (Sterbenz.sterbenz radix2 (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t)));
      [ apply generic_format_opp; exact FX
      | apply generic_format_opp; exact FP
      | ]. lra.
  - have HrX : Rabs (FT2R xh) = FT2R xh by (rewrite Rabs_pos_eq //; lra).
    rewrite HrX in HXP.
    apply (Sterbenz.sterbenz radix2 (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t)));
      [ exact FX | exact FP | ]. lra. }
rewrite -(BMINUS_round_correct t xh (BMULT (BDIV xh y) y) FIN_dh).
symmetry; apply: round_generic; exact HgFLT.
Qed.

Lemma bridge_dt :
  FT2R (BMINUS xh (BMULT (BDIV xh y) y)) - FT2R (Fast2Mult_err (BDIV xh y) y)
    = FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)).
Proof.
have Heq : FT2R (BMINUS xh (BMULT (BDIV xh y) y)) - FT2R (Fast2Mult_err (BDIV xh y) y)
         = FT2R xh - FT2R (BDIV xh y) * FT2R y
  by rewrite -bridge_dh -prodExact; ring.
have Hgflx : generic_format radix2 (FLX_exp (fprec t))
    (FT2R (BMINUS xh (BMULT (BDIV xh y) y)) - FT2R (Fast2Mult_err (BDIV xh y) y)).
{ rewrite Heq -bridge_th.
  apply: (div_error_FLX radix2 (fprec t) (Znearest choice)
           (FT2R xh) (FT2R y)); [ exact Fxh_flx | exact Fy_flx ]. }

have HgFLT : generic_format radix2 (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
    (FT2R (BMINUS xh (BMULT (BDIV xh y) y)) - FT2R (Fast2Mult_err (BDIV xh y) y)).
{ destruct (Rle_lt_dec (bpow radix2 (emin + fprec t - 1))
              (Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y))
                     - FT2R (Fast2Mult_err (BDIV xh y) y)))) as [Hbig | Hsmall].
  - apply: generic_format_FLT_FLX; [ exact Hbig | exact Hgflx ].
  - have Fdh : generic_format radix2 (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
                 (FT2R (BMINUS xh (BMULT (BDIV xh y) y))) by apply generic_format_FLT_FT2R.
    have Fpil : generic_format radix2 (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
                 (FT2R (Fast2Mult_err (BDIV xh y) y)) by apply generic_format_FLT_FT2R.
    have Hsplit : FT2R (BMINUS xh (BMULT (BDIV xh y) y)) - FT2R (Fast2Mult_err (BDIV xh y) y)
                = FT2R (BMINUS xh (BMULT (BDIV xh y) y))
                  + (- FT2R (Fast2Mult_err (BDIV xh y) y)) by ring.
    rewrite Hsplit.
    apply FLT_format_plus_small;
      [ apply fprec_gt_0 | exact Fdh | apply generic_format_opp; exact Fpil |].
    rewrite -Hsplit.
    apply Rlt_le. eapply Rlt_le_trans; [ exact Hsmall |].
    apply bpow_le. change (@common.emin t) with (SpecFloat.emin (fprec t) (femax t)). lia. }
rewrite -(BMINUS_round_correct t (BMINUS xh (BMULT (BDIV xh y) y))
            (Fast2Mult_err (BDIV xh y) y) FIN_dt).
symmetry; apply: round_generic; exact HgFLT.
Qed.

Lemma bridge_d :
  round radix2 (FLX_exp (fprec t)) (Znearest choice)
    (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) + FT2R xl)
    = FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                          (Fast2Mult_err (BDIV xh y) y)) xl).
Proof.
rewrite -(BPLUS_round_correct t _ xl FIN_d).
by rewrite rnd_plus_FLT_FLX_eq'.
Qed.

Lemma bridge_tl :
  round radix2 (FLX_exp (fprec t)) (Znearest choice)
    (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                         (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
    = FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                (Fast2Mult_err (BDIV xh y) y)) xl) y).
Proof.
rewrite -(BDIV_round_correct t _ y Hyne (FINtl xh xl y FIN)).
by rewrite round_FLT_FLX //; exact UF_tl.
Qed.

Lemma DWDivFP_FLX_FLT :
  DWDivFP.DWDivFP3 (fprec t) choice (FT2R xh) (FT2R xl) (FT2R y)
    = F2Rp (DDModels.DWDivFP xh xl y).
Proof.
rewrite /DWDivFP.DWDivFP3.
cbv zeta.
rewrite DWTimesFP.TwoProdE.
rewrite bridge_th bridge_prod.
rewrite /F2Rp; cbv beta iota.
change (fst (Fast2Mult (BDIV xh y) y)) with (BMULT (BDIV xh y) y).
change (snd (Fast2Mult (BDIV xh y) y)) with (Fast2Mult_err (BDIV xh y) y).
rewrite bridge_dh bridge_dt bridge_d bridge_tl.
rewrite (FastTwoSumEq_FLT (BDIV xh y) _ FIN).
by rewrite /DDModels.DWDivFP.
Qed.

Lemma paper_reduced :
  DWDivFP.DWDivFP3 (fprec t) choice (FT2R xh) (FT2R xl) (FT2R y)
    = F2Sum.Fast2Sum (fprec t) choice (FT2R (BDIV xh y))
        (round radix2 (FLX_exp (fprec t)) (Znearest choice)
          (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                               (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)).
Proof.
rewrite /DWDivFP.DWDivFP3.
cbv zeta.
rewrite DWTimesFP.TwoProdE.
rewrite bridge_th bridge_prod.
rewrite /F2Rp; cbv beta iota.
change (fst (Fast2Mult (BDIV xh y) y)) with (BMULT (BDIV xh y) y).
change (snd (Fast2Mult (BDIV xh y) y)) with (Fast2Mult_err (BDIV xh y) y).
by rewrite bridge_dh bridge_dt bridge_d.
Qed.

End BridgeDWDivFP.

Section DWDivFP_DoubleWord.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Lemma DWDivFP_is_DW (xh xl y : ftype t) :
  is_finite (BPLUS (BDIV xh y)
              (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                           (Fast2Mult_err (BDIV xh y) y)) xl) y)) = true ->
  Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                          (Fast2Mult_err (BDIV xh y) y)) xl) y))
    <= Rabs (FT2R (BDIV xh y)) ->
  double_word_prop (fst (DWDivFP xh xl y)) (snd (DWDivFP xh xl y)).
Proof.
move => Hfin Hord.
have Heqr : DWDivFP xh xl y
          = Fast2Sum (BDIV xh y)
              (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                           (Fast2Mult_err (BDIV xh y) y)) xl) y)
  by rewrite /DWDivFP /Fast2Mult_err /Fast2Mult /Fast2Sum //=.
rewrite Heqr.
have HDW := Fast2Sum_is_DW (BDIV xh y)
             (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                          (Fast2Mult_err (BDIV xh y) y)) xl) y) Hfin Hord.
by move: HDW; rewrite /double_word /double_word_prop /Fast2Sum_sum /Fast2Sum_err.
Qed.

End DWDivFP_DoubleWord.

Section FiniteAccuracyDWDivFP.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (common.emin (t:=t)).
Notation u   := (bpow radix2 (- fprec t)).

Variables (xh xl y : ftype t).
Let zh := FT2R (fst (DWDivFP xh xl y)).
Let zl := FT2R (snd (DWDivFP xh xl y)).

Hypothesis DWx : double_word xh xl.
Hypothesis FIN : is_finite_p (DWDivFP xh xl y).
Hypothesis Hp4 : (4 <= fprec t)%Z.
Hypothesis Hyne : FT2R y <> 0.
Hypothesis UF_th   : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xh / FT2R y).
Hypothesis UF_prod : bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R (BDIV xh y) * FT2R y).

Hypothesis UF_tl   : bpow radix2 (emin + fprec t - 1)
                     <= Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                                   (Fast2Mult_err (BDIV xh y) y)) xl)
                              / FT2R y).

Definition relative_error_DWDivFP :=
  Rabs ((zh + zl - (FT2R xh + FT2R xl) / FT2R y) / ((FT2R xh + FT2R xl) / FT2R y)).

Theorem relative_errorDWDivFP_correct :
  relative_error_DWDivFP <= 3 * u ^ 2.
Proof.
have HFy : generic_format radix2 (FLX_exp (fprec t)) (FT2R y).
{ apply (generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t)).
  apply generic_format_FLT_FT2R. }
have HDWx : DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl)
  by (apply (dw_word_DWdouble xh xl y); exact DWx).
pose proof (@DWDFP3_correct (fprec t) (fprec_gt_one t) choice eq_refl
              (FT2R xh) (FT2R xl) (FT2R y) HDWx HFy Hp4 Hyne) as Hpaper.
rewrite (DWDivFP_FLX_FLT xh xl y FIN Hp4 Hyne UF_th UF_prod UF_tl) in Hpaper.
rewrite /F2Rp/= in Hpaper.
unfold relative_error_DWDivFP, zh, zl.
eapply Rle_trans; [ apply Req_le; reflexivity | ].
rewrite (_ : 3 * u ^ 2 = 3 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t)));
  [ exact Hpaper | rewrite /=; ring ].
Qed.

End FiniteAccuracyDWDivFP.

Section DWDivFP_Finite.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin  := (@common.emin t).
Notation fexp  := (SpecFloat.fexp (fprec t) (femax t)).
Notation ulp   := (Ulp.ulp Zaux.radix2 fexp).
Notation Omega := (bpow Zaux.radix2 (femax t)).

Definition DWDivFP_relative_normal_quotient_precond
    (xh xl y : ftype t) : Prop :=
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite y  = true /\
  double_word_prop xh xl /\
  bpow Zaux.radix2
    (SpecFloat.emin (fprec t) (femax t) + fprec t - 1)
    <= Rabs (FT2R xh / FT2R y) /\
  Rabs (FT2R xh)          <= bpow Zaux.radix2 (femax t - 2) /\
  Rabs (FT2R xh / FT2R y) <= bpow Zaux.radix2 (femax t - 2) /\
  bpow Zaux.radix2
    (SpecFloat.emin (fprec t) (femax t) + 2 * fprec t)
    <= Rabs (FT2R xh).

Definition DWDivFP_internal_precond (xh xl y : ftype t) : Prop :=
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite y = true /\
  double_word_prop xh xl /\
  is_finite (BDIV xh y) = true /\
  bpow Zaux.radix2
    (SpecFloat.emin (fprec t) (femax t) + 2 * fprec t)
    <= Rabs (FT2R xh).

Lemma DWDivFP_denom_nonzero_from_finite (a b : ftype t) :
  is_finite b = true ->
  is_finite (BDIV a b) = true ->
  FT2R b <> 0%R.
Proof.
intros Hb Hfin Hb0.
rewrite <- B2R_float_of_ftype in Hb0.
unfold BDIV, BINOP in Hfin.
rewrite is_finite_Binary float_of_ftype_of_float in Hfin.
rewrite is_finite_Binary in Hb.
destruct (float_of_ftype b) eqn:E; simpl in Hb; try discriminate.
- destruct (float_of_ftype a); cbn [Binary.Bdiv] in Hfin; try discriminate.
- revert Hb0. cbn [Binary.B2R]. apply F2R_neq_0. destruct s; simpl; lia.
Qed.

Lemma DWDivFP_internal_precond_of_strong_precond (xh xl y : ftype t) :
  DWDivFP_strong_precond xh xl y ->
  FT2R xh <> 0 ->
  DWDivFP_internal_precond xh xl y.
Proof.
intros (Hfxh & Hfxl & Hfy & Hdwp & Hfth & _ & _ & Hxhlb) Hxhne.
destruct Hxhlb as [Hxh0 | Hxhlb]; [contradiction |].
repeat split; assumption.
Qed.

Lemma DWDivFP_inputs_finite_of_finite_post_cond (xh xl y : ftype t) :
  DWDivFP_finite_post_cond xh xl y ->
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite y = true.
Proof.
unfold DWDivFP_finite_post_cond.
move => Hfin.
have Hfxh := FINxh xh xl y Hfin.
have Hpih := FINpih xh xl y Hfin.
have [_ Hfy] := BMULT_finite_e t (BDIV xh y) y Hpih.
have Hd := FIN_d xh xl y Hfin.
have [_ Hfxl] := BPLUS_finite_e t _ xl Hd.
exact (conj Hfxh (conj Hfxl Hfy)).
Qed.

Lemma DWDivFP_internal_precond_of_weak_pre_and_finite_post_cond (xh xl y : ftype t) :
  DWDivFP_weak_pre_and_finite_post_cond xh xl y ->
  FT2R xh <> 0 ->
  DWDivFP_internal_precond xh xl y.
Proof.
move => [[Hdwp Hxhlb] Hfin] Hxhne.
destruct Hxhlb as [Hxh0 | Hxhlb]; [contradiction |].
have [Hfxh [Hfxl Hfy]] :=
  DWDivFP_inputs_finite_of_finite_post_cond xh xl y Hfin.
have Hfth : is_finite (BDIV xh y) = true.
{ unfold DWDivFP_finite_post_cond in Hfin.
  exact (FINth xh xl y Hfin). }
repeat split; assumption.
Qed.

Local Instance valid_fexp_inst_div : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.

Lemma thy_residual (xh y : ftype t) :
  is_finite (BDIV xh y) = true -> FT2R y <> 0 ->
  bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xh / FT2R y) ->
  Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh)
    <= Rabs (FT2R xh) * bpow radix2 (- fprec t).
Proof.
move => Hfth Hyne Hnorm.
have Hyy : FT2R xh / FT2R y * FT2R y = FT2R xh.
{ unfold Rdiv. rewrite Rmult_assoc (Rinv_l (FT2R y) Hyne) Rmult_1_r. reflexivity. }
have Hth : FT2R (BDIV xh y) = round radix2 fexp (Znearest choice) (FT2R xh / FT2R y)
  by rewrite BDIV_round_correct.
have Hid : FT2R (BDIV xh y) * FT2R y - FT2R xh
         = (FT2R (BDIV xh y) - FT2R xh / FT2R y) * FT2R y
  by field; exact Hyne.
have He : Rabs (FT2R (BDIV xh y) - FT2R xh / FT2R y) <= / 2 * ulp (FT2R xh / FT2R y)
  by rewrite Hth;
     exact (@error_le_half_ulp radix2 fexp valid_fexp_inst_div choice (FT2R xh / FT2R y)).
have Hu : ulp (FT2R xh / FT2R y) <= Rabs (FT2R xh / FT2R y) * bpow radix2 (1 - fprec t)
  by apply ulp_FLT_le; exact Hnorm.
have Hxhy : Rabs (FT2R xh / FT2R y) * Rabs (FT2R y) = Rabs (FT2R xh)
  by rewrite -Rabs_mult Hyy.
have Hyp : 0 <= Rabs (FT2R y) by apply Rabs_pos.
have Hb1p : bpow radix2 (1 - fprec t) = 2 * bpow radix2 (- fprec t).
{ replace (1 - fprec t)%Z with (1 + - fprec t)%Z by lia.
  rewrite bpow_plus. have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
rewrite Hid Rabs_mult.
apply Rle_trans with (/ 2 * ulp (FT2R xh / FT2R y) * Rabs (FT2R y)).
{ apply Rmult_le_compat_r; [ exact Hyp | exact He ]. }
apply Rle_trans with
  (/ 2 * (Rabs (FT2R xh / FT2R y) * bpow radix2 (1 - fprec t)) * Rabs (FT2R y)).
{ apply Rmult_le_compat_r; [ exact Hyp |].
  apply Rmult_le_compat_l; [ lra | exact Hu ]. }
have Hbp : bpow radix2 (- fprec t) = / 2 * bpow radix2 (1 - fprec t)
  by rewrite Hb1p; lra.
rewrite Hbp -Hxhy. apply Req_le. field.
Qed.

Lemma th_finite (xh y : ftype t) :
  is_finite xh = true -> FT2R y <> 0 ->
  Rabs (FT2R xh / FT2R y) <= bpow radix2 (femax t - 2) ->
  is_finite (BDIV xh y) = true.
Proof.
move => Hfxh Hyne Hq.
have HΩ : 0 < Omega by apply bpow_gt_0.
have Hlt : Rabs (FT2R xh / FT2R y) < Omega.
{ eapply Rle_lt_trans; [exact Hq|]. apply bpow_lt; pose proof femax_lb t; lia. }
apply (no_overflow_div_is_finite t xh y Hfxh Hyne).
eapply Rle_lt_trans; [apply round_abs_le_abs_plus_half_ulp|].
have Hu := ulp_below_overflow _ Hlt.
have H4 := @bpow_femax_minus_two t.
have Hhalf : bpow radix2 (femax t - fprec t) <= /2 * Omega.
{ have -> : (/2 * Omega = bpow radix2 (femax t - 1))%R.
  { have -> : Omega = (bpow radix2 (femax t - 1) * bpow radix2 1)%R
      by rewrite -bpow_plus; f_equal; lia.
    have -> : bpow radix2 1 = 2%R by reflexivity. lra. }
  apply bpow_le; pose proof fprec_lb t; lia. }
lra.
Qed.

Lemma half_ulp_le (v : R) :
  (4 <= fprec t)%Z -> Rabs v < Omega -> / 2 * ulp v <= / 16 * Omega.
Proof.
move => Hp4 Hv.
have Hu := ulp_below_overflow v Hv.
have Hufe : bpow radix2 (femax t - fprec t) <= / 16 * Omega.
{ have -> : (/ 16 * Omega = bpow radix2 (femax t - 4))%R.
  { have -> : Omega = (bpow radix2 (femax t - 4) * bpow radix2 4)%R
      by rewrite -bpow_plus; f_equal; lia.
    have -> : bpow radix2 4 = 16%R by (simpl; lra). lra. }
  apply bpow_le; lia. }
have HΩ0 : 0 <= Omega by apply bpow_ge_0.
lra.
Qed.

Lemma DWDivFP_cascade_acc (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_relative_normal_quotient_precond xh xl y ->
  is_finite (BDIV xh y) = true /\
  is_finite (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y) = true /\
  is_finite (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) = true /\
  Rabs (FT2R (BDIV xh y)) <= / 2 * Omega /\
  Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) <= / 2 * Omega /\
  Rabs (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) < Omega.
Proof.
intros Hp4 (Hfxh & Hfxl & Hfy & Hdwp & Hquot & Hxhb & Hqub & Hxhlb).

have HΩ : 0 < Omega by apply bpow_gt_0.
have HΩ0 : 0 <= Omega by apply bpow_ge_0.
have HΩ32 : 32 <= Omega.
{ have -> : (32 = bpow radix2 5)%R by (simpl; lra).
  apply bpow_le; pose proof (fprec_lt_femax t); lia. }
have Hu16 : (bpow radix2 (- fprec t)) <= / 16.
{ have -> : (/ 16 = bpow radix2 (-4))%R by (simpl; lra).
  apply bpow_le; lia. }
have Hu0 : 0 <= (bpow radix2 (- fprec t)) by (apply bpow_ge_0).
have He0 : 0 <= bpow radix2 (@common.emin t) by apply bpow_ge_0.
have H4Ω : bpow radix2 (femax t - 2) = / 4 * Omega
  by apply bpow_femax_minus_two.
have Hyne : FT2R y <> 0.
{ intro H0.
  have Hp := bpow_gt_0 radix2 (SpecFloat.emin (fprec t) (femax t) + fprec t - 1).
  move: Hquot; rewrite H0 /Rdiv Rinv_0 Rmult_0_r Rabs_R0 => Hc. lra. }
have HYe : bpow radix2 emin <= Rabs (FT2R y)
  by apply nonzero_float_abs_ge_emin, Hyne.
have HYpos : 0 < Rabs (FT2R y)
  by (eapply Rlt_le_trans; [apply bpow_gt_0 | exact HYe]).
have Hxh4 : Rabs (FT2R xh) <= / 4 * Omega by (rewrite -H4Ω; exact Hxhb).
have Hxhp : 0 <= Rabs (FT2R xh) by apply Rabs_pos.

have He1 : bpow radix2 emin <= 1.
{ have Hb0 : bpow radix2 0 = 1 by reflexivity.
  rewrite -Hb0. apply bpow_le.
  change (@common.emin t) with (SpecFloat.emin (fprec t) (femax t)).
  unfold SpecFloat.emin. pose proof (femax_lb t). pose proof (fprec_gt_0 t). lia. }
have HW : Rabs (FT2R xh) * bpow radix2 (- fprec t) <= / 64 * Omega.
{ apply Rle_trans with (/ 4 * Omega * bpow radix2 (- fprec t)).
  - apply Rmult_le_compat_r; [ apply bpow_ge_0 | exact Hxh4 ].
  - apply Rle_trans with (/ 4 * Omega * / 16).
    + apply Rmult_le_compat_l; [ apply Rmult_le_pos; [ lra | apply bpow_ge_0 ] | exact Hu16 ].
    + apply Req_le; field. }
have HW0 : 0 <= Rabs (FT2R xh) * bpow radix2 (- fprec t)
  by apply Rmult_le_pos; [ exact Hxhp | apply bpow_ge_0 ].
have Hnorm : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xh / FT2R y).
{ change (@common.emin t) with (SpecFloat.emin (fprec t) (femax t)). exact Hquot. }

have Fth : is_finite (BDIV xh y) = true
  by apply th_finite; [ exact Hfxh | exact Hyne | exact Hqub ].
have Hthy_res : Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh) <= Rabs (FT2R xh) * (bpow radix2 (- fprec t))
  by apply thy_residual; [ exact Fth | exact Hyne | exact Hnorm ].
have Hthy_xh : Rabs (FT2R (BDIV xh y) * FT2R y) <= Rabs (FT2R xh) + Rabs (FT2R xh) * (bpow radix2 (- fprec t)).
{ have Hti := Rabs_triang_inv (FT2R (BDIV xh y) * FT2R y) (FT2R xh).
  rewrite Rplus_comm.
  apply Rcomplements.Rle_minus_l.
  eapply Rle_trans. apply Hti. exact Hthy_res. }
have Hthy_lt : Rabs (FT2R (BDIV xh y) * FT2R y) < Omega.
{ apply (abst_lt_Om _ Omega (Rabs (FT2R xh)) (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 emin) 1 1 0);
    [ lra | lra | lra | lra | lra | lra | exact HΩ32 | exact Hxh4 | exact HW | exact He1
    | exact Hxhp | exact HW0 | exact He0
    | (eapply Rle_trans; [ exact Hthy_xh |]; apply Req_le; ring) ]. }

have Fpih : is_finite (BMULT (BDIV xh y) y) = true.
{ apply no_overflow_mult_is_finite; [ exact Fth | exact Hfy |].
  eapply Rle_lt_trans; [ apply round_abs_le_abs_plus_half_ulp |].
  apply (abst_fin _ _ _ (Rabs (FT2R xh)) (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 emin) 1 1 0);
    [ lra | lra | lra | lra | lra | lra | exact HΩ32 | exact Hxh4 | exact HW | exact He1
    | exact Hxhp | exact HW0 | exact He0
    | (eapply Rle_trans; [ exact Hthy_xh |]; apply Req_le; ring)
    | exact (half_ulp_le _ Hp4 Hthy_lt) ]. }
have Hpih_e : FT2R (BMULT (BDIV xh y) y)
            = round radix2 fexp (Znearest choice) (FT2R (BDIV xh y) * FT2R y)
  by rewrite BMULT_round_correct.
have Hpiherr : Rabs (FT2R (BMULT (BDIV xh y) y) - FT2R (BDIV xh y) * FT2R y)
             <= Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 2 + bpow radix2 emin.
{ rewrite Hpih_e.
  apply (abst_pih_err (Rabs (FT2R xh)) (bpow radix2 (- fprec t)) (bpow radix2 emin)
                      (Rabs (FT2R (BDIV xh y) * FT2R y)));
    [ exact Hxhp | apply bpow_ge_0 | exact Hu16 | apply bpow_ge_0 | apply Rabs_pos
    | exact Hthy_xh
    | exact (@round_err_emin t (FT2R (BDIV xh y) * FT2R y)) ]. }
have Hpih_b : Rabs (FT2R (BMULT (BDIV xh y) y))
            <= Rabs (FT2R xh) + Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 3 + bpow radix2 emin.
{ apply Rle_trans with (Rabs (FT2R (BMULT (BDIV xh y) y) - FT2R (BDIV xh y) * FT2R y)
                        + Rabs (FT2R (BDIV xh y) * FT2R y)).
  - apply Rcomplements.Rle_minus_l.
    exact (Rabs_triang_inv (FT2R (BMULT (BDIV xh y) y)) (FT2R (BDIV xh y) * FT2R y)).
  - eapply Rle_trans; [ apply Rplus_le_compat; [ exact Hpiherr | exact Hthy_xh ] |].
    apply Req_le; ring. }
have Hpih_lt : Rabs (FT2R (BMULT (BDIV xh y) y)) < Omega.
{ apply (abst_lt_Om _ Omega (Rabs (FT2R xh)) (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 emin) 1 3 1);
    [ lra | lra | lra | lra | lra | lra | exact HΩ32 | exact Hxh4 | exact HW | exact He1
    | exact Hxhp | exact HW0 | exact He0
    | (eapply Rle_trans; [ exact Hpih_b |]; apply Req_le; ring) ]. }

have FBpih : is_finite (BOPP (BMULT (BDIV xh y) y)) = true
  by (apply (BOPP_is_finite t (BMULT (BDIV xh y) y)); exact Fpih).
have Hpe_e : FT2R (BDIV xh y) * FT2R y + FT2R (BOPP (BMULT (BDIV xh y) y))
           = FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y).
{ rewrite -BOPP_binary; [ ring | right; exact Fpih ]. }
have Hpe_lt : Rabs (FT2R (BDIV xh y) * FT2R y + FT2R (BOPP (BMULT (BDIV xh y) y))) < Omega.
{ rewrite Hpe_e.
  have Hsym : Rabs (FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y))
            = Rabs (FT2R (BMULT (BDIV xh y) y) - FT2R (BDIV xh y) * FT2R y)
    by rewrite -Rabs_Ropp; f_equal; ring.
  rewrite Hsym.
  apply (abst_lt_Om _ Omega (Rabs (FT2R xh)) (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 emin) 0 2 1);
    [ lra | lra | lra | lra | lra | lra | exact HΩ32 | exact Hxh4 | exact HW | exact He1
    | exact Hxhp | exact HW0 | exact He0
    | (eapply Rle_trans; [ exact Hpiherr |]; apply Req_le; ring) ]. }
have Hpe_b : Rabs (FT2R (BDIV xh y) * FT2R y + FT2R (BOPP (BMULT (BDIV xh y) y)))
           <= Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 2 + bpow radix2 emin.
{ rewrite Hpe_e.
  have Hs : Rabs (FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y))
          = Rabs (FT2R (BMULT (BDIV xh y) y) - FT2R (BDIV xh y) * FT2R y)
      by (rewrite -Rabs_Ropp; f_equal; ring).
  rewrite Hs. exact Hpiherr. }
have Fpil : is_finite (BFMA (BDIV xh y) y (BOPP (BMULT (BDIV xh y) y))) = true.
{ apply no_overflow_fma_is_finite; [ exact Fth | exact Hfy | exact FBpih |].
  eapply Rle_lt_trans; [ apply round_abs_le_abs_plus_half_ulp |].
  apply (abst_fin _ _ _ (Rabs (FT2R xh)) (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 emin) 0 2 1);
    [ lra | lra | lra | lra | lra | lra | exact HΩ32 | exact Hxh4 | exact HW | exact He1
    | exact Hxhp | exact HW0 | exact He0
    | (eapply Rle_trans; [ exact Hpe_b |]; apply Req_le; ring)
    | exact (half_ulp_le _ Hp4 Hpe_lt) ]. }
have Fpil' : is_finite (Fast2Mult_err (BDIV xh y) y) = true by exact Fpil.
have Hpil_e : FT2R (Fast2Mult_err (BDIV xh y) y)
            = round radix2 fexp (Znearest choice)
                (FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y)).
{ change (FT2R (Fast2Mult_err (BDIV xh y) y))
    with (FT2R (BFMA (BDIV xh y) y (BOPP (BMULT (BDIV xh y) y)))).
  rewrite -BFMA_round_correct; [| exact Fpil]. rewrite Hpe_e. reflexivity. }
have Hpil_b : Rabs (FT2R (Fast2Mult_err (BDIV xh y) y)) <= Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 3 + bpow radix2 emin * 2.
{ rewrite Hpil_e.
  have Hsym : Rabs (FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y))
            = Rabs (FT2R (BMULT (BDIV xh y) y) - FT2R (BDIV xh y) * FT2R y)
      by (rewrite -Rabs_Ropp; f_equal; ring).
  eapply Rle_trans.
  - apply (abst_round_step (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 (- fprec t))
             (bpow radix2 emin) (Rabs (FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y))) _ 2 1);
      [ apply bpow_ge_0 | exact Hu16 | apply bpow_ge_0 | apply Rabs_pos | exact HW0
      | lra | lra | lra | lra
      | (rewrite Hsym; eapply Rle_trans; [ exact Hpiherr |]; apply Req_le; ring)
      | exact (@round_ub_emin t
          (FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y))) ].
  - apply Req_le; ring. }

have Hxhpih_b : Rabs (FT2R xh - FT2R (BMULT (BDIV xh y) y)) <= Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 3 + bpow radix2 emin.
{ have Hsplit : Rabs (FT2R xh - FT2R (BMULT (BDIV xh y) y))
              <= Rabs (FT2R xh - FT2R (BDIV xh y) * FT2R y)
               + Rabs (FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y)).
  { replace (FT2R xh - FT2R (BMULT (BDIV xh y) y))
       with ((FT2R xh - FT2R (BDIV xh y) * FT2R y)
             + (FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y))) by ring.
    apply Rabs_triang. }
  have Hsym : Rabs (FT2R xh - FT2R (BDIV xh y) * FT2R y)
            = Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh)
    by rewrite -Rabs_Ropp; f_equal; ring.
  rewrite Hsym in Hsplit.
  eapply Rle_trans; [ exact Hsplit |].
  apply Rle_trans with (Rabs (FT2R xh) * (bpow radix2 (- fprec t))
                        + (Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 2 + bpow radix2 emin)).
  - apply Rplus_le_compat; [ exact Hthy_res |].
    have Hs2 : Rabs (FT2R (BDIV xh y) * FT2R y - FT2R (BMULT (BDIV xh y) y))
             = Rabs (FT2R (BMULT (BDIV xh y) y) - FT2R (BDIV xh y) * FT2R y)
        by (rewrite -Rabs_Ropp; f_equal; ring).
    rewrite Hs2; exact Hpiherr.
  - apply Req_le; ring. }
have Hxhpih_lt : Rabs (FT2R xh - FT2R (BMULT (BDIV xh y) y)) < Omega.
{ apply (abst_lt_Om _ Omega (Rabs (FT2R xh)) (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 emin) 0 3 1);
    [ lra | lra | lra | lra | lra | lra | exact HΩ32 | exact Hxh4 | exact HW | exact He1
    | exact Hxhp | exact HW0 | exact He0
    | (eapply Rle_trans; [ exact Hxhpih_b |]; apply Req_le; ring) ]. }
have Fdh : is_finite (BMINUS xh (BMULT (BDIV xh y) y)) = true.
{ apply no_overflow_minus_is_finite; [ exact Hfxh | exact Fpih |].
  red. eapply Rle_lt_trans; [ apply round_abs_le_abs_plus_half_ulp |].
  apply (abst_fin _ _ _ (Rabs (FT2R xh)) (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 emin) 0 3 1);
    [ lra | lra | lra | lra | lra | lra | exact HΩ32 | exact Hxh4 | exact HW | exact He1
    | exact Hxhp | exact HW0 | exact He0
    | (eapply Rle_trans; [ exact Hxhpih_b |]; apply Req_le; ring)
    | exact (half_ulp_le _ Hp4 Hxhpih_lt) ]. }
have Hdh_e : FT2R (BMINUS xh (BMULT (BDIV xh y) y))
           = round radix2 fexp (Znearest choice) (FT2R xh - FT2R (BMULT (BDIV xh y) y))
  by rewrite BMINUS_round_correct.
have Hdh_b : Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y)))
           <= Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 4 + bpow radix2 emin * 2.
{ rewrite Hdh_e.
  eapply Rle_trans.
  - apply (abst_round_step (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 (- fprec t))
             (bpow radix2 emin) (Rabs (FT2R xh - FT2R (BMULT (BDIV xh y) y))) _ 3 1);
      [ apply bpow_ge_0 | exact Hu16 | apply bpow_ge_0 | apply Rabs_pos | exact HW0
      | lra | lra | lra | lra
      | (eapply Rle_trans; [ exact Hxhpih_b |]; apply Req_le; ring)
      | exact (@round_ub_emin t
          (FT2R xh - FT2R (BMULT (BDIV xh y) y))) ].
  - apply Req_le; ring. }

have Hdtarg_b : Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y))
                      - FT2R (Fast2Mult_err (BDIV xh y) y))
              <= Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 7 + bpow radix2 emin * 4.
{ apply Rle_trans with (Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y)))
                        + Rabs (FT2R (Fast2Mult_err (BDIV xh y) y))).
  - replace (FT2R (BMINUS xh (BMULT (BDIV xh y) y)) - FT2R (Fast2Mult_err (BDIV xh y) y))
       with (FT2R (BMINUS xh (BMULT (BDIV xh y) y)) + - FT2R (Fast2Mult_err (BDIV xh y) y)) by ring.
    eapply Rle_trans; [ apply Rabs_triang |]. rewrite Rabs_Ropp. apply Rle_refl.
  - apply Rle_trans with (Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 4 + bpow radix2 emin * 2
                          + (Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 3 + bpow radix2 emin * 2)).
    + apply Rplus_le_compat; [ exact Hdh_b | exact Hpil_b ].
    + apply Req_le; ring. }
have Hdtarg_lt : Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y))
                       - FT2R (Fast2Mult_err (BDIV xh y) y)) < Omega.
{ apply (abst_lt_Om _ Omega (Rabs (FT2R xh)) (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 emin) 0 7 4);
    [ lra | lra | lra | lra | lra | lra | exact HΩ32 | exact Hxh4 | exact HW | exact He1
    | exact Hxhp | exact HW0 | exact He0
    | (eapply Rle_trans; [ exact Hdtarg_b |]; apply Req_le; ring) ]. }
have Fdt : is_finite (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                             (Fast2Mult_err (BDIV xh y) y)) = true.
{ apply no_overflow_minus_is_finite; [ exact Fdh | exact Fpil' |].
  red. eapply Rle_lt_trans; [ apply round_abs_le_abs_plus_half_ulp |].
  apply (abst_fin _ _ _ (Rabs (FT2R xh)) (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 emin) 0 7 4);
    [ lra | lra | lra | lra | lra | lra | exact HΩ32 | exact Hxh4 | exact HW | exact He1
    | exact Hxhp | exact HW0 | exact He0
    | (eapply Rle_trans; [ exact Hdtarg_b |]; apply Req_le; ring)
    | exact (half_ulp_le _ Hp4 Hdtarg_lt) ]. }
have Hdt_e : FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y))
           = round radix2 fexp (Znearest choice)
               (FT2R (BMINUS xh (BMULT (BDIV xh y) y)) - FT2R (Fast2Mult_err (BDIV xh y) y))
  by rewrite BMINUS_round_correct.
have Hdt_b : Rabs (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)))
           <= Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 8 + bpow radix2 emin * 5.
{ rewrite Hdt_e.
  eapply Rle_trans.
  - apply (abst_round_step (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 (- fprec t))
             (bpow radix2 emin) (Rabs (FT2R (BMINUS xh (BMULT (BDIV xh y) y))
                                        - FT2R (Fast2Mult_err (BDIV xh y) y))) _ 7 4);
      [ apply bpow_ge_0 | exact Hu16 | apply bpow_ge_0 | apply Rabs_pos | exact HW0
      | lra | lra | lra | lra
      | (eapply Rle_trans; [ exact Hdtarg_b |]; apply Req_le; ring)
      | exact (@round_ub_emin t (FT2R (BMINUS xh (BMULT (BDIV xh y) y))
                              - FT2R (Fast2Mult_err (BDIV xh y) y))) ].
  - apply Req_le; ring. }

have Hxl_b : Rabs (FT2R xl) <= Rabs (FT2R xh) * (bpow radix2 (- fprec t)) + bpow radix2 emin.
{ have Hdwu := DW_acc_lemmas.dw_low_le_half_ulp xh xl Hdwp.
  have Hul := @ulp_le_lin t (FT2R xh).
  have Hb1p : bpow radix2 (1 - fprec t) = 2 * (bpow radix2 (- fprec t)).
  { replace (1 - fprec t)%Z with (1 + - fprec t)%Z by lia.
    rewrite bpow_plus. have -> : bpow radix2 1 = 2%R by reflexivity. ring. }
  rewrite Hb1p in Hul.
  apply (abst_xl (Rabs (FT2R xh)) (bpow radix2 (- fprec t)) (bpow radix2 emin)
                 _ (ulp (FT2R xh)));
    [ apply bpow_ge_0 | exact Hdwu | exact Hul ]. }

have Hdarg_b : Rabs (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y))
                     + FT2R xl)
             <= Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 9 + bpow radix2 emin * 6.
{ apply Rle_trans with (Rabs (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)))
                        + Rabs (FT2R xl)).
  - apply Rabs_triang.
  - apply Rle_trans with (Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 8 + bpow radix2 emin * 5
                          + (Rabs (FT2R xh) * (bpow radix2 (- fprec t)) + bpow radix2 emin)).
    + apply Rplus_le_compat; [ exact Hdt_b | exact Hxl_b ].
    + apply Req_le; ring. }
have Hdarg_lt : Rabs (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                   (Fast2Mult_err (BDIV xh y) y)) + FT2R xl) < Omega.
{ apply (abst_lt_Om _ Omega (Rabs (FT2R xh)) (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 emin) 0 9 6);
    [ lra | lra | lra | lra | lra | lra | exact HΩ32 | exact Hxh4 | exact HW | exact He1
    | exact Hxhp | exact HW0 | exact He0
    | (eapply Rle_trans; [ exact Hdarg_b |]; apply Req_le; ring) ]. }
have Fd : is_finite (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                   (Fast2Mult_err (BDIV xh y) y)) xl) = true.
{ apply no_overflow_sum_is_finite; [ exact Fdt | exact Hfxl |].
  red. eapply Rle_lt_trans; [ apply round_abs_le_abs_plus_half_ulp |].
  apply (abst_fin _ _ _ (Rabs (FT2R xh)) (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 emin) 0 9 6);
    [ lra | lra | lra | lra | lra | lra | exact HΩ32 | exact Hxh4 | exact HW | exact He1
    | exact Hxhp | exact HW0 | exact He0
    | (eapply Rle_trans; [ exact Hdarg_b |]; apply Req_le; ring)
    | exact (half_ulp_le _ Hp4 Hdarg_lt) ]. }
have Hd_e : FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                (Fast2Mult_err (BDIV xh y) y)) xl)
          = round radix2 fexp (Znearest choice)
              (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y))
               + FT2R xl)
  by rewrite BPLUS_round_correct.
have Hd_b : Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                      (Fast2Mult_err (BDIV xh y) y)) xl))
          <= Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 10 + bpow radix2 emin * 7.
{ rewrite Hd_e.
  eapply Rle_trans.
  - apply (abst_round_step (Rabs (FT2R xh) * bpow radix2 (- fprec t)) (bpow radix2 (- fprec t))
             (bpow radix2 emin)
             (Rabs (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y))
                    + FT2R xl)) _ 9 6);
      [ apply bpow_ge_0 | exact Hu16 | apply bpow_ge_0 | apply Rabs_pos | exact HW0
      | lra | lra | lra | lra
      | (eapply Rle_trans; [ exact Hdarg_b |]; apply Req_le; ring)
      | exact (@round_ub_emin t
                 (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y))
                  + FT2R xl)) ].
  - apply Req_le; ring. }

have Hxhq : Rabs (FT2R xh) <= / 4 * Omega * Rabs (FT2R y).
{ have Heq : Rabs (FT2R xh) = Rabs (FT2R xh / FT2R y) * Rabs (FT2R y)
    by (rewrite -Rabs_mult; f_equal; field; exact Hyne).
  rewrite Heq -H4Ω. apply Rmult_le_compat_r; [ apply Rabs_pos | exact Hqub ]. }
have Hdy_b : Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                       (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
           <= 5 / 32 * Omega + 7.
{ rewrite Rabs_mult Rabs_inv.

  apply Rle_trans with ((Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 10 + bpow radix2 emin * 7) * / Rabs (FT2R y)).
  { apply Rmult_le_compat_r; [ apply Rlt_le, Rinv_0_lt_compat; exact HYpos | exact Hd_b ]. }

  apply (Rmult_le_reg_r (Rabs (FT2R y)) _ _ HYpos).
  rewrite Rmult_assoc Rinv_l; [ rewrite Rmult_1_r | lra ].

  have H1 : Rabs (FT2R xh) * (bpow radix2 (- fprec t)) * 10 <= 5 / 32 * Omega * Rabs (FT2R y).
  { apply (abst_H1 _ Omega (Rabs (FT2R y)) (bpow radix2 (- fprec t)));
      [ apply bpow_ge_0 | apply Rabs_pos | exact Hu0 | exact Hu16 |].
    apply Rmult_le_compat_r; [ lra | apply Rmult_le_compat_r; [ exact Hu0 | exact Hxhq ] ]. }
  have H2 : bpow radix2 emin * 7 <= 7 * Rabs (FT2R y).
  { rewrite Rmult_comm. apply Rmult_le_compat_l; [ lra | exact HYe ]. }
  eapply Rle_trans; [ apply Rplus_le_compat; [ exact H1 | exact H2 ] |].
  apply Req_le; ring. }
have Hdy_lt : Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                        (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y) < Omega.
{ apply (abst_dy_lt _ Omega); [ exact HΩ32 | exact Hdy_b ]. }
have Ftl : is_finite (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                          (Fast2Mult_err (BDIV xh y) y)) xl) y) = true.
{ apply (no_overflow_div_is_finite t _ y Fd Hyne).
  eapply Rle_lt_trans; [ apply round_abs_le_abs_plus_half_ulp |].
  apply (abst_fin_dy _ _ Omega);
    [ exact HΩ32 | exact Hdy_b | exact (half_ulp_le _ Hp4 Hdy_lt) ]. }

have Hth_r : round radix2 fexp (Znearest choice) (FT2R xh / FT2R y) = FT2R (BDIV xh y)
  by apply (BDIV_round_correct t xh y Hyne Fth).
have Htl_r : round radix2 fexp (Znearest choice)
               (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                    (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
           = FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                       (Fast2Mult_err (BDIV xh y) y)) xl) y)
  by apply (BDIV_round_correct t _ y Hyne Ftl).
have Hxhy4 : Rabs (FT2R xh / FT2R y) <= / 4 * Omega by (rewrite -H4Ω; exact Hqub).
have Hthv : Rabs (FT2R (BDIV xh y))
          <= Rabs (FT2R xh / FT2R y) + Rabs (FT2R xh / FT2R y) * bpow radix2 (- fprec t)
             + / 2 * bpow radix2 emin
  by (rewrite -Hth_r; apply (@round_ub_emin t)).
have Htlv : Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                    (Fast2Mult_err (BDIV xh y) y)) xl) y))
          <= Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                       (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
             + Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                         (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
               * bpow radix2 (- fprec t)
             + / 2 * bpow radix2 emin
  by (rewrite -Htl_r; apply (@round_ub_emin t)).
have Hsum_le : Rabs (FT2R (BDIV xh y)
                     + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                         (Fast2Mult_err (BDIV xh y) y)) xl) y))
             <= (Rabs (FT2R xh / FT2R y) + Rabs (FT2R xh / FT2R y) * bpow radix2 (- fprec t)
                 + / 2 * bpow radix2 emin)
              + (Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                    (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
                 + Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                     (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
                   * bpow radix2 (- fprec t)
                 + / 2 * bpow radix2 emin).
{ eapply Rle_trans; [ apply Rabs_triang |].
  apply Rplus_le_compat; [ exact Hthv | exact Htlv ]. }
have Hsum_lt : Rabs (FT2R (BDIV xh y)
                     + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                         (Fast2Mult_err (BDIV xh y) y)) xl) y)) < Omega.
{ apply (abst_fst_sum _ (Rabs (FT2R xh / FT2R y))
           (Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                              (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y))
           Omega (bpow radix2 (- fprec t)) (bpow radix2 emin));
    [ apply bpow_ge_0 | exact Hu16 | apply bpow_ge_0 | exact He1 | exact HΩ32
    | apply Rabs_pos | exact Hxhy4 | apply Rabs_pos | exact Hdy_b | exact Hsum_le ]. }
have Hfp : is_finite (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) = true.
{
apply no_overflow_sum_is_finite; [ exact Fth | exact Ftl |].
eapply Rle_lt_trans; [ apply round_abs_le_abs_plus_half_ulp |].
apply (abst_fst_fin _ _ (Rabs (FT2R xh / FT2R y))
         (Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                            (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y))
         Omega (bpow radix2 (- fprec t)) (bpow radix2 emin));
  [ apply bpow_ge_0 | exact Hu16 | apply bpow_ge_0 | exact He1 | exact HΩ32
  | apply Rabs_pos | exact Hxhy4 | apply Rabs_pos | exact Hdy_b
  | exact Hsum_le | exact (half_ulp_le _ Hp4 Hsum_lt) ].
}
have Hthb : Rabs (FT2R (BDIV xh y)) <= / 2 * Omega.
{ eapply Rle_trans; [ exact Hthv |].
  apply (abst_th_half (Rabs (FT2R xh / FT2R y)) (bpow radix2 (- fprec t)) (bpow radix2 emin) Omega);
    [ apply Rabs_pos | exact Hxhy4 | apply bpow_ge_0 | exact Hu16 | apply bpow_ge_0 | exact He1 | exact HΩ32 ]. }
have Htlb : Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) <= / 2 * Omega.
{ eapply Rle_trans; [ exact Htlv |].
  apply (abst_tl_half (Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)) (bpow radix2 (- fprec t)) (bpow radix2 emin) Omega);
    [ apply Rabs_pos | exact Hdy_b | apply bpow_ge_0 | exact Hu16 | apply bpow_ge_0 | exact He1 | exact HΩ32 ]. }
split; [ exact Fth | split; [ exact Ftl | split; [ exact Hfp | split; [ exact Hthb
  | split; [ exact Htlb | exact Hsum_lt ]]]]].
Qed.

Lemma DWDivFP_fst_finite_acc (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_relative_normal_quotient_precond xh xl y ->
  is_finite (fst (DWDivFP xh xl y)) = true.
Proof.
intros Hp4 COND.
have Hfstred : fst (DWDivFP xh xl y)
             = BPLUS (BDIV xh y)
                 (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                              (Fast2Mult_err (BDIV xh y) y)) xl) y)
  by rewrite /DWDivFP /Fast2Mult_err /Fast2Mult /Fast2Sum //=.
rewrite Hfstred.
exact (proj1 (proj2 (proj2 (DWDivFP_cascade_acc xh xl y Hp4 COND)))).
Qed.

Lemma DWDivFP_snd_finite_acc (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_relative_normal_quotient_precond xh xl y ->
  is_finite (snd (DWDivFP xh xl y)) = true.
Proof.
intros Hp4 COND.
destruct (DWDivFP_cascade_acc xh xl y Hp4 COND)
  as (Fth & Ftl & Hfp & Hthb & Htlb & Hsum_lt).
have HΩ32 : 32 <= Omega.
{ have -> : (32 = bpow radix2 5)%R by (simpl; lra).
  apply bpow_le; pose proof (fprec_lt_femax t); lia. }
have Hsndred : snd (DWDivFP xh xl y)
             = BMINUS (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y) (BMINUS (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) (BDIV xh y))
  by rewrite /DWDivFP /Fast2Mult_err /Fast2Mult /Fast2Sum //=.
rewrite Hsndred.
have Hs_r : round radix2 fexp (Znearest choice) (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) = FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y))
  by (rewrite (BPLUS_round_correct t (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y) Hfp)).

have Herr : Rabs (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)) <= / 2 * ulp (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) + Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)).
{ rewrite -Hs_r.
  apply Rle_trans with (Rabs (round radix2 fexp (Znearest choice) (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y))) + Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y))).
  - have -> : round radix2 fexp (Znearest choice) (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)
            = (round radix2 fexp (Znearest choice) (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y))) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y) by ring.
    apply Rabs_triang.
  - apply Rplus_le_compat_r. exact (@error_le_half_ulp radix2 fexp valid_fexp_inst_div choice (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y))). }
have HU1 : / 2 * ulp (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) <= / 16 * Omega by exact (half_ulp_le _ Hp4 Hsum_lt).
have Hd_lt : Rabs (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)) < Omega.
{ apply Rle_lt_trans with (/ 16 * Omega + / 2 * Omega); [| lra ].
  eapply Rle_trans; [ exact Herr |]. apply Rplus_le_compat; [ exact HU1 | exact Htlb ]. }
have Fz : is_finite (BMINUS (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) (BDIV xh y)) = true.
{ apply no_overflow_minus_is_finite; [ exact Hfp | exact Fth |].
  red. eapply Rle_lt_trans; [ apply round_abs_le_abs_plus_half_ulp |].
  apply (abst_z _ (/ 2 * ulp (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y))) (/ 2 * ulp (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y))) (Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y))) Omega);
    [ exact HΩ32 | exact HU1 | exact Htlb | exact (half_ulp_le _ Hp4 Hd_lt) | exact Herr ]. }
have Hz_r : round radix2 fexp (Znearest choice) (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)) = FT2R (BMINUS (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) (BDIV xh y))
  by (rewrite (BMINUS_round_correct t (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) (BDIV xh y) Fz)).
have Htlz : Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y) - FT2R (BMINUS (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) (BDIV xh y))) <= / 2 * ulp (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) + / 2 * ulp (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)).
{ rewrite -Hz_r.
  apply Rle_trans with (Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y) - (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y))) + Rabs ((FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)) - round radix2 fexp (Znearest choice) (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)))).
  - have -> : FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y) - round radix2 fexp (Znearest choice) (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)) = (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y) - (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y))) + ((FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)) - round radix2 fexp (Znearest choice) (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y))) by ring.
    apply Rabs_triang.
  - apply Rplus_le_compat.
    + rewrite -Hs_r.
      have -> : FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y) - (round radix2 fexp (Znearest choice) (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y))
              = - (round radix2 fexp (Znearest choice) (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y))) by ring.
      rewrite Rabs_Ropp. exact (@error_le_half_ulp radix2 fexp valid_fexp_inst_div choice (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y))).
    + have -> : (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)) - round radix2 fexp (Znearest choice) (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)) = - (round radix2 fexp (Znearest choice) (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)) - (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y))) by ring.
      rewrite Rabs_Ropp. exact (@error_le_half_ulp radix2 fexp valid_fexp_inst_div choice (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y))). }
have Htlz_lt : Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y) - FT2R (BMINUS (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) (BDIV xh y))) < Omega.
{ apply Rle_lt_trans with (/ 16 * Omega + / 16 * Omega); [| lra ].
  eapply Rle_trans; [ exact Htlz |].
  apply Rplus_le_compat; [ exact HU1 | exact (half_ulp_le _ Hp4 Hd_lt) ]. }
apply no_overflow_minus_is_finite; [ exact Ftl | exact Fz |].
red. eapply Rle_lt_trans; [ apply round_abs_le_abs_plus_half_ulp |].
apply (abst_snd _ (/ 2 * ulp (FT2R (BDIV xh y) + FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y))) (/ 2 * ulp (FT2R (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) - FT2R (BDIV xh y)))
            (/ 2 * ulp (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y) - FT2R (BMINUS (BPLUS (BDIV xh y) (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y)) (Fast2Mult_err (BDIV xh y) y)) xl) y)) (BDIV xh y)))) Omega);
  [ exact HΩ32 | exact HU1 | exact (half_ulp_le _ Hp4 Hd_lt)
  | exact (half_ulp_le _ Hp4 Htlz_lt) | exact Htlz ].
Qed.

Lemma cond_UF_prod_internal (xh xl y : ftype t) :
  DWDivFP_internal_precond xh xl y ->
  bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xh / FT2R y) ->
  bpow radix2 (emin + 2 * fprec t - 1) <=
    Rabs (FT2R (BDIV xh y) * FT2R y).
Proof.
move => [Hfxh [Hfxl [Hfy [Hdwp [Hfth Hxhlb]]]]] Hquot.
have Hyne : FT2R y <> 0.
{ exact (DWDivFP_denom_nonzero_from_finite xh y Hfy Hfth). }
have Hres := thy_residual xh y Hfth Hyne Hquot.
have HX0 : 0 <= Rabs (FT2R xh) by apply Rabs_pos.
have Hu2 : bpow radix2 (- fprec t) <= /2.
{ have H3 : bpow radix2 (1 - fprec t) = 2 * bpow radix2 (- fprec t).
  { replace (1 - fprec t)%Z with (1 + - fprec t)%Z by lia.
    rewrite bpow_plus. have -> : bpow radix2 1 = 2 by reflexivity. ring. }
  have H2 : bpow radix2 (1 - fprec t) <= 1.
  { have -> : (1:R) = bpow radix2 0 by reflexivity.
    apply bpow_le. pose proof (fprec_gt_one t). lia. }
  lra. }
have HRX : Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh)
            <= Rabs (FT2R xh) * /2.
{ eapply Rle_trans; [ exact Hres |].
  apply Rmult_le_compat_l; [ exact HX0 | exact Hu2 ]. }
have HP : Rabs (FT2R xh) -
            Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh)
          <= Rabs (FT2R (BDIV xh y) * FT2R y).
{ have Hpre : Rabs (FT2R xh) -
      Rabs (FT2R (BDIV xh y) * FT2R y)
      <= Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh).
  { rewrite (Rabs_minus_sym (FT2R (BDIV xh y) * FT2R y) (FT2R xh)).
    exact (Rabs_triang_inv (FT2R xh)
      (FT2R (BDIV xh y) * FT2R y)). }
  exact (abst_revtri _ _ _ Hpre). }
have HB : bpow radix2 (emin + 2 * fprec t - 1) =
          /2 * bpow radix2 (emin + 2 * fprec t).
{ set k := (emin + 2 * fprec t - 1)%Z.
  have -> : (emin + 2 * fprec t = k + 1)%Z by (unfold k; lia).
  rewrite bpow_plus. have -> : bpow radix2 1 = 2 by reflexivity. field. }
rewrite HB.
apply (abst_prod_lb (Rabs (FT2R (BDIV xh y) * FT2R y))
        (Rabs (FT2R (BDIV xh y) * FT2R y - FT2R xh))
        (Rabs (FT2R xh))
        (bpow radix2 (emin + 2 * fprec t)));
  [ exact HRX | exact HP | exact Hxhlb ].
Qed.

Lemma DWDivFP_residual_le_high_internal (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_internal_precond xh xl y ->
  is_finite_p (DWDivFP xh xl y) ->
  bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xh / FT2R y) ->
  Rabs (FT2R (BPLUS
    (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
            (Fast2Mult_err (BDIV xh y) y)) xl)) <= Rabs (FT2R xh).
Proof.
move => Hp4 COND FIN Hquot.
move: (COND) => [Hfxh [Hfxl [Hfy [Hdwp [Hfth Hxhlb]]]]].
set u := bpow radix2 (- fprec t).
have Hu0 : 0 <= u by (unfold u; apply bpow_ge_0).
have Hu : u <= /16.
{ unfold u. have -> : (/16:R) = bpow radix2 (-4) by (simpl; lra).
  apply bpow_le; lia. }
have Hx0 : 0 <= Rabs (FT2R xh) by apply Rabs_pos.
have Hyne := DWDivFP_denom_nonzero_from_finite xh y Hfy Hfth.
have UFprod := cond_UF_prod_internal xh xl y COND Hquot.
have Hdh := bridge_dh xh xl y FIN Hp4 Hyne Hquot UFprod.
have Hdt := bridge_dt xh xl y FIN Hp4 Hyne Hquot UFprod.
have Hprod := prodExact xh xl y FIN UFprod.
have HdtE :
  FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                (Fast2Mult_err (BDIV xh y) y)) =
  FT2R xh - FT2R (BDIV xh y) * FT2R y.
{ rewrite -Hdt -Hdh. lra. }
have Hres := thy_residual xh y Hfth Hyne Hquot.
fold u in Hres.
have HdtB :
  Rabs (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                      (Fast2Mult_err (BDIV xh y) y)))
  <= u * Rabs (FT2R xh).
{ rewrite HdtE Rabs_minus_sym.
  replace (u * Rabs (FT2R xh)) with (Rabs (FT2R xh) * u) by ring.
  exact Hres. }
have Hxl := DW_acc_lemmas.dw_low_le_u_high xh xl Hdwp.
specialize (Hxl STD).
fold u in Hxl.
set a := (FT2R (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                       (Fast2Mult_err (BDIV xh y) y)) + FT2R xl)%R.
have Ha : Rabs a <= 2*u*Rabs (FT2R xh).
{ unfold a. eapply Rle_trans; [apply Rabs_triang|].
  replace (2*u*Rabs (FT2R xh))
    with (u*Rabs (FT2R xh) + u*Rabs (FT2R xh)) by ring.
  apply Rplus_le_compat; [exact HdtB | exact Hxl]. }
have Hr : Rabs
    (round radix2 (FLX_exp (fprec t)) (Znearest choice) a - a)
    <= u * Rabs a.
{ have H := Relative.relative_error_N_FLX radix2 (fprec t)
      (fprec_gt_0 t) choice a.
  have Heq : /2 * bpow radix2 (- fprec t + 1) = u.
  { unfold u. replace (- fprec t + 1)%Z with (1 + - fprec t)%Z by lia.
    rewrite bpow_plus. change (bpow radix2 1) with 2. lra. }
  rewrite Heq in H. exact H. }
have Hd := bridge_d xh xl y FIN.
fold a in Hd.
rewrite Hd in Hr.
have Htri := Rabs_triang
  (FT2R (BPLUS
    (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
            (Fast2Mult_err (BDIV xh y) y)) xl) - a) a.
specialize (Htri NANS STD NANS STD NANS STD NANS STD NANS STD NANS STD
                   NANS STD).
replace
  (FT2R (BPLUS
    (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
            (Fast2Mult_err (BDIV xh y) y)) xl) - a + a)%R
  with (FT2R (BPLUS
    (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
            (Fast2Mult_err (BDIV xh y) y)) xl)) in Htri by ring.
have Hua : u * Rabs a <= 2*u*u*Rabs (FT2R xh).
{ have H := Rmult_le_compat_l u _ _ Hu0 Ha. nra. }
have Hcoef : 2*u + 2*u*u <= 1 by nra.
eapply Rle_trans; [exact Htri|].
eapply Rle_trans; [apply Rplus_le_compat; [exact Hr|exact Ha]|].
nra.
Qed.

Lemma DWDivFP_ordering_internal (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_internal_precond xh xl y ->
  is_finite_p (DWDivFP xh xl y) ->
  bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xh / FT2R y) ->
  Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                          (Fast2Mult_err (BDIV xh y) y)) xl) y))
    <= Rabs (FT2R (BDIV xh y)).
Proof.
move => Hp4 COND FIN Hquot.
move: (COND) => [Hfxh [Hfxl [Hfy [Hdwp [Hfth Hxhlb]]]]].
have Hyne := DWDivFP_denom_nonzero_from_finite xh y Hfy Hfth.
have Ftl := FINtl xh xl y FIN.
set d := BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
               (Fast2Mult_err (BDIV xh y) y)) xl.
rewrite -(BDIV_round_correct t xh y Hyne Hfth)
        -(BDIV_round_correct t d y Hyne Ftl).
rewrite -!round_NE_abs.
apply round_le; [ apply FLT.FLT_exp_valid, fprec_gt_0 | apply valid_rnd_N |].
rewrite !Rabs_mult.
apply Rmult_le_compat_r; [ apply Rabs_pos |].
exact (DWDivFP_residual_le_high_internal xh xl y Hp4 COND FIN Hquot).
Qed.

Corollary DWDivFP_double_word_from_internal_normal_quotient
    (xh xl y : ftype t) :
  (4 <= fprec t)%Z ->
  DWDivFP_internal_precond xh xl y ->
  is_finite_p (DWDivFP xh xl y) ->
  bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R xh / FT2R y) ->
  double_word_prop (fst (DWDivFP xh xl y))
                   (snd (DWDivFP xh xl y)).
Proof.
move => Hp4 COND FIN Hquot.
apply DWDivFP_is_DW.
- exact (proj1 FIN).
- exact (DWDivFP_ordering_internal xh xl y Hp4 COND FIN Hquot).
Qed.

End DWDivFP_Finite.

Section CondAccuracyDWDivFP.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (@common.emin t).
Notation u := (bpow radix2 (- fprec t)).

Variables (xh xl y : ftype t).

Hypothesis Hp4 : (4 <= fprec t)%Z.
Hypothesis COND : DWDivFP_internal_precond xh xl y.
Hypothesis FIN : is_finite_p (DWDivFP xh xl y).
Hypothesis Hquot : bpow radix2 (emin + fprec t - 1)
  <= Rabs (FT2R xh / FT2R y).
Hypothesis Hdyn : bpow radix2 (emin + fprec t - 1)
  <= Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                               (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y).

Local Theorem DWDivFP_relative_accuracy_normal_quotient :
  relative_error_DWDivFP xh xl y <= 3 * u ^ 2.
Proof.
move: (COND) => [Hfxh [Hfxl [Hfy [Hdwp [Hfth Hxhlb]]]]].
have Hyne := DWDivFP_denom_nonzero_from_finite xh y Hfy Hfth.
exact (relative_errorDWDivFP_correct xh xl y Hdwp FIN Hp4 Hyne
         Hquot (cond_UF_prod_internal xh xl y COND Hquot) Hdyn).
Qed.

End CondAccuracyDWDivFP.

Section CondAccuracyDWDivFP_underflow.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (@common.emin t).
Notation u := (bpow radix2 (- fprec t)).

Variables (xh xl y : ftype t).

Hypothesis Hp4 : (4 <= fprec t)%Z.
Hypothesis COND : DWDivFP_internal_precond xh xl y.
Hypothesis FIN : is_finite_p (DWDivFP xh xl y).
Hypothesis Hquot : bpow radix2 (emin + fprec t - 1)
  <= Rabs (FT2R xh / FT2R y).
Hypothesis Huf : Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                          (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
                 < bpow radix2 (emin + fprec t - 1).

Local Instance vfe_uf : Generic_fmt.Valid_exp (SpecFloat.fexp (fprec t) (femax t)).
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.
Local Instance vfe_flt : Generic_fmt.Valid_exp
  (FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t)).
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.
Local Instance vflx_uf : Generic_fmt.Valid_exp (FLX_exp (fprec t)).
Proof. apply FLX.FLX_exp_valid, fprec_gt_0. Qed.

Local Theorem DWDivFP_error_underflow_perturbation :
  Rabs (FT2R (fst (DWDivFP xh xl y)) + FT2R (snd (DWDivFP xh xl y))
        - (FT2R xh + FT2R xl) / FT2R y)
    <= 3 * u ^ 2 * Rabs ((FT2R xh + FT2R xl) / FT2R y)
       + Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                         (Fast2Mult_err (BDIV xh y) y)) xl) y)
               - round radix2 (FLX_exp (fprec t)) (Znearest choice)
                   (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                        (Fast2Mult_err (BDIV xh y) y)) xl)
                    / FT2R y)).
Proof.
set d := BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                       (Fast2Mult_err (BDIV xh y) y)) xl.
move: (COND) => [Hfxh [Hfxl [Hfy [Hdwp [Hfth Hxhlb]]]]].
have Hyne := DWDivFP_denom_nonzero_from_finite xh y Hfy Hfth.
have UFprod : bpow radix2 (emin + 2 * fprec t - 1) <= Rabs (FT2R (BDIV xh y) * FT2R y)
  by exact (cond_UF_prod_internal xh xl y COND Hquot).
have HFy : generic_format radix2 (FLX_exp (fprec t)) (FT2R y)
  by (apply (generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t));
      apply generic_format_FLT_FT2R).
have HDWx : DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl)
  by (apply (dw_word_DWdouble xh xl y); exact Hdwp).

set v0 := (FT2R d / FT2R y).
have Fth : generic_format radix2 (FLX_exp (fprec t)) (FT2R (BDIV xh y))
  by (apply (generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t));
      apply generic_format_FLT_FT2R).
have Ftls : generic_format radix2 (FLX_exp (fprec t))
              (round radix2 (FLX_exp (fprec t)) (Znearest choice) v0).
{ apply generic_format_round; typeclasses eauto. }
have Ftl : generic_format radix2 (FLX_exp (fprec t)) (FT2R (BDIV d y))
  by (apply (generic_format_FLX_FLT radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t));
      apply generic_format_FLT_FT2R).

have Fbnd_lo_flx : generic_format radix2 (FLX_exp (fprec t))
                 (bpow radix2 (emin + fprec t - 1)).
{ apply generic_format_bpow. unfold FLX_exp, common.emin. pose proof (fprec_gt_one t). lia. }
have Fbnd_lo_flt : generic_format radix2 (SpecFloat.fexp (fprec t) (femax t))
                 (bpow radix2 (emin + fprec t - 1)).
{ apply generic_format_bpow. unfold SpecFloat.fexp, common.emin. pose proof (fprec_gt_one t). lia. }
have Hth_gelo : bpow radix2 (emin + fprec t - 1) <= Rabs (FT2R (BDIV xh y)).
{ rewrite -(BDIV_round_correct t xh y Hyne (FINth xh xl y FIN)).
  apply abs_round_ge_generic;
    first [ exact Fbnd_lo_flt | exact Fbnd_lo_flx
          | exact Hquot
          | exact vfe_flt | apply valid_rnd_N | typeclasses eauto ]. }
have Htls_le : Rabs (round radix2 (FLX_exp (fprec t)) (Znearest choice) v0)
               <= bpow radix2 (emin + fprec t - 1).
{ apply abs_round_le_generic;
    first [ exact Fbnd_lo_flx | (apply Rlt_le; exact Huf) | exact vflx_uf | apply valid_rnd_N ]. }
have Htl_le : Rabs (FT2R (BDIV d y)) <= bpow radix2 (emin + fprec t - 1).
{ rewrite -(BDIV_round_correct t d y Hyne (FINtl xh xl y FIN)).
  apply abs_round_le_generic;
    first [ exact Fbnd_lo_flt | (apply Rlt_le; exact Huf) | exact vfe_flt | apply valid_rnd_N ]. }
have Hord_p : Rabs (round radix2 (FLX_exp (fprec t)) (Znearest choice) v0)
              <= Rabs (FT2R (BDIV xh y)) by (eapply Rle_trans; [ exact Htls_le | exact Hth_gelo ]).
have Hord_r : Rabs (FT2R (BDIV d y)) <= Rabs (FT2R (BDIV xh y))
  by (eapply Rle_trans; [ exact Htl_le | exact Hth_gelo ]).

pose proof (@DWDFP3_correct (fprec t) (fprec_gt_one t) choice eq_refl
              (FT2R xh) (FT2R xl) (FT2R y) HDWx HFy Hp4 Hyne) as Hpaper.
rewrite (paper_reduced xh xl y FIN Hp4 Hyne Hquot UFprod) in Hpaper.
move: Hpaper.
case Ep : (F2Sum.Fast2Sum (fprec t) choice (FT2R (BDIV xh y))
             (round radix2 (FLX_exp (fprec t)) (Znearest choice) v0)) => [zhp zlp].
move => Hpaper.

have Hsum_p : zhp + zlp = FT2R (BDIV xh y)
              + round radix2 (FLX_exp (fprec t)) (Znearest choice) v0.
{ have Hs := @flx_f2s_sum t (FT2R (BDIV xh y))
              (round radix2 (FLX_exp (fprec t)) (Znearest choice) v0) Fth Ftls Hord_p.
  rewrite Ep /= in Hs. exact Hs. }

have Hrun : F2Sum.Fast2Sum (fprec t) choice (FT2R (BDIV xh y)) (FT2R (BDIV d y))
            = F2Rp (DDModels.Fast2Sum (BDIV xh y) (BDIV d y)).
{ apply (FastTwoSumEq_FLT (BDIV xh y) (BDIV d y)). exact FIN. }
have Hsum_r : FT2R (fst (DWDivFP xh xl y)) + FT2R (snd (DWDivFP xh xl y))
              = FT2R (BDIV xh y) + FT2R (BDIV d y).
{ have Hs := @flx_f2s_sum t
    (FT2R (BDIV xh y)) (FT2R (BDIV d y)) Fth Ftl Hord_r.
  have Heqr : DWDivFP xh xl y = DDModels.Fast2Sum (BDIV xh y) (BDIV d y)
    by rewrite /DWDivFP /Fast2Mult_err /Fast2Mult /Fast2Sum //=.
  rewrite Hrun /F2Rp /= in Hs. rewrite Heqr. exact Hs. }

have Hdiff : Rabs ((FT2R (fst (DWDivFP xh xl y)) + FT2R (snd (DWDivFP xh xl y)))
                   - (zhp + zlp))
             <= Rabs (FT2R (BDIV d y)
                      - round radix2 (FLX_exp (fprec t)) (Znearest choice) v0).
{ have -> : (FT2R (fst (DWDivFP xh xl y)) + FT2R (snd (DWDivFP xh xl y))) - (zhp + zlp)
           = FT2R (BDIV d y)
             - round radix2 (FLX_exp (fprec t)) (Znearest choice) v0
    by rewrite Hsum_r Hsum_p; ring.
  apply Rle_refl. }

have Hxhne : FT2R xh <> 0.
{ intro Hx0. move: Hquot; rewrite Hx0 /Rdiv Rmult_0_l Rabs_R0 => Hc.
  have := bpow_gt_0 radix2 (emin + fprec t - 1). lra. }
have Hsne : FT2R xh + FT2R xl <> 0.
{ intro Hs0. apply Hxhne. move: Hdwp; rewrite /double_word_prop Hs0.
  rewrite /rounded round_0 //. }
have Hpabs : Rabs (zhp + zlp - (FT2R xh + FT2R xl) / FT2R y)
             <= 3 * u ^ 2 * Rabs ((FT2R xh + FT2R xl) / FT2R y).
{ have Hconv : Rabs (zhp + zlp - (FT2R xh + FT2R xl) / FT2R y)
             = Rabs ((zhp + zlp - (FT2R xh + FT2R xl) / FT2R y)
                     / ((FT2R xh + FT2R xl) / FT2R y))
               * Rabs ((FT2R xh + FT2R xl) / FT2R y).
  { rewrite -Rabs_mult. f_equal. field. split; [ exact Hyne | exact Hsne ]. }
  rewrite Hconv.
  have Hupow : 3 * u ^ 2 = 3 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t))
    by (rewrite /=; ring).
  apply Rmult_le_compat_r; [ apply Rabs_pos |].
  rewrite Hupow. exact Hpaper. }

eapply Rle_trans with
  (Rabs ((FT2R (fst (DWDivFP xh xl y)) + FT2R (snd (DWDivFP xh xl y))) - (zhp + zlp))
   + Rabs (zhp + zlp - (FT2R xh + FT2R xl) / FT2R y)).
{ have -> : FT2R (fst (DWDivFP xh xl y)) + FT2R (snd (DWDivFP xh xl y))
            - (FT2R xh + FT2R xl) / FT2R y
          = ((FT2R (fst (DWDivFP xh xl y)) + FT2R (snd (DWDivFP xh xl y))) - (zhp + zlp))
            + (zhp + zlp - (FT2R xh + FT2R xl) / FT2R y) by ring.
  apply Rabs_triang. }
rewrite Rplus_comm. apply Rplus_le_compat; [ exact Hpabs | exact Hdiff ].
Qed.

End CondAccuracyDWDivFP_underflow.

Local Lemma DWDivFP_tl_perturbation_le_eta
  {NANS: Nans} {t : type} {STD: is_standard t}
  (xh xl y : ftype t)
  (Hp4 : (4 <= fprec t)%Z)
  (COND : DWDivFP_internal_precond xh xl y)
  (FIN : is_finite_p (DWDivFP xh xl y)) :
  Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                  (Fast2Mult_err (BDIV xh y) y)) xl) y)
        - round radix2 (FLX_exp (fprec t)) (Znearest choice)
            (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                 (Fast2Mult_err (BDIV xh y) y)) xl)
             / FT2R y))
    <= bpow radix2 (@common.emin t).
Proof.
move: (COND) => [Hfxh [Hfxl [Hfy [Hdwp [Hfth Hxhlb]]]]].
have Hyne := DWDivFP_denom_nonzero_from_finite xh y Hfy Hfth.
have Htl_r : FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                       (Fast2Mult_err (BDIV xh y) y)) xl) y)
             = round radix2 (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
                 (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                      (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
  by rewrite (BDIV_round_correct t _ y Hyne (FINtl xh xl y FIN)).
rewrite Htl_r. exact (@round_FLT_FLX_diff t _).
Qed.

Local Lemma DWDivFP_error_exact_division
  {NANS: Nans} {t : type} {STD: is_standard t}
  (xh xl y : ftype t)
  (Hp4 : (4 <= fprec t)%Z)
  (COND : DWDivFP_internal_precond xh xl y)
  (FIN : is_finite_p (DWDivFP xh xl y))
  (Hquot : bpow radix2 (@common.emin t + fprec t - 1)
            <= Rabs (FT2R xh / FT2R y))
  (Hd0 : FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                             (Fast2Mult_err (BDIV xh y) y)) xl) = 0) :
  Rabs (FT2R (fst (DWDivFP xh xl y)) + FT2R (snd (DWDivFP xh xl y))
        - (FT2R xh + FT2R xl) / FT2R y)
    <= 3 * (bpow radix2 (- fprec t)) ^ 2
       * Rabs ((FT2R xh + FT2R xl) / FT2R y).
Proof.
have Hv0 : FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                               (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y = 0
  by rewrite Hd0 /Rdiv Rmult_0_l.
have Huf : Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                     (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
           < bpow radix2 (@common.emin t + fprec t - 1)
  by rewrite Hv0 Rabs_R0; apply bpow_gt_0.
have Habs := DWDivFP_error_underflow_perturbation
  xh xl y Hp4 COND FIN Hquot Huf.
move: (COND) => [Hfxh [Hfxl [Hfy [Hdwp [Hfth Hxhlb]]]]].
have Hyne := DWDivFP_denom_nonzero_from_finite xh y Hfy Hfth.
have Hpert : Rabs (FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                             (Fast2Mult_err (BDIV xh y) y)) xl) y)
                   - round radix2 (FLX_exp (fprec t)) (Znearest choice)
                       (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                            (Fast2Mult_err (BDIV xh y) y)) xl)
                        / FT2R y)) = 0.
{ have Htl_r : FT2R (BDIV (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                         (Fast2Mult_err (BDIV xh y) y)) xl) y)
               = round radix2 (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
                   (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                        (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)
    by rewrite (BDIV_round_correct t _ y Hyne (FINtl xh xl y FIN)).
  by rewrite Htl_r Hv0 !round_0 Rminus_diag Rabs_R0. }
rewrite Hpert Rplus_0_r in Habs.
exact Habs.
Qed.

Section CondAccuracyDWDivFP_mixed.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (@common.emin t).
Notation u := (bpow radix2 (- fprec t)).

Variables (xh xl y : ftype t).

Hypothesis Hp4 : (4 <= fprec t)%Z.
Hypothesis COND : DWDivFP_internal_precond xh xl y.
Hypothesis FIN : is_finite_p (DWDivFP xh xl y).
Hypothesis Hquot : bpow radix2 (emin + fprec t - 1)
  <= Rabs (FT2R xh / FT2R y).

Theorem DWDivFP_error_mixed_acc :
  Rabs (FT2R (fst (DWDivFP xh xl y)) + FT2R (snd (DWDivFP xh xl y))
        - (FT2R xh + FT2R xl) / FT2R y)
    <= 3 * u ^ 2 * Rabs ((FT2R xh + FT2R xl) / FT2R y) + bpow radix2 emin.
Proof.
destruct (Rle_or_lt (bpow radix2 (emin + fprec t - 1))
            (Rabs (FT2R (BPLUS (BMINUS (BMINUS xh (BMULT (BDIV xh y) y))
                                       (Fast2Mult_err (BDIV xh y) y)) xl) / FT2R y)))
  as [Hdyn | Huf].
-
  move: (COND) => [Hfxh [Hfxl [Hfy [Hdwp [Hfth Hxhlb]]]]].
  have Hyne := DWDivFP_denom_nonzero_from_finite xh y Hfy Hfth.
  have Hxhne : FT2R xh <> 0.
  { intro Hx0. move: Hquot; rewrite Hx0 /Rdiv Rmult_0_l Rabs_R0 => Hc.
    have := bpow_gt_0 radix2 (emin + fprec t - 1). lra. }
  have Hsne : FT2R xh + FT2R xl <> 0.
  { intro Hs0. apply Hxhne. move: Hdwp; rewrite /double_word_prop Hs0.
    rewrite /rounded round_0 //. }
  have HDne : (FT2R xh + FT2R xl) / FT2R y <> 0.
  { apply Rmult_integral_contrapositive_currified;
      [ exact Hsne | apply Rinv_neq_0_compat; exact Hyne ]. }
  pose proof (DWDivFP_relative_accuracy_normal_quotient
    xh xl y Hp4 COND FIN Hquot Hdyn) as Hrel.
  unfold relative_error_DWDivFP in Hrel.
  set (E := FT2R (fst (DWDivFP xh xl y)) + FT2R (snd (DWDivFP xh xl y))
            - (FT2R xh + FT2R xl) / FT2R y) in *.
  set (D := (FT2R xh + FT2R xl) / FT2R y) in *.
  have Habs : Rabs E = Rabs (E / D) * Rabs D
    by (rewrite -Rabs_mult; f_equal; field; exact HDne).
  rewrite Habs.
  eapply Rle_trans; [ apply Rmult_le_compat_r; [ apply Rabs_pos | exact Hrel ] | ].
  have Hb := bpow_ge_0 radix2 emin. lra.
-
  eapply Rle_trans;
    [ exact (DWDivFP_error_underflow_perturbation
        xh xl y Hp4 COND FIN Hquot Huf) |].
  apply Rplus_le_compat_l.
  exact (DWDivFP_tl_perturbation_le_eta xh xl y Hp4 COND FIN).
Qed.

End CondAccuracyDWDivFP_mixed.

Section RelativeAccuracyDWDivFP.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Notation emin := (@common.emin t).
Notation u := (bpow radix2 (- fprec t)).

Variables (xh xl y : ftype t).

Hypothesis Hp4 : (4 <= fprec t)%Z.

Theorem DWDivFP_relative_accuracy_from_weak_pre_and_finite_post_cond :
  DWDivFP_weak_pre_and_finite_post_cond xh xl y ->
  DWDivFP_relative_regime_cond xh xl y ->
  relative_error_DWDivFP xh xl y <= 3 * u ^ 2.
Proof.
move => CHECKED [Hquot Hcorr].
have Hxhne : FT2R xh <> 0.
{ intro Hxh0. move: Hquot. rewrite Hxh0 /Rdiv Rmult_0_l Rabs_R0.
  intros Hbad. exact (Rlt_not_le _ _
    (bpow_gt_0 radix2 (emin + fprec t - 1)) Hbad). }
have INTERNAL :=
  DWDivFP_internal_precond_of_weak_pre_and_finite_post_cond
    xh xl y CHECKED Hxhne.
have FIN : is_finite_p (DWDivFP xh xl y) := proj2 CHECKED.
specialize (FIN STD).
destruct Hcorr as [Hd0 | Hdyn]; last first.
- exact (DWDivFP_relative_accuracy_normal_quotient
    xh xl y Hp4 INTERNAL FIN Hquot Hdyn).
-

  move: (INTERNAL) => [Hfxh [Hfxl [Hfy [Hdwp [Hfth Hxhlb]]]]].
  have Hyne := DWDivFP_denom_nonzero_from_finite xh y Hfy Hfth.
  have Hsne : FT2R xh + FT2R xl <> 0.
  { intro Hs0. apply Hxhne. move: Hdwp; rewrite /double_word_prop Hs0.
    rewrite /rounded round_0 //. }
  have HDne : (FT2R xh + FT2R xl) / FT2R y <> 0.
  { apply Rmult_integral_contrapositive_currified;
      [ exact Hsne | apply Rinv_neq_0_compat; exact Hyne ]. }
  have HQpos : 0 < Rabs ((FT2R xh + FT2R xl) / FT2R y)
    by (apply Rabs_pos_lt; exact HDne).
  have Habs := DWDivFP_error_exact_division
    xh xl y Hp4 INTERNAL FIN Hquot Hd0.
  unfold relative_error_DWDivFP.
  set (E := FT2R (fst (DWDivFP xh xl y)) + FT2R (snd (DWDivFP xh xl y))
            - (FT2R xh + FT2R xl) / FT2R y) in *.
  set (D := (FT2R xh + FT2R xl) / FT2R y) in *.
  rewrite /Rdiv Rabs_mult Rabs_inv.
  apply (Rmult_le_reg_r (Rabs D)); [ exact HQpos |].
  rewrite Rmult_assoc Rinv_l; [ rewrite Rmult_1_r; exact Habs |].
  apply Rgt_not_eq; exact HQpos.
Qed.

Hypothesis COND : DWDivFP_relative_precond xh xl y.

Theorem DWDivFP_relative_accuracy :
  relative_error_DWDivFP xh xl y <= 3 * u ^ 2.
Proof.
move: (COND) => [SAFE REGIME].
move: (REGIME) => [Hquot Hcorr].
have Hxhne : FT2R xh <> 0.
{ intro Hxh0. move: Hquot. rewrite Hxh0 /Rdiv Rmult_0_l Rabs_R0.
  intros Hbad. exact (Rlt_not_le _ _
    (bpow_gt_0 radix2 (emin + fprec t - 1)) Hbad). }
have CONDn : DWDivFP_relative_normal_quotient_precond xh xl y.
{ move: (SAFE) => [Hfxh [Hfxl [Hfy [Hdwp [_ [Hxhb [Hqub Hxhlb]]]]]]].
  destruct Hxhlb as [Hxh0 | Hxhlb]; [contradiction |].
  repeat split; assumption. }
have FIN : is_finite_p (DWDivFP xh xl y).
{ split;
    [ exact (DWDivFP_fst_finite_acc xh xl y Hp4 CONDn)
    | exact (DWDivFP_snd_finite_acc xh xl y Hp4 CONDn) ]. }
have CHECKED : DWDivFP_weak_pre_and_finite_post_cond xh xl y.
{ move: (SAFE) => [Hfxh [Hfxl [Hfy [Hdwp [Hfth [Hxhb [Hqub Hxhlb]]]]]]].
  unfold DWDivFP_weak_pre_and_finite_post_cond, DWDivFP_weak_precond,
         DWDivFP_finite_post_cond.
  exact (conj (conj Hdwp Hxhlb) FIN). }
exact (DWDivFP_relative_accuracy_from_weak_pre_and_finite_post_cond
  CHECKED (conj Hquot Hcorr)).
Qed.

End RelativeAccuracyDWDivFP.
