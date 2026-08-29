(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Whole range mixed error and output validity results for [DWTimesDW].

    This file imports the common runtime model facts and normal range relative
    result from [DWMulDW_relative_acc], then handles the leading product
    underflow gap and exposes the mixed guarantee ladder. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common FLT_helpers.
Require Import DWTimesDW DDConds DWord_defs Fast2Mult_acc TwoSum_acc Fast2Sum_acc.
Require Import DWPlusFP_relative_acc_helpers DW_acc_lemmas.
Require Import DWMulFP_relative_acc DWMulDW_relative_acc.
From Flocq Require Import Pff2Flocq Core Mult_error.
From Stdlib Require Import Reals.Reals.
Require Import mathcomp.ssreflect.ssreflect.

Set Bullet Behavior "Strict Subproofs".

Section FarLow0Apparatus.
Context {NANS: Nans} {t : type} {STD: is_standard t}.
Notation u      := (bpow Zaux.radix2 (- fprec t)).
Notation eminA  := (SpecFloat.emin (fprec t) (femax t)).
(* The explicit FLX rounding chain of the low order DW*DW nodes with a floor
   term f at the low by low node.  This is notation (pure syntax), not a
   synthetic algorithm Definition; it expands to the real nodes' FLX rounds. *)
Local Notation FLXlow0 axh axl ayh ayl f :=
  (F2Sum.Fast2Sum (fprec t) choice
    (round radix2 (FLX_exp (fprec t)) (Znearest choice) (axh*ayh))
    (round radix2 (FLX_exp (fprec t)) (Znearest choice)
      ((axh*ayh - round radix2 (FLX_exp (fprec t)) (Znearest choice) (axh*ayh))
       + round radix2 (FLX_exp (fprec t)) (Znearest choice)
           (axl*ayh
            + round radix2 (FLX_exp (fprec t)) (Znearest choice)
                ((axh*ayl + axl*ayl) + f))))).

(* Hard arm for the explicit FLX low node chain. *)
Local Lemma flx_dwtimesdw_hard
    (axh axl ayh ayl f : R) :
  (5 <= fprec t)%Z ->
  DWPlus.double_word (fprec t) choice axh axl ->
  DWPlus.double_word (fprec t) choice ayh ayl ->
  1 <= axh <= 2-2*u -> 1 <= ayh <= 2-2*u ->
  axh*ayh <= 2 ->
  Rabs f <= 8/9*u^2*(axh*ayh) ->
  let '(rzh,rzl) := F2Sum.Fast2Sum (fprec t) choice
    (round radix2 (FLX_exp (fprec t)) (Znearest choice) (axh*ayh))
    (round radix2 (FLX_exp (fprec t)) (Znearest choice)
      ((axh*ayh - round radix2 (FLX_exp (fprec t)) (Znearest choice) (axh*ayh))
       + round radix2 (FLX_exp (fprec t)) (Znearest choice)
           (axl*ayh
            + round radix2 (FLX_exp (fprec t)) (Znearest choice)
                ((axh*ayl + axl*ayl) + f)))) in
  Rabs ((rzh+rzl)-(axh+axl)*(ayh+ayl)-f) <=
    4*u^2*Rabs ((axh+axl)*(ayh+ayl))+3*Rabs f.
Proof.
move => Hp5 DWx DWy Hxh Hyh HP Hf.
have Hp1 : (1 < fprec t)%Z by lia.
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu1 : u < 1 by (unfold u;apply Bayleyaux.bpow_lt_1;lia).
have Hu : u <= /32.
{ unfold u. have -> : (/32:R)=bpow radix2 (-5) by (simpl;lra).
  apply bpow_le;lia. }
have Hxlu : Rabs axl <= u.
{ exact (@DWTimesDW.double_lpart_u (fprec t) Hp1 choice axh axl
    DWx ltac:(lra)). }
have Hylu : Rabs ayl <= u.
{ exact (@DWTimesDW.double_lpart_u (fprec t) Hp1 choice ayh ayl
    DWy ltac:(lra)). }
set rp := round radix2 (FLX_exp (fprec t)) (Znearest choice).
set ch := rp (axh*ayh).
set cl1 := axh*ayh-ch.
set base1 := axh*ayl+axl*ayl.
set tl1 := rp (base1+f).
(* reconcile the goal's cl2 argument (def form axl*ayh+tl1) with the
   analysis form cross+f+(tl1-(base1+f)) *)
have Ecl2arg : axl*ayh + tl1 = (axh*ayl+ayh*axl+axl*ayl)+f+(tl1-(base1+f)).
{ unfold base1. ring. }
rewrite Ecl2arg.
set cross := axh*ayl+ayh*axl+axl*ayl.
set cl2 := rp (cross+f+(tl1-(base1+f))).
set cl3 := rp (cl1+cl2).
have Hxhyl : Rabs (axh*ayl) <= 2*u-2*u^2.
{ rewrite Rabs_mult Rabs_pos_eq; [|lra].
  replace (2*u-2*u^2)%R with ((2-2*u)*u)%R by ring.
  apply Rmult_le_compat; try apply Rabs_pos; lra. }
have Hlow : Rabs (axl*ayl) <= u^2.
{ rewrite Rabs_mult. replace (u^2)%R with (u*u)%R by ring.
  apply Rmult_le_compat; try apply Rabs_pos; assumption. }
have Hbase1 : Rabs base1 <= 2*u-u^2.
{ unfold base1. eapply Rle_trans; [apply Rabs_triang|]. nra. }
have Htl1 := low0_tl1_sharp
  (axh*ayh) f base1 Hp5 ltac:(nra) HP Hf Hbase1.
destruct Htl1 as [Htl1 He1].
change (Rabs tl1 <= 2*u) in Htl1.
change (Rabs (tl1-(base1+f)) <= u^2) in He1.
have Hsumxy : axh+ayh <= 3-2*u.
{ apply (@DWTimesDW.l5_2F (fprec t) Hp1 axh ayh).
  - exact (proj1 (proj1 DWx)).
  - exact (proj1 (proj1 DWy)).
  - split; lra.
  - split; lra.
  - exact HP. }
have Hcross0 : Rabs (axh*ayl+ayh*axl) <= 3*u-2*u^2.
{ eapply Rle_trans; [apply Rabs_triang|].
  rewrite !Rabs_mult.
  rewrite (Rabs_pos_eq axh); [|lra].
  rewrite (Rabs_pos_eq ayh); [|lra].
  have H1 := Rmult_le_compat_l axh _ _ ltac:(lra) Hylu.
  have H2 := Rmult_le_compat_l ayh _ _ ltac:(lra) Hxlu.
  nra. }
have Hcross : Rabs cross <= 3*u-u^2.
{ unfold cross. replace (axh*ayl+ayh*axl+axl*ayl)%R with
    ((axh*ayl+ayh*axl)+(axl*ayl))%R by ring.
  eapply Rle_trans; [apply Rabs_triang|]. nra. }
have Hcl2 := low0_cl2_sharp
  (axh*ayh) f (tl1-(base1+f)) cross Hp5 ltac:(nra) HP
  Hf He1 Hcross.
destruct Hcl2 as [Hcl2 He2].
change (Rabs cl2 <= 3*u) in Hcl2.
change (Rabs (cl2-(cross+f+(tl1-(base1+f)))) <= 2*u^2) in He2.
have Hcl1 : Rabs cl1 <= u.
{ unfold cl1,ch,rp.
  replace (axh*ayh-
    round radix2 (FLX_exp (fprec t)) (Znearest choice) (axh*ayh))%R with
    (-(round radix2 (FLX_exp (fprec t)) (Znearest choice) (axh*ayh)-
       axh*ayh))%R by ring.
  rewrite Rabs_Ropp.
  replace u with (/2*u*bpow radix2 1)%R.
  2:{ simpl. nra. }
  apply (@Bayleyaux.error_le_half_ulp' (fprec t) Hp1 choice
    (axh*ayh) 1%Z).
  rewrite Rabs_pos_eq; [change (axh*ayh<=2);exact HP|nra]. }
have Fcl1 : generic_format radix2 (FLX_exp (fprec t)) cl1.
{ have Hneg : generic_format radix2 (FLX_exp (fprec t)) (-cl1).
  {
  replace (-cl1)%R with
    (rp (axh*ayh)-axh*ayh)%R by (unfold cl1,ch;ring).
  unfold rp. apply Mult_error.mult_error_FLX;
    [exact (fprec_gt_0 t)|apply valid_rnd_N|
     exact (proj1 (proj1 DWx))|exact (proj1 (proj1 DWy))]. }
  have Hopp := generic_format_opp radix2 (FLX_exp (fprec t)) (-cl1) Hneg.
  rewrite Ropp_involutive in Hopp. exact Hopp. }
have Hcl3 := low0_cl3_sharp cl1 cl2 Hp5 Hcl1 Hcl2.
destruct Hcl3 as [Hcl3 He3].
change (Rabs cl3 <= 4*u) in Hcl3.
change (Rabs (cl3-(cl1+cl2)) <= 2*u^2) in He3.
have Hchge : 1 <= Rabs ch.
{ unfold ch,rp.
  rewrite -(round_generic radix2 (FLX_exp (fprec t))
    (Znearest choice) 1).
  2:{ change (generic_format radix2 (FLX_exp (fprec t))
        (bpow radix2 0)); apply generic_format_bpow;unfold FLX_exp;lia. }
  rewrite -(@Bayleyaux.rnd_p_abs (fprec t) Hp1 choice choiceP (axh*ayh)).
  apply round_le; [apply FLX_exp_valid, fprec_gt_0|apply valid_rnd_N|].
  rewrite Rabs_pos_eq; nra. }
have H4u : 4*u <= 1.
{ have H := bpow_le radix2 (-fprec t) (-2) ltac:(lia).
  change (u <= /4) in H. nra. }
have Hord : Rabs cl3 <= Rabs ch.
{ lra. }
have Fch : generic_format radix2 (FLX_exp (fprec t)) ch.
{ unfold ch,rp. apply generic_format_round;
    [apply FLX_exp_valid, fprec_gt_0|apply valid_rnd_N]. }
have Fcl3 : generic_format radix2 (FLX_exp (fprec t)) cl3.
{ unfold cl3,rp. apply generic_format_round;
    [apply FLX_exp_valid, fprec_gt_0|apply valid_rnd_N]. }
have Hrsym : forall z,
  round radix2 (FLX_exp (fprec t)) (Znearest choice) (-z) =
  -round radix2 (FLX_exp (fprec t)) (Znearest choice) z.
{ exact (@rnd_p_sym (fprec t) choice choiceP). }
have Hrad : (radix_val radix2 <= 3)%Z by (change (2<=3)%Z;lia).
have Hfast := @F2Sum.F2Sum_correct_abs (fprec t) Hp1 choice
  Hrsym Hrad ch cl3 Fch Fcl3 Hord.
unfold F2Sum.Fast2Sum_correct in Hfast.
case Efast: (F2Sum.Fast2Sum (fprec t) choice ch cl3) => [rzh rzl].
rewrite Efast /= in Hfast.
have Hsum : rzh+rzl=ch+cl3 by lra.
have Herrid :
  rzh+rzl-(axh+axl)*(ayh+ayl)-f =
    (tl1-(base1+f))+(cl2-(cross+f+(tl1-(base1+f))))+
      (cl3-(cl1+cl2)).
{ rewrite Hsum. unfold cl1,base1,cross. ring. }
have Fcl2 : generic_format radix2 (FLX_exp (fprec t)) cl2.
{ unfold cl2,rp. apply generic_format_round;
    [apply FLX_exp_valid,fprec_gt_0|apply valid_rnd_N]. }
have Hxlb := Hxlu. move/Rabs_le_inv: Hxlb => [Hxl Hxlu'].
have Hylb := Hylu. move/Rabs_le_inv: Hylb => [Hyl Hylu'].
have Hxp : 0 < axh+axl by nra.
have Hyp : 0 < ayh+ayl by nra.
have Hxyabs : Rabs ((axh+axl)*(ayh+ayl))=
    (axh+axl)*(ayh+ayl).
{ rewrite Rabs_mult !Rabs_pos_eq; lra. }
have Hxylo : (1-u)^2 <= Rabs ((axh+axl)*(ayh+ayl)).
{ rewrite Hxyabs.
  have H1 : 1-u <= axh+axl by lra.
  have H2 : 1-u <= ayh+ayl by lra.
  replace ((1-u)^2)%R with ((1-u)*(1-u))%R by ring.
  apply Rmult_le_compat; nra. }
have He3zero_eq : axh=1 \/ ayh=1 -> cl3-(cl1+cl2)=0.
{ move => [Hxeq|Hyeq].
  - have Hcl10 : cl1=0.
    { unfold cl1,ch,rp. rewrite Hxeq Rmult_1_l.
      rewrite round_generic; [ring|exact (proj1 (proj1 DWy))]. }
    unfold cl3,rp. rewrite Hcl10 Rplus_0_l.
    rewrite round_generic; [ring|exact Fcl2].
  - have Hcl10 : cl1=0.
    { unfold cl1,ch,rp. rewrite Hyeq Rmult_1_r.
      rewrite round_generic; [ring|exact (proj1 (proj1 DWx))]. }
    unfold cl3,rp. rewrite Hcl10 Rplus_0_l.
    rewrite round_generic; [ring|exact Fcl2]. }
have Hnext (a : R) :
    generic_format radix2 (FLX_exp (fprec t)) a ->
    1 <= a -> a<>1 -> 1+2*u <= a.
{ move => Fa Ha Hane.
  have Hlt : 1<a by lra.
  have Hsucc : succ radix2 (FLX_exp (fprec t)) 1 <= a.
  { apply succ_le_lt; try assumption.
    - apply FLX_exp_valid. exact (fprec_gt_0 t).
    - change (generic_format radix2 (FLX_exp (fprec t))
        (bpow radix2 0)).
      apply generic_format_bpow. unfold FLX_exp. lia. }
  rewrite succ_eq_pos in Hsucc; [|lra].
  have Hulp : Ulp.ulp radix2 (FLX_exp (fprec t)) 1=2*u.
  { rewrite ulp_neq_0; [|lra].
    unfold cexp, FLX_exp. rewrite mag_1.
    change (bpow radix2 (1-fprec t)=2*bpow radix2 (-fprec t)).
    rewrite bpow_plus. reflexivity. }
  rewrite Hulp in Hsucc. exact Hsucc. }
rewrite Herrid.
have Hfinish3 : Rabs ((tl1-(base1+f))+
    (cl2-(cross+f+(tl1-(base1+f))))+(cl3-(cl1+cl2))) <= 3*u^2 ->
    Rabs ((tl1-(base1+f))+
      (cl2-(cross+f+(tl1-(base1+f))))+(cl3-(cl1+cl2))) <=
      4*u^2*Rabs ((axh+axl)*(ayh+ayl))+3*Rabs f.
{ move => Herr3.
  have Hc : 3 <= 4*((1-u)^2) by nra.
  have Hcoef0 := Rmult_le_compat_r (u^2) _ _ (pow2_ge_0 u) Hc.
  have Hcoef : 3*u^2 <= 4*u^2*((1-u)^2).
  { eapply Rle_trans;[exact Hcoef0|]. apply Req_le. ring. }
  have Hscale := Rmult_le_compat_l (4*u^2) _ _ ltac:(nra) Hxylo.
  eapply Rle_trans;[exact Herr3|].
  eapply Rle_trans;[exact Hcoef|].
  eapply Rle_trans;[exact Hscale|].
  have Hf0 := Rabs_pos f. nra. }
have Hfinish4 : axh<>1 -> ayh<>1 ->
    Rabs ((tl1-(base1+f))+
      (cl2-(cross+f+(tl1-(base1+f))))+(cl3-(cl1+cl2))) <= 4*u^2 ->
    Rabs ((tl1-(base1+f))+
      (cl2-(cross+f+(tl1-(base1+f))))+(cl3-(cl1+cl2))) <=
      4*u^2*Rabs ((axh+axl)*(ayh+ayl))+3*Rabs f.
{ move => Hxne Hyne Herr4.
  have Hxn := Hnext axh (proj1 (proj1 DWx)) (proj1 Hxh) Hxne.
  have Hyn := Hnext ayh (proj1 (proj1 DWy)) (proj1 Hyh) Hyne.
  have Hxy1 : 1 <= Rabs ((axh+axl)*(ayh+ayl)).
  { rewrite Hxyabs.
    have Hsx : 1+u <= axh+axl by lra.
    have Hsy : 1+u <= ayh+ayl by lra.
    have Hmul : (1+u)*(1+u) <= (axh+axl)*(ayh+ayl).
    { apply Rmult_le_compat; [nra|nra|exact Hsx|exact Hsy]. }
    eapply Rle_trans;[|exact Hmul]. nra. }
  have Hscale := Rmult_le_compat_l (4*u^2) _ _ ltac:(nra) Hxy1.
  replace (4*u^2*1)%R with (4*u^2)%R in Hscale by ring.
  eapply Rle_trans;[exact Herr4|].
  eapply Rle_trans;[exact Hscale|].
  have Hf0 := Rabs_pos f. nra. }
have Hpow2 : 2*u=bpow radix2 (1-fprec t).
{ change (2*bpow radix2 (-fprec t)=bpow radix2 (1-fprec t)).
  rewrite bpow_plus /= IZR_Zpower_pos /=.
  have -> : IZR (Z.pow_pos 2 1)=2 by reflexivity. ring. }
destruct (Rlt_dec (Rabs cl2) (2*u)) as [Hcl2small|Hcl2large].
- have Harg2 : Rabs (cross+f+(tl1-(base1+f))) < 2*u.
  { destruct (Rle_dec (2*u)
      (Rabs (cross+f+(tl1-(base1+f))))) as [Hge|Hlt]; [|lra].
    have Hmono :
      round radix2 (FLX_exp (fprec t)) (Znearest choice) (2*u) <=
      round radix2 (FLX_exp (fprec t)) (Znearest choice)
        (Rabs (cross+f+(tl1-(base1+f)))).
    { apply round_le;
        [apply FLX_exp_valid,fprec_gt_0|apply valid_rnd_N|exact Hge]. }
    have F2u : generic_format radix2 (FLX_exp (fprec t)) (2*u).
    { rewrite Hpow2. apply generic_format_bpow. unfold FLX_exp. lia. }
    rewrite (round_generic radix2 (FLX_exp (fprec t))
      (Znearest choice) (2*u) F2u) in Hmono.
    rewrite (@Bayleyaux.rnd_p_abs (fprec t) Hp1 choice choiceP
      (cross+f+(tl1-(base1+f)))) in Hmono.
    fold rp cl2 in Hmono. lra. }
  have He2small := @Bayleyaux.error_le_half_ulp' (fprec t) Hp1 choice
    (cross+f+(tl1-(base1+f))) (1-fprec t)%Z.
  specialize (He2small ltac:(rewrite -Hpow2;apply Rlt_le;exact Harg2)).
  have He2small' :
    Rabs (cl2-(cross+f+(tl1-(base1+f)))) <= u^2.
  { change (Rabs (cl2-(cross+f+(tl1-(base1+f)))) <=
      /2*u*bpow radix2 (1-fprec t)) in He2small.
    eapply Rle_trans; [exact He2small|].
    rewrite -Hpow2. nra. }
  have Htri1 := Rabs_triang
    ((tl1-(base1+f))+(cl2-(cross+f+(tl1-(base1+f)))))
    (cl3-(cl1+cl2)).
  have Htri0 := Rabs_triang (tl1-(base1+f))
    (cl2-(cross+f+(tl1-(base1+f)))).
  destruct (Req_dec axh 1) as [Hxeq|Hxne].
  + apply Hfinish3.
    have He3z := He3zero_eq (or_introl Hxeq). rewrite He3z Rplus_0_r.
    eapply Rle_trans;[exact Htri0|]. nra.
  + destruct (Req_dec ayh 1) as [Hyeq|Hyne].
    * apply Hfinish3.
      have He3z := He3zero_eq (or_intror Hyeq). rewrite He3z Rplus_0_r.
      eapply Rle_trans;[exact Htri0|]. nra.
    * apply (Hfinish4 Hxne Hyne).
      eapply Rle_trans; [exact Htri1|].
      eapply Rle_trans; [apply Rplus_le_compat_r;exact Htri0|].
      eapply Rle_trans.
      { apply Rplus_le_compat.
        - apply Rplus_le_compat; [exact He1|exact He2small'].
        - exact He3. }
      nra.
- have Hcl2ge : 2*u <= Rabs cl2 by lra.
  have Hcl2pow : bpow radix2 (1-fprec t) <= Rabs cl2.
  { rewrite -Hpow2. exact Hcl2ge. }
  destruct (@DWTimesFP.ex_mul (fprec t) cl2 (1-fprec t)%Z
    Hcl2pow Fcl2) as [mcl2 Hmcl2].
  have Fx : generic_format radix2 (FLX_exp (fprec t)) axh
    by exact (proj1 (proj1 DWx)).
  have Fy : generic_format radix2 (FLX_exp (fprec t)) ayh
    by exact (proj1 (proj1 DWy)).
  have Hx1 : bpow radix2 0 <= Rabs axh.
  { change (1<=Rabs axh). rewrite Rabs_pos_eq; lra. }
  have Hy1 : bpow radix2 0 <= Rabs ayh.
  { change (1<=Rabs ayh). rewrite Rabs_pos_eq; lra. }
  destruct (@DWTimesFP.ex_mul (fprec t) axh 0%Z Hx1 Fx)
    as [mx Hmx].
  destruct (@DWTimesFP.ex_mul (fprec t) ayh 0%Z Hy1 Fy)
    as [my Hmy].
  have Hprodgrid : axh*ayh=IZR (mx*my)*(4*u^2).
  { change (bpow radix2 0) with 1 in Hmx.
    change (bpow radix2 0) with 1 in Hmy.
    rewrite Hmx Hmy !Rmult_1_r mult_IZR. ring. }
  have Hch1 : bpow radix2 0 <= Rabs ch by exact Hchge.
  destruct (@DWTimesFP.ex_mul (fprec t) ch 0%Z Hch1 Fch)
    as [mch Hmch].
  have Hchgrid : ch=IZR (mch*2^(fprec t-1))*(4*u^2).
  { rewrite Hmch.
    have HE : 2*u=4*u^2*bpow radix2 (fprec t-1).
    { change (2*bpow radix2 (-fprec t) =
        4*bpow radix2 (-fprec t)^2*bpow radix2 (fprec t-1)).
      replace 2 with (bpow radix2 1) by reflexivity.
      replace 4 with (bpow radix2 2) by reflexivity.
      replace (bpow radix2 (-fprec t)^2) with
        (bpow radix2 (-fprec t)*bpow radix2 (-fprec t)) by ring.
      rewrite -!bpow_plus. f_equal. ring. }
    rewrite HE mult_IZR.
    rewrite (IZR_Zpower radix2); [|lia].
    change (bpow radix2 0) with 1. ring. }
  set mcl1 := (mx*my-mch*2^(fprec t-1))%Z.
  have Hgrid2 : cl2=IZR mcl2*(4*u^2).
  { rewrite Hmcl2 -Hpow2. ring. }
  have Hgrid1 : cl1=IZR mcl1*(4*u^2).
  { unfold cl1,mcl1. rewrite Hprodgrid Hchgrid -Rmult_minus_distr_r.
    rewrite minus_IZR. reflexivity. }
  set mg := (mcl1+mcl2)%Z.
  have Hgrid : cl1+cl2=IZR mg*(4*u^2).
  { rewrite Hgrid1 Hgrid2 /mg plus_IZR. ring. }
  have Harg3 : Rabs (cl1+cl2) <= 4*u.
  { eapply Rle_trans; [apply Rabs_triang|]. nra. }
  have Hmg : Rabs (IZR mg) <= bpow radix2 (fprec t).
  { have Hg := Harg3.
    rewrite Hgrid Rabs_mult in Hg.
    have Hpos : Rabs (4*u^2)=4*u^2.
    { rewrite Rabs_pos_eq; [reflexivity|]. clear -Hu0; nra. }
    rewrite Hpos in Hg.
    have H4u2pos : 0<4*u^2 by (clear -Hu0;nra).
    apply (Rmult_le_reg_r (4*u^2)); [exact H4u2pos|].
    eapply Rle_trans; [exact Hg|].
    apply Req_le.
    change (4*bpow radix2 (-fprec t) =
      bpow radix2 (fprec t)*(4*bpow radix2 (-fprec t)^2)).
    replace 4 with (bpow radix2 2) by reflexivity.
    replace (bpow radix2 (-fprec t)^2) with
      (bpow radix2 (-fprec t)*bpow radix2 (-fprec t)) by ring.
    rewrite -!bpow_plus. f_equal. ring. }
  have Hunit : 4*u^2=bpow radix2 (2-2*fprec t).
  { change (4*bpow radix2 (-fprec t)^2 =
      bpow radix2 (2-2*fprec t)).
    replace 4 with (bpow radix2 2) by reflexivity.
    replace (bpow radix2 (-fprec t)^2) with
      (bpow radix2 (-fprec t)*bpow radix2 (-fprec t)) by ring.
    rewrite -!bpow_plus. f_equal. ring. }
  have Fsum : generic_format radix2 (FLX_exp (fprec t)) (cl1+cl2).
  { rewrite Hgrid.
    destruct Hmg as [Hmg|Hmg].
    - replace (IZR mg*(4*u^2))%R with
        (F2R (Float radix2 mg (2-2*fprec t))) by
        (rewrite Hunit /F2R /=;ring).
      apply (@DWPlus.FLX_format_Rabs_Fnum (fprec t)
        (F2R (Float radix2 mg (2-2*fprec t)))
        (Float radix2 mg (2-2*fprec t)));
        [reflexivity|exact Hmg].
    - have Hpoweq : Rabs (IZR mg)=bpow radix2 (fprec t) by lra.
      have Hbp : Rabs (bpow radix2 (fprec t))=
          bpow radix2 (fprec t) by
          (rewrite Rabs_pos_eq; [reflexivity|apply bpow_ge_0]).
      rewrite -Hbp in Hpoweq.
      destruct (Rabs_eq_Rabs _ _ Hpoweq) as [Hm|Hm]; rewrite Hm.
      + replace (bpow radix2 (fprec t)*(4*u^2))%R with
          (bpow radix2 (2-fprec t)) by
          (rewrite Hunit -bpow_plus;f_equal;ring).
        apply generic_format_bpow. unfold FLX_exp. lia.
      + rewrite Ropp_mult_distr_l_reverse.
        apply generic_format_opp.
        replace (bpow radix2 (fprec t)*(4*u^2))%R with
          (bpow radix2 (2-fprec t)) by
          (rewrite Hunit -bpow_plus;f_equal;ring).
        apply generic_format_bpow. unfold FLX_exp. lia. }
  have He3zero : cl3-(cl1+cl2)=0.
  { unfold cl3,rp. rewrite round_generic; [ring|exact Fsum]. }
  apply Hfinish3. rewrite He3zero Rplus_0_r.
  eapply Rle_trans; [apply Rabs_triang|].
  eapply Rle_trans; [apply Rplus_le_compat; [exact He1|exact He2]|].
  nra.
Qed.

Local Lemma flx_dwtimesdw_easy
    (axh axl ayh ayl f : R) :
  (5 <= fprec t)%Z ->
  DWPlus.double_word (fprec t) choice axh axl ->
  DWPlus.double_word (fprec t) choice ayh ayl ->
  1 <= axh <= 2-2*u -> 1 <= ayh <= 2-2*u ->
  2 < axh*ayh ->
  Rabs f <= 8/9*u^2*(axh*ayh) ->
  let '(rzh,rzl) := F2Sum.Fast2Sum (fprec t) choice
    (round radix2 (FLX_exp (fprec t)) (Znearest choice) (axh*ayh))
    (round radix2 (FLX_exp (fprec t)) (Znearest choice)
      ((axh*ayh - round radix2 (FLX_exp (fprec t)) (Znearest choice) (axh*ayh))
       + round radix2 (FLX_exp (fprec t)) (Znearest choice)
           (axl*ayh
            + round radix2 (FLX_exp (fprec t)) (Znearest choice)
                ((axh*ayl + axl*ayl) + f)))) in
  Rabs ((rzh+rzl)-(axh+axl)*(ayh+ayl)-f) <=
    4*u^2*Rabs ((axh+axl)*(ayh+ayl))+3*Rabs f.
Proof.
move => Hp5 DWx DWy Hxh Hyh HP Hf.
have Hp1 : (1 < fprec t)%Z by lia.
have Hu0 : 0 < u by apply bpow_gt_0.
have Hu : u <= /32.
{ unfold u. have -> : (/32:R)=bpow radix2 (-5) by (simpl;lra).
  apply bpow_le;lia. }
have Hxlu : Rabs axl <= u.
{ exact (@DWTimesDW.double_lpart_u (fprec t) Hp1 choice axh axl
    DWx ltac:(lra)). }
have Hylu : Rabs ayl <= u.
{ exact (@DWTimesDW.double_lpart_u (fprec t) Hp1 choice ayh ayl
    DWy ltac:(lra)). }
set rp := round radix2 (FLX_exp (fprec t)) (Znearest choice).
set ch := rp (axh*ayh).
set cl1 := axh*ayh-ch.
set base1 := axh*ayl+axl*ayl.
set tl1 := rp (base1+f).
set cross := axh*ayl+ayh*axl+axl*ayl.
set e1 := tl1-(base1+f).
have Ecl2arg : axl*ayh + tl1 = cross+f+e1.
{ unfold cross,e1,base1. ring. }
rewrite Ecl2arg.
set cl2 := rp (cross+f+e1).
set e2 := cl2-(cross+f+e1).
set cl3 := rp (cl1+cl2).
set e3 := cl3-(cl1+cl2).
have HP4 : axh*ayh < 4 by nra.
have Hlow : Rabs (axl*ayl) <= u^2.
{ rewrite Rabs_mult. replace (u^2)%R with (u*u)%R by ring.
  apply Rmult_le_compat; try apply Rabs_pos; assumption. }
have Hxhyl : Rabs (axh*ayl) <= 2*u-2*u^2.
{ rewrite Rabs_mult Rabs_pos_eq; [|lra].
  replace (2*u-2*u^2)%R with ((2-2*u)*u)%R by ring.
  apply Rmult_le_compat; try apply Rabs_pos; lra. }
have Hbase : Rabs base1 <= 2*u-u^2.
{ unfold base1. eapply Rle_trans; [apply Rabs_triang|]. nra. }
have Hf4 : Rabs f <= 32/9*u^2 by nra.
have Harg1 : Rabs (base1+f) <= 2*u+23/9*u^2.
{ eapply Rle_trans; [apply Rabs_triang|]. nra. }
have He1b : Rabs e1 <= 2*u^2.
{ unfold e1,tl1,rp. exact (round_error_le_2u2_below_four_u
    (base1+f) Hp5 ltac:(eapply Rle_trans;[exact Harg1|];nra)). }
have Hcross : Rabs cross <= 4*u-3*u^2.
{ unfold cross.
  have Htwo : Rabs (axh*ayl+ayh*axl) <= (axh+ayh)*u.
  { eapply Rle_trans; [apply Rabs_triang|].
    rewrite !Rabs_mult.
    have Hax : Rabs axh=axh by (apply Rabs_pos_eq;lra).
    have Hay : Rabs ayh=ayh by (apply Rabs_pos_eq;lra).
    rewrite Hax Hay.
    have H1 := Rmult_le_compat_l axh _ _ ltac:(lra) Hylu.
    have H2 := Rmult_le_compat_l ayh _ _ ltac:(lra) Hxlu. nra. }
  replace (axh*ayl+ayh*axl+axl*ayl)%R with
    ((axh*ayl+ayh*axl)+axl*ayl)%R by ring.
  eapply Rle_trans; [apply Rabs_triang|]. nra. }
have Harg2 : Rabs (cross+f+e1) <= 4*u+23/9*u^2.
{ have H0 := Rabs_triang (cross+f) e1.
  have H1 := Rabs_triang cross f.
  eapply Rle_trans; [exact H0|].
  eapply Rle_trans; [apply Rplus_le_compat_r;exact H1|]. nra. }
have Hcl2 : Rabs cl2 <= 4*u.
{ unfold cl2,rp. exact (round_abs_le_four_u_with_easy_margin
    (cross+f+e1) Hp5 Harg2). }
have He2b : Rabs e2 <= 3*u^2.
{ unfold e2,cl2,rp. exact (round_error_le_3u2_with_easy_margin
    (cross+f+e1) Hp5 Harg2). }
have Hcl1 : Rabs cl1 <= 2*u.
{ unfold cl1,ch,rp.
  replace (axh*ayh-round radix2 (FLX_exp (fprec t))
    (Znearest choice) (axh*ayh))%R with
    (-(round radix2 (FLX_exp (fprec t)) (Znearest choice)
      (axh*ayh)-axh*ayh))%R by ring.
  rewrite Rabs_Ropp.
  have H := @Bayleyaux.error_le_half_ulp' (fprec t) Hp1 choice
    (axh*ayh) 2%Z.
  specialize (H ltac:(rewrite Rabs_pos_eq;[apply Rlt_le;exact HP4|nra])).
  change (Rabs (round radix2 (FLX_exp (fprec t)) (Znearest choice)
    (axh*ayh)-axh*ayh) <= /2*u*bpow radix2 2) in H.
  replace (bpow radix2 2) with 4 in H by reflexivity. nra. }
have Harg3 : Rabs (cl1+cl2) <= 6*u.
{ eapply Rle_trans; [apply Rabs_triang|]. nra. }
have He3b : Rabs e3 <= 4*u^2.
{ unfold e3,cl3,rp.
  have H := @Bayleyaux.error_le_half_ulp' (fprec t) Hp1 choice
    (cl1+cl2) (3-fprec t)%Z.
  have Hb : Rabs (cl1+cl2) <= bpow radix2 (3-fprec t).
  { eapply Rle_trans; [exact Harg3|].
    change (6*bpow radix2 (-fprec t) <= bpow radix2 (3-fprec t)).
    rewrite bpow_plus. replace (bpow radix2 3) with 8 by reflexivity. nra. }
  specialize (H Hb).
  have HE : (/2*u*bpow radix2 (3-fprec t)=4*u^2)%R.
  { have H8 : bpow radix2 (3-fprec t)=8*u.
    { change (bpow radix2 (3-fprec t)=
        8*bpow radix2 (-fprec t)).
      replace (8*bpow radix2 (-fprec t))%R with
        (bpow radix2 3*bpow radix2 (-fprec t))%R by reflexivity.
      rewrite -bpow_plus. f_equal. }
    rewrite H8. replace (u^2)%R with (u*u)%R by ring. field. }
  rewrite HE in H. exact H. }
have Fcl1 : generic_format radix2 (FLX_exp (fprec t)) cl1.
{ have Hneg : generic_format radix2 (FLX_exp (fprec t)) (-cl1).
  { replace (-cl1)%R with (rp (axh*ayh)-axh*ayh)%R by
      (unfold cl1,ch;ring).
    unfold rp. apply Mult_error.mult_error_FLX;
      [exact (fprec_gt_0 t)|apply valid_rnd_N|
       exact (proj1 (proj1 DWx))|exact (proj1 (proj1 DWy))]. }
  have Hopp := generic_format_opp radix2 (FLX_exp (fprec t)) (-cl1) Hneg.
  rewrite Ropp_involutive in Hopp. exact Hopp. }
have Fch : generic_format radix2 (FLX_exp (fprec t)) ch.
{ unfold ch,rp. apply generic_format_round;
    [apply FLX_exp_valid,fprec_gt_0|apply valid_rnd_N]. }
have Fcl3 : generic_format radix2 (FLX_exp (fprec t)) cl3.
{ unfold cl3,rp. apply generic_format_round;
    [apply FLX_exp_valid,fprec_gt_0|apply valid_rnd_N]. }
have Hchge : 2 <= Rabs ch.
{ unfold ch,rp.
  rewrite -(round_generic radix2 (FLX_exp (fprec t))
    (Znearest choice) 2).
  2:{ change (generic_format radix2 (FLX_exp (fprec t))
      (bpow radix2 1));apply generic_format_bpow;unfold FLX_exp;lia. }
  rewrite -(@Bayleyaux.rnd_p_abs (fprec t) Hp1 choice choiceP
    (axh*ayh)).
  apply round_le;[apply FLX_exp_valid,fprec_gt_0|apply valid_rnd_N|].
  rewrite Rabs_pos_eq;nra. }
have H8u : bpow radix2 (3-fprec t)=8*u.
{ change (bpow radix2 (3-fprec t)=8*bpow radix2 (-fprec t)).
  replace (8*bpow radix2 (-fprec t))%R with
    (bpow radix2 3*bpow radix2 (-fprec t))%R by reflexivity.
  rewrite -bpow_plus. f_equal. }
have Hcl3 : Rabs cl3 <= 8*u.
{ unfold cl3,rp.
  rewrite -(@Bayleyaux.rnd_p_abs (fprec t) Hp1 choice choiceP (cl1+cl2)).
  rewrite -(round_generic radix2 (FLX_exp (fprec t))
    (Znearest choice) (8*u)).
  2:{ rewrite -H8u. apply generic_format_bpow. unfold FLX_exp. lia. }
  apply round_le;[apply FLX_exp_valid,fprec_gt_0|apply valid_rnd_N|].
  eapply Rle_trans;[exact Harg3|]. nra. }
have Hord : Rabs cl3 <= Rabs ch by nra.
have Hrsym : forall z, rp (-z) = -rp z.
{ move=>z;unfold rp;exact (@rnd_p_sym (fprec t) choice choiceP z). }
have Hfast := @F2Sum.F2Sum_correct_abs (fprec t) Hp1 choice
  Hrsym ltac:(change (2<=3)%Z;lia) ch cl3 Fch Fcl3 Hord.
unfold F2Sum.Fast2Sum_correct in Hfast.
case Efast: (F2Sum.Fast2Sum (fprec t) choice ch cl3) => [rzh rzl].
rewrite Efast /= in Hfast.
have Hsum : rzh+rzl=ch+cl3 by lra.
have Herrid : rzh+rzl-(axh+axl)*(ayh+ayl)-f=e1+e2+e3.
{ rewrite Hsum. unfold e2,e3,cl1,cross. ring. }
rewrite Herrid.
have Hxy : 2*(1-u)^2 < Rabs ((axh+axl)*(ayh+ayl)).
{ have Hxlb := Hxlu. move/Rabs_le_inv: Hxlb => [Hxl Hxlu'].
  have Hylb := Hylu. move/Rabs_le_inv: Hylb => [Hyl Hylu'].
  have Hxp : 0 <= axh+axl by nra.
  have Hyp : 0 <= ayh+ayl by nra.
  rewrite Rabs_mult (Rabs_pos_eq _ Hxp) (Rabs_pos_eq _ Hyp).
  have H1 : axh*(1-u) <= axh+axl by nra.
  have H2 : ayh*(1-u) <= ayh+ayl by nra.
  have Hm : (axh*(1-u))*(ayh*(1-u)) <=
      (axh+axl)*(ayh+ayl).
  { apply Rmult_le_compat; [nra|nra|exact H1|exact H2]. }
  have Hs : 0 < (1-u)^2 by nra.
  have Hstrict := Rmult_lt_compat_r ((1-u)^2) _ _ Hs HP.
  eapply Rlt_le_trans;[|exact Hm].
  replace ((axh*(1-u))*(ayh*(1-u)))%R with
    ((axh*ayh)*(1-u)^2)%R by ring. nra. }
have Hscaled := Rmult_lt_compat_l (4*u^2) _ _ ltac:(nra) Hxy.
have Hscaled' : 4*u^2*(2*(1-u)^2) <=
    4*u^2*Rabs ((axh+axl)*(ayh+ayl)) by (apply Rlt_le;exact Hscaled).
have Hfabs0 := Rabs_pos f.
have Hcoef7 : 7*u^2 <= 4*u^2*(2*(1-u)^2) by nra.
have Hcoef9 : 9*u^2 <= 4*u^2*(2*(1-u)^2)+3*u^2 by nra.
destruct (Rle_dec (Rabs f) (u^2)) as [Hfs|Hfl].
- have He1s : Rabs e1 <= u^2.
  { unfold e1,tl1,rp. apply round_error_le_u2_with_low0_margin;
      [exact Hp5|].
    eapply Rle_trans;[apply Rabs_triang|]. lra. }
  have He2s : Rabs e2 <= 2*u^2.
  { unfold e2,cl2,rp. apply round_error_le_2u2_below_four_u;
      [exact Hp5|].
    have Ht := Rabs_triang (cross+f) e1.
    have Ht' := Rabs_triang cross f.
    eapply Rle_trans;[exact Ht|].
    eapply Rle_trans;[apply Rplus_le_compat_r;exact Ht'|]. lra. }
  have Ht0 := Rabs_triang e1 e2.
  have Ht1 := Rabs_triang (e1+e2) e3.
  eapply Rle_trans;[exact Ht1|].
  eapply Rle_trans;[apply Rplus_le_compat_r;exact Ht0|].
  have Herr7 : Rabs e1+Rabs e2+Rabs e3 <= 7*u^2 by lra.
  eapply Rle_trans;[exact Herr7|].
  eapply Rle_trans;[exact Hcoef7|].
  eapply Rle_trans;[exact Hscaled'|].
  have Hf0 := Rabs_pos f. lra.
- have Ht0 := Rabs_triang e1 e2.
  have Ht1 := Rabs_triang (e1+e2) e3.
  eapply Rle_trans;[exact Ht1|].
  eapply Rle_trans;[apply Rplus_le_compat_r;exact Ht0|].
  have Herr9 : Rabs e1+Rabs e2+Rabs e3 <= 9*u^2 by lra.
  have Hfloor3 : 3*u^2 < 3*Rabs f by lra.
  eapply Rle_trans;[exact Herr9|].
  eapply Rle_trans;[exact Hcoef9|].
  apply Rplus_le_compat;[exact Hscaled'|apply Rlt_le;exact Hfloor3].
Qed.

(* Homogeneity and symmetry of the FLX chain. *)
Local Lemma flx_Asym_r (xh xl yh yl f : R) :
  FLXlow0 xh xl (-yh) (-yl) (-f) = F2Sum.pair_opp (FLXlow0 xh xl yh yl f).
Proof.
rewrite !(=^~Ropp_mult_distr_r, rnd_p_sym (fprec t) choice choiceP,
  F2Sum.Fast2Sum_asym (rnd_p_sym (fprec t) choice choiceP)) //.
have -> : (- (xh*yh) - - round radix2 (FLX_exp (fprec t)) (Znearest choice) (xh*yh)) =
    -((xh*yh)-round radix2 (FLX_exp (fprec t)) (Znearest choice) (xh*yh)) by ring.
by rewrite !(=^~Ropp_plus_distr, rnd_p_sym (fprec t) choice choiceP,
  F2Sum.Fast2Sum_asym (rnd_p_sym (fprec t) choice choiceP)) ?Ropp_involutive //;
  apply (rnd_p_sym (fprec t) choice choiceP).
Qed.

Local Lemma flx_Asym_l (xh xl yh yl f : R) :
  FLXlow0 (-xh) (-xl) yh yl (-f) = F2Sum.pair_opp (FLXlow0 xh xl yh yl f).
Proof.
rewrite !(=^~Ropp_mult_distr_l, rnd_p_sym (fprec t) choice choiceP,
  F2Sum.Fast2Sum_asym (rnd_p_sym (fprec t) choice choiceP)) //.
have -> : (- (xh*yh) - - round radix2 (FLX_exp (fprec t)) (Znearest choice) (xh*yh)) =
    -((xh*yh)-round radix2 (FLX_exp (fprec t)) (Znearest choice) (xh*yh)) by ring.
by rewrite !(=^~Ropp_plus_distr, rnd_p_sym (fprec t) choice choiceP,
  F2Sum.Fast2Sum_asym (rnd_p_sym (fprec t) choice choiceP)) ?Ropp_involutive //;
  apply (rnd_p_sym (fprec t) choice choiceP).
Qed.

Local Lemma flx_Sx (xh xl yh yl f : R) (e : Z) :
  FLXlow0 (xh*bpow radix2 e) (xl*bpow radix2 e) yh yl (f*bpow radix2 e) =
  DWTimesFP.map_pair (fun z => z*bpow radix2 e) (FLXlow0 xh xl yh yl f).
Proof.
rewrite !(Rmult_comm _ yh) !(Rmult_comm _ yl)
  !(=^~Rmult_assoc, Bayleyaux.round_bpow, =^~Rmult_plus_distr_r,
    F2Sum.Fast2SumS, =^~Rmult_minus_distr_r)
  !(Rmult_comm yh) //.
all: apply Generic_fmt.generic_format_round.
all: try apply valid_rnd_N.
all: apply FLX_exp_valid; exact (fprec_gt_0 t).
Qed.

Local Lemma flx_Sy (xh xl yh yl f : R) (e : Z) :
  FLXlow0 xh xl (yh*bpow radix2 e) (yl*bpow radix2 e) (f*bpow radix2 e) =
  DWTimesFP.map_pair (fun z => z*bpow radix2 e) (FLXlow0 xh xl yh yl f).
Proof.
rewrite !(=^~Rmult_assoc, Bayleyaux.round_bpow,
  =^~Rmult_plus_distr_r, F2Sum.Fast2SumS,
  =^~Rmult_minus_distr_r) //.
all: apply Generic_fmt.generic_format_round.
all: try apply valid_rnd_N.
all: apply FLX_exp_valid; exact (fprec_gt_0 t).
Qed.

(* Scaling reduction to normalized leading words (direct positive). *)
Local Lemma flx_positive (xh0 xl0 yh0 yl0 f0 : R) :
  (5 <= fprec t)%Z ->
  DWPlus.double_word (fprec t) choice xh0 xl0 ->
  DWPlus.double_word (fprec t) choice yh0 yl0 ->
  0 < xh0 -> 0 < yh0 ->
  Rabs f0 <= 8/9*u^2*Rabs (xh0*yh0) ->
  let '(rzh,rzl) := FLXlow0 xh0 xl0 yh0 yl0 f0 in
  Rabs ((rzh+rzl)-(xh0+xl0)*(yh0+yl0)-f0) <=
    4*u^2*Rabs ((xh0+xl0)*(yh0+yl0))+3*Rabs f0.
Proof.
move => Hp5 DWx DWy Hxp Hyp Hf.
have Hp1 : (1 < fprec t)%Z by lia.
destruct DWx as [[Fxh Fxl] Ex].
destruct DWy as [[Fyh Fyl] Ey].
destruct (DWPlus.scale_generic_12 (p:=fprec t) Fxh Hxp)
  as [ex Hx].
destruct (DWPlus.scale_generic_12 (p:=fprec t) Fyh Hyp)
  as [ey Hy].
set bx := bpow radix2 ex.
set sy := bpow radix2 ey.
set axh := xh0*bx. set axl := xl0*bx.
set ayh := yh0*sy. set ayl := yl0*sy.
set af := f0*bx*sy.
have Hbx : 0<bx by (unfold bx;apply bpow_gt_0).
have Hsy : 0<sy by (unfold sy;apply bpow_gt_0).
have DWax : DWPlus.double_word (fprec t) choice axh axl.
{ split; [split|].
  - unfold axh,bx. exact (DWPlus.formatS Hp1 Fxh ex).
  - unfold axl,bx. exact (DWPlus.formatS Hp1 Fxl ex).
  - unfold axh,axl,bx.
    rewrite -Rmult_plus_distr_r Bayleyaux.round_bpow -Ex. reflexivity. }
have DWay : DWPlus.double_word (fprec t) choice ayh ayl.
{ split; [split|].
  - unfold ayh,sy. exact (DWPlus.formatS Hp1 Fyh ey).
  - unfold ayl,sy. exact (DWPlus.formatS Hp1 Fyl ey).
  - unfold ayh,ayl,sy.
    rewrite -Rmult_plus_distr_r Bayleyaux.round_bpow -Ey. reflexivity. }
have Hax : 1<=axh<=2-2*u by (unfold axh,bx;exact Hx).
have Hay : 1<=ayh<=2-2*u by (unfold ayh,sy;exact Hy).
have Haf : Rabs af <= 8/9*u^2*(axh*ayh).
{ unfold af,axh,ayh.
  rewrite !Rabs_mult.
  have Abx : Rabs bx=bx by (apply Rabs_pos_eq;lra).
  have Asy : Rabs sy=sy by (apply Rabs_pos_eq;lra).
  rewrite Abx Asy.
  rewrite Rabs_mult in Hf.
  have Ax : Rabs xh0=xh0 by (apply Rabs_pos_eq;lra).
  have Ay : Rabs yh0=yh0 by (apply Rabs_pos_eq;lra).
  rewrite Ax Ay in Hf.
  have Hs := Rmult_le_compat_r (bx*sy) _ _ ltac:(nra) Hf.
  nra. }
case E0: (FLXlow0 xh0 xl0 yh0 yl0 f0) => [rzh0 rzl0].
have Escaled : FLXlow0 axh axl ayh ayl af = (rzh0*bx*sy,rzl0*bx*sy).
{ unfold axh,axl,ayh,ayl,af,bx,sy.
  rewrite (flx_Sy (xh0*bpow radix2 ex) (xl0*bpow radix2 ex)
    yh0 yl0 (f0*bpow radix2 ex) ey).
  rewrite (flx_Sx xh0 xl0 yh0 yl0 f0 ex) E0.
  reflexivity. }
have Hnorm :
  let '(rzh,rzl) := FLXlow0 axh axl ayh ayl af in
  Rabs ((rzh+rzl)-(axh+axl)*(ayh+ayl)-af) <=
    4*u^2*Rabs ((axh+axl)*(ayh+ayl))+3*Rabs af.
{ destruct (Rle_dec (axh*ayh) 2) as [Hhard|Heasy].
  - exact (flx_dwtimesdw_hard
      axh axl ayh ayl af Hp5 DWax DWay Hax Hay Hhard Haf).
  - apply flx_dwtimesdw_easy;
      try assumption; lra. }
rewrite Escaled /= in Hnorm.
have Hb : 0<bx*sy by nra.
have HL : Rabs (((rzh0+rzl0)-(xh0+xl0)*(yh0+yl0)-f0)*(bx*sy)) =
    (bx*sy)*Rabs ((rzh0+rzl0)-(xh0+xl0)*(yh0+yl0)-f0).
{ rewrite Rabs_mult (Rabs_pos_eq (bx*sy)); [ring|lra]. }
have HP : Rabs (((xh0+xl0)*(yh0+yl0))*(bx*sy)) =
    (bx*sy)*Rabs ((xh0+xl0)*(yh0+yl0)).
{ rewrite Rabs_mult (Rabs_pos_eq (bx*sy)); [ring|lra]. }
have HF : Rabs (f0*(bx*sy))=(bx*sy)*Rabs f0.
{ rewrite Rabs_mult (Rabs_pos_eq (bx*sy)); [ring|lra]. }
replace ((rzh0*bx*sy+rzl0*bx*sy)-
  (axh+axl)*(ayh+ayl)-af)%R with
  (((rzh0+rzl0)-(xh0+xl0)*(yh0+yl0)-f0)*(bx*sy))%R in Hnorm
  by (unfold axh,axl,ayh,ayl,af;ring).
replace ((axh+axl)*(ayh+ayl))%R with
  (((xh0+xl0)*(yh0+yl0))*(bx*sy))%R in Hnorm
  by (unfold axh,axl,ayh,ayl;ring).
replace af with (f0*(bx*sy)) in Hnorm by (unfold af;ring).
rewrite HL HP HF in Hnorm.
apply (Rmult_le_reg_l (bx*sy)); [exact Hb|].
have HEq : ((bx*sy)*(4*u^2*Rabs ((xh0+xl0)*(yh0+yl0))+
    3*Rabs f0))%R =
    (4*u^2*((bx*sy)*Rabs ((xh0+xl0)*(yh0+yl0)))+
      3*((bx*sy)*Rabs f0))%R by ring.
rewrite HEq. exact Hnorm.
Qed.

(* Sign reduction (direct mixed). *)
Local Lemma flx_mixed (xh0 xl0 yh0 yl0 f0 : R) :
  (5 <= fprec t)%Z ->
  DWPlus.double_word (fprec t) choice xh0 xl0 ->
  DWPlus.double_word (fprec t) choice yh0 yl0 ->
  xh0<>0 -> yh0<>0 ->
  Rabs f0 <= 8/9*u^2*Rabs (xh0*yh0) ->
  let '(rzh,rzl) := FLXlow0 xh0 xl0 yh0 yl0 f0 in
  Rabs ((rzh+rzl)-(xh0+xl0)*(yh0+yl0)-f0) <=
    4*u^2*Rabs ((xh0+xl0)*(yh0+yl0))+3*Rabs f0.
Proof.
move => Hp5 DWx DWy Hx0 Hy0 Hf.
have DWopp (ah al : R) :
    DWPlus.double_word (fprec t) choice ah al ->
    DWPlus.double_word (fprec t) choice (-ah) (-al).
{ move => [[Fh Fl] E]. split;[split|].
  - exact (generic_format_opp _ _ _ Fh).
  - exact (generic_format_opp _ _ _ Fl).
  - replace (-ah+-al)%R with (-(ah+al))%R by ring.
    rewrite (@rnd_p_sym (fprec t) choice choiceP). f_equal. exact E. }
case E0: (FLXlow0 xh0 xl0 yh0 yl0 f0) => [rzh0 rzl0].
destruct (Rlt_dec 0 xh0) as [Hxp|Hxn].
- destruct (Rlt_dec 0 yh0) as [Hyp|Hyn].
  + have H := flx_positive
      xh0 xl0 yh0 yl0 f0 Hp5 DWx DWy Hxp Hyp Hf.
    change (Rabs (fst (FLXlow0 xh0 xl0 yh0 yl0 f0)+
      snd (FLXlow0 xh0 xl0 yh0 yl0 f0)-(xh0+xl0)*(yh0+yl0)-f0) <=
      4*u^2*Rabs ((xh0+xl0)*(yh0+yl0))+3*Rabs f0) in H.
    rewrite E0 /= in H. exact H.
  + have Hyn' : 0 < -yh0 by lra.
    have DWyn := DWopp yh0 yl0 DWy.
    have Hfn : Rabs (-f0) <= 8/9*u^2*Rabs (xh0*(-yh0)).
    { rewrite Rabs_Ropp.
      replace (xh0*(-yh0))%R with (-(xh0*yh0))%R by ring.
      rewrite Rabs_Ropp. exact Hf. }
    have H := flx_positive
      xh0 xl0 (-yh0) (-yl0) (-f0) Hp5 DWx DWyn Hxp Hyn' Hfn.
    change (Rabs (fst (FLXlow0 xh0 xl0 (-yh0) (-yl0) (-f0))+
      snd (FLXlow0 xh0 xl0 (-yh0) (-yl0) (-f0))-
      (xh0+xl0)*(-yh0+-yl0)- -f0) <=
      4*u^2*Rabs ((xh0+xl0)*(-yh0+-yl0))+3*Rabs (-f0)) in H.
    have En : FLXlow0 xh0 xl0 (-yh0) (-yl0) (-f0)=(-rzh0,-rzl0).
    { rewrite (flx_Asym_r xh0 xl0 yh0 yl0 f0) E0. reflexivity. }
    rewrite En /= in H.
    replace ((-rzh0+-rzl0)-
      (xh0+xl0)*(-yh0+-yl0)- -f0)%R with
      (-((rzh0+rzl0)-(xh0+xl0)*(yh0+yl0)-f0))%R in H by ring.
    rewrite Rabs_Ropp in H.
    replace ((xh0+xl0)*(-yh0+-yl0))%R with
      (-((xh0+xl0)*(yh0+yl0)))%R in H by ring.
    rewrite Rabs_Ropp Rabs_Ropp in H. exact H.
- have Hxn' : 0 < -xh0 by lra.
  have DWxn := DWopp xh0 xl0 DWx.
  destruct (Rlt_dec 0 yh0) as [Hyp|Hyn].
  + have Hfn : Rabs (-f0) <= 8/9*u^2*Rabs ((-xh0)*yh0).
    { rewrite Rabs_Ropp.
      replace ((-xh0)*yh0)%R with (-(xh0*yh0))%R by ring.
      rewrite Rabs_Ropp. exact Hf. }
    have H := flx_positive
      (-xh0) (-xl0) yh0 yl0 (-f0) Hp5 DWxn DWy Hxn' Hyp Hfn.
    change (Rabs (fst (FLXlow0 (-xh0) (-xl0) yh0 yl0 (-f0))+
      snd (FLXlow0 (-xh0) (-xl0) yh0 yl0 (-f0))-
      (-xh0+-xl0)*(yh0+yl0)- -f0) <=
      4*u^2*Rabs ((-xh0+-xl0)*(yh0+yl0))+3*Rabs (-f0)) in H.
    have En : FLXlow0 (-xh0) (-xl0) yh0 yl0 (-f0)=(-rzh0,-rzl0).
    { rewrite (flx_Asym_l xh0 xl0 yh0 yl0 f0) E0. reflexivity. }
    rewrite En /= in H.
    replace ((-rzh0+-rzl0)-
      (-xh0+-xl0)*(yh0+yl0)- -f0)%R with
      (-((rzh0+rzl0)-(xh0+xl0)*(yh0+yl0)-f0))%R in H by ring.
    rewrite Rabs_Ropp in H.
    replace ((-xh0+-xl0)*(yh0+yl0))%R with
      (-((xh0+xl0)*(yh0+yl0)))%R in H by ring.
    rewrite Rabs_Ropp Rabs_Ropp in H. exact H.
  + have Hyn' : 0 < -yh0 by lra.
    have DWyn := DWopp yh0 yl0 DWy.
    have Hfp : Rabs f0 <= 8/9*u^2*Rabs ((-xh0)*(-yh0)).
    { replace ((-xh0)*(-yh0))%R with (xh0*yh0)%R by ring. exact Hf. }
    have H := flx_positive
      (-xh0) (-xl0) (-yh0) (-yl0) f0
      Hp5 DWxn DWyn Hxn' Hyn' Hfp.
    change (Rabs (fst (FLXlow0 (-xh0) (-xl0) (-yh0) (-yl0) f0)+
      snd (FLXlow0 (-xh0) (-xl0) (-yh0) (-yl0) f0)-
      (-xh0+-xl0)*(-yh0+-yl0)-f0) <=
      4*u^2*Rabs ((-xh0+-xl0)*(-yh0+-yl0))+3*Rabs f0) in H.
    have En1 : FLXlow0 (-xh0) (-xl0) yh0 yl0 (-f0)=(-rzh0,-rzl0).
    { rewrite (flx_Asym_l xh0 xl0 yh0 yl0 f0) E0. reflexivity. }
    have En : FLXlow0 (-xh0) (-xl0) (-yh0) (-yl0) f0=(rzh0,rzl0).
    { replace f0 with (-(-f0)) by ring.
      rewrite (flx_Asym_r (-xh0) (-xl0) yh0 yl0 (-f0)) En1.
      unfold F2Sum.pair_opp. simpl. f_equal; ring. }
    rewrite En /= in H.
    replace ((-xh0+-xl0)*(-yh0+-yl0))%R with
      ((xh0+xl0)*(yh0+yl0))%R in H by ring.
    exact H.
Qed.

(* The far underflow bound for the low by low product, directly for the real DWTimesDW, via the
   FLT floor decomposition (no synthetic floored algorithm). *)
Lemma DWTimesDW_abs_low0_far (xh xl yh yl : ftype t) :
  double_word xh xl -> double_word yh yl ->
  is_finite_p (DWTimesDW xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  9/8*bpow radix2 (eminA+2*fprec t-1) < Rabs (FT2R xh*FT2R yh) ->
  Rabs (FT2R xl*FT2R yl) < bpow radix2 (eminA+fprec t-1) ->
  bpow radix2 (eminA+fprec t-1) <=
    Rabs (FT2R xh*FT2R yl+FT2R (BMULT xl yl)) ->
  bpow radix2 (eminA+fprec t-1) <=
    Rabs (FT2R xl*FT2R yh+FT2R (BFMA xh yl (BMULT xl yl))) ->
  bpow radix2 (eminA+fprec t-1) <=
    Rabs (FT2R (Fast2Mult_err xh yh)+
      FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) ->
  Rabs (FT2R (fst (DWTimesDW xh xl yh yl)) +
        FT2R (snd (DWTimesDW xh xl yh yl)) -
        (FT2R xh+FT2R xl)*(FT2R yh+FT2R yl)) <=
    4*u^2*Rabs ((FT2R xh+FT2R xl)*(FT2R yh+FT2R yl))+2*bpow radix2 eminA.
Proof.
move => DWx DWy FIN Hp5 Hfar U0 N1 N2 N3.
have Hp3 : (3 <= fprec t)%Z by lia.
have Fmul := DWTimesDW_mul_finite xh xl yh yl FIN.
have T0 : bpow radix2 (eminA+2*fprec t-1) <= Rabs (FT2R xh*FT2R yh).
{ have HT0 := bpow_gt_0 radix2 (eminA+2*fprec t-1). nra. }
have Hdec := relerr_error_relative_floor_decomposition xh xl yh yl
  Hp3 DWx DWy FIN Fmul T0.
destruct Hdec as
  (er0 & er1 & er2 & er3 & ef0 & ef1 & ef2 & ef3 &
   Heq & R0 & R1 & R2 & R3 & F0b & F1b & F2b & F3b & Hef &
   ER1 & ER2 & ER3 & ER1f & ER2f & ER3f &
   Z0 & Z1 & Z2 & Z3 & G0 & G1 & G2 & G3 &
   Teq0 & Teq1 & Teq2 & Seq0 & Seq1 & Seq2 & Seq3).
destruct G0 as [[Ef0 N0]|[Er0 N0small]].
{ exfalso;exact (Rlt_not_le _ _ U0 N0). }
destruct G1 as [[Ef1 N1']|[Er1eq N1small]].
2:{ exfalso;exact (Rlt_not_le _ _ N1small N1). }
destruct G2 as [[Ef2 N2']|[Er2eq N2small]].
2:{ exfalso;exact (Rlt_not_le _ _ N2small N2). }
destruct G3 as [[Ef3 N3']|[Er3eq N3small]].
2:{ exfalso;exact (Rlt_not_le _ _ N3small N3). }
subst er0; subst ef1; subst ef2; subst ef3.
rewrite Rplus_0_r in Seq1. rewrite Rplus_0_r in Seq2.
rewrite Rplus_0_r in Seq3.
have T0e : FT2R (BMULT xl yl) = FT2R xl*FT2R yl + ef0
  by (rewrite Teq0; ring).
(* node reconciliations to the real nodes *)
have Etl1 : round radix2 (FLX_exp (fprec t)) (Znearest choice)
    ((FT2R xh*FT2R yl + FT2R xl*FT2R yl) + ef0) =
    FT2R (BFMA xh yl (BMULT xl yl)).
{ rewrite Seq1. f_equal. rewrite T0e. ring. }
have Ecl2 : round radix2 (FLX_exp (fprec t)) (Znearest choice)
    (FT2R xl*FT2R yh + FT2R (BFMA xh yl (BMULT xl yl))) =
    FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))).
{ rewrite Seq2. reflexivity. }
have HDWx : DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl)
  by (apply (dw_word_DWdouble xh xl xh);exact DWx).
have HDWy : DWPlus.double_word (fprec t) choice (FT2R yh) (FT2R yl)
  by (apply (dw_word_DWdouble yh yl yh);exact DWy).
have Fxh := proj1 (proj1 HDWx).
have Fyh := proj1 (proj1 HDWy).
have Htp := DWMulFP_relative_acc.Fast2Mult_correct_weak xh yh Fmul ltac:(auto).
rewrite /DWTimesFP.Fast2Mult /F2Rp /= in Htp.
have Ech := f_equal fst Htp. have Ecl1raw := f_equal snd Htp.
simpl in Ech, Ecl1raw.
have Fcl1 : generic_format radix2 (FLX_exp (fprec t))
    (FT2R xh*FT2R yh -
     round radix2 (FLX_exp (fprec t)) (Znearest choice) (FT2R xh*FT2R yh)).
{ rewrite -Ropp_minus_distr. apply generic_format_opp.
  apply Mult_error.mult_error_FLX;
    [exact (fprec_gt_0 t)|apply valid_rnd_N|exact Fxh|exact Fyh]. }
have Ecl1 : FT2R xh*FT2R yh -
    round radix2 (FLX_exp (fprec t)) (Znearest choice) (FT2R xh*FT2R yh) =
    FT2R (Fast2Mult_err xh yh).
{ rewrite -Ecl1raw. symmetry. apply round_generic;
    [apply valid_rnd_N|exact Fcl1]. }
have Hbridge : FLXlow0 (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl) ef0 =
    F2Rp (DWTimesDW xh xl yh yl).
{ rewrite Etl1 Ecl2 Ecl1 Ech -Seq3.
  rewrite (FastTwoSumEq_FLT (Fast2Mult_mul xh yh)
    (BPLUS (Fast2Mult_err xh yh)
      (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) FIN).
  reflexivity. }
(* floor budget from the far threshold *)
have HP0 : 0 < Rabs (FT2R xh*FT2R yh).
{ eapply Rlt_le_trans;[apply bpow_gt_0|exact T0]. }
have Hxh0 : FT2R xh<>0.
{ intro H. rewrite H Rmult_0_l Rabs_R0 in HP0. lra. }
have Hyh0 : FT2R yh<>0.
{ intro H. rewrite H Rmult_0_r Rabs_R0 in HP0. lra. }
have Hbudget : Rabs ef0 <= 8/9*u^2*Rabs (FT2R xh*FT2R yh).
{ have H := low0_half_floor_budget_above_nine_eighths
    (Rabs (FT2R xh*FT2R yh)) Hfar. lra. }
have Hmix := flx_mixed (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl) ef0
  Hp5 HDWx HDWy Hxh0 Hyh0 Hbudget.
change (Rabs (fst (FLXlow0 (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl) ef0)+
    snd (FLXlow0 (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl) ef0)-
    (FT2R xh+FT2R xl)*(FT2R yh+FT2R yl)-ef0) <=
  4*u^2*Rabs ((FT2R xh+FT2R xl)*(FT2R yh+FT2R yl))+3*Rabs ef0) in Hmix.
rewrite Hbridge /F2Rp in Hmix. cbn [fst snd] in Hmix.
have Hz : (FT2R (fst (DWTimesDW xh xl yh yl))+
   FT2R (snd (DWTimesDW xh xl yh yl))-
   (FT2R xh+FT2R xl)*(FT2R yh+FT2R yl))%R =
  ((FT2R (fst (DWTimesDW xh xl yh yl))+
   FT2R (snd (DWTimesDW xh xl yh yl))-
   (FT2R xh+FT2R xl)*(FT2R yh+FT2R yl)-ef0)+ef0)%R by ring.
rewrite Hz.
eapply Rle_trans;[apply Rabs_triang|].
eapply Rle_trans;[apply Rplus_le_compat_r;exact Hmix|].
have H4f : 4*Rabs ef0 <= 2*bpow radix2 eminA by (have := F0b; nra).
replace (4*u^2*Rabs ((FT2R xh+FT2R xl)*(FT2R yh+FT2R yl))+3*Rabs ef0+Rabs ef0)%R
  with (4*u^2*Rabs ((FT2R xh+FT2R xl)*(FT2R yh+FT2R yl))+4*Rabs ef0)%R by ring.
apply Rplus_le_compat_l. exact H4f.
Qed.

End FarLow0Apparatus.

Section DWMulDW_Division_Helpers.
Context {NANS: Nans} {t : type} {STD: is_standard t}.
Notation u := (bpow Zaux.radix2 (- fprec t)).
Notation fexp := (SpecFloat.fexp (fprec t) (femax t)).
Notation eminA := (SpecFloat.emin (fprec t) (femax t)).
Notation ulp := (Ulp.ulp Zaux.radix2 fexp).
Notation OmegaA := (bpow Zaux.radix2 (femax t)).
Local Instance valid_fexp_inst_dh : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.
Variables (xh xl yh yl : ftype t).
Let zh := FT2R (fst (DWTimesDW xh xl yh yl)).
Let zl := FT2R (snd (DWTimesDW xh xl yh yl)).
Let xr := (FT2R xh + FT2R xl).
Let yr := (FT2R yh + FT2R yl).


Corollary DWTimesDW_abs_low0_normal :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  bpow radix2 (eminA + 2 * fprec t - 1) <=
    Rabs (FT2R xh * FT2R yh) ->
  bpow radix2 (eminA + fprec t - 1) <=
    Rabs (FT2R xl * FT2R yl) ->
  Rabs (zh+zl-xr*yr) <= 4*u^2*Rabs (xr*yr).
Proof.
move => Hdw Hdwy Hfin Hp5 Nprod N0.
have Hrel := DWTimesDW_relative_accuracy_core
  xh xl yh yl Hdw Hdwy Hfin Hp5 Nprod N0.
have Hprod0 : 0 < Rabs (FT2R xh*FT2R yh).
{ eapply Rlt_le_trans; [apply bpow_gt_0|exact Nprod]. }
have Hxhne : FT2R xh<>0.
{ intro H0. rewrite H0 Rmult_0_l Rabs_R0 in Hprod0. lra. }
have Hyhne : FT2R yh<>0.
{ intro H0. rewrite H0 Rmult_0_r Rabs_R0 in Hprod0. lra. }
have Hxrne : xr<>0.
{ intro H0. apply Hxhne.
  unfold double_word in Hdw. fold xr in Hdw.
  rewrite H0 /rounded round_0 in Hdw. exact Hdw. }
have Hyrne : yr<>0.
{ intro H0. apply Hyhne.
  unfold double_word in Hdwy. fold yr in Hdwy.
  rewrite H0 /rounded round_0 in Hdwy. exact Hdwy. }
have Hxyne : xr*yr<>0
  by apply Rmult_integral_contrapositive_currified; assumption.
unfold relative_error_DWTimesDW in Hrel.
have Heq : Rabs (zh+zl-xr*yr) =
    Rabs ((zh+zl-xr*yr)/(xr*yr))*Rabs (xr*yr).
{ rewrite -Rabs_mult. f_equal. field; split; assumption. }
rewrite Heq. apply Rmult_le_compat_r; [apply Rabs_pos|exact Hrel].
Qed.

(** Absolute paper bound for the broader exact node regime.  Each node may
    be normal or merely representable on the physical FIX lattice. *)


(** If both the low by low node and the final correction node are subnormal,
    their relative components vanish.  The two remaining relative errors fit
    strictly inside the paper [4*u^2] budget; all additive pieces retain the
    shared allowance of two ulps. *)
Theorem DWTimesDW_abs_low0_final_underflow :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  bpow radix2 (eminA+2*fprec t-1) <=
    Rabs (FT2R xh*FT2R yh) ->
  Rabs (FT2R xl*FT2R yl) < bpow radix2 (eminA+fprec t-1) ->
  Rabs (FT2R (Fast2Mult_err xh yh)+
    FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) <
      bpow radix2 (eminA+fprec t-1) ->
  Rabs (zh+zl-xr*yr) <=
    4*u^2*Rabs (xr*yr)+2*bpow radix2 eminA.
Proof.
move => DWx DWy FIN Hp5 Nprod N0 N3.
have Hp3 : (3 <= fprec t)%Z by lia.
have Fmul := DWTimesDW_mul_finite xh xl yh yl FIN.
have H := relerr_error_relative_floor_decomposition xh xl yh yl
  Hp3 DWx DWy FIN Fmul Nprod.
destruct H as
  (er0 & er1 & er2 & er3 & ef0 & ef1 & ef2 & ef3 &
   Heq & R0 & R1 & R2 & R3 & F0b & F1b & F2b & F3b & Hef &
   ER1 & ER2 & ER3 & ER1f & ER2f & ER3f &
   Z0 & Z1 & Z2 & Z3 & G0 & G1 & G2 & G3 &
   T0 & T1 & T2 & S0 & S1 & S2 & S3).
destruct G0 as [[Ef0 N0normal]|[Er0 N0small]].
{ exfalso;exact (Rlt_not_le _ _ N0 N0normal). }
destruct G3 as [[Ef3 N3normal]|[Er3 N3small]].
{ exfalso;exact (Rlt_not_le _ _ N3 N3normal). }
subst er0; subst er3.
set P := Rabs (FT2R xh*FT2R yh).
set eta := bpow radix2 eminA.
have Hu0 : 0 < u by (unfold u;apply bpow_gt_0).
have Hu : u <= /32.
{ unfold u. have -> : (/32:R)=bpow radix2 (-5) by (simpl;lra).
  apply bpow_le;lia. }
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have Heta0 : 0 < eta by (unfold eta;apply bpow_gt_0).
have Hxl := @dw_low_le_u_high t STD xh xl DWx.
have Hyl := @dw_low_le_u_high t STD yh yl DWy.
fold u in Hxl,Hyl.
have HA : Rabs (FT2R xh*FT2R yl) <= u*P.
{ unfold P. rewrite !Rabs_mult.
  have H := Rmult_le_compat_l (Rabs (FT2R xh)) _ _
    (Rabs_pos _) Hyl. nra. }
have HB : Rabs (FT2R xl*FT2R yh) <= u*P.
{ unfold P. rewrite !Rabs_mult.
  have H := Rmult_le_compat_r (Rabs (FT2R yh)) _ _
    (Rabs_pos _) Hxl. nra. }
have HC : Rabs (FT2R xl*FT2R yl) <= u^2*P.
{ unfold P. rewrite !Rabs_mult.
  have H := Rmult_le_compat _ _ _ _
    (Rabs_pos _) (Rabs_pos _) Hxl Hyl.
  eapply Rle_trans; [exact H|]. right; ring. }
set T := bpow radix2 (eminA+2*fprec t-1).
fold P T in Nprod.
have Hscale : u^2*T=/2*eta.
{ replace (u^2) with (u*u) by ring. unfold u,T,eta.
  rewrite -(bpow_plus radix2 (-fprec t) (-fprec t)).
  rewrite -(bpow_plus radix2 (-fprec t+-fprec t)
    (eminA+2*fprec t-1)).
  replace (-fprec t+-fprec t+(eminA+2*fprec t-1))%Z with
    (eminA-1)%Z by ring.
  rewrite (bpow_plus radix2 eminA (-1)).
  change (bpow radix2 (-1)) with (/2:R). ring. }
have HetaP : eta <= 2*u^2*P.
{ have Hs := Rmult_le_compat_l (u^2) _ _ (pow2_ge_0 u) Nprod.
  nra. }
fold u eta in ER1f,ER2f.
ring_simplify in ER1f. ring_simplify in ER2f.
replace (FT2R xh*FT2R yl+FT2R xl*FT2R yl+0) with
  (FT2R xh*FT2R yl+FT2R xl*FT2R yl) in ER1f by ring.
replace (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
  FT2R xl*FT2R yl+0+er1) with
  (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
   FT2R xl*FT2R yl+er1) in ER2f by ring.
have Harg1 : Rabs (FT2R xh*FT2R yl+FT2R xl*FT2R yl) <=
    u*P+u^2*P.
{ eapply Rle_trans; [apply Rabs_triang|]. nra. }
have HE1 : Rabs er1 <= u^2*P+2*u^3*P.
{ eapply Rle_trans; [exact ER1f|].
  have Hm := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Harg1.
  have He := Rmult_le_compat_l (/2*u) _ _ ltac:(nra) HetaP.
  eapply Rle_trans.
  - apply Rplus_le_compat; [exact Hm|].
    replace (u*/2*eta) with (/2*u*eta) by ring. exact He.
  - nra. }
have Harg2 : Rabs (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
    FT2R xl*FT2R yl+er1) <= 2*u*P+u^2*P+Rabs er1.
{ have H1 := Rabs_triang
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+FT2R xl*FT2R yl) er1.
  have H2 := Rabs_triang
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl) (FT2R xl*FT2R yl).
  have H3 := Rabs_triang (FT2R xl*FT2R yh) (FT2R xh*FT2R yl).
  nra. }
have HE2 : Rabs er2 <= 2*u^2*P+4*u^3*P+2*u^4*P.
{ eapply Rle_trans; [exact ER2f|].
  have Hm := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Harg2.
  have He := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) HetaP.
  eapply Rle_trans.
  - apply Rplus_le_compat; [exact Hm|exact He].
  - have Harg2' : 2*u*P+u^2*P+Rabs er1 <=
        2*u*P+u^2*P+(u^2*P+2*u^3*P) by nra.
    have Hm' := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Harg2'.
    eapply Rle_trans.
    + apply Rplus_le_compat_r. exact Hm'.
    + nra. }
have Hcore : Rabs (er1+er2) <= 4*u^2*((1-u)^2*P).
{ eapply Rle_trans; [apply Rabs_triang|].
  have Hsmall : 15*u-2*u^2 <= 1 by nra.
  nra. }
have Hprod := aux_dw_exact_product_lower xh xl yh yl DWx DWy.
specialize (Hprod STD). fold u xr yr P in Hprod.
have Hcore' : Rabs (er1+er2) <= 4*u^2*Rabs (xr*yr).
{ eapply Rle_trans; [exact Hcore|].
  apply Rmult_le_compat_l; [nra|exact Hprod]. }
rewrite Heq.
replace (0+er1+er2+0+(ef0+ef1+ef2+ef3)) with
  (er1+er2+(ef0+ef1+ef2+ef3)) by ring.
have Htri := Rabs_triang (er1+er2) (ef0+ef1+ef2+ef3).
fold eta in Hef.
eapply Rle_trans; [exact Htri|].
eapply Rle_trans.
- apply Rplus_le_compat; [exact Hcore'|exact Hef].
- right; ring.
Qed.

(** If the first cross term FMA underflows but the following two nodes are
    normal, the small node hypothesis replaces one full [u*P] contribution.
    The two active physical floors consume one ulp; their propagation consumes
    at most the second ulp, leaving the paper [4*u^2] term unchanged. *)
Theorem DWTimesDW_abs_low0_low1_tail_normal :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  bpow radix2 (eminA+2*fprec t-1) <=
    Rabs (FT2R xh*FT2R yh) ->
  Rabs (FT2R xl*FT2R yl) < bpow radix2 (eminA+fprec t-1) ->
  Rabs (FT2R xh*FT2R yl+FT2R (BMULT xl yl)) <
    bpow radix2 (eminA+fprec t-1) ->
  bpow radix2 (eminA+fprec t-1) <=
    Rabs (FT2R xl*FT2R yh+
      FT2R (BFMA xh yl (BMULT xl yl))) ->
  bpow radix2 (eminA+fprec t-1) <=
    Rabs (FT2R (Fast2Mult_err xh yh)+
      FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) ->
  Rabs (zh+zl-xr*yr) <=
    4*u^2*Rabs (xr*yr)+2*bpow radix2 eminA.
Proof.
move => DWx DWy FIN Hp5 Nprod N0 N1 N2 N3.
have Hp3 : (3 <= fprec t)%Z by lia.
have Fmul := DWTimesDW_mul_finite xh xl yh yl FIN.
have H := relerr_error_relative_floor_decomposition xh xl yh yl
  Hp3 DWx DWy FIN Fmul Nprod.
destruct H as
  (er0 & er1 & er2 & er3 & ef0 & ef1 & ef2 & ef3 &
   Heq & R0 & R1 & R2 & R3 & F0b & F1b & F2b & F3b & Hef &
   ER1 & ER2 & ER3 & ER1f & ER2f & ER3f &
   Z0 & Z1 & Z2 & Z3 & G0 & G1 & G2 & G3 &
   T0 & T1 & T2 & S0 & S1 & S2 & S3).
destruct G0 as [[Ef0 N0normal]|[Er0 N0small]].
{ exfalso; exact (Rlt_not_le _ _ N0 N0normal). }
destruct G1 as [[Ef1 N1normal]|[Er1 N1small]].
{ exfalso; exact (Rlt_not_le _ _ N1 N1normal). }
destruct G2 as [[Ef2 N2normal]|[Er2 N2small]].
2:{ exfalso; exact (Rlt_not_le _ _ N2small N2). }
destruct G3 as [[Ef3 N3normal]|[Er3 N3small]].
2:{ exfalso; exact (Rlt_not_le _ _ N3small N3). }
subst er0; subst er1; subst ef2; subst ef3.
set P := Rabs (FT2R xh*FT2R yh).
set eta := bpow radix2 eminA.
set U := bpow radix2 (eminA+fprec t-1).
have Hu0 : 0 < u by (unfold u;apply bpow_gt_0).
have Hu : u <= /32.
{ unfold u. have -> : (/32:R)=bpow radix2 (-5) by (simpl;lra).
  apply bpow_le;lia. }
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have Heta0 : 0 < eta by (unfold eta;apply bpow_gt_0).
have Hxl := @dw_low_le_u_high t STD xh xl DWx.
have Hyl := @dw_low_le_u_high t STD yh yl DWy.
fold u in Hxl,Hyl.
have HA : Rabs (FT2R xh*FT2R yl) <= u*P.
{ unfold P. rewrite !Rabs_mult.
  have Hm := Rmult_le_compat_l (Rabs (FT2R xh)) _ _
    (Rabs_pos _) Hyl. nra. }
have HB : Rabs (FT2R xl*FT2R yh) <= u*P.
{ unfold P. rewrite !Rabs_mult.
  have Hm := Rmult_le_compat_r (Rabs (FT2R yh)) _ _
    (Rabs_pos _) Hxl. nra. }
have HC : Rabs (FT2R xl*FT2R yl) <= u^2*P.
{ unfold P. rewrite !Rabs_mult.
  have Hm := Rmult_le_compat _ _ _ _
    (Rabs_pos _) (Rabs_pos _) Hxl Hyl.
  eapply Rle_trans; [exact Hm|]. right; ring. }
have Hcl1u : Rabs (FT2R (Fast2Mult_err xh yh)) <=
    /2*ulp (FT2R xh*FT2R yh)
  by (apply Fast2Mult_accuracy_norm;exact Fmul).
have Hulp : ulp (FT2R xh*FT2R yh) <=
    P*bpow radix2 (1-fprec t).
{ unfold P. apply ulp_FLT_le.
  eapply Rle_trans; [|exact Nprod]. apply bpow_le.
  unfold eminA, common.emin, SpecFloat.emin.
  pose proof fprec_lb t. lia. }
have HBp : bpow radix2 (1-fprec t)=2*u.
{ unfold u.
  change (bpow radix2 (1-fprec t)=
    bpow radix2 1*bpow radix2 (-fprec t)).
  rewrite -(bpow_plus radix2 1 (-fprec t)). f_equal;lia. }
have Hcl1 : Rabs (FT2R (Fast2Mult_err xh yh)) <= u*P.
{ rewrite HBp in Hulp. nra. }
have HUscale : u*U=/2*eta.
{ unfold u,U,eta. rewrite -(bpow_plus radix2 (-fprec t)
    (eminA+fprec t-1)).
  replace (-fprec t+(eminA+fprec t-1))%Z with (eminA-1)%Z by ring.
  rewrite (bpow_plus radix2 eminA (-1)).
  change (bpow radix2 (-1)) with (/2:R). ring. }
have Hscale : u^2*bpow radix2 (eminA+2*fprec t-1)=/2*eta.
{ replace (u^2) with (u*u) by ring. unfold u,eta.
  rewrite -(bpow_plus radix2 (-fprec t) (-fprec t)).
  rewrite -(bpow_plus radix2 (-fprec t+-fprec t)
    (eminA+2*fprec t-1)).
  replace (-fprec t+-fprec t+(eminA+2*fprec t-1))%Z with
    (eminA-1)%Z by ring.
  rewrite (bpow_plus radix2 eminA (-1)).
  change (bpow radix2 (-1)) with (/2:R). ring. }
have HetaP : eta <= 2*u^2*P.
{ have Hs := Rmult_le_compat_l (u^2) _ _ (pow2_ge_0 u) Nprod.
  rewrite Hscale in Hs.
  fold P in Hs.
  apply (Rmult_le_reg_l (/2)); [lra|].
  eapply Rle_trans; [exact Hs|]. nra. }
fold P eta U in N1small,F0b,F1b,ER2,ER3.
replace (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
  FT2R xl*FT2R yl+0+0)%R with
  (FT2R xl*FT2R yh+FT2R xh*FT2R yl+FT2R xl*FT2R yl)%R
  in ER2 by ring.
replace (FT2R (Fast2Mult_err xh yh)+FT2R xl*FT2R yh+
  FT2R xh*FT2R yl+FT2R xl*FT2R yl+0+0+er2)%R with
  (FT2R (Fast2Mult_err xh yh)+FT2R xl*FT2R yh+
   FT2R xh*FT2R yl+FT2R xl*FT2R yl+er2)%R in ER3 by ring.
replace (ef0+ef1+0)%R with (ef0+ef1)%R in ER3 by ring.
have HEF01 : Rabs (ef0+ef1) <= eta.
{ eapply Rle_trans; [apply Rabs_triang|]. nra. }
have Hcentral2 : Rabs (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
    FT2R xl*FT2R yl) <= u*P+U+/2*eta.
{ have Hinput :
    Rabs ((FT2R xh*FT2R yl+FT2R (BMULT xl yl))+(-ef0)) <=
    Rabs (FT2R xh*FT2R yl+FT2R (BMULT xl yl))+Rabs (-ef0)
    := Rabs_triang _ _.
  specialize (Hinput NANS STD).
  have HT0 : FT2R (BMULT xl yl)=FT2R xl*FT2R yl+ef0 by nra.
  replace ((FT2R xh*FT2R yl+FT2R (BMULT xl yl))+(-ef0))%R with
    (FT2R xh*FT2R yl+FT2R xl*FT2R yl) in Hinput.
  2:{ replace (FT2R (BMULT xl yl)) with
        (FT2R xl*FT2R yl+ef0) by (symmetry;exact HT0). ring. }
  have Hsum := Rabs_triang (FT2R xl*FT2R yh)
    (FT2R xh*FT2R yl+FT2R xl*FT2R yl).
  replace (FT2R xl*FT2R yh+
    (FT2R xh*FT2R yl+FT2R xl*FT2R yl))%R with
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+FT2R xl*FT2R yl)%R
    in Hsum by ring.
  rewrite Rabs_Ropp in Hinput.
  eapply Rle_trans; [exact Hsum|].
  eapply Rle_trans with (r2:=u*P+(U+/2*eta)); [|right;ring].
  apply Rplus_le_compat; [exact HB|].
  eapply Rle_trans; [exact Hinput|]. nra. }
have HE2 : Rabs er2 <= u^2*P+/2*eta+3/2*u*eta.
{ eapply Rle_trans; [exact ER2|].
  have Hm := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Hcentral2.
  have Hf := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) HEF01.
  nra. }
have Hcentral3 : Rabs (FT2R (Fast2Mult_err xh yh)+
    FT2R xl*FT2R yh+FT2R xh*FT2R yl+FT2R xl*FT2R yl+er2) <=
    2*u*P+U+/2*eta+Rabs er2.
{ have H0 := Rabs_triang (FT2R (Fast2Mult_err xh yh))
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
      FT2R xl*FT2R yl+er2).
  specialize (H0 NANS STD).
  have H1 := Rabs_triang
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+FT2R xl*FT2R yl) er2.
  replace (FT2R (Fast2Mult_err xh yh)+
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
      FT2R xl*FT2R yl+er2))%R with
    (FT2R (Fast2Mult_err xh yh)+FT2R xl*FT2R yh+
      FT2R xh*FT2R yl+FT2R xl*FT2R yl+er2)%R in H0 by ring.
  replace (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
    FT2R xl*FT2R yl+er2)%R with
    ((FT2R xl*FT2R yh+FT2R xh*FT2R yl+
      FT2R xl*FT2R yl)+er2)%R in H1 by ring.
  eapply Rle_trans; [exact H0|].
  eapply Rle_trans.
  - apply Rplus_le_compat; [exact Hcl1|exact H1].
  - nra. }
have HE3 : Rabs er3 <= 2*u^2*P+/2*eta+3/2*u*eta+u*Rabs er2.
{ eapply Rle_trans; [exact ER3|].
  have Hm := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Hcentral3.
  have Hf := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) HEF01.
  nra. }
have Hprod := aux_dw_exact_product_lower xh xl yh yl DWx DWy.
specialize (Hprod STD). fold u xr yr P in Hprod.
have Hrel : Rabs (er2+er3) <=
    4*u^2*Rabs (xr*yr)+eta.
{ eapply Rle_trans; [apply Rabs_triang|].
  have HB0 : 0 <= u^2*P by
    (apply Rmult_le_pos;[apply pow_le;left;exact Hu0|exact HP0]).
  have HE2u := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) HE2.
  have HE3b : Rabs er3 <=
      2*(u^2*P)+u*(u^2*P)+/2*eta+2*u*eta+3/2*u^2*eta.
  { eapply Rle_trans; [exact HE3|].
    eapply Rle_trans.
    - apply Rplus_le_compat_l. exact HE2u.
    - apply Req_le. field. }
  have Hsum : Rabs er2+Rabs er3 <=
      3*(u^2*P)+u*(u^2*P)+eta+7/2*u*eta+3/2*u^2*eta.
  { eapply Rle_trans.
    - apply Rplus_le_compat; [exact HE2|exact HE3b].
    - apply Req_le. field. }
  have Hueta := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) HetaP.
  have Hu2eta := Rmult_le_compat_l (u^2) _ _ (pow2_ge_0 u) HetaP.
  have Hprop : 7/2*u*eta+3/2*u^2*eta <=
      7*u*(u^2*P)+3*u^2*(u^2*P).
  { have H7 := Rmult_le_compat_l (7/2) _ _ ltac:(lra) Hueta.
    have H3 := Rmult_le_compat_l (3/2) _ _ ltac:(lra) Hu2eta.
    replace (7/2*u*eta+3/2*u^2*eta)%R with
      (7/2*(u*eta)+3/2*(u^2*eta))%R by field.
    replace (7*u*(u^2*P)+3*u^2*(u^2*P))%R with
      (7/2*(u*(2*u^2*P))+3/2*(u^2*(2*u^2*P)))%R by field.
    apply Rplus_le_compat; [exact H7|exact H3]. }
  have H16 : 16*u <= 1 by lra.
  have Hu2pos : 0 <= u^2 by apply pow2_ge_0.
  have Hcoef0 : 3+8*u+3*u^2 <= 4*(1-u)^2.
  { eapply Rle_trans with
      (r2:=(3+8*u+3*u^2)+(1-16*u+u^2)).
    - lra.
    - apply Req_le. field. }
  have Hcoef : (3+8*u+3*u^2)*(u^2*P) <=
      4*(1-u)^2*(u^2*P)
    by (apply Rmult_le_compat_r;[exact HB0|exact Hcoef0]).
  have Hpaper : 4*u^2*((1-u)^2*P) <=
      4*u^2*Rabs (xr*yr).
  { apply Rmult_le_compat_l; [apply Rmult_le_pos;[lra|exact Hu2pos]|exact Hprod]. }
  have Hsum' : Rabs er2+Rabs er3 <=
      (3*(u^2*P)+u*(u^2*P)+eta)+
      (7/2*u*eta+3/2*u^2*eta).
  { eapply Rle_trans; [exact Hsum|]. apply Req_le. field. }
  eapply Rle_trans; [exact Hsum'|].
  eapply Rle_trans with
      (r2:=(3+8*u+3*u^2)*(u^2*P)+eta).
  - eapply Rle_trans.
    + apply Rplus_le_compat_l. exact Hprop.
    + apply Req_le. field.
  - eapply Rle_trans.
    + apply Rplus_le_compat_r. exact Hcoef.
    + eapply Rle_trans; [|apply Rplus_le_compat_r;exact Hpaper].
      apply Req_le. field. }
rewrite Heq.
replace (0+0+er2+er3+(ef0+ef1+0+0)) with
  ((er2+er3)+(ef0+ef1)) by ring.
have Htri := Rabs_triang (er2+er3) (ef0+ef1).
eapply Rle_trans; [exact Htri|]. nra.
Qed.

(** Symmetric tail case: the low by low node and the second FMA underflow,
    while the first FMA and final addition are normal.  Here the subnormal
    second FMA input bounds the whole correction entering the last round, so
    the relative pieces fit in [4*u^2] and the two floor terms total one ulp. *)
Theorem DWTimesDW_abs_low0_low2_other_normal :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  bpow radix2 (eminA+2*fprec t-1) <=
    Rabs (FT2R xh*FT2R yh) ->
  Rabs (FT2R xl*FT2R yl) < bpow radix2 (eminA+fprec t-1) ->
  bpow radix2 (eminA+fprec t-1) <=
    Rabs (FT2R xh*FT2R yl+FT2R (BMULT xl yl)) ->
  Rabs (FT2R xl*FT2R yh+
    FT2R (BFMA xh yl (BMULT xl yl))) <
    bpow radix2 (eminA+fprec t-1) ->
  bpow radix2 (eminA+fprec t-1) <=
    Rabs (FT2R (Fast2Mult_err xh yh)+
      FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) ->
  Rabs (zh+zl-xr*yr) <=
    4*u^2*Rabs (xr*yr)+2*bpow radix2 eminA.
Proof.
move => DWx DWy FIN Hp5 Nprod N0 N1 N2 N3.
have Hp3 : (3 <= fprec t)%Z by lia.
have Fmul := DWTimesDW_mul_finite xh xl yh yl FIN.
have H := relerr_error_relative_floor_decomposition xh xl yh yl
  Hp3 DWx DWy FIN Fmul Nprod.
destruct H as
  (er0 & er1 & er2 & er3 & ef0 & ef1 & ef2 & ef3 &
   Heq & R0 & R1 & R2 & R3 & F0b & F1b & F2b & F3b & Hef &
   ER1 & ER2 & ER3 & ER1f & ER2f & ER3f &
   Z0 & Z1 & Z2 & Z3 & G0 & G1 & G2 & G3 &
   T0 & T1 & T2 & S0 & S1 & S2 & S3).
destruct G0 as [[Ef0 N0normal]|[Er0 N0small]].
{ exfalso; exact (Rlt_not_le _ _ N0 N0normal). }
destruct G1 as [[Ef1 N1normal]|[Er1 N1small]].
2:{ exfalso; exact (Rlt_not_le _ _ N1small N1). }
destruct G2 as [[Ef2 N2normal]|[Er2 N2small]].
{ exfalso; exact (Rlt_not_le _ _ N2 N2normal). }
destruct G3 as [[Ef3 N3normal]|[Er3 N3small]].
2:{ exfalso; exact (Rlt_not_le _ _ N3small N3). }
subst er0; subst ef1; subst er2; subst ef3.
set P := Rabs (FT2R xh*FT2R yh).
set eta := bpow radix2 eminA.
set U := bpow radix2 (eminA+fprec t-1).
have Hu0 : 0 < u by (unfold u;apply bpow_gt_0).
have Hu : u <= /32.
{ unfold u. have -> : (/32:R)=bpow radix2 (-5) by (simpl;lra).
  apply bpow_le;lia. }
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have Heta0 : 0 < eta by (unfold eta;apply bpow_gt_0).
have Hxl := @dw_low_le_u_high t STD xh xl DWx.
have Hyl := @dw_low_le_u_high t STD yh yl DWy.
fold u in Hxl,Hyl.
have HA : Rabs (FT2R xh*FT2R yl) <= u*P.
{ unfold P. rewrite !Rabs_mult.
  have Hm := Rmult_le_compat_l (Rabs (FT2R xh)) _ _
    (Rabs_pos _) Hyl. nra. }
have HC : Rabs (FT2R xl*FT2R yl) <= u^2*P.
{ unfold P. rewrite !Rabs_mult.
  have Hm := Rmult_le_compat _ _ _ _
    (Rabs_pos _) (Rabs_pos _) Hxl Hyl.
  eapply Rle_trans; [exact Hm|]. apply Req_le. ring. }
have Hcl1u : Rabs (FT2R (Fast2Mult_err xh yh)) <=
    /2*ulp (FT2R xh*FT2R yh)
  by (apply Fast2Mult_accuracy_norm;exact Fmul).
have Hulp : ulp (FT2R xh*FT2R yh) <=
    P*bpow radix2 (1-fprec t).
{ unfold P. apply ulp_FLT_le.
  eapply Rle_trans; [|exact Nprod]. apply bpow_le.
  unfold eminA, common.emin, SpecFloat.emin.
  pose proof fprec_lb t. lia. }
have HBp : bpow radix2 (1-fprec t)=2*u.
{ unfold u.
  change (bpow radix2 (1-fprec t)=
    bpow radix2 1*bpow radix2 (-fprec t)).
  rewrite -(bpow_plus radix2 1 (-fprec t)). f_equal;lia. }
have Hcl1 : Rabs (FT2R (Fast2Mult_err xh yh)) <= u*P.
{ rewrite HBp in Hulp. nra. }
have HUscale : u*U=/2*eta.
{ unfold u,U,eta. rewrite -(bpow_plus radix2 (-fprec t)
    (eminA+fprec t-1)).
  replace (-fprec t+(eminA+fprec t-1))%Z with (eminA-1)%Z by ring.
  rewrite (bpow_plus radix2 eminA (-1)).
  change (bpow radix2 (-1)) with (/2:R). ring. }
have Hscale : u^2*bpow radix2 (eminA+2*fprec t-1)=/2*eta.
{ replace (u^2) with (u*u) by ring. unfold u,eta.
  rewrite -(bpow_plus radix2 (-fprec t) (-fprec t)).
  rewrite -(bpow_plus radix2 (-fprec t+-fprec t)
    (eminA+2*fprec t-1)).
  replace (-fprec t+-fprec t+(eminA+2*fprec t-1))%Z with
    (eminA-1)%Z by ring.
  rewrite (bpow_plus radix2 eminA (-1)).
  change (bpow radix2 (-1)) with (/2:R). ring. }
have HetaP : eta <= 2*u^2*P.
{ have Hs := Rmult_le_compat_l (u^2) _ _ (pow2_ge_0 u) Nprod.
  rewrite Hscale in Hs. fold P in Hs.
  apply (Rmult_le_reg_l (/2)); [lra|].
  eapply Rle_trans; [exact Hs|]. nra. }
fold P eta U in N2small,F0b,F2b,ER1,ER3.
replace (FT2R xh*FT2R yl+FT2R xl*FT2R yl+0)%R with
  (FT2R xh*FT2R yl+FT2R xl*FT2R yl)%R in ER1 by ring.
replace (FT2R (Fast2Mult_err xh yh)+FT2R xl*FT2R yh+
  FT2R xh*FT2R yl+FT2R xl*FT2R yl+0+er1+0)%R with
  (FT2R (Fast2Mult_err xh yh)+FT2R xl*FT2R yh+
   FT2R xh*FT2R yl+FT2R xl*FT2R yl+er1)%R in ER3 by ring.
replace (ef0+0+ef2)%R with (ef0+ef2)%R in ER3 by ring.
have HEF02 : Rabs (ef0+ef2) <= eta.
{ eapply Rle_trans; [apply Rabs_triang|]. nra. }
have Hcentral1 : Rabs (FT2R xh*FT2R yl+FT2R xl*FT2R yl) <=
    u*P+u^2*P.
{ eapply Rle_trans; [apply Rabs_triang|]. nra. }
have HE1 : Rabs er1 <= u^2*P+u^3*P+/2*u*eta.
{ eapply Rle_trans; [exact ER1|].
  have Hm := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Hcentral1.
  have Hf := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) F0b.
  eapply Rle_trans.
  - apply Rplus_le_compat; [exact Hm|exact Hf].
  - apply Req_le. field. }
have Hcentral3 : Rabs (FT2R (Fast2Mult_err xh yh)+
    FT2R xl*FT2R yh+FT2R xh*FT2R yl+FT2R xl*FT2R yl+er1) <=
    u*P+U+/2*eta.
{ have HT1 : FT2R (BFMA xh yl (BMULT xl yl))=
      FT2R xh*FT2R yl+FT2R xl*FT2R yl+er1+ef0 by nra.
  have Hinput :
      Rabs ((FT2R xl*FT2R yh+
        FT2R (BFMA xh yl (BMULT xl yl)))+(-ef0)) <=
      Rabs (FT2R xl*FT2R yh+
        FT2R (BFMA xh yl (BMULT xl yl)))+Rabs (-ef0)
      := Rabs_triang _ _.
  pose proof (@Hinput NANS STD NANS STD) as Hinput0.
  replace ((FT2R xl*FT2R yh+
    FT2R (BFMA xh yl (BMULT xl yl)))+(-ef0))%R with
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
      FT2R xl*FT2R yl+er1)%R in Hinput0.
  2:{ replace (FT2R (BFMA xh yl (BMULT xl yl))) with
        (FT2R xh*FT2R yl+FT2R xl*FT2R yl+er1+ef0)
        by (symmetry;exact HT1). ring. }
  rewrite Rabs_Ropp in Hinput0.
  have Hsum := Rabs_triang (FT2R (Fast2Mult_err xh yh))
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
      FT2R xl*FT2R yl+er1).
  specialize (Hsum NANS STD).
  replace (FT2R (Fast2Mult_err xh yh)+
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
      FT2R xl*FT2R yl+er1))%R with
    (FT2R (Fast2Mult_err xh yh)+FT2R xl*FT2R yh+
      FT2R xh*FT2R yl+FT2R xl*FT2R yl+er1)%R in Hsum by ring.
  eapply Rle_trans; [exact Hsum|].
  eapply Rle_trans.
  - apply Rplus_le_compat; [exact Hcl1|exact Hinput0].
  - lra. }
have HE3 : Rabs er3 <= u^2*P+/2*eta+3/2*u*eta.
{ eapply Rle_trans; [exact ER3|].
  have Hm := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Hcentral3.
  have Hf := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) HEF02.
  eapply Rle_trans.
  - apply Rplus_le_compat; [exact Hm|exact Hf].
  - nra. }
have Hprod := aux_dw_exact_product_lower xh xl yh yl DWx DWy.
specialize (Hprod STD). fold u xr yr P in Hprod.
have Hrel : Rabs (er1+er3) <= 4*u^2*Rabs (xr*yr).
{ eapply Rle_trans; [apply Rabs_triang|].
  have Hhalf : /2*eta <= u^2*P by lra.
  have Hueta := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) HetaP.
  have Hraw : Rabs er1+Rabs er3 <=
      3*(u^2*P)+5*u*(u^2*P).
  { eapply Rle_trans.
    - apply Rplus_le_compat; [exact HE1|exact HE3].
    - nra. }
  have Hcoef0 : 3+5*u <= 4*(1-u)^2.
  { have H13 : 13*u <= 1 by lra.
    have Hu2pos : 0 <= u^2 by apply pow2_ge_0.
    eapply Rle_trans with (r2:=(3+5*u)+(1-13*u+4*u^2)).
    - lra.
    - apply Req_le. field. }
  have HB0 : 0 <= u^2*P by
    (apply Rmult_le_pos;[apply pow2_ge_0|exact HP0]).
  have Hcoef := Rmult_le_compat_r (u^2*P) _ _ HB0 Hcoef0.
  have Hpaper : 4*u^2*((1-u)^2*P) <= 4*u^2*Rabs (xr*yr).
  { apply Rmult_le_compat_l; [apply Rmult_le_pos;[lra|apply pow2_ge_0]|exact Hprod]. }
  eapply Rle_trans; [exact Hraw|].
  eapply Rle_trans with (r2:=(3+5*u)*(u^2*P)).
  - apply Req_le. field.
  - eapply Rle_trans; [exact Hcoef|].
    eapply Rle_trans with (r2:=4*u^2*((1-u)^2*P)).
    + apply Req_le. field.
    + exact Hpaper. }
rewrite Heq.
replace (0+er1+0+er3+(ef0+0+ef2+0)) with
  ((er1+er3)+(ef0+ef2)) by ring.
have Htri := Rabs_triang (er1+er3) (ef0+ef2).
eapply Rle_trans; [exact Htri|].
eapply Rle_trans.
- apply Rplus_le_compat; [exact Hrel|exact HEF02].
- have := Heta0. nra.
Qed.
Local Lemma leading_product_gap_low_low_zero
    (xh0 xl0 yh0 yl0 : ftype t) :
  double_word_prop xh0 xl0 -> double_word_prop yh0 yl0 ->
  is_finite (BMULT xl0 yl0)=true ->
  Rabs (FT2R xh0*FT2R yh0) <
    bpow radix2 (common.emin (t:=t)+2*fprec t-1) ->
  FT2R (BMULT xl0 yl0)=0.
Proof.
move => DWx DWy F0 Hgap.
set u := bpow radix2 (-fprec t).
set eta := bpow radix2 (common.emin (t:=t)).
have Hu0 : 0 < u by apply bpow_gt_0.
have Hxl := @dw_low_le_u_high t STD xh0 xl0 DWx.
have Hyl := @dw_low_le_u_high t STD yh0 yl0 DWy.
fold u in Hxl, Hyl.
have Hlow : Rabs (FT2R xl0*FT2R yl0) <=
    u^2*Rabs (FT2R xh0*FT2R yh0).
{ rewrite !Rabs_mult.
  have H := Rmult_le_compat _ _ _ _
    (Rabs_pos _) (Rabs_pos _) Hxl Hyl.
  eapply Rle_trans; [exact H|]. right; ring. }
have Hu2 : 0 < u^2 by nra.
have Hscaled := Rmult_lt_compat_l (u^2) _ _ Hu2 Hgap.
have Hscale : u^2*bpow radix2
  (common.emin (t:=t)+2*fprec t-1)=/2*eta.
{ replace (u^2)%R with (u*u)%R by ring.
  unfold u, eta. rewrite -!bpow_plus.
  replace (-fprec t+-fprec t+
    (common.emin (t:=t)+2*fprec t-1))%Z
    with (common.emin (t:=t)-1)%Z by ring.
  rewrite (bpow_plus radix2 (common.emin (t:=t)) (-1)).
  change (bpow radix2 (-1)) with (/2:R). ring. }
have Htiny : Rabs (FT2R xl0*FT2R yl0) < /2*eta by nra.
have Hr := round_FLT_abs_lt_half_emin_0
  (FT2R xl0*FT2R yl0) Htiny.
rewrite (BMULT_round_correct t xl0 yl0 F0) in Hr.
exact Hr.
Qed.

(* ===== Algorithm 12 underflow gap for the whole range mixed API ===== *)

(* Error bound for the compensated core in the [Fast2Mult] gap, before the
   final [Fast2Sum].  The exact sum [ch+cl3] differs from [xr*yr] by at most
   [5/2*eta] plus the [u^2*P] term for the omitted [xl*yl] product.  The four
   rounding charges are [eta/2], [eta/2], [eta/2], and [eta]. *)
Lemma DWTimesDW_core_error_floor_gap (xh0 xl0 yh0 yl0 : ftype t) :
  (3 <= fprec t)%Z ->
  double_word_prop xh0 xl0 -> double_word_prop yh0 yl0 ->
  is_finite_p (DWTimesDW xh0 xl0 yh0 yl0) ->
  Rabs (FT2R xh0*FT2R yh0) <
    bpow radix2 (common.emin (t:=t)+2*fprec t-1) ->
  Rabs ((FT2R (Fast2Mult_mul xh0 yh0)+
         FT2R (BPLUS (Fast2Mult_err xh0 yh0)
                     (BFMA xl0 yh0 (BFMA xh0 yl0 (BMULT xl0 yl0)))))-
        (FT2R xh0+FT2R xl0)*(FT2R yh0+FT2R yl0))
    <= 5/2*bpow radix2 (common.emin (t:=t))+
       u^2*Rabs (FT2R xh0*FT2R yh0).
Proof.
move => Hp3 DWx0 DWy0 FIN Hgap.
set u := bpow radix2 (-fprec t).
set eta := bpow radix2 (common.emin (t:=t)).
set T := bpow radix2 (common.emin (t:=t)+2*fprec t-1).
set N := bpow radix2 (common.emin (t:=t)+fprec t-1).
set P0 := (FT2R xh0*FT2R yh0)%R.
set P := Rabs P0.
set X := (FT2R xh0+FT2R xl0)%R.
set M := (FT2R yh0+FT2R yl0)%R.
have Hu0 : 0 < u by (unfold u;apply bpow_gt_0).
have Hu : u <= /8.
{ unfold u. have -> : (/8:R)=bpow radix2 (-3) by (simpl;lra).
  apply bpow_le; lia. }
have Heta0 : 0 < eta by (unfold eta;apply bpow_gt_0).
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have HN0 : 0 < N by (unfold N;apply bpow_gt_0).
have Hxl := @dw_low_le_u_high t STD xh0 xl0 DWx0.
have Hml := @dw_low_le_u_high t STD yh0 yl0 DWy0.
fold u in Hxl,Hml.
have Hxhml : Rabs (FT2R xh0*FT2R yl0) <= u*P.
{ unfold P,P0. rewrite !Rabs_mult.
  have H := Rmult_le_compat_l (Rabs (FT2R xh0)) _ _
    (Rabs_pos _) Hml. eapply Rle_trans; [exact H|]. right;ring. }
have Hxlmh : Rabs (FT2R xl0*FT2R yh0) <= u*P.
{ unfold P,P0. rewrite !Rabs_mult.
  have H := Rmult_le_compat_r (Rabs (FT2R yh0)) _ _
    (Rabs_pos _) Hxl. eapply Rle_trans; [exact H|]. right;ring. }
have Hxlml : Rabs (FT2R xl0*FT2R yl0) <= u^2*P.
{ unfold P,P0. rewrite !Rabs_mult.
  have H := Rmult_le_compat _ _ _ _ (Rabs_pos _) (Rabs_pos _) Hxl Hml.
  eapply Rle_trans; [exact H|]. right;ring. }
have HuT : u*T=N.
{ unfold u,T,N. rewrite -bpow_plus. f_equal;ring. }
have HuP_N : u*P < N.
{ have H := Rmult_lt_compat_l u _ _ Hu0 Hgap.
  rewrite HuT in H. exact H. }
have HtwoN : 2*N=bpow radix2 (@common.emin t+fprec t).
{ unfold N. transitivity
    (bpow radix2 1*bpow radix2 (@common.emin t+fprec t-1));
    [change (bpow radix2 1) with (2:R);ring|].
  rewrite -bpow_plus. f_equal;ring. }
have HfourN : 4*N=bpow radix2 (@common.emin t+fprec t+1).
{ unfold N. transitivity
    (bpow radix2 2*bpow radix2 (@common.emin t+fprec t-1));
    [change (bpow radix2 2) with (4:R);ring|].
  rewrite -bpow_plus. f_equal;ring. }
set ch := Fast2Mult_mul xh0 yh0.
set cl1 := Fast2Mult_err xh0 yh0.
set tl0 := BMULT xl0 yl0.
set tl1 := BFMA xh0 yl0 tl0.
set cl2 := BFMA xl0 yh0 tl1.
set cl3 := BPLUS cl1 cl2.
have Fch : is_finite ch=true by
  (unfold ch,Fast2Mult_mul,Fast2Mult,fst;exact (DWTimesDW_mul_finite xh0 xl0 yh0 yl0 FIN)).
have F0 : is_finite tl0=true by
  (unfold tl0;exact (DWTimesDW_low_low_finite xh0 xl0 yh0 yl0 FIN)).
have F1 : is_finite tl1=true by
  (unfold tl1,tl0;exact (DWTimesDW_first_correction_finite xh0 xl0 yh0 yl0 FIN)).
have F2 : is_finite cl2=true by
  (unfold cl2,tl1,tl0;exact (DWTimesDW_second_correction_finite xh0 xl0 yh0 yl0 FIN)).
have F3 : is_finite cl3=true by
  (unfold cl3,cl1,cl2,tl1,tl0;
   exact (DWTimesDW_correction_finite xh0 xl0 yh0 yl0 FIN)).
have Ffast := DWTimesDW_fast2mult_finite xh0 xl0 yh0 yl0 FIN.
have Fcl1 : is_finite cl1=true by exact (proj2 Ffast).
have Htl00 := leading_product_gap_low_low_zero
  xh0 xl0 yh0 yl0 DWx0 DWy0 F0 Hgap.
fold tl0 in Htl00.
have Hdelta := Fast2Mult_sum_error_floor xh0 yh0 ltac:(lia) Ffast.
fold P0 ch cl1 eta in Hdelta.
have H1r : FT2R tl1=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
    (FT2R xh0*FT2R yl0).
{ unfold tl1. rewrite -(BFMA_round_correct t xh0 yl0 tl0 F1) Htl00.
  f_equal;ring. }
have He1 : Rabs (FT2R tl1-FT2R xh0*FT2R yl0) <= /2*eta.
{ rewrite H1r. eapply Rle_trans.
  - apply round_FLT_error_below_binade with(k:=0%Z);
      [lia|].
    replace (@common.emin t+fprec t+0)%Z with
      (@common.emin t+fprec t)%Z by ring.
    rewrite -HtwoN. nra.
  - right. unfold eta.
    replace (@common.emin t+0)%Z with (@common.emin t) by ring.
    reflexivity. }
have HNfmt : generic_format radix2
    (SpecFloat.fexp (fprec t) (femax t)) N.
{ unfold N. apply generic_format_bpow. unfold SpecFloat.fexp,FLT_exp.
  unfold common.emin,SpecFloat.emin. lia. }
have Htl1N : Rabs (FT2R tl1) <= N.
{ rewrite H1r -round_NE_abs.
  rewrite -(round_generic radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) N HNfmt).
  apply round_le; [exact valid_fexp_inst_dh|apply valid_rnd_N|].
  eapply Rle_trans; [exact Hxhml|]. lra. }
set a2 := FT2R xl0*FT2R yh0+FT2R tl1.
have Ha2 : Rabs a2 < 2*N.
{ unfold a2. eapply Rle_lt_trans; [apply Rabs_triang|]. nra. }
have H2r : FT2R cl2=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) a2.
{ unfold cl2,a2. symmetry;exact (BFMA_round_correct t xl0 yh0 tl1 F2). }
have He2 : Rabs (FT2R cl2-a2) <= /2*eta.
{ rewrite H2r. eapply Rle_trans.
  - apply round_FLT_error_below_binade with(k:=0%Z);
      [lia|].
    replace (@common.emin t+fprec t+0)%Z with
      (@common.emin t+fprec t)%Z by ring.
    rewrite -HtwoN. exact Ha2.
  - right. unfold eta.
    replace (@common.emin t+0)%Z with (@common.emin t) by ring.
    reflexivity. }
have H2Nfmt : generic_format radix2
    (SpecFloat.fexp (fprec t) (femax t)) (2*N).
{ rewrite HtwoN. apply generic_format_bpow.
  unfold SpecFloat.fexp,FLT_exp,common.emin,SpecFloat.emin. lia. }
have Hcl2N : Rabs (FT2R cl2) <= 2*N.
{ rewrite H2r -round_NE_abs.
  rewrite -(round_generic radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) (2*N) H2Nfmt).
  apply round_le; [exact valid_fexp_inst_dh|apply valid_rnd_N|]. lra. }
have Hcl1N : Rabs (FT2R cl1) <= /2*N.
{ have Hc := Fast2Mult_accuracy_norm xh0 yh0 Fch.
  fold cl1 P0 in Hc.
  have HgapP : Rabs P0 <
      bpow radix2 (@common.emin t+fprec t+(fprec t-1)).
  { change (P < T) in Hgap. unfold T in Hgap.
    replace (@common.emin t+fprec t+(fprec t-1))%Z with
      (@common.emin t+2*fprec t-1)%Z by ring.
    exact Hgap. }
  have Hb := half_ulp_FLT_below_binade
    (t:=t) P0 (fprec t-1) ltac:(lia) HgapP.
  unfold N. eapply Rle_trans; [exact Hc|].
  replace (@common.emin t+fprec t-1)%Z with
    (@common.emin t+(fprec t-1))%Z by ring.
  exact Hb. }
set a3 := FT2R cl1+FT2R cl2.
have Ha3 : Rabs a3 < 4*N.
{ unfold a3. eapply Rle_lt_trans; [apply Rabs_triang|]. nra. }
have H3r : FT2R cl3=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) a3.
{ unfold cl3,a3. symmetry;exact (BPLUS_round_correct t cl1 cl2 F3). }
have He3 : Rabs (FT2R cl3-a3) <= eta.
{ rewrite H3r.
  have H := round_FLT_error_below_binade
    (t:=t) a3 1%Z ltac:(lia)
      ltac:(replace (@common.emin t+fprec t+1)%Z with
        (@common.emin t+fprec t+1)%Z by ring;
        rewrite -HfourN;exact Ha3).
  eapply Rle_trans; [exact H|]. unfold eta.
  rewrite (bpow_plus radix2 (@common.emin t) 1).
  change (bpow radix2 1) with (2:R). ring_simplify; lra. }
have H4Nfmt : generic_format radix2
    (SpecFloat.fexp (fprec t) (femax t)) (4*N).
{ rewrite HfourN. apply generic_format_bpow.
  unfold SpecFloat.fexp,FLT_exp,common.emin,SpecFloat.emin. lia. }
have Hcl3N : Rabs (FT2R cl3) <= 4*N.
{ rewrite H3r -round_NE_abs.
  rewrite -(round_generic radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) (4*N) H4Nfmt).
  apply round_le; [exact valid_fexp_inst_dh|apply valid_rnd_N|]. lra. }
have Herr : Rabs ((FT2R ch+FT2R cl3)-X*M) <=
    5/2*eta+u^2*P.
{ fold ch in Hdelta.
  set A := FT2R ch+FT2R cl1-P0.
  set B := -FT2R xl0*FT2R yl0.
  set C := FT2R tl1-FT2R xh0*FT2R yl0.
  set D := FT2R cl2-a2.
  set E := FT2R cl3-a3.
  have Heq : (FT2R ch+FT2R cl3)-X*M = A+B+C+D+E.
  { unfold A,B,C,D,E,X,M,a2,a3,P0. ring. }
  rewrite Heq.
  have Ht1 := Rabs_triang (A+B+C+D) E.
  have Ht2 := Rabs_triang (A+B+C) D.
  have Ht3 := Rabs_triang (A+B) C.
  have Ht4 := Rabs_triang A B.
  have Htri : Rabs (A+B+C+D+E) <=
      Rabs A+Rabs B+Rabs C+Rabs D+Rabs E.
  { eapply Rle_trans; [exact Ht1|]. apply Rplus_le_compat_r.
    eapply Rle_trans; [exact Ht2|]. apply Rplus_le_compat_r.
    eapply Rle_trans; [exact Ht3|]. apply Rplus_le_compat_r.
    exact Ht4. }
  have Hlow : Rabs B <= u^2*P
    by unfold B; replace (-FT2R xl0*FT2R yl0) with (-(FT2R xl0*FT2R yl0)) by ring;
       rewrite Rabs_Ropp;exact Hxlml.
  fold A in Hdelta. fold C in He1. fold D in He2. fold E in He3.
  eapply Rle_trans; [exact Htri|].
  eapply Rle_trans.
  - apply Rplus_le_compat; [|exact He3].
    apply Rplus_le_compat; [|exact He2].
    apply Rplus_le_compat; [|exact He1].
    apply Rplus_le_compat; [exact Hdelta|exact Hlow].
  - ring_simplify. lra. }
exact Herr.
Qed.

(* Bridge: the output pair of Algorithm 12 IS the closing Fast2Sum of
   (ch, cl3), so a preservation of the sum fact about that Fast2Sum transfers to
   the algorithm's output.  Pure definitional unfolding. *)
Local Lemma DWTimesDW_double_word_of_sum (xh0 xl0 yh0 yl0 : ftype t) :
  is_finite_p (DWTimesDW xh0 xl0 yh0 yl0) ->
  let ch := Fast2Mult_mul xh0 yh0 in
  let cl3 := BPLUS (Fast2Mult_err xh0 yh0)
                   (BFMA xl0 yh0 (BFMA xh0 yl0 (BMULT xl0 yl0))) in
  FT2R (fst (DWTimesDW xh0 xl0 yh0 yl0))+
  FT2R (snd (DWTimesDW xh0 xl0 yh0 yl0)) =
    FT2R ch+FT2R cl3 ->
  double_word_prop (fst (DWTimesDW xh0 xl0 yh0 yl0))
                   (snd (DWTimesDW xh0 xl0 yh0 yl0)).
Proof.
move => FIN ch cl3 Hsum.
set d := DWTimesDW xh0 xl0 yh0 yl0.
fold d in Hsum, FIN.
unfold double_word_prop, rounded. fold d. rewrite Hsum.
have Hfst : fst d=BPLUS ch cl3 by reflexivity.
rewrite Hfst. symmetry. apply BPLUS_round_correct.
rewrite -Hfst. exact (proj1 FIN).
Qed.

(* Two magnitude bounds on the closing Fast2Sum's arguments, in relative form
   (multiples of u*P and eta rather than of N).  They are coarser than the
   core chain's bounds in N form, but being expressed in u*P they make the
   ordering test of DWTimesDW_error_floor_gap a single crossing computation
   instead of the bootstrap with two steps that bounds in N form would force:
   |cl3| <= 6uP+4eta against |ch| >= (1-u)P-eta/2 cross only below P ~ 6*eta.

   Separate lemmas rather than inline [have]s so each nonlinear step runs
   against a small context; nra does not cope with the about twenty hypotheses
   in scope inside the gap theorem. *)
Lemma gap_ch_lower_bound (xh0 yh0 : ftype t) :
  is_finite (BMULT xh0 yh0)=true ->
  (1-u)*Rabs (FT2R xh0*FT2R yh0)-/2*bpow radix2 (common.emin (t:=t))
    <= Rabs (FT2R (Fast2Mult_mul xh0 yh0)).
Proof.
move => Fch.
set u' := bpow radix2 (-fprec t).
set eta := bpow radix2 (common.emin (t:=t)).
set P0 := (FT2R xh0*FT2R yh0)%R.
set P := Rabs P0.
set ch := Fast2Mult_mul xh0 yh0.
have Hchr : FT2R ch=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) P0.
{ unfold ch,Fast2Mult_mul,Fast2Mult,fst. symmetry.
  exact (BMULT_round_correct t xh0 yh0 Fch). }
have Hcherr := round_FLT_error_rel_emin (t:=t) P0.
fold u' eta in Hcherr. rewrite -Hchr in Hcherr. fold P in Hcherr.
have Hrev := Rabs_triang_inv P0 (P0-FT2R ch).
replace (P0-(P0-FT2R ch))%R with (FT2R ch) in Hrev by ring.
fold P in Hrev.
replace (P0-FT2R ch)%R with (-(FT2R ch-P0))%R in Hrev by ring.
rewrite Rabs_Ropp in Hrev. lra.
Qed.

Local Lemma gap_cl1_upper_bound (xh0 yh0 : ftype t) :
  (3 <= fprec t)%Z ->
  is_finite_p (Fast2Mult xh0 yh0) ->
  Rabs (FT2R (Fast2Mult_err xh0 yh0))
    <= u*Rabs (FT2R xh0*FT2R yh0)+bpow radix2 (common.emin (t:=t)).
Proof.
move => Hp3 Ffast.
have Fch : is_finite (BMULT xh0 yh0)=true by exact (proj1 Ffast).
set u' := bpow radix2 (-fprec t).
set eta := bpow radix2 (common.emin (t:=t)).
set P0 := (FT2R xh0*FT2R yh0)%R.
set P := Rabs P0.
set ch := Fast2Mult_mul xh0 yh0.
set cl1 := Fast2Mult_err xh0 yh0.
have Hdelta := Fast2Mult_sum_error_floor xh0 yh0 Hp3 Ffast.
fold P0 ch cl1 eta in Hdelta.
have Hchr : FT2R ch=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice) P0.
{ unfold ch,Fast2Mult_mul,Fast2Mult,fst. symmetry.
  exact (BMULT_round_correct t xh0 yh0 Fch). }
have Hcherr := round_FLT_error_rel_emin (t:=t) P0.
fold u' eta in Hcherr. rewrite -Hchr in Hcherr. fold P in Hcherr.
have Htri := Rabs_triang (FT2R ch+FT2R cl1-P0) (P0-FT2R ch).
replace (FT2R ch+FT2R cl1-P0+(P0-FT2R ch))%R with (FT2R cl1)%R
  in Htri by ring.
replace (P0-FT2R ch)%R with (-(FT2R ch-P0))%R in Htri by ring.
rewrite Rabs_Ropp in Htri. lra.
Qed.

(* |cl3| <= 6uP + 4eta.  Each node's rounding costs a relative u factor plus
   eta/2; in the gap tl0 = 0, so only three products enter.  u <= /32 turns
   every u*(u*P) term into (u*P)/32, which keeps the whole computation linear
   in the two atoms u*P and eta. *)
Lemma gap_cl3_upper_bound (xh0 xl0 yh0 yl0 : ftype t) :
  (5 <= fprec t)%Z ->
  double_word_prop xh0 xl0 -> double_word_prop yh0 yl0 ->
  is_finite_p (DWTimesDW xh0 xl0 yh0 yl0) ->
  Rabs (FT2R xh0*FT2R yh0) <
    bpow radix2 (common.emin (t:=t)+2*fprec t-1) ->
  Rabs (FT2R (BPLUS (Fast2Mult_err xh0 yh0)
                    (BFMA xl0 yh0 (BFMA xh0 yl0 (BMULT xl0 yl0)))))
    <= 6*u*Rabs (FT2R xh0*FT2R yh0)+
       4*bpow radix2 (common.emin (t:=t)).
Proof.
move => Hp5 DWx0 DWy0 FIN Hgap.
have Hp3 : (3 <= fprec t)%Z by lia.
set u' := bpow radix2 (-fprec t).
set eta := bpow radix2 (common.emin (t:=t)).
set P0 := (FT2R xh0*FT2R yh0)%R.
set P := Rabs P0.
set cl1 := Fast2Mult_err xh0 yh0.
set tl0 := BMULT xl0 yl0.
set tl1 := BFMA xh0 yl0 tl0.
set cl2 := BFMA xl0 yh0 tl1.
set cl3 := BPLUS cl1 cl2.
have Hu0 : 0 < u' by (unfold u';apply bpow_gt_0).
have Hu : u' <= /32.
{ unfold u'. have -> : (/32:R)=bpow radix2 (-5) by (simpl;lra).
  apply bpow_le; lia. }
have Heta0 : 0 < eta by (unfold eta;apply bpow_gt_0).
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have HuP0 : 0 <= u'*P by nra.
have F0 : is_finite tl0=true by
  (unfold tl0;exact (DWTimesDW_low_low_finite xh0 xl0 yh0 yl0 FIN)).
have F1 : is_finite tl1=true by
  (unfold tl1,tl0;exact (DWTimesDW_first_correction_finite xh0 xl0 yh0 yl0 FIN)).
have F2 : is_finite cl2=true by
  (unfold cl2,tl1,tl0;exact (DWTimesDW_second_correction_finite xh0 xl0 yh0 yl0 FIN)).
have F3 : is_finite cl3=true by
  (unfold cl3,cl1,cl2,tl1,tl0;exact (DWTimesDW_correction_finite xh0 xl0 yh0 yl0 FIN)).
have Ffast := DWTimesDW_fast2mult_finite xh0 xl0 yh0 yl0 FIN.
(* the two cross products, each at most u*P *)
have Hxl := @dw_low_le_u_high t STD xh0 xl0 DWx0.
have Hml := @dw_low_le_u_high t STD yh0 yl0 DWy0.
fold u' in Hxl,Hml.
have Hxhyl : Rabs (FT2R xh0*FT2R yl0) <= u'*P.
{ unfold P,P0. rewrite !Rabs_mult.
  have H := Rmult_le_compat_l (Rabs (FT2R xh0)) _ _
    (Rabs_pos _) Hml. eapply Rle_trans; [exact H|]. right;ring. }
have Hxlyh : Rabs (FT2R xl0*FT2R yh0) <= u'*P.
{ unfold P,P0. rewrite !Rabs_mult.
  have H := Rmult_le_compat_r (Rabs (FT2R yh0)) _ _
    (Rabs_pos _) Hxl. eapply Rle_trans; [exact H|]. right;ring. }
(* |cl1| <= uP + eta *)
have Hcl1 := gap_cl1_upper_bound xh0 yh0 Hp3 Ffast.
fold u' eta P0 P cl1 in Hcl1.
(* tl0 = 0 in the gap *)
have Htl00 := leading_product_gap_low_low_zero
  xh0 xl0 yh0 yl0 DWx0 DWy0 F0 Hgap.
fold tl0 in Htl00.
(* |tl1| <= 2uP + eta *)
have H1r : FT2R tl1=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
    (FT2R xh0*FT2R yl0).
{ unfold tl1. rewrite -(BFMA_round_correct t xh0 yl0 tl0 F1) Htl00.
  f_equal;ring. }
have Htl1 : Rabs (FT2R tl1) <= 2*(u'*P)+eta.
{ have He := round_FLT_error_rel_emin (t:=t) (FT2R xh0*FT2R yl0).
  fold u' eta in He. rewrite -H1r in He.
  have Htri := Rabs_triang (FT2R tl1-FT2R xh0*FT2R yl0)
    (FT2R xh0*FT2R yl0).
  replace (FT2R tl1-FT2R xh0*FT2R yl0+FT2R xh0*FT2R yl0)%R
    with (FT2R tl1)%R in Htri by ring.
  have HuA : u'*Rabs (FT2R xh0*FT2R yl0) <= /32*(u'*P).
  { eapply Rle_trans.
    - apply Rmult_le_compat_r; [apply Rabs_pos|exact Hu].
    - apply Rmult_le_compat_l; [lra|exact Hxhyl]. }
  lra. }
(* |cl2| <= 4uP + 2eta *)
have H2r : FT2R cl2=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
    (FT2R xl0*FT2R yh0+FT2R tl1).
{ unfold cl2. symmetry;exact (BFMA_round_correct t xl0 yh0 tl1 F2). }
have Hcl2 : Rabs (FT2R cl2) <= 4*(u'*P)+2*eta.
{ set a2 := (FT2R xl0*FT2R yh0+FT2R tl1)%R.
  have Ha2 : Rabs a2 <= 3*(u'*P)+eta.
  { unfold a2. eapply Rle_trans; [apply Rabs_triang|]. lra. }
  have Ha20 : 0 <= Rabs a2 by apply Rabs_pos.
  have He := round_FLT_error_rel_emin (t:=t) a2.
  fold u' eta in He. rewrite -H2r in He.
  have Htri := Rabs_triang (FT2R cl2-a2) a2.
  replace (FT2R cl2-a2+a2)%R with (FT2R cl2)%R in Htri by ring.
  have HuA : u'*Rabs a2 <= /32*(3*(u'*P)+eta).
  { eapply Rle_trans.
    - apply Rmult_le_compat_r; [exact Ha20|exact Hu].
    - apply Rmult_le_compat_l; [lra|exact Ha2]. }
  lra. }
(* |cl3| <= 6uP + 4eta *)
have H3r : FT2R cl3=round radix2
    (SpecFloat.fexp (fprec t) (femax t)) (Znearest choice)
    (FT2R cl1+FT2R cl2).
{ unfold cl3. symmetry;exact (BPLUS_round_correct t cl1 cl2 F3). }
set a3 := (FT2R cl1+FT2R cl2)%R.
have Ha3 : Rabs a3 <= 5*(u'*P)+3*eta.
{ unfold a3. eapply Rle_trans; [apply Rabs_triang|]. lra. }
have Ha30 : 0 <= Rabs a3 by apply Rabs_pos.
have He := round_FLT_error_rel_emin (t:=t) a3.
fold u' eta in He. rewrite -H3r in He.
have Htri := Rabs_triang (FT2R cl3-a3) a3.
replace (FT2R cl3-a3+a3)%R with (FT2R cl3)%R in Htri by ring.
have HuA : u'*Rabs a3 <= /32*(5*(u'*P)+3*eta).
{ eapply Rle_trans.
  - apply Rmult_le_compat_r; [exact Ha30|exact Hu].
  - apply Rmult_le_compat_l; [lra|exact Ha3]. }
have Hgoal : 6*u'*P = 6*(u'*P) by ring.
rewrite Hgoal. lra.
Qed.

(* Mixed error and output validity for Algorithm 12 in the [Fast2Mult] gap.
   If [|cl3| <= |ch|], [FastTwoSum_correct] preserves the sum.  Otherwise the
   leading product is small enough that [ch+cl3] lies on the shared FLT/FIX
   lattice, and [Fast2Sum_sum_exact_of_sum_small] preserves it.  The core
   contributes the full [5/2*eta] floor term. *)
Lemma DWTimesDW_error_floor_gap (xh0 xl0 yh0 yl0 : ftype t) :
  (5 <= fprec t)%Z ->
  double_word_prop xh0 xl0 -> double_word_prop yh0 yl0 ->
  is_finite_p (DWTimesDW xh0 xl0 yh0 yl0) ->
  Rabs (FT2R xh0*FT2R yh0) <
    bpow radix2 (common.emin (t:=t)+2*fprec t-1) ->
  Rabs ((FT2R (fst (DWTimesDW xh0 xl0 yh0 yl0))+
         FT2R (snd (DWTimesDW xh0 xl0 yh0 yl0)))-
        (FT2R xh0+FT2R xl0)*(FT2R yh0+FT2R yl0))
    <= 5/2*bpow radix2 (common.emin (t:=t))+
       u^2*Rabs (FT2R xh0*FT2R yh0) /\
  double_word_prop (fst (DWTimesDW xh0 xl0 yh0 yl0))
                   (snd (DWTimesDW xh0 xl0 yh0 yl0)).
Proof.
move => Hp5 DWx0 DWy0 FIN Hgap.
have Hp3 : (3 <= fprec t)%Z by lia.
have Hcore := DWTimesDW_core_error_floor_gap xh0 xl0 yh0 yl0
  Hp3 DWx0 DWy0 FIN Hgap.
have Hchlo0 := gap_ch_lower_bound xh0 yh0 (DWTimesDW_mul_finite xh0 xl0 yh0 yl0 FIN).
have Hcl30 := gap_cl3_upper_bound xh0 xl0 yh0 yl0 Hp5 DWx0 DWy0 FIN Hgap.
set d := DWTimesDW xh0 xl0 yh0 yl0.
set u' := bpow radix2 (-fprec t).
set eta := bpow radix2 (common.emin (t:=t)).
set P0 := (FT2R xh0*FT2R yh0)%R.
set P := Rabs P0.
set X := (FT2R xh0+FT2R xl0)%R.
set M := (FT2R yh0+FT2R yl0)%R.
set ch := Fast2Mult_mul xh0 yh0.
set cl1 := Fast2Mult_err xh0 yh0.
set tl0 := BMULT xl0 yl0.
set tl1 := BFMA xh0 yl0 tl0.
set cl2 := BFMA xl0 yh0 tl1.
set cl3 := BPLUS cl1 cl2.
fold u' eta P0 P X M ch cl1 tl0 tl1 cl2 cl3 in Hcore.
fold u' eta P0 P ch in Hchlo0.
fold u' eta P0 P cl1 tl0 tl1 cl2 cl3 in Hcl30.
have Hu0 : 0 < u' by (unfold u';apply bpow_gt_0).
have Hu : u' <= /32.
{ unfold u'. have -> : (/32:R)=bpow radix2 (-5) by (simpl;lra).
  apply bpow_le; lia. }
have Heta0 : 0 < eta by (unfold eta;apply bpow_gt_0).
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have Fe : is_finite_p (Fast2Sum ch cl3).
{ unfold d, DWTimesDW in FIN. fold ch cl1 tl0 tl1 cl2 cl3 in FIN.
  exact FIN. }
destruct (Rle_dec (Rabs (FT2R cl3)) (Rabs (FT2R ch))) as [Hord|Hnord].
- (* ordered: the closing Fast2Sum pair reconstructs the sum exactly in FLT,
     including for subnormal values *)
  have Hsum := FastTwoSum_correct ch cl3 (proj1 Fe) Hord.
  change (FT2R (snd d)=FT2R ch+FT2R cl3-FT2R (fst d)) in Hsum.
  have HsumE : FT2R (fst d)+FT2R (snd d)=FT2R ch+FT2R cl3
    by (rewrite Hsum;ring).
  split.
  + rewrite HsumE. exact Hcore.
  + exact (Fast2Sum_is_DW ch cl3 (proj1 Fe) Hord).
- (* Unordered closing Fast2Sum.  |cl3| > |ch| can only happen when the
     leading product is tiny: |cl3| <= 6uP+4eta while |ch| >= (1-u)P-eta/2,
     and at u <= /32 those cross only below 6*eta, so P < 6*eta.  The exact
     sum ch+cl3 is then bounded using the compensated core error -- not by
     the triangle inequality on |ch| and |cl3| separately, which would
     overshoot -- and the shared FLT/FIX lattice at exponent emin makes
     Fast2Sum exact there, with no ordering and no precision hypothesis. *)
  have HuP' : u'*P <= /32*P.
  { have H := Rmult_le_compat_r P _ _ HP0 Hu. nra. }
  have HsmallP : P < 6*eta.
  { apply Rnot_le_lt. move => HPbig.
    have Hcontra : Rabs (FT2R cl3) <= Rabs (FT2R ch).
    { eapply Rle_trans; [exact Hcl30|]. eapply Rle_trans; [|exact Hchlo0].
      have H6 : 6*u'*P = 6*(u'*P) by ring.
      rewrite H6. nra. }
    exact (Hnord Hcontra). }
  have HXM : Rabs (X*M) <= (1+u')^2*P.
  { have Hxl := @dw_low_le_u_high t STD xh0 xl0 DWx0.
    have Hml := @dw_low_le_u_high t STD yh0 yl0 DWy0.
    fold u' in Hxl,Hml.
    have Hx : Rabs X <= (1+u')*Rabs (FT2R xh0).
    { unfold X. eapply Rle_trans; [apply Rabs_triang|]. nra. }
    have Hy : Rabs M <= (1+u')*Rabs (FT2R yh0).
    { unfold M. eapply Rle_trans; [apply Rabs_triang|]. nra. }
    have H := Rmult_le_compat _ _ _ _ (Rabs_pos _) (Rabs_pos _) Hx Hy.
    rewrite Rabs_mult. eapply Rle_trans; [exact H|].
    unfold P,P0. rewrite Rabs_mult. right;ring. }
  have Hu2P : u'^2*P <= /1024*P.
  { have H : (u'^2 <= /1024)%R by nra.
    have H2 := Rmult_le_compat_r P _ _ HP0 H. nra. }
  have Hbig16 : 16*eta <= bpow radix2 (common.emin (t:=t)+fprec t).
  { unfold eta. have -> : (16:R)=bpow radix2 4 by (simpl;lra).
    rewrite -bpow_plus. apply bpow_le; lia. }
  have Hsumsmall : Rabs (FT2R ch+FT2R cl3) <=
      bpow radix2 (common.emin (t:=t)+fprec t).
  { have Htri2 := Rabs_triang ((FT2R ch+FT2R cl3)-X*M) (X*M).
    replace ((FT2R ch+FT2R cl3)-X*M+X*M)%R with (FT2R ch+FT2R cl3)%R
      in Htri2 by ring.
    have Hstep : Rabs (FT2R ch+FT2R cl3) <= 5/2*eta+u'^2*P+(1+u')^2*P.
    { eapply Rle_trans; [exact Htri2|].
      apply Rplus_le_compat; [exact Hcore|exact HXM]. }
    (* 2.5*eta + P/1024 + (1+u)^2*P < 2.5*eta + 6.4*eta < 16*eta *)
    have Hexp : (1+u')^2*P = P+(2*u'*P+u'^2*P) by ring.
    have Hstep2 : 5/2*eta+u'^2*P+(1+u')^2*P <= 16*eta.
    { rewrite Hexp. nra. }
    eapply Rle_trans; [exact Hstep|].
    eapply Rle_trans; [exact Hstep2|exact Hbig16]. }
  have Hsum := Fast2Sum_sum_exact_of_sum_small ch cl3 Fe Hsumsmall.
  change (FT2R (fst d)+FT2R (snd d)=FT2R ch+FT2R cl3) in Hsum.
  split.
  + rewrite Hsum. exact Hcore.
  + exact (DWTimesDW_double_word_of_sum xh0 xl0 yh0 yl0 FIN Hsum).
Qed.

(** Common proof near the threshold.  The numerical premise records exactly how
    much of the physical floor is available after the [4u^2] relative term. *)
Local Lemma DWTimesDW_abs_normal_near_threshold_core
    (floor_coeff : R) :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  bpow radix2 (eminA+2*fprec t-1) <=
    Rabs (FT2R xh*FT2R yh) ->
  Rabs (FT2R xh*FT2R yh) <=
    9/8*bpow radix2 (eminA+2*fprec t-1) ->
  (15/2-4*(1-u)^2)*(9/8) <= 2*floor_coeff ->
  Rabs (zh+zl-xr*yr) <=
    4*u^2*Rabs (xr*yr)+floor_coeff*bpow radix2 eminA.
Proof.
move => DWx DWy FIN Hp5 Nprod Pnear Hcoef.
have Hp3 : (3 <= fprec t)%Z by lia.
have Fmul := DWTimesDW_mul_finite xh xl yh yl FIN.
have F0 := DWTimesDW_low_low_finite xh xl yh yl FIN.
have F1 := DWTimesDW_first_correction_finite xh xl yh yl FIN.
have F2 := DWTimesDW_second_correction_finite xh xl yh yl FIN.
have F3 := DWTimesDW_correction_finite xh xl yh yl FIN.
have HerrEq := relerr_error_eq xh xl yh yl Hp3 DWx DWy FIN Fmul Nprod.
have HerrRaw := aux_eta_bnd xh xl yh yl Hp5 DWx DWy
  Fmul F0 F1 F2 F3 Nprod.
rewrite HerrEq.
set P := Rabs (FT2R xh*FT2R yh) in Nprod, Pnear, HerrRaw *.
set T := bpow radix2 (eminA+2*fprec t-1) in Nprod, Pnear *.
set eta := bpow radix2 eminA.
have Hu0 : 0 < u by (unfold u;apply bpow_gt_0).
have Hu : u <= /32.
{ unfold u. have -> : (/32:R)=bpow radix2 (-5) by (simpl;lra).
  apply bpow_le; lia. }
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have HT0 : 0 < T by (unfold T;apply bpow_gt_0).
have Heta0 : 0 < eta by (unfold eta;apply bpow_gt_0).
have Hscale : u^2*T=/2*eta.
{ replace (u^2) with (u*u) by ring. unfold u,T,eta.
  rewrite -(bpow_plus radix2 (-fprec t) (-fprec t)).
  rewrite -(bpow_plus radix2 (-fprec t+-fprec t)
    (eminA+2*fprec t-1)).
  replace (-fprec t+-fprec t+(eminA+2*fprec t-1))%Z with
    (eminA-1)%Z by ring.
  rewrite (bpow_plus radix2 eminA (-1)).
  change (bpow radix2 (-1)) with (/2:R). ring. }
have Hprod := aux_dw_exact_product_lower xh xl yh yl DWx DWy.
specialize (Hprod STD). fold u xr yr P in Hprod.
have Hpaperpart : 4*u^2*((1-u)^2*P) <=
    4*u^2*Rabs (xr*yr).
{ apply Rmult_le_compat_l; [nra|exact Hprod]. }
eapply Rle_trans; [exact HerrRaw|].
eapply Rle_trans; [|apply Rplus_le_compat_r;exact Hpaperpart].
have HnearScaled := Rmult_le_compat_l (u^2) _ _
  (pow2_ge_0 u) Pnear.
have Hbudget : 15/2*u^2*P <=
    4*u^2*((1-u)^2*P)+floor_coeff*eta.
{ have Hnonneg : 0 <= 15/2-4*(1-u)^2 by nra.
  have Hstep := Rmult_le_compat_l
    (15/2-4*(1-u)^2) _ _ Hnonneg HnearScaled.
  nra. }
replace (u*u) with (u^2) by ring. exact Hbudget.
Qed.

(* At the sharper [2*eta] floor, the budget near the threshold requires p >= 8. *)
Theorem DWTimesDW_abs_normal_near_threshold :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW xh xl yh yl) ->
  (8 <= fprec t)%Z ->
  bpow radix2 (eminA+2*fprec t-1) <=
    Rabs (FT2R xh*FT2R yh) ->
  Rabs (FT2R xh*FT2R yh) <=
    9/8*bpow radix2 (eminA+2*fprec t-1) ->
  Rabs (zh+zl-xr*yr) <=
    4*u^2*Rabs (xr*yr)+2*bpow radix2 eminA.
Proof.
move => DWx DWy FIN Hp8 Nprod Pnear.
eapply (DWTimesDW_abs_normal_near_threshold_core 2);
  [exact DWx | exact DWy | exact FIN | lia | exact Nprod | exact Pnear |].
have Hu0 : 0 < u by (unfold u;apply bpow_gt_0).
have Hu : u <= /256.
{ unfold u. have -> : (/256:R)=bpow radix2 (-8) by (simpl;lra).
  apply bpow_le; lia. }
nra.
Qed.

(* The [5/2*eta] mixed floor leaves enough budget already at p >= 5. *)
Local Theorem DWTimesDW_abs_normal_near_threshold_floor52 :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  bpow radix2 (eminA+2*fprec t-1) <=
    Rabs (FT2R xh*FT2R yh) ->
  Rabs (FT2R xh*FT2R yh) <=
    9/8*bpow radix2 (eminA+2*fprec t-1) ->
  Rabs (zh+zl-xr*yr) <=
    4*u^2*Rabs (xr*yr)+5/2*bpow radix2 eminA.
Proof.
move => DWx DWy FIN Hp5 Nprod Pnear.
eapply (DWTimesDW_abs_normal_near_threshold_core (5/2));
  [exact DWx | exact DWy | exact FIN | exact Hp5 |
   exact Nprod | exact Pnear |].
have Hu0 : 0 < u by (unfold u;apply bpow_gt_0).
have Hu : u <= /32.
{ unfold u. have -> : (/32:R)=bpow radix2 (-5) by (simpl;lra).
  apply bpow_le; lia. }
nra.
Qed.

(** Absolute form of the existing multiplication estimate independent of the regime
    on the normal leading branch.  This is used only for the pure relative
    fallback outside the regimes covered by the sharp paper result with a floor. *)
Theorem DWTimesDW_abs_low0_low1_low2_final_normal :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  bpow radix2 (eminA+2*fprec t-1) <=
    Rabs (FT2R xh*FT2R yh) ->
  Rabs (FT2R xl*FT2R yl) < bpow radix2 (eminA+fprec t-1) ->
  Rabs (FT2R xh*FT2R yl+FT2R (BMULT xl yl)) <
    bpow radix2 (eminA+fprec t-1) ->
  Rabs (FT2R xl*FT2R yh+
    FT2R (BFMA xh yl (BMULT xl yl))) <
    bpow radix2 (eminA+fprec t-1) ->
  bpow radix2 (eminA+fprec t-1) <=
    Rabs (FT2R (Fast2Mult_err xh yh)+
      FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) ->
  Rabs (zh+zl-xr*yr) <=
    4*u^2*Rabs (xr*yr)+2*bpow radix2 eminA.
Proof.
move => DWx DWy FIN Hp5 Nprod N0 N1 N2 N3.
have Hp3 : (3 <= fprec t)%Z by lia.
have Fmul := DWTimesDW_mul_finite xh xl yh yl FIN.
have H := relerr_error_relative_floor_decomposition xh xl yh yl
  Hp3 DWx DWy FIN Fmul Nprod.
destruct H as
  (er0 & er1 & er2 & er3 & ef0 & ef1 & ef2 & ef3 &
   Heq & R0 & R1 & R2 & R3 & F0b & F1b & F2b & F3b & Hef &
   ER1 & ER2 & ER3 & ER1f & ER2f & ER3f &
   Z0 & Z1 & Z2 & Z3 & G0 & G1 & G2 & G3 &
   T0 & T1 & T2 & S0 & S1 & S2 & S3).
destruct G0 as [[Ef0 N0normal]|[Er0 N0small]].
{ exfalso; exact (Rlt_not_le _ _ N0 N0normal). }
destruct G1 as [[Ef1 N1normal]|[Er1 N1small]].
{ exfalso; exact (Rlt_not_le _ _ N1 N1normal). }
destruct G2 as [[Ef2 N2normal]|[Er2 N2small]].
{ exfalso; exact (Rlt_not_le _ _ N2 N2normal). }
destruct G3 as [[Ef3 N3normal]|[Er3 N3small]].
2:{ exfalso; exact (Rlt_not_le _ _ N3small N3). }
subst er0; subst er1; subst er2; subst ef3.
set P := Rabs (FT2R xh*FT2R yh).
set eta := bpow radix2 eminA.
set U := bpow radix2 (eminA+fprec t-1).
have Hu0 : 0 < u by (unfold u;apply bpow_gt_0).
have Hu : u <= /32.
{ unfold u. have -> : (/32:R)=bpow radix2 (-5) by (simpl;lra).
  apply bpow_le;lia. }
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have Heta0 : 0 < eta by (unfold eta;apply bpow_gt_0).
have Hcl1u : Rabs (FT2R (Fast2Mult_err xh yh)) <=
    /2*ulp (FT2R xh*FT2R yh)
  by (apply Fast2Mult_accuracy_norm;exact Fmul).
have Hulp : ulp (FT2R xh*FT2R yh) <=
    P*bpow radix2 (1-fprec t).
{ unfold P. apply ulp_FLT_le.
  eapply Rle_trans; [|exact Nprod]. apply bpow_le.
  unfold eminA, common.emin, SpecFloat.emin.
  pose proof fprec_lb t. lia. }
have HBp : bpow radix2 (1-fprec t)=2*u.
{ unfold u.
  change (bpow radix2 (1-fprec t)=
    bpow radix2 1*bpow radix2 (-fprec t)).
  rewrite -(bpow_plus radix2 1 (-fprec t)). f_equal;lia. }
have Hcl1 : Rabs (FT2R (Fast2Mult_err xh yh)) <= u*P.
{ rewrite HBp in Hulp. nra. }
have HUscale : u*U=/2*eta.
{ unfold u,U,eta. rewrite -(bpow_plus radix2 (-fprec t)
    (eminA+fprec t-1)).
  replace (-fprec t+(eminA+fprec t-1))%Z with (eminA-1)%Z by ring.
  rewrite (bpow_plus radix2 eminA (-1)).
  change (bpow radix2 (-1)) with (/2:R). ring. }
have Hscale : u^2*bpow radix2 (eminA+2*fprec t-1)=/2*eta.
{ replace (u^2) with (u*u) by ring. unfold u,eta.
  rewrite -(bpow_plus radix2 (-fprec t) (-fprec t)).
  rewrite -(bpow_plus radix2 (-fprec t+-fprec t)
    (eminA+2*fprec t-1)).
  replace (-fprec t+-fprec t+(eminA+2*fprec t-1))%Z with
    (eminA-1)%Z by ring.
  rewrite (bpow_plus radix2 eminA (-1)).
  change (bpow radix2 (-1)) with (/2:R). ring. }
have HetaP : eta <= 2*u^2*P.
{ have Hs := Rmult_le_compat_l (u^2) _ _ (pow2_ge_0 u) Nprod.
  rewrite Hscale in Hs. fold P in Hs.
  apply (Rmult_le_reg_l (/2)); [lra|].
  eapply Rle_trans; [exact Hs|]. nra. }
fold P eta U in N2small,F0b,F1b,F2b,ER3.
replace (FT2R (Fast2Mult_err xh yh)+FT2R xl*FT2R yh+
  FT2R xh*FT2R yl+FT2R xl*FT2R yl+0+0+0)%R with
  (FT2R (Fast2Mult_err xh yh)+FT2R xl*FT2R yh+
   FT2R xh*FT2R yl+FT2R xl*FT2R yl)%R in ER3 by ring.
have HEF01 : Rabs (ef0+ef1) <= eta.
{ eapply Rle_trans; [apply Rabs_triang|]. nra. }
have HEF012 : Rabs (ef0+ef1+ef2) <= 3/2*eta.
{ have Ht := Rabs_triang (ef0+ef1) ef2.
  eapply Rle_trans; [exact Ht|]. nra. }
have HT1 : FT2R (BFMA xh yl (BMULT xl yl))=
    FT2R xh*FT2R yl+FT2R xl*FT2R yl+(ef0+ef1) by nra.
have Hcorr : Rabs (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
    FT2R xl*FT2R yl) <= U+eta.
{ have Hinput :
      Rabs ((FT2R xl*FT2R yh+
        FT2R (BFMA xh yl (BMULT xl yl)))+(-(ef0+ef1))) <=
      Rabs (FT2R xl*FT2R yh+
        FT2R (BFMA xh yl (BMULT xl yl)))+Rabs (-(ef0+ef1))
      := Rabs_triang _ _.
  pose proof (@Hinput NANS STD NANS STD) as Hinput0.
  replace ((FT2R xl*FT2R yh+
    FT2R (BFMA xh yl (BMULT xl yl)))+(-(ef0+ef1)))%R with
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+
      FT2R xl*FT2R yl)%R in Hinput0.
  2:{ replace (FT2R (BFMA xh yl (BMULT xl yl))) with
        (FT2R xh*FT2R yl+FT2R xl*FT2R yl+(ef0+ef1))
        by (symmetry;exact HT1). ring. }
  rewrite Rabs_Ropp in Hinput0.
  eapply Rle_trans; [exact Hinput0|]. lra. }
have Hcentral3 : Rabs (FT2R (Fast2Mult_err xh yh)+
    FT2R xl*FT2R yh+FT2R xh*FT2R yl+FT2R xl*FT2R yl) <=
    u*P+U+eta.
{ have Ht := Rabs_triang (FT2R (Fast2Mult_err xh yh))
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+FT2R xl*FT2R yl).
  specialize (Ht NANS STD).
  replace (FT2R (Fast2Mult_err xh yh)+
    (FT2R xl*FT2R yh+FT2R xh*FT2R yl+FT2R xl*FT2R yl))%R with
    (FT2R (Fast2Mult_err xh yh)+FT2R xl*FT2R yh+
      FT2R xh*FT2R yl+FT2R xl*FT2R yl)%R in Ht by ring.
  eapply Rle_trans; [exact Ht|]. lra. }
have HE3 : Rabs er3 <= u^2*P+/2*eta+5/2*u*eta.
{ eapply Rle_trans; [exact ER3|].
  have Hm := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) Hcentral3.
  have Hf := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) HEF012.
  eapply Rle_trans.
  - apply Rplus_le_compat; [exact Hm|exact Hf].
  - nra. }
have Hprod := aux_dw_exact_product_lower xh xl yh yl DWx DWy.
specialize (Hprod STD). fold u xr yr P in Hprod.
have Hrel : Rabs er3 <= 4*u^2*Rabs (xr*yr)+/2*eta.
{ have Hueta := Rmult_le_compat_l u _ _ (Rlt_le _ _ Hu0) HetaP.
  have Hcoef0 : 1+5*u <= 4*(1-u)^2.
  { have H13 : 13*u <= 1 by lra.
    have Hu2pos : 0 <= u^2 by apply pow2_ge_0.
    eapply Rle_trans with (r2:=(1+5*u)+(3-13*u+4*u^2)).
    - lra.
    - apply Req_le. field. }
  have HB0 : 0 <= u^2*P by
    (apply Rmult_le_pos;[apply pow2_ge_0|exact HP0]).
  have Hcoef := Rmult_le_compat_r (u^2*P) _ _ HB0 Hcoef0.
  have Hraw : Rabs er3 <= (1+5*u)*(u^2*P)+/2*eta.
  { eapply Rle_trans; [exact HE3|].
    eapply Rle_trans with
      (r2:=u^2*P+/2*eta+5*u*(u^2*P)).
    - apply Rplus_le_compat_l.
      have H5 := Rmult_le_compat_l (5/2) _ _ ltac:(lra) Hueta.
      replace (5/2*u*eta)%R with (5/2*(u*eta))%R by field.
      replace (5*u*(u^2*P))%R with
        (5/2*(u*(2*u^2*P)))%R by field.
      exact H5.
    - apply Req_le. field. }
  have Hpaper : 4*u^2*((1-u)^2*P) <= 4*u^2*Rabs (xr*yr).
  { apply Rmult_le_compat_l; [apply Rmult_le_pos;[lra|apply pow2_ge_0]|exact Hprod]. }
  eapply Rle_trans; [exact Hraw|].
  eapply Rle_trans with (r2:=4*(1-u)^2*(u^2*P)+/2*eta).
  - apply Rplus_le_compat_r. exact Hcoef.
  - eapply Rle_trans with (r2:=4*u^2*((1-u)^2*P)+/2*eta).
    + apply Req_le. field.
    + apply Rplus_le_compat_r. exact Hpaper. }
rewrite Heq.
replace (0+0+0+er3+(ef0+ef1+ef2+0)) with
  (er3+(ef0+ef1+ef2)) by ring.
have Htri := Rabs_triang er3 (ef0+ef1+ef2).
eapply Rle_trans; [exact Htri|].
eapply Rle_trans.
- apply Rplus_le_compat; [exact Hrel|exact HEF012].
- apply Req_le. field.
Qed.

(** Whole range mixed analysis.  The normal arm retains the paper's [4u^2]
    coefficient.  Physical underflow in the low order nodes is represented
    explicitly by the [2.5 eta] term.  A separate gap lemma covers leading
    products below the Fast2Mult exactness threshold, so no normality condition
    is required by the mixed API. *)

(* ---------- public assembly: the whole range mixed API ---------- *)

(* Normal arm at the 5/2*eta floor.  The near the threshold leg uses the _floor52
   variant, so the whole tree holds at p >= 5. *)
Local Theorem DWTimesDW_error_floor_normal :
  (5 <= fprec t)%Z ->
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW xh xl yh yl) ->
  bpow radix2 (eminA+2*fprec t-1) <= Rabs (FT2R xh*FT2R yh) ->
  Rabs (zh+zl-xr*yr) <=
    4*u^2*Rabs (xr*yr)+5/2*bpow radix2 eminA.
Proof.
move => Hp5 DWx DWy FIN Nprod.
have Heta0 : 0 < bpow radix2 eminA by apply bpow_gt_0.
set T := bpow radix2 (eminA + 2 * fprec t - 1).
set N := bpow radix2 (eminA + fprec t - 1).
set P := Rabs (FT2R xh * FT2R yh).
fold T P in Nprod.
destruct (Rle_or_lt P (9 / 8 * T)) as [Hnear | Hfar].
- exact (DWTimesDW_abs_normal_near_threshold_floor52
    DWx DWy FIN Hp5 Nprod Hnear).
- have H2 : Rabs (zh+zl-xr*yr) <=
      4*u^2*Rabs (xr*yr)+2*bpow radix2 eminA.
  { destruct (Rle_or_lt N (Rabs (FT2R xl * FT2R yl))) as [N0 | U0].
    - have H := DWTimesDW_abs_low0_normal
        DWx DWy FIN ltac:(lia) Nprod N0.
      eapply Rle_trans; [exact H|]. nra.
    - destruct (Rle_or_lt N
        (Rabs (FT2R (Fast2Mult_err xh yh) +
               FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))))
        as [N3 | U3].
      + destruct (Rle_or_lt N
          (Rabs (FT2R xh * FT2R yl + FT2R (BMULT xl yl)))) as [N1 | U1].
        * destruct (Rle_or_lt N
            (Rabs (FT2R xl * FT2R yh +
                   FT2R (BFMA xh yl (BMULT xl yl))))) as [N2 | U2].
          -- exact (DWTimesDW_abs_low0_far xh xl yh yl
               DWx DWy FIN ltac:(lia) Hfar U0 N1 N2 N3).
          -- exact (DWTimesDW_abs_low0_low2_other_normal
               DWx DWy FIN ltac:(lia) Nprod U0 N1 U2 N3).
        * destruct (Rle_or_lt N
            (Rabs (FT2R xl * FT2R yh +
                   FT2R (BFMA xh yl (BMULT xl yl))))) as [N2 | U2].
          -- exact (DWTimesDW_abs_low0_low1_tail_normal
               DWx DWy FIN ltac:(lia) Nprod U0 U1 N2 N3).
          -- exact (DWTimesDW_abs_low0_low1_low2_final_normal
               DWx DWy FIN ltac:(lia) Nprod U0 U1 U2 N3).
      + exact (DWTimesDW_abs_low0_final_underflow
          DWx DWy FIN ltac:(lia) Nprod U0 U3). }
  lra.
Qed.

(* Whole range error bound.  The mixed condition places no lower bound on the
   leading product.  The gap lemma covers [P = 0] and [0 < P < T], while the
   regime tree covers [T <= P].  The resulting floor term is [5/2*eta], and
   the proof requires [p >= 5]. *)
Theorem DWTimesDW_accuracy_from_weak_pre_and_finite_post_cond :
  (5 <= fprec t)%Z ->
  DWTimesDW_weak_pre_and_finite_post_cond xh xl yh yl ->
  Rabs (zh+zl-xr*yr) <=
    4*u^2*Rabs (xr*yr)+5/2*bpow radix2 eminA.
Proof.
move => Hp5 [[DWx DWy] FIN].
destruct (Rle_or_lt (bpow radix2 (eminA+2*fprec t-1))
    (Rabs (FT2R xh*FT2R yh))) as [Nprod | Hgap].
- exact (DWTimesDW_error_floor_normal Hp5 DWx DWy FIN Nprod).
- (* gap (P = 0 included): the u^2*P residual is absorbed into 4u^2|xr*yr|
     because |xr*yr| >= (1-u)^2*P and 4*(1-u)^2 >= 1 for u <= /2. *)
  have Hgap' : Rabs (FT2R xh*FT2R yh) <
      bpow radix2 (common.emin (t:=t)+2*fprec t-1) by exact Hgap.
  have H := proj1 (DWTimesDW_error_floor_gap xh xl yh yl
    Hp5 DWx DWy FIN Hgap').
  fold zh zl xr yr in H.
  have HXM := aux_dw_exact_product_lower xh xl yh yl DWx DWy.
  specialize (HXM STD). fold u xr yr in HXM.
  set P := Rabs (FT2R xh*FT2R yh).
  set Q := Rabs (xr*yr).
  fold P in H. fold P Q in HXM. fold Q.
  have Heta : bpow radix2 (common.emin (t:=t)) = bpow radix2 eminA
    by reflexivity.
  rewrite Heta in H.
  have Hu0 : 0 < u by apply bpow_gt_0.
  have Hu : u <= /32.
  { have -> : (/32:R)=bpow radix2 (-5) by (simpl;lra).
    apply bpow_le; lia. }
  have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
  (* absorb the gap lemma's u^2*P residual into the target's 4u^2*|xr*yr|,
     using |xr*yr| >= (1-u)^2*P and 4*(1-u)^2 >= 1 at u <= /32 *)
  have Hc : 1 <= 4*(1-u)^2 by nra.
  have Hup : 0 <= u^2*P by nra.
  have H1 : u^2*P*1 <= u^2*P*(4*(1-u)^2)
    by (apply Rmult_le_compat_l; [exact Hup|exact Hc]).
  have H2 : 4*u^2*((1-u)^2*P) <= 4*u^2*Q
    by (apply Rmult_le_compat_l; [nra|exact HXM]).
  lra.
Qed.

(* Whole range output validity.  Both regimes preserve the closing Fast2Sum's sum, so
   both give the double-word property: above the threshold through the
   ordering |cl3| <= |ch| (aux_cl3_le_ch), in the gap through the small sum
   lattice argument inside DWTimesDW_error_floor_gap. *)
Theorem DWTimesDW_double_word_from_weak_pre_and_finite_post_cond :
  (5 <= fprec t)%Z ->
  DWTimesDW_weak_pre_and_finite_post_cond xh xl yh yl ->
  double_word_prop (fst (DWTimesDW xh xl yh yl))
                   (snd (DWTimesDW xh xl yh yl)).
Proof.
move => Hp5 [[DWx DWy] FIN].
have Hp3 : (3 <= fprec t)%Z by lia.
destruct (Rle_or_lt (bpow radix2 (eminA+2*fprec t-1))
    (Rabs (FT2R xh*FT2R yh))) as [Nprod | Hgap].
- have Hfp : is_finite (BPLUS (Fast2Mult_mul xh yh)
                 (BPLUS (Fast2Mult_err xh yh)
                        (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) = true
    by exact (proj1 FIN).
  destruct (BPLUS_finite_e t _ _ Hfp) as [_ Hfcl3].
  have Hfmul : is_finite (BMULT xh yh)=true
    by exact (DWTimesDW_mul_finite xh xl yh yl FIN).
  have Nprod' : bpow radix2 (common.emin (t:=t)+2*fprec t-1) <=
      Rabs (FT2R xh*FT2R yh) by exact Nprod.
  have Hord := aux_cl3_le_ch xh xl yh yl Hp3 DWx DWy Hfmul Hfcl3 Nprod'.
  exact (DWTimesDW_double_word_from_pre xh xl yh yl Hfp Hord).
- have Hgap' : Rabs (FT2R xh*FT2R yh) <
      bpow radix2 (common.emin (t:=t)+2*fprec t-1) by exact Hgap.
  exact (proj2 (DWTimesDW_error_floor_gap xh xl yh yl
    Hp5 DWx DWy FIN Hgap')).
Qed.

End DWMulDW_Division_Helpers.

Section MixedCondBridgeDWTimesDW.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Definition DWTimesDW_guarantee
    (xh xl yh yl : ftype t) : Prop :=
  let '(zh, zl) := DWTimesDW xh xl yh yl in
  Rabs
    (FT2R zh + FT2R zl -
       (FT2R xh + FT2R xl) * (FT2R yh + FT2R yl))
    <= 4 * bpow Zaux.radix2 (- fprec t) ^ 2 *
         Rabs ((FT2R xh + FT2R xl) * (FT2R yh + FT2R yl)) +
       5 / 2 * bpow Zaux.radix2 (@common.emin t) /\
  double_word_prop zh zl.

Theorem DWTimesDW_guarantee_from_weak_pre_and_finite_post_cond
    (xh xl yh yl : ftype t) :
  (5 <= fprec t)%Z ->
  DWTimesDW_weak_pre_and_finite_post_cond xh xl yh yl ->
  DWTimesDW_guarantee xh xl yh yl.
Proof.
intros Hp5 Hcond.
have Hacc :=
  DWTimesDW_accuracy_from_weak_pre_and_finite_post_cond xh xl yh yl Hp5 Hcond.
have Hdw :=
  DWTimesDW_double_word_from_weak_pre_and_finite_post_cond xh xl yh yl Hp5 Hcond.
unfold DWTimesDW_guarantee.
revert Hacc Hdw.
destruct (DWTimesDW xh xl yh yl) as [zh zl].
cbn [fst snd]. intros Hacc Hdw. exact (conj Hacc Hdw).
Qed.

Lemma DWTimesDW_weak_pre_and_finite_post_cond_of_strong_precond
    (xh xl yh yl : ftype t) :
  DWTimesDW_strong_precond xh xl yh yl ->
  DWTimesDW_weak_pre_and_finite_post_cond xh xl yh yl.
Proof.
move => Hsafe.
have Hfin := DWTimesDW_finite_post_cond_from_strong_precond xh xl yh yl Hsafe.
move: Hsafe => [_ [_ [Hdx [Hdy _]]]].
unfold DWTimesDW_weak_pre_and_finite_post_cond, DWTimesDW_weak_precond,
       DWTimesDW_finite_post_cond.
exact (conj (conj Hdx Hdy) Hfin).
Qed.

Theorem DWTimesDW_guarantee_from_strong_precond
    (xh xl yh yl : ftype t) :
  (5 <= fprec t)%Z ->
  DWTimesDW_strong_precond xh xl yh yl ->
  DWTimesDW_guarantee xh xl yh yl.
Proof.
intros Hp5 Hsafe.
apply DWTimesDW_guarantee_from_weak_pre_and_finite_post_cond; [exact Hp5 |].
exact (DWTimesDW_weak_pre_and_finite_post_cond_of_strong_precond
  xh xl yh yl Hsafe).
Qed.

Lemma DWTimesDW_inputs_finite_of_finite_post_cond
    (xh xl yh yl : ftype t) :
  DWTimesDW_finite_post_cond xh xl yh yl ->
  is_finite xh = true /\
  is_finite xl = true /\
  is_finite yh = true /\
  is_finite yl = true.
Proof.
unfold DWTimesDW_finite_post_cond.
move => Hfin.
exact (conj (DWTimesDW_xh_finite xh xl yh yl Hfin)
       (conj (DWTimesDW_xl_finite xh xl yh yl Hfin)
       (conj (DWTimesDW_yh_finite xh xl yh yl Hfin)
             (DWTimesDW_yl_finite xh xl yh yl Hfin)))).
Qed.

End MixedCondBridgeDWTimesDW.
