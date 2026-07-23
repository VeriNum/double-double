(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(** Multiplication regime lemmas used specifically by double-word division. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs dd_tactics common FLT_helpers.
Require Import DWTimesFP DWTimesDW DDModels DWord_defs Fast2Mult_acc
  TwoSum_acc Fast2Sum_acc DWMulDW_acc.
Require Import DWPlusFP_acc_helpers.
From Flocq Require Import Pff2Flocq Core.
From Stdlib Require Import Reals.Reals.
Require Import mathcomp.ssreflect.ssreflect.
From Stdlib Require Import Logic.FunctionalExtensionality.

Set Bullet Behavior "Strict Subproofs".


(* ===== direct far low-low-underflow apparatus ===== *)
Section FarLow0Apparatus.
Context {NANS: Nans} {t : type} {STD: is_standard t}.
Notation u      := (bpow Zaux.radix2 (- fprec t)).
Notation eminA  := (SpecFloat.emin (fprec t) (femax t)).
(* The explicit FLX rounding chain of the low-order DW*DW nodes with a floor
   term f at the low-low node.  This is a NOTATION (pure syntax), not a
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

(* Perturbed-free hard arm: the explicit FLX chain (real algorithm's low-node
   error analysis), no synthetic Definition.  Mirrors the proof of the former
   DWTimesDW12_low0_floored_normalized_hard, whose statement was the packaged
   Definition; here the conclusion is about the explicit Fast2Sum ch cl3. *)
Lemma flx_dwtimesdw_hard
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

Lemma flx_dwtimesdw_easy
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

(* Homogeneity/symmetry of the FLX chain (direct analogues of the
   former DWTimesDW12_low0_floored_{Asym_r,Asym_l,Sx,Sy}). *)
Lemma flx_Asym_r (xh xl yh yl f : R) :
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

Lemma flx_Asym_l (xh xl yh yl f : R) :
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

Lemma flx_Sx (xh xl yh yl f : R) (e : Z) :
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

Lemma flx_Sy (xh xl yh yl f : R) (e : Z) :
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
Lemma flx_positive (xh0 xl0 yh0 yl0 f0 : R) :
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
Lemma flx_mixed (xh0 xl0 yh0 yl0 f0 : R) :
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

(* The far low-low-underflow bound, DIRECTLY for the real DWTimesDW3, via the
   FLT floor decomposition (no synthetic floored algorithm). *)
Lemma DWTimesDW_abs_low0_far (xh xl yh yl : ftype t) :
  double_word xh xl -> double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
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
  Rabs (FT2R (fst (DWTimesDW3 xh xl yh yl)) +
        FT2R (snd (DWTimesDW3 xh xl yh yl)) -
        (FT2R xh+FT2R xl)*(FT2R yh+FT2R yl)) <=
    4*u^2*Rabs ((FT2R xh+FT2R xl)*(FT2R yh+FT2R yl))+2*bpow radix2 eminA.
Proof.
move => DWx DWy FIN Hp5 Hfar U0 N1 N2 N3.
have Hp3 : (3 <= fprec t)%Z by lia.
have Fmul := FINmul xh xl yh yl FIN.
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
have Htp := Fast2Mult_correct_weak xh yh Fmul ltac:(auto).
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
    F2Rp (DWTimesDW3 xh xl yh yl).
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
have Hz : (FT2R (fst (DWTimesDW3 xh xl yh yl))+
   FT2R (snd (DWTimesDW3 xh xl yh yl))-
   (FT2R xh+FT2R xl)*(FT2R yh+FT2R yl))%R =
  ((FT2R (fst (DWTimesDW3 xh xl yh yl))+
   FT2R (snd (DWTimesDW3 xh xl yh yl))-
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
Local Instance valid_fexp_inst_acc : Generic_fmt.Valid_exp fexp.
Proof. apply FLT.FLT_exp_valid, fprec_gt_0. Qed.
Variables (xh xl yh yl : ftype t).
Let zh := FT2R (fst (DWTimesDW3 xh xl yh yl)).
Let zl := FT2R (snd (DWTimesDW3 xh xl yh yl)).
Let xr := (FT2R xh + FT2R xl).
Let yr := (FT2R yh + FT2R yl).


(** General, regime-independent accuracy theorem.  Unlike the normal-regime
    theorem below, this theorem permits subnormal intermediate operations.
    Its hypotheses are grouped in [DWTimesDW_accuracy_pre] so that the
    difference from [DWTimesDW_cond] is visible at the statement level. *)
Theorem DWTimesDW_relerr_low0_normal :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  bpow radix2 (eminA + 2 * fprec t - 1) <=
    Rabs (FT2R xh * FT2R yh) ->
  bpow radix2 (eminA + fprec t - 1) <=
    Rabs (FT2R xl * FT2R yl) ->
  relative_error_DWTimesDW xh xl yh yl <= 4 * u ^ 2.
Proof.
move => Hdw Hdwy Hfin Hp5 Nprod N0.
have Hfmul : is_finite (BMULT xh yh)=true
  by exact (FINmul xh xl yh yl Hfin).
have Hftl0 : is_finite (BMULT xl yl)=true
  by exact (FINtl0 xh xl yh yl Hfin).
have N1 := normal_low0_implies_low1
  xh xl yh yl ltac:(lia) Hdw Hftl0 N0.
have F2fix := normal_low0_implies_low2_FIX xh xl yh yl Hdwy N0.
specialize (F2fix NANS STD).
have E2 := FIX_FLT_or_normal
  (FT2R (BFMA xh yl (BMULT xl yl))+FT2R xl*FT2R yh) F2fix.
have F3fix := closing_arg_FIX_of_normal_product xh yh
  (BFMA xl yh (BFMA xh yl (BMULT xl yl))) Hfmul Nprod.
specialize (F3fix NANS STD NANS STD).
specialize (F3fix NANS STD).
have E3 := FIX_FLT_or_normal
  (FT2R (Fast2Mult_err xh yh)+
   FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) F3fix.
have Hbridge := DWTimesDW3_FLX_FLT_exact_or_normal
  xh xl yh yl Hfin Nprod N0 N1 E2 E3.
have HDWx : DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl)
  by (apply (dw_word_DWdouble xh xl xh); exact Hdw).
have HDWy : DWPlus.double_word (fprec t) choice (FT2R yh) (FT2R yl)
  by (apply (dw_word_DWdouble yh yl yh); exact Hdwy).
have Hpaper :
  (let (zh, zl) := DWTimesDW.DWTimesDW12 (fprec t) choice
                     (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl) in
   let xy := (FT2R xh + FT2R xl) * (FT2R yh + FT2R yl) in
   Rabs ((zh + zl - xy) / xy) <
     4 * (bpow radix2 (- fprec t) * bpow radix2 (- fprec t)))
  := @DWTimesDW.DWTimesDW12_correct (fprec t) (fprec_gt_one t)
       choice choiceP Hp5 (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl)
       HDWx HDWy.
rewrite Hbridge /F2Rp /= in Hpaper.
unfold relative_error_DWTimesDW, zh, zl, xr, yr.
replace (4*u^2)%R with
  (4*(bpow radix2 (-fprec t)*bpow radix2 (-fprec t)))%R by ring.
apply Rlt_le. exact Hpaper.
Qed.

Corollary DWTimesDW_abs_low0_normal :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  bpow radix2 (eminA + 2 * fprec t - 1) <=
    Rabs (FT2R xh * FT2R yh) ->
  bpow radix2 (eminA + fprec t - 1) <=
    Rabs (FT2R xl * FT2R yl) ->
  Rabs (zh+zl-xr*yr) <= 4*u^2*Rabs (xr*yr).
Proof.
move => Hdw Hdwy Hfin Hp5 Nprod N0.
have Hrel := DWTimesDW_relerr_low0_normal
  Hdw Hdwy Hfin Hp5 Nprod N0.
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

(** Absolute paper bound for the broader exact-node regime.  Each node may
    be normal or merely representable on the physical FIX lattice. *)
Theorem DWTimesDW_abs_FIX_or_normal :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  bpow radix2 (eminA+2*fprec t-1) <=
    Rabs (FT2R xh*FT2R yh) ->
  (generic_format radix2 (FIX_exp eminA) (FT2R xl*FT2R yl) \/
   bpow radix2 (eminA+fprec t-1) <= Rabs (FT2R xl*FT2R yl)) ->
  (generic_format radix2 (FIX_exp eminA)
      (FT2R xh*FT2R yl+FT2R (BMULT xl yl)) \/
   bpow radix2 (eminA+fprec t-1) <=
      Rabs (FT2R xh*FT2R yl+FT2R (BMULT xl yl))) ->
  (generic_format radix2 (FIX_exp eminA)
      (FT2R (BFMA xh yl (BMULT xl yl))+FT2R xl*FT2R yh) \/
   bpow radix2 (eminA+fprec t-1) <=
      Rabs (FT2R (BFMA xh yl (BMULT xl yl))+FT2R xl*FT2R yh)) ->
  (generic_format radix2 (FIX_exp eminA)
      (FT2R (Fast2Mult_err xh yh)+
       FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) \/
   bpow radix2 (eminA+fprec t-1) <=
      Rabs (FT2R (Fast2Mult_err xh yh)+
       FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl))))) ->
  Rabs (zh+zl-xr*yr) <= 4*u^2*Rabs (xr*yr).
Proof.
move => Hdw Hdwy Hfin Hp5 Nprod E0 E1 E2 E3.
have Hbridge := DWTimesDW3_FLX_FLT_FIX_or_normal
  xh xl yh yl Hfin Nprod E0 E1 E2 E3.
have HDWx : DWPlus.double_word (fprec t) choice (FT2R xh) (FT2R xl)
  by (apply (dw_word_DWdouble xh xl xh); exact Hdw).
have HDWy : DWPlus.double_word (fprec t) choice (FT2R yh) (FT2R yl)
  by (apply (dw_word_DWdouble yh yl yh); exact Hdwy).
have Hpaper :
  (let (zh, zl) := DWTimesDW.DWTimesDW12 (fprec t) choice
                     (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl) in
   let xy := (FT2R xh+FT2R xl)*(FT2R yh+FT2R yl) in
   Rabs ((zh+zl-xy)/xy) <
     4*(bpow radix2 (-fprec t)*bpow radix2 (-fprec t)))
  := @DWTimesDW.DWTimesDW12_correct (fprec t) (fprec_gt_one t)
       choice choiceP Hp5 (FT2R xh) (FT2R xl) (FT2R yh) (FT2R yl)
       HDWx HDWy.
rewrite Hbridge /F2Rp /= in Hpaper.
have Hprod0 : 0 < Rabs (FT2R xh*FT2R yh).
{ eapply Rlt_le_trans; [apply bpow_gt_0|exact Nprod]. }
have Hxhne : FT2R xh<>0.
{ intro H0. rewrite H0 Rmult_0_l Rabs_R0 in Hprod0. lra. }
have Hyhne : FT2R yh<>0.
{ intro H0. rewrite H0 Rmult_0_r Rabs_R0 in Hprod0. lra. }
have Hxrne : xr<>0.
{ intro H0. apply Hxhne. unfold double_word in Hdw. fold xr in Hdw.
  rewrite H0 /rounded round_0 in Hdw. exact Hdw. }
have Hyrne : yr<>0.
{ intro H0. apply Hyhne. unfold double_word in Hdwy. fold yr in Hdwy.
  rewrite H0 /rounded round_0 in Hdwy. exact Hdwy. }
have Heq : Rabs (zh+zl-xr*yr) =
    Rabs ((zh+zl-xr*yr)/(xr*yr))*Rabs (xr*yr).
{ rewrite -Rabs_mult. f_equal. field; split; assumption. }
rewrite Heq. apply Rmult_le_compat_r; [apply Rabs_pos|].
apply Rlt_le. replace (4*u^2)%R with
  (4*(bpow radix2 (-fprec t)*bpow radix2 (-fprec t)))%R by ring.
exact Hpaper.
Qed.


(** Absolute form of the existing regime-independent multiplication estimate
    on the normal-leading branch.  This is used only for the pure-relative
    fallback outside the sharp floored-paper regimes. *)
Theorem DWTimesDW_abs_normal_coarse :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  (5 <= fprec t)%Z ->
  bpow radix2 (eminA+2*fprec t-1) <=
    Rabs (FT2R xh*FT2R yh) ->
  Rabs (zh+zl-xr*yr) <= 8*u^2*Rabs (xr*yr).
Proof.
move => DWx DWy FIN Hp5 Nprod.
have DWxp : double_word_prop xh xl := DWx.
have DWyp : double_word_prop yh yl := DWy.
have Hrel := DWTimesDW_relerr_bound
  xh xl yh yl Hp5
  (conj DWxp (conj DWyp (conj FIN (or_intror Nprod)))).
have Hprod := aux_dw_exact_product_lower xh xl yh yl DWx DWy.
specialize (Hprod STD).
fold u xr yr in Hprod.
have HP : 0 < Rabs (FT2R xh*FT2R yh).
{ eapply Rlt_le_trans; [apply bpow_gt_0|exact Nprod]. }
have Hu : u <= /32.
{ unfold u. have -> : (/32:R)=bpow radix2 (-5) by (simpl;lra).
  apply bpow_le; lia. }
have HXY : 0 < Rabs (xr*yr).
{ eapply Rlt_le_trans; [|exact Hprod].
  apply Rmult_lt_0_compat; [nra|exact HP]. }
have Hne : xr*yr<>0.
{ intro H0. rewrite H0 Rabs_R0 in HXY. lra. }
have Hxr : xr<>0 by (intro H0;apply Hne;rewrite H0;ring).
have Hyr : yr<>0 by (intro H0;apply Hne;rewrite H0;ring).
unfold relative_error_DWTimesDW in Hrel.
have Heq : Rabs (zh+zl-xr*yr) =
    Rabs ((zh+zl-xr*yr)/(xr*yr))*Rabs (xr*yr).
{ rewrite -Rabs_mult. f_equal. field; split; assumption. }
rewrite Heq. apply Rmult_le_compat_r; [apply Rabs_pos|exact Hrel].
Qed.

(** If both the low-low node and the final correction node are subnormal,
    their relative components vanish.  The two remaining relative errors fit
    strictly inside the paper [4*u^2] budget; all additive pieces retain the
    common two-ulps allowance. *)
Theorem DWTimesDW_abs_low0_final_underflow :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  (14 <= fprec t)%Z ->
  bpow radix2 (eminA+2*fprec t-1) <=
    Rabs (FT2R xh*FT2R yh) ->
  Rabs (FT2R xl*FT2R yl) < bpow radix2 (eminA+fprec t-1) ->
  Rabs (FT2R (Fast2Mult_err xh yh)+
    FT2R (BFMA xl yh (BFMA xh yl (BMULT xl yl)))) <
      bpow radix2 (eminA+fprec t-1) ->
  Rabs (zh+zl-xr*yr) <=
    4*u^2*Rabs (xr*yr)+2*bpow radix2 eminA.
Proof.
move => DWx DWy FIN Hp14 Nprod N0 N3.
have Hp3 : (3 <= fprec t)%Z by lia.
have Fmul := FINmul xh xl yh yl FIN.
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
have Hu : u <= /16384.
{ unfold u. have -> : (/16384:R)=bpow radix2 (-14) by (simpl;lra).
  apply bpow_le;lia. }
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have Heta0 : 0 < eta by (unfold eta;apply bpow_gt_0).
have Hxl := aux_dwu_rel xh xl DWx.
have Hyl := aux_dwu_rel yh yl DWy.
specialize (Hxl STD); specialize (Hyl STD).
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

(** If the first cross-term FMA underflows but the following two nodes are
    normal, the small-node hypothesis replaces one full [u*P] contribution.
    The two active physical floors consume one ulp; their propagation consumes
    at most the second ulp, leaving the paper [4*u^2] term unchanged. *)
Theorem DWTimesDW_abs_low0_low1_tail_normal :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  (14 <= fprec t)%Z ->
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
move => DWx DWy FIN Hp14 Nprod N0 N1 N2 N3.
have Hp3 : (3 <= fprec t)%Z by lia.
have Fmul := FINmul xh xl yh yl FIN.
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
have Hu : u <= /16384.
{ unfold u. have -> : (/16384:R)=bpow radix2 (-14) by (simpl;lra).
  apply bpow_le;lia. }
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have Heta0 : 0 < eta by (unfold eta;apply bpow_gt_0).
have Hxl := aux_dwu_rel xh xl DWx.
have Hyl := aux_dwu_rel yh yl DWy.
specialize (Hxl STD); specialize (Hyl STD).
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

(** Symmetric tail case: the low-low node and the second FMA underflow,
    while the first FMA and final addition are normal.  Here the subnormal
    second-FMA input bounds the whole correction entering the last round, so
    the relative pieces fit in [4*u^2] and the two floor pieces total one ulp. *)
Theorem DWTimesDW_abs_low0_low2_other_normal :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  (14 <= fprec t)%Z ->
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
move => DWx DWy FIN Hp14 Nprod N0 N1 N2 N3.
have Hp3 : (3 <= fprec t)%Z by lia.
have Fmul := FINmul xh xl yh yl FIN.
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
have Hu : u <= /16384.
{ unfold u. have -> : (/16384:R)=bpow radix2 (-14) by (simpl;lra).
  apply bpow_le;lia. }
have HP0 : 0 <= P by (unfold P;apply Rabs_pos).
have Heta0 : 0 < eta by (unfold eta;apply bpow_gt_0).
have Hxl := aux_dwu_rel xh xl DWx.
have Hyl := aux_dwu_rel yh yl DWy.
specialize (Hxl STD); specialize (Hyl STD).
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
Lemma leading_product_gap_low_low_zero
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
have Hxl := aux_dwu_rel xh0 xl0 DWx.
have Hyl := aux_dwu_rel yh0 yl0 DWy.
specialize (Hxl STD); specialize (Hyl STD).
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

(* ulp is at most a relative step plus the subnormal floor: a universal bound
   used to keep the extra DW x DW rounding-error terms small. *)
Theorem DWTimesDW_abs_normal_near_threshold :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  (14 <= fprec t)%Z ->
  bpow radix2 (eminA+2*fprec t-1) <=
    Rabs (FT2R xh*FT2R yh) ->
  Rabs (FT2R xh*FT2R yh) <=
    9/8*bpow radix2 (eminA+2*fprec t-1) ->
  Rabs (zh+zl-xr*yr) <=
    4*u^2*Rabs (xr*yr)+2*bpow radix2 eminA.
Proof.
move => DWx DWy FIN Hp14 Nprod Pnear.
have Hp5 : (5 <= fprec t)%Z by lia.
have Hp3 : (3 <= fprec t)%Z by lia.
have Fmul := FINmul xh xl yh yl FIN.
have F0 := FINtl0 xh xl yh yl FIN.
have F1 := FINtl1 xh xl yh yl FIN.
have F2 := FINcl2 xh xl yh yl FIN.
have F3 := FINcl3 xh xl yh yl FIN.
have HerrEq := relerr_error_eq xh xl yh yl Hp3 DWx DWy FIN Fmul Nprod.
have HerrRaw := aux_eta_bnd xh xl yh yl Hp5 DWx DWy
  Fmul F0 F1 F2 F3 Nprod.
rewrite HerrEq.
set P := Rabs (FT2R xh*FT2R yh) in Nprod, Pnear, HerrRaw *.
set T := bpow radix2 (eminA+2*fprec t-1) in Nprod, Pnear *.
set eta := bpow radix2 eminA.
have Hu0 : 0 < u by (unfold u;apply bpow_gt_0).
have Hu : u <= /16384.
{ unfold u. have -> : (/16384:R)=bpow radix2 (-14) by (simpl;lra).
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
    4*u^2*((1-u)^2*P)+2*eta.
{ have Hcoef :
      (15/2-4*(1-u)^2)*(9/8) <= 4 by nra.
  have Hnonneg : 0 <= 15/2-4*(1-u)^2 by nra.
  have Hstep := Rmult_le_compat_l
    (15/2-4*(1-u)^2) _ _ Hnonneg HnearScaled.
  nra. }
replace (u*u) with (u^2) by ring. exact Hbudget.
Qed.

(** Absolute form of the existing regime-independent multiplication estimate
    on the normal-leading branch.  This is used only for the pure-relative
    fallback outside the sharp floored-paper regimes. *)
Theorem DWTimesDW_abs_low0_low1_low2_final_normal :
  double_word xh xl ->
  double_word yh yl ->
  is_finite_p (DWTimesDW3 xh xl yh yl) ->
  (14 <= fprec t)%Z ->
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
move => DWx DWy FIN Hp14 Nprod N0 N1 N2 N3.
have Hp3 : (3 <= fprec t)%Z by lia.
have Fmul := FINmul xh xl yh yl FIN.
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
have Hu : u <= /16384.
{ unfold u. have -> : (/16384:R)=bpow radix2 (-14) by (simpl;lra).
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

End DWMulDW_Division_Helpers.
