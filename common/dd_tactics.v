Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs.
Require Import DDModels.


Ltac field_simplify_round :=
  match goal with |- context[Generic_fmt.round _ _ _ ?a] =>
  try field_simplify a
end. 

Ltac BPLUS_correct t a b :=
unfold FT2R;
match goal with | FIN : Binary.is_finite _ _ (BPLUS a b) = true |- context [Binary.B2R _ _ (BPLUS a b)] =>
  let X:= fresh in set (X:= Binary.B2R _ _ (BPLUS a b)); unfold BPLUS, BINOP in X ;
  let H4 := fresh in pose proof (is_finite_sum_no_overflow a b FIN) as H4; apply Rlt_bool_true in H4;
  unfold FT2R in H4;
  let H := fresh in 
  assert (H : Binary.is_finite _ _ a = true /\ Binary.is_finite _ _ b = true);
  [destruct a; destruct b; 
      simpl in FIN; split; try discriminate; auto;
          match goal with | H: Binary.is_finite _ _
                   (BPLUS (Binary.B754_infinity _ _ ?s)
                      (Binary.B754_infinity _ _ ?s0)) = _ |- Binary.is_finite _ _ _ = _ =>
            destruct s; destruct s0; try discriminate; auto end 
  | ]; 
    let H1 := fresh in let H2 := fresh in  destruct H as (H1 & H2);
    let H3 := fresh in pose proof (Binary.Bplus_correct  (fprec t) (femax t) 
        (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE a b H1 H2) as H3;
    rewrite H4 in H3 ;
    destruct H3 as (H3 & _); clear H4; unfold BPLUS, BINOP in X; subst X; try field_simplify_round;
    rewrite H3; try reflexivity 
end.

Ltac BMINUS_correct t a b :=
unfold FT2R;
match goal with | FIN : Binary.is_finite _ _ (BMINUS a b) = true |- context [Binary.B2R _ _ (BMINUS a b)] =>
  let X:= fresh in set (X:= Binary.B2R _ _ (BMINUS a b)); unfold BMINUS, BINOP in X ;
  let H4 := fresh in pose proof (is_finite_minus_no_overflow a b FIN) as H4; apply Rlt_bool_true in H4;
  unfold FT2R in H4;
  let H := fresh in 
  assert (H : Binary.is_finite _ _ a = true /\ Binary.is_finite _ _ b = true);
  [destruct a; destruct b; 
      simpl in FIN; split; try discriminate; auto;
          match goal with | H: Binary.is_finite _ _
                   (BMINUS (Binary.B754_infinity _ _ ?s)
                      (Binary.B754_infinity _ _ ?s0)) = _ |- Binary.is_finite _ _ _ = _ =>
            destruct s; destruct s0; try discriminate; auto end 
  | ]; 
    let H1 := fresh in let H2 := fresh in  destruct H as (H1 & H2);
    let H3 := fresh in pose proof (Binary.Bminus_correct  (fprec t) (femax t) 
        (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE a b H1 H2) as H3;
    rewrite H4 in H3 ;
    destruct H3 as (H3 & _); clear H4 ; unfold BMINUS, BINOP in X; subst X; try field_simplify_round; 
    rewrite H3; try reflexivity 
end.

Ltac BMULT_correct t a b :=
unfold FT2R;
match goal with | FIN : Binary.is_finite _ _ (BMULT a b) = true |- context [Binary.B2R _ _ (BMULT a b)] =>
  let X:= fresh in set (X:= Binary.B2R _ _ (BMULT a b)); unfold BMULT, BINOP in X ;
  let H4 := fresh in pose proof (is_finite_BMULT_no_overflow a b FIN) as H4; apply Rlt_bool_true in H4;
  unfold FT2R in H4;
    let H3 := fresh in try pose proof (Binary.Bmult_correct  (fprec t) (femax t) 
        (fprec_gt_0 t) (fprec_lt_femax t) (mult_nan t) BinarySingleNaN.mode_NE a b) as H3;
    unfold common.rounded in H4; rewrite H4 in H3 ;
    destruct H3 as (H3 & _); clear H4 ; unfold BMULT, BINOP in X; subst X; try field_simplify_round; 
    rewrite H3; try reflexivity 
end.

Ltac rewrite_format :=
repeat match goal with |- context [Generic_fmt.round Zaux.radix2 (FLT.FLT_exp emin (fprec ?t))
  (Generic_fmt.Znearest choice) ?A] =>
change (Generic_fmt.round Zaux.radix2 (FLT.FLT_exp emin (fprec t))
  (Generic_fmt.Znearest choice) A) with
(Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
(BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) A) end.