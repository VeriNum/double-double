(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

From Stdlib Require Import Reals.Reals.
Require Import Flocq.Core.Raux.

Section Rorder.

Lemma Rle_bool_to_Rle :
  forall x y,
    Rle_bool x y = true ->
    (x <= y)%R.
Proof.
  intros x y H.
  destruct (Rle_dec x y) as [Hle | Hgt].
  - (* x <= y *) 
    exact Hle.
  - (* x > y *) 
  apply Rnot_le_lt in Hgt.
  apply Rle_bool_false in Hgt.
  rewrite Hgt in H; discriminate.
Qed.

Lemma Rlt_bool_to_Rlt :
  forall x y,
    Rlt_bool x y = true ->
    (x < y)%R.
Proof.
  intros x y H.
  destruct (Rlt_dec x y) as [Hlt | Hge].
  - exact Hlt.
  - 
  apply Rnot_lt_le in Hge.
  apply Rle_bool_true in Hge.
  rewrite <- negb_Rle_bool in Hge. 
  destruct Rlt_bool; discriminate.
Qed.

Lemma Rle_bool_to_Rlt_false_1 :
  forall x y,
    Rle_bool x y = false ->
    (x > y)%R.
Proof.
  intros x y H.
  destruct (Rlt_dec y x) as [Hgt | Hle]; auto.
  apply Rnot_lt_le in Hle.
  apply Rle_bool_true in Hle.
  rewrite Hle in H; discriminate.
Qed.

Lemma Rle_bool_to_Rle_false :
  forall x y,
    Rle_bool x y = false ->
    (y < x)%R.
Proof.
  intros x y H.
  apply Rgt_lt.
  apply Rle_bool_to_Rlt_false_1; auto.
Qed.

End Rorder.
