Require Import Coq.Reals.Reals.
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

End Rorder.