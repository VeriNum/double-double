(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.

(* fast2_mult_acc_check(x, y) is the Tier B check that confirms the rounded
   product is finite: it returns 1 iff x*y is finite, certifying the weaker
   Fast2Mult_cond_acc.  This condition supports the bound on the returned error
   component, but not exact reconstruction or a proof that the output is a
   valid double word.  The C body is just
   `t'1 = isfinite_double(x*y); return t'1;`, so the proof simply forwards
   through the isfinite_double call and reads off its spec iff. *)
Lemma body_fast2_mult_acc_check:
  semax_body Vprog Gprog f_fast2_mult_acc_check fast2_mult_acc_check_spec.
Proof.
  start_function.
  forward_call.
  Intros vret.
  forward.
  Exists vret.
  entailer!.
  (* entailer! has already used vret = true; the residual goal is the
     unconditional Fast2Mult_cond_acc x y.  H is the isfinite_double spec
     iff (vret = true <-> is_finite (BMULT x y) = true); its forward
     direction closes the goal. *)
  unfold DDConds.Fast2Mult_cond_acc.
  apply H; reflexivity.
Qed.
