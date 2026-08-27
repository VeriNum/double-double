(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import DD.verif_proofs.verif_fp_utils_common.

(* fast2_mult_acc_check(x, y) is the Tier B check that confirms the rounded
   product is finite: it returns 1 iff x*y is finite.  This fact supports the
   bound on the returned error component, but not exact reconstruction or a
   proof that the output is a valid double-word.  The C body is just
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
  (* [entailer!] has already used [vret = true].  The residual goal states
     that the rounded product is finite.  The forward direction of [H], the
     [isfinite_double] specification, closes it. *)
  apply H; reflexivity.
Qed.
