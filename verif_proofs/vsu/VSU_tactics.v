(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* VSU tactic for this library.  [solve_SF_dd] rewrites the [CompSpecs]
   equation before proving [complete_type] and [var_sizes], allowing local
   [struct dword] lookups to reduce.  Invoke it on one focused goal at a time;
   semicolon composition after [mkVSU] does not instantiate the generated
   existential variables correctly. *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.

Ltac solve_SF_dd body :=
  apply SF_internal_sound; eapply _SF_internal;
  [ reflexivity
  | try match goal with CSeq: @eq compspecs _ _ |- _ => rewrite <- CSeq end;
    repeat apply Forall_cons; try apply Forall_nil; try computable; try reflexivity
  | try match goal with CSeq: @eq compspecs _ _ |- _ => rewrite <- CSeq end;
    unfold var_sizes_ok; repeat constructor; try (simpl; rep_lia)
  | reflexivity
  | match goal with OK: QPprogram_OK _, CSeq: @eq compspecs _ _ |- _ =>
       rewrite <- CSeq; clear CSeq OK end;
    apply_semax_body body
  | eexists; split; [ fast_Qed_reflexivity | fast_Qed_reflexivity ] ].
