(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* Shared VSU-building tactic for the double-word library.

   solve_SF_dd is a variant of VST's solve_SF_internal that rewrites the
   CompSpecs equation (CSeq, introduced by mkComponent) into the complete_type
   and var_sizes premises *before* discharging them.  This makes cenv_cs the
   concrete per-TU CompSpecs, so the composite lookup for functions with local
   struct variables (e.g. `struct dword sh;`) reduces instead of getting stuck
   on the opaque QP compspecs.

   Use it under sequential `1:{ solve_SF_dd body_f. }` focusing (one focused
   goal at a time); a `;`-composition after mkVSU mis-elaborates the evars that
   `eapply _SF_internal` introduces. *)

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
