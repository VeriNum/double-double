(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

(* This file contains the floating-point functional models in IEEE-754
  format for the double-word operations. *)

Require Import vcfloat.VCFloat.
Require Import float_acc_lems op_defs common.


Section TwoSumModel.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Definition TwoSumF (a b : ftype t) :=
let s  := BPLUS a b in
let a' := BMINUS s b in
let b' := BMINUS s a' in
let da := BMINUS a a' in
let db := BMINUS b b' in (BPLUS a b, BPLUS da db).

Definition TwoSumF_err (a b : ftype t) := snd (TwoSumF a b).
Definition TwoSumF_sum (a b : ftype t) := fst (TwoSumF a b).

End TwoSumModel.

Section FastTwoSumModel.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

Definition Fast2Sum (a b : ftype t) :=
let s := BPLUS a b in
let z := BMINUS s a in 
let t := BMINUS b z in (s, t).

Definition Fast2Sum_err (a b : ftype t) := snd (Fast2Sum a b).
Definition Fast2Sum_sum (a b : ftype t) := fst (Fast2Sum a b).

End FastTwoSumModel.


Section Fast2MultModel.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

(** Algorithm 3 : Fast2Mult *)
Definition Fast2Mult (a b : ftype t) :=
let m := BMULT a b in
let p := BFMA a b (BOPP m) in (m, p).

Definition Fast2Mult_err (a b : ftype t) := snd (Fast2Mult a b).
Definition Fast2Mult_mul (a b : ftype t) := fst (Fast2Mult a b).

End Fast2MultModel.


Section DWord.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

(** Definition 1.4 *)
Definition double_word : ftype t -> ftype t -> Type :=
  fun xh xl => FT2R xh = rounded t (FT2R xh + FT2R xl).

(* Propositional double_word, suitable for VST PROP clauses. *)
Definition double_word_prop (xh xl : ftype t) : Prop :=
  FT2R xh = rounded t (FT2R xh + FT2R xl).

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))).

End DWord.


Section DWops.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

(** Algorithm 4 : Addition of DW number and FP number *)
Definition DWPlusFP (xh xl y : ftype t) := 
let (sh, sl) := TwoSumF xh y in
let v:= BPLUS xl sl in
let (zh, zl) := Fast2Sum sh v in (zh, zl).

(** Algorithm 6 : Addition of two DW numbers *)
Definition DWPlusDW (xh xl yh yl : ftype t) :=
let (sh, sl) := TwoSumF xh yh in
let (th, tl) := TwoSumF xl yl in
let c:= BPLUS sl th in
let (vh, vl) := Fast2Sum sh c in 
let w:= BPLUS tl vl in
let (zh, zl) := Fast2Sum vh w in (zh, zl).

(** Algorithm 9: multiply a double-word number by a floating-point number. *)
Definition DWTimesFP (xh xl y : ftype t) :=
let (ch, cl1) := Fast2Mult xh y in
let cl3 := BFMA xl y cl1 in
let (zh, zl) := Fast2Sum ch cl3 in (zh, zl).

(** Algorithm 12: multiply two double-word numbers. *)
Definition DWTimesDW (xh xl yh yl : ftype t) :=
let (ch, cl1) := Fast2Mult xh yh in
let tl0 := BMULT xl yl in 
let tl1 := BFMA xh yl tl0 in
let cl2 := BFMA xl yh tl1 in
let cl3 := BPLUS cl1 cl2 in
let (zh, zl) := Fast2Sum ch cl3 in (zh, zl).

(** Algorithm 15: divide a double-word number by a floating-point number. *)
Definition DWDivFP (xh xl y : ftype t) :=
let th := BDIV xh y in
let (pih, pil) := Fast2Mult th y in
let dh := BMINUS xh pih in
let dt := BMINUS dh pil in
let d  := BPLUS dt xl in
let tl := BDIV d y in
let (zh, zl) := Fast2Sum th tl in (zh, zl).

(** Algorithm 18: divide two double-word numbers. *)
Definition DWDivDW (xh xl yh yl : ftype t) :=
let th := BDIV (Zconst t 1) yh in
let rh := BFMA (BOPP yh) th (Zconst t 1) in
let rl := BOPP (BMULT yl th) in
let (eh, el) := Fast2Sum rh rl in
let (dh, dl) := DWTimesFP eh el th in
let (mh, ml) := DWPlusFP dh dl th in
let (zh, zl) := DWTimesDW xh xl mh ml in (zh, zl).

End DWops.
