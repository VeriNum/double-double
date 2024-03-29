(* This file contains the floating-point functional models in IEEE-754
  format for the 2Sum and Fast2Mult implementations.*)

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

Notation ulp := (Ulp.ulp Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))). 

End DWord.

Section DWops.
Context {NANS: Nans} {t : type} {STD: is_standard t}.

(** Algorithm 4 : Addition of DW number and FP number *)
Definition DWPlusFP (xh xl y : ftype t) := 
let (sh, sl) := TwoSumF xh y in
let v:= BPLUS xl sl in
let (zh, zl) := Fast2Sum sh v in (zh, zl).

(** Algorithm 4p : Addition of DW number and FP number *)
Definition DWPlusFP' (xh xl y : ftype t) := 
let xhp := BPLUS xh xl in
let (sh, sl) := TwoSumF xhp y in
let v:= BPLUS xl sl in
let (zh, zl) := Fast2Sum sh v in (zh, zl).

(** Algorithm 5 : Addition of two DW numbers *)
Definition SloppyDWPlusDW (xh xl yh yl : ftype t) := 
let (sh, sl) := TwoSumF xh yh in
let v:= BPLUS xl yl in
let w:= BPLUS sl v in
let (zh, zl) := Fast2Sum sh w in (zh, zl).

(** Algorithm 6 : Addition of two DW numbers *)
Definition AccurateDWPlusDW (xh xl yh yl : ftype t) := 
let (sh, sl) := TwoSumF xh yh in
let (th, tl) := TwoSumF xl yl in
let c:= BPLUS sl th in
let (vh, vl) := Fast2Sum sh c in 
let w:= BPLUS tl vl in
let (zh, zl) := Fast2Sum vh w in (zh, zl).

(** Algorithm 7 : Multiplication of a DW number by a FP number *)
Definition DWTimesFP1 (xh xl y : ftype t) := 
let (ch, cl1) := Fast2Mult xh y in
let cl2 := BMULT xl y in
let (th, tl1) := Fast2Sum ch cl2 in 
let tl2 := BMULT tl1 cl1 in
let (zh, zl) := Fast2Sum th tl2 in (zh, zl).

(** Algorithm 8 : Multiplication of a DW number by a FP number *)
Definition DWTimesFP2 (xh xl y : ftype t) := 
let (ch, cl1) := Fast2Mult xh y in
let cl2 := BMULT xl y in
let cl3 := BPLUS cl1 cl2 in
let (zh, zl) := Fast2Sum ch cl3 in (zh, zl).

(** Algorithm 9 : Multiplication of a DW number by a FP number*)
Definition DWTimesFP3 (xh xl y : ftype t) := 
let (ch, cl1) := Fast2Mult xh y in
let cl3 := BFMA xl y cl1 in
let (zh, zl) := Fast2Sum ch cl3 in (zh, zl).

(** Algorithm 10 : Multiplication of a DW number by a DW number*)
Definition DWTimesDW1 (xh xl yh yl : ftype t) := 
let (ch, cl1) := Fast2Mult xh yh in
let tl1 := BMULT xh yl in
let tl2 := BMULT xl yh in
let cl2 := BPLUS tl1 tl2 in
let cl3 := BPLUS cl1 cl2 in 
let (zh, zl) := Fast2Sum ch cl3 in (zh, zl).

(** Algorithm 11 : Multiplication of a DW number by a DW number*)
Definition DWTimesDW2 (xh xl yh yl : ftype t) := 
let (ch, cl1) := Fast2Mult xh yh in
let tl        := BMULT xh yl in
let cl2       := BFMA  xl yh tl in
let cl3       := BPLUS cl1 cl2 in
let (zh,zl)   := Fast2Sum ch cl3 in (zh, zl).

(** Algorithm 12 : Multiplication of a DW number by a DW number *)
Definition DWTimesDW3 (xh xl yh yl : ftype t) := 
let (ch, cl1) := Fast2Mult xh yh in
let tl0 := BMULT xl yl in 
let tl1 := BFMA xh yl tl0 in
let cl2 := BFMA xl yh tl1 in
let cl3 := BPLUS cl1 cl2 in
let (zh, zl) := Fast2Sum ch cl3 in (zh, zl).

(** Algorithm 13 : Division of a DW number by a FP number*)
Definition DWDivFP1 := True.

(** Algorithm 14 : Division of a DW number by a FP number*)
Definition DWDivFP2 := True.

(** Algorithm 15 : Division of a DW number by a FP number*)
Definition DWDivFP3 := True.

(** Algorithm 16 : Division of a DW number by a DW number*)
Definition DWDivDW1 := True.

(** Algorithm 17 : Division of a DW number by a DW number*)
Definition DWDivDW2 := True.

(** Algorithm 18 : Division of a DW number by a DW number*)
Definition DWDivDW3 := True.

End DWops.

