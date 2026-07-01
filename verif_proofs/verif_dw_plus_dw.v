(* Copyright 2023-2026 Ariel Kellison *)
(* Licensed under the MIT License. See LICENSE. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.

Require Import DDModels.
Require Import DD.accuracy_proofs.dw_opps.DWPlusDW_acc_helpers.   (* exposes the bridge lemmas *)
Require Import DD.verif_proofs.verif_objs.dw_plus_dw.

#[export] Instance CompSpecs :
  compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition f2val (pq: ftype Tdouble * ftype Tdouble) : val*val :=
 (Vfloat (fst pq), Vfloat (snd pq)).

Definition dword := Tstruct _dword noattr.

(* Re-declare two_sum and fast_2sum specs locally under THIS file's CompSpecs.
   The body proofs in verif_two_sum.v / verif_fast_2sum.v are verified under
   different compspecs (one per program), but the funspec interface is
   identical — same struct, same args, same condition. *)
Definition two_sum_spec :=
  DECLARE _two_sum
  WITH s: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr dword, tdouble, tdouble ]
    PROP()
    PARAMS (s; Vfloat a; Vfloat b)
    SEP(data_at_ Tsh dword s)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh dword (f2val (TwoSumF a b)) s).

Definition fast_2sum_spec :=
  DECLARE _fast_2sum
  WITH s: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr dword, tdouble, tdouble ]
    PROP()
    PARAMS (s; Vfloat a; Vfloat b)
    SEP(data_at_ Tsh dword s)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh dword (f2val (Fast2Sum a b)) s).

Definition dw_plus_dw1_spec :=
  DECLARE _dw_plus_dw1
  WITH s: val, x : val, y: val,
      xh : ftype Tdouble * ftype Tdouble,
      yh : ftype Tdouble * ftype Tdouble
  PRE [tptr dword, tptr dword, tptr dword ] (* c lang types *)
    PROP()
    PARAMS (s; x; y)
    SEP(data_at_ Tsh dword s;
          data_at Tsh dword (f2val xh) x;
          data_at Tsh dword (f2val yh) y)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh dword
          (f2val (SloppyDWPlusDW (fst xh) (snd xh) (fst yh) (snd yh))) s; (* final dword is stored at address s *)
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y). (* initial dwords unchanged *)

(* Collect the function-API specs together into Gprog: list funspec *)
Definition Gprog1 : funspecs := [fast_2sum_spec; two_sum_spec; dw_plus_dw1_spec].

Definition dw_plus_dw2_spec :=
  DECLARE _dw_plus_dw2
  WITH s: val, x : val, y: val,
      xh : ftype Tdouble * ftype Tdouble,
      yh : ftype Tdouble * ftype Tdouble
  PRE [tptr dword, tptr dword, tptr dword ] (* c lang types *)
    PROP()
    PARAMS (s; x; y)
    SEP(data_at_ Tsh dword s;
          data_at Tsh dword (f2val xh) x;
          data_at Tsh dword (f2val yh) y)
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh dword
          (f2val (AccurateDWPlusDW (fst xh) (snd xh) (fst yh) (snd yh))) s; (* final dword is stored at address s *)
        data_at Tsh dword (f2val xh) x;
        data_at Tsh dword (f2val yh) y). (* initial dwords unchanged *)

(* Collect the function-API specs together into Gprog: list funspec *)
Definition Gprog2 : funspecs := [fast_2sum_spec; two_sum_spec; dw_plus_dw2_spec].

(* body_dw_plus_dw2: each forward_call discharges the inner precondition
   via the DWPlusDWCondBridge lemmas from accuracy_proofs/DWPlusDW.v.
   The Fast2Sum bridges transitively depend on Hc_le_sh / Hw_le_vh which
   are still admitted at the time this proof was written (Phase 3). *)
Lemma body_dw_plus_dw2: semax_body Vprog Gprog2 f_dw_plus_dw2 dw_plus_dw2_spec.
Proof.
  start_function.

  (* Step 1: two_sum(&sh, x->s, y->s) *)
  forward.  (* _t'9 = x->s *)
  forward.  (* _t'10 = y->s *)
  forward_call (v_sh, fst xh, fst yh).

  (* Step 2: two_sum(&th, x->t, y->t) *)
  forward.  (* _t'7 = x->t *)
  forward.  (* _t'8 = y->t *)
  forward_call (v_th, snd xh, snd yh).
 
  (* Step 3: c = sh.t + th.s *)
  forward.  (* _t'5 = sh.t *)
  forward.  (* _t'6 = th.s *)
  forward.  (* _c = _t'5 + _t'6 *)

  (* Step 4: fast_2sum(&vh, sh.s, c)
     c = BPLUS (TwoSumF_err xh yh) (TwoSumF_sum xl yl). *)
  forward.  (* _t'4 = sh.s *)
  forward_call (v_vh, TwoSumF_sum (fst xh) (fst yh),
                BPLUS (TwoSumF_err (fst xh) (fst yh))
                      (TwoSumF_sum (snd xh) (snd yh))).

  (* Step 5: w = th.t + vh.t *)
  forward.  (* _t'2 = th.t *)
  forward.  (* _t'3 = vh.t *)
  forward.  (* _w = _t'2 + _t'3 *)

  (* Step 6: fast_2sum(st, vh.s, w)
     vh.s = Fast2Sum_sum sh c; w = BPLUS (TwoSumF_err xl yl) (Fast2Sum_err sh c). *)
  forward.  (* _t'1 = vh.s *)
  forward_call (s,
                Fast2Sum_sum (TwoSumF_sum (fst xh) (fst yh))
                             (BPLUS (TwoSumF_err (fst xh) (fst yh))
                                    (TwoSumF_sum (snd xh) (snd yh))),
                BPLUS (TwoSumF_err (snd xh) (snd yh))
                      (Fast2Sum_err (TwoSumF_sum (fst xh) (fst yh))
                                    (BPLUS (TwoSumF_err (fst xh) (fst yh))
                                           (TwoSumF_sum (snd xh) (snd yh))))).

  unfold f2val, AccurateDWPlusDW, TwoSumF, Fast2Sum,
         TwoSumF_sum, TwoSumF_err, Fast2Sum_sum, Fast2Sum_err, fst, snd.
  entailer!.
Qed.
