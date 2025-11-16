Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Require Import DDModels common.
Require Import fast_2mult fp_utils_specs.
Require Import Coq.Bool.Bool.


#[export] Instance CompSpecs : 
  compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Notation emin := (SpecFloat.emin (fprec Tdouble) (femax Tdouble)).

Definition NoOverflowUnderflow_fast_2mult (a b : ftype Tdouble) : Prop :=
  is_finite (BMULT a b) = true /\ 
  (bpow Zaux.radix2 (emin + 2 * fprec Tdouble - 1) <= Rabs (FT2R a * FT2R b))%R. 

Definition dword := Tstruct _dword noattr.

Definition f2val (pq: ftype Tdouble * ftype Tdouble) : val*val :=
 (Vfloat (fst pq), Vfloat (snd pq)).

Definition fast_2mult_spec := 
  DECLARE _fast_2mult
  WITH st: val, a : ftype Tdouble, b : ftype Tdouble
  PRE [ tptr dword, tdouble, tdouble ] (* c lang types *)
    PROP()
    PARAMS (st; Vfloat a; Vfloat b) (*functions params *)
    SEP(data_at_ Tsh dword st) (* preds on mem *)
  POST [ tvoid ]
    PROP(NoOverflowUnderflow_fast_2mult a b)
    RETURN()
    SEP(data_at Tsh dword (f2val (Fast2Mult a b)) st).

Definition exit_spec :=
  DECLARE _exit
  WITH st : val, dw : reptype dword (* frame *)
  PRE [ tint ]
    PROP()
    PARAMS (Vint (Int.repr 1))   (* matches exit(EXIT_FAILURE) *)
    SEP(data_at Tsh dword dw st)
  POST [ tvoid ]
    PROP(False)    (* exit never returns *)
    LOCAL()
    SEP(data_at Tsh dword dw st).

(* Collect the function-API specs together into Gprog: list funspec *)
Definition Gprog : funspecs := MathASI ++ [exit_spec; isnormal_double_spec; isfinite_double_spec; fast_2mult_spec].

Definition tbool (b : bool) : int :=
  if b then Int.one else Int.zero.

(* The function satisfies its API spec (with a semax-body proof) *)
Lemma body_fast_2mult: semax_body Vprog Gprog f_fast_2mult fast_2mult_spec.
Proof.
start_function.
forward.
forward.  (* _t'7 = _st->_s; *) 
forward_call. (* _t'1 = _isfinite_double (_t'7); *)
Intros vret_fin.
set (Post1 :=
  EX b_fin b_nrm : bool, EX t2 : int,
    PROP ( (* meaning of the booleans *)
           b_fin = true <-> is_finite (BMULT a b) = true;
           b_nrm = true <->
             (bpow Zaux.radix2 (emin + 2 * fprec Tdouble - 1)
               <= Rabs (FT2R (BMULT a b)))%R;
           (* how t2 encodes the guard:
              t2 ≠ 0  <->  (¬ b_fin ∨ ¬ b_nrm)  *)
           (Int.eq t2 Int.zero = true <-> (b_fin = true /\ b_nrm = true))
         )
    LOCAL ( temp _t'1 (Vint (tbool b_fin));           (* result of isfinite_double *)
            temp _t'2 (Vint t2);                      (* guard flag *)
            temp _t'7 (Vfloat (BMULT a b));       (* st->s *)
            temp _st st; temp _a (Vfloat a); temp _b (Vfloat b))
SEP (@data_at CompSpecs Tsh dword (Vfloat (Float.mul a b), @snd val val (@default_val CompSpecs dword)) st)).
forward_if Post1.

- (* !isfinite(st->s), so t'2 = 1; *)
forward; unfold Post1.
entailer!.
Exists vret_fin 
  (Rle_bool (bpow Zaux.radix2 (emin + 2 * fprec Tdouble - 1)) (Rabs (FT2R (BMULT a b)))) Int.one.
entailer!. repeat split; try apply Rle_bool_true. admit. admit. admit. admit.

-  (*  isfinite(st->s), now check isnormal_double *)
forward.  (* _t'6 = _st->_s; *) 
forward_call. (* _t'3 = _isnormal_double (_t'6); *)
Intros vret_nrm.
forward. (* _t'2 = (tbool) (!_t'3); *)

unfold Post1.
entailer!.
Exists vret_fin vret_nrm Int.zero.
entailer!.
cbv [bool2val]; destruct vret_nrm; auto. admit. admit.

- (* if (_t'2) exit(EXIT_FAILURE); *)
unfold Post1.
Intros vret t2 t0.
(* Postcondition for the outer if: drop _t'2 from the state *)
set (Post2 :=
  EX vret0 : bool,
    PROP (NoOverflowUnderflow_fast_2mult a b)
    LOCAL ( temp _t'1 (Vint (if vret0 then Int.one else Int.zero));
            temp _t'7 (Vfloat (Float.mul a b));
            temp _st st; temp _a (Vfloat a); temp _b (Vfloat b))
SEP (@data_at CompSpecs Tsh dword (Vfloat (Float.mul a b), @snd val val (@default_val CompSpecs dword)) st)).
forward_if Post2.

+ 
forward_call (st,(Vfloat (Float.mul a b), snd (default_val dword))).
unfold Post2.
entailer!.

+
forward.
unfold Post2.
entailer!.
Exists vret.
entailer!.
destruct H2.
admit.

+ 
unfold Post2.
Intros vret2. 
forward.
forward_call (a,b, (BOPP (BMULT a b))).
forward. 
entailer!.
unfold NoOverflowUnderflow_fast_2mult; split.

Qed.




