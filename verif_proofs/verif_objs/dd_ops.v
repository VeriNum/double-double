From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.17".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "aarch64".
  Definition model := "default".
  Definition abi := "apple".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "dd_lib/dd_ops.c".
  Definition normalized := true.
End Info.

Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_cls : ident := $"__builtin_cls".
Definition ___builtin_clsl : ident := $"__builtin_clsl".
Definition ___builtin_clsll : ident := $"__builtin_clsll".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _a : ident := $"a".
Definition _ap : ident := $"ap".
Definition _b : ident := $"b".
Definition _bp : ident := $"bp".
Definition _c : ident := $"c".
Definition _c2 : ident := $"c2".
Definition _c3 : ident := $"c3".
Definition _ch : ident := $"ch".
Definition _da : ident := $"da".
Definition _db : ident := $"db".
Definition _delta : ident := $"delta".
Definition _dw_div_dw18 : ident := $"dw_div_dw18".
Definition _dw_mult_dw12 : ident := $"dw_mult_dw12".
Definition _dw_mult_fp9 : ident := $"dw_mult_fp9".
Definition _dw_mult_fp9_guarded : ident := $"dw_mult_fp9_guarded".
Definition _dw_mult_fp_check : ident := $"dw_mult_fp_check".
Definition _dw_plus_dw1 : ident := $"dw_plus_dw1".
Definition _dw_plus_dw2 : ident := $"dw_plus_dw2".
Definition _dw_plus_dw2_guarded : ident := $"dw_plus_dw2_guarded".
Definition _dw_plus_dw_check : ident := $"dw_plus_dw_check".
Definition _dw_plus_fp : ident := $"dw_plus_fp".
Definition _dw_plus_fp_check : ident := $"dw_plus_fp_check".
Definition _dw_plus_fp_guarded : ident := $"dw_plus_fp_guarded".
Definition _dword : ident := $"dword".
Definition _e : ident := $"e".
Definition _exit : ident := $"exit".
Definition _fast2_mult_check : ident := $"fast2_mult_check".
Definition _fast2_sum_check : ident := $"fast2_sum_check".
Definition _fast_2mult : ident := $"fast_2mult".
Definition _fast_2mult_guarded : ident := $"fast_2mult_guarded".
Definition _fast_2sum : ident := $"fast_2sum".
Definition _fast_2sum_guarded : ident := $"fast_2sum_guarded".
Definition _fma : ident := $"fma".
Definition _m : ident := $"m".
Definition _main : ident := $"main".
Definition _rh : ident := $"rh".
Definition _rl : ident := $"rl".
Definition _s : ident := $"s".
Definition _sh : ident := $"sh".
Definition _st : ident := $"st".
Definition _t : ident := $"t".
Definition _t0 : ident := $"t0".
Definition _t1 : ident := $"t1".
Definition _th : ident := $"th".
Definition _two_sum : ident := $"two_sum".
Definition _two_sum_check : ident := $"two_sum_check".
Definition _two_sum_guarded : ident := $"two_sum_guarded".
Definition _v : ident := $"v".
Definition _vh : ident := $"vh".
Definition _w : ident := $"w".
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _z : ident := $"z".
Definition _zh : ident := $"zh".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition f_two_sum := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _dword noattr))) :: (_a, tdouble) ::
                (_b, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := ((_ap, tdouble) :: (_bp, tdouble) :: (_da, tdouble) ::
               (_db, tdouble) :: (_t'2, tdouble) :: (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _st (tptr (Tstruct _dword noattr)))
        (Tstruct _dword noattr)) _s tdouble)
    (Ebinop Oadd (Etempvar _a tdouble) (Etempvar _b tdouble) tdouble))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _st (tptr (Tstruct _dword noattr)))
            (Tstruct _dword noattr)) _s tdouble))
      (Sset _ap
        (Ebinop Osub (Etempvar _t'2 tdouble) (Etempvar _b tdouble) tdouble)))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _st (tptr (Tstruct _dword noattr)))
              (Tstruct _dword noattr)) _s tdouble))
        (Sset _bp
          (Ebinop Osub (Etempvar _t'1 tdouble) (Etempvar _ap tdouble)
            tdouble)))
      (Ssequence
        (Sset _da
          (Ebinop Osub (Etempvar _a tdouble) (Etempvar _ap tdouble) tdouble))
        (Ssequence
          (Sset _db
            (Ebinop Osub (Etempvar _b tdouble) (Etempvar _bp tdouble)
              tdouble))
          (Sassign
            (Efield
              (Ederef (Etempvar _st (tptr (Tstruct _dword noattr)))
                (Tstruct _dword noattr)) _t tdouble)
            (Ebinop Oadd (Etempvar _da tdouble) (Etempvar _db tdouble)
              tdouble)))))))
|}.

Definition f_two_sum_guarded := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _dword noattr))) :: (_a, tdouble) ::
                (_b, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _two_sum_check (Tfunction (tdouble :: tdouble :: nil) tint
                             cc_default))
      ((Etempvar _a tdouble) :: (Etempvar _b tdouble) :: nil))
    (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
      (Scall None (Evar _exit (Tfunction (tint :: nil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip))
  (Scall None
    (Evar _two_sum (Tfunction
                     ((tptr (Tstruct _dword noattr)) :: tdouble :: tdouble ::
                      nil) tvoid cc_default))
    ((Etempvar _st (tptr (Tstruct _dword noattr))) ::
     (Etempvar _a tdouble) :: (Etempvar _b tdouble) :: nil)))
|}.

Definition f_fast_2sum := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _dword noattr))) :: (_a, tdouble) ::
                (_b, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := ((_z, tdouble) :: (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _st (tptr (Tstruct _dword noattr)))
        (Tstruct _dword noattr)) _s tdouble)
    (Ebinop Oadd (Etempvar _a tdouble) (Etempvar _b tdouble) tdouble))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _st (tptr (Tstruct _dword noattr)))
            (Tstruct _dword noattr)) _s tdouble))
      (Sset _z
        (Ebinop Osub (Etempvar _t'1 tdouble) (Etempvar _a tdouble) tdouble)))
    (Sassign
      (Efield
        (Ederef (Etempvar _st (tptr (Tstruct _dword noattr)))
          (Tstruct _dword noattr)) _t tdouble)
      (Ebinop Osub (Etempvar _b tdouble) (Etempvar _z tdouble) tdouble))))
|}.

Definition f_fast_2sum_guarded := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _dword noattr))) :: (_a, tdouble) ::
                (_b, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _fast2_sum_check (Tfunction (tdouble :: tdouble :: nil) tint
                               cc_default))
      ((Etempvar _a tdouble) :: (Etempvar _b tdouble) :: nil))
    (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
      (Scall None (Evar _exit (Tfunction (tint :: nil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip))
  (Scall None
    (Evar _fast_2sum (Tfunction
                       ((tptr (Tstruct _dword noattr)) :: tdouble ::
                        tdouble :: nil) tvoid cc_default))
    ((Etempvar _st (tptr (Tstruct _dword noattr))) ::
     (Etempvar _a tdouble) :: (Etempvar _b tdouble) :: nil)))
|}.

Definition f_fast_2mult := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _dword noattr))) :: (_a, tdouble) ::
                (_b, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tdouble) :: (_t'2, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _st (tptr (Tstruct _dword noattr)))
        (Tstruct _dword noattr)) _s tdouble)
    (Ebinop Omul (Etempvar _a tdouble) (Etempvar _b tdouble) tdouble))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _st (tptr (Tstruct _dword noattr)))
            (Tstruct _dword noattr)) _s tdouble))
      (Scall (Some _t'1)
        (Evar _fma (Tfunction (tdouble :: tdouble :: tdouble :: nil) tdouble
                     cc_default))
        ((Etempvar _a tdouble) :: (Etempvar _b tdouble) ::
         (Eunop Oneg (Etempvar _t'2 tdouble) tdouble) :: nil)))
    (Sassign
      (Efield
        (Ederef (Etempvar _st (tptr (Tstruct _dword noattr)))
          (Tstruct _dword noattr)) _t tdouble) (Etempvar _t'1 tdouble))))
|}.

Definition f_fast_2mult_guarded := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _dword noattr))) :: (_a, tdouble) ::
                (_b, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _fast2_mult_check (Tfunction (tdouble :: tdouble :: nil) tint
                                cc_default))
      ((Etempvar _a tdouble) :: (Etempvar _b tdouble) :: nil))
    (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
      (Scall None (Evar _exit (Tfunction (tint :: nil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip))
  (Scall None
    (Evar _fast_2mult (Tfunction
                        ((tptr (Tstruct _dword noattr)) :: tdouble ::
                         tdouble :: nil) tvoid cc_default))
    ((Etempvar _st (tptr (Tstruct _dword noattr))) ::
     (Etempvar _a tdouble) :: (Etempvar _b tdouble) :: nil)))
|}.

Definition f_dw_plus_fp := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _dword noattr))) ::
                (_x, (tptr (Tstruct _dword noattr))) :: (_y, tdouble) :: nil);
  fn_vars := ((_sh, (Tstruct _dword noattr)) :: nil);
  fn_temps := ((_v, tdouble) :: (_t'4, tdouble) :: (_t'3, tdouble) ::
               (_t'2, tdouble) :: (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'4
      (Efield
        (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
          (Tstruct _dword noattr)) _s tdouble))
    (Scall None
      (Evar _two_sum (Tfunction
                       ((tptr (Tstruct _dword noattr)) :: tdouble ::
                        tdouble :: nil) tvoid cc_default))
      ((Eaddrof (Evar _sh (Tstruct _dword noattr))
         (tptr (Tstruct _dword noattr))) :: (Etempvar _t'4 tdouble) ::
       (Etempvar _y tdouble) :: nil)))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
            (Tstruct _dword noattr)) _t tdouble))
      (Ssequence
        (Sset _t'3 (Efield (Evar _sh (Tstruct _dword noattr)) _t tdouble))
        (Sset _v
          (Ebinop Oadd (Etempvar _t'2 tdouble) (Etempvar _t'3 tdouble)
            tdouble))))
    (Ssequence
      (Sset _t'1 (Efield (Evar _sh (Tstruct _dword noattr)) _s tdouble))
      (Scall None
        (Evar _fast_2sum (Tfunction
                           ((tptr (Tstruct _dword noattr)) :: tdouble ::
                            tdouble :: nil) tvoid cc_default))
        ((Etempvar _st (tptr (Tstruct _dword noattr))) ::
         (Etempvar _t'1 tdouble) :: (Etempvar _v tdouble) :: nil)))))
|}.

Definition f_dw_plus_fp_guarded := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _dword noattr))) ::
                (_x, (tptr (Tstruct _dword noattr))) :: (_y, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _dw_plus_fp_check (Tfunction
                                ((tptr (Tstruct _dword noattr)) :: tdouble ::
                                 nil) tint cc_default))
      ((Etempvar _x (tptr (Tstruct _dword noattr))) ::
       (Etempvar _y tdouble) :: nil))
    (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
      (Scall None (Evar _exit (Tfunction (tint :: nil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip))
  (Scall None
    (Evar _dw_plus_fp (Tfunction
                        ((tptr (Tstruct _dword noattr)) ::
                         (tptr (Tstruct _dword noattr)) :: tdouble :: nil)
                        tvoid cc_default))
    ((Etempvar _st (tptr (Tstruct _dword noattr))) ::
     (Etempvar _x (tptr (Tstruct _dword noattr))) :: (Etempvar _y tdouble) ::
     nil)))
|}.

Definition f_dw_plus_dw1 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _dword noattr))) ::
                (_x, (tptr (Tstruct _dword noattr))) ::
                (_y, (tptr (Tstruct _dword noattr))) :: nil);
  fn_vars := ((_sh, (Tstruct _dword noattr)) :: nil);
  fn_temps := ((_v, tdouble) :: (_w, tdouble) :: (_t'6, tdouble) ::
               (_t'5, tdouble) :: (_t'4, tdouble) :: (_t'3, tdouble) ::
               (_t'2, tdouble) :: (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'5
      (Efield
        (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
          (Tstruct _dword noattr)) _s tdouble))
    (Ssequence
      (Sset _t'6
        (Efield
          (Ederef (Etempvar _y (tptr (Tstruct _dword noattr)))
            (Tstruct _dword noattr)) _s tdouble))
      (Scall None
        (Evar _two_sum (Tfunction
                         ((tptr (Tstruct _dword noattr)) :: tdouble ::
                          tdouble :: nil) tvoid cc_default))
        ((Eaddrof (Evar _sh (Tstruct _dword noattr))
           (tptr (Tstruct _dword noattr))) :: (Etempvar _t'5 tdouble) ::
         (Etempvar _t'6 tdouble) :: nil))))
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
            (Tstruct _dword noattr)) _t tdouble))
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _y (tptr (Tstruct _dword noattr)))
              (Tstruct _dword noattr)) _t tdouble))
        (Sset _v
          (Ebinop Oadd (Etempvar _t'3 tdouble) (Etempvar _t'4 tdouble)
            tdouble))))
    (Ssequence
      (Ssequence
        (Sset _t'2 (Efield (Evar _sh (Tstruct _dword noattr)) _t tdouble))
        (Sset _w
          (Ebinop Oadd (Etempvar _t'2 tdouble) (Etempvar _v tdouble) tdouble)))
      (Ssequence
        (Sset _t'1 (Efield (Evar _sh (Tstruct _dword noattr)) _s tdouble))
        (Scall None
          (Evar _fast_2sum (Tfunction
                             ((tptr (Tstruct _dword noattr)) :: tdouble ::
                              tdouble :: nil) tvoid cc_default))
          ((Etempvar _st (tptr (Tstruct _dword noattr))) ::
           (Etempvar _t'1 tdouble) :: (Etempvar _w tdouble) :: nil))))))
|}.

Definition f_dw_plus_dw2 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _dword noattr))) ::
                (_x, (tptr (Tstruct _dword noattr))) ::
                (_y, (tptr (Tstruct _dword noattr))) :: nil);
  fn_vars := ((_sh, (Tstruct _dword noattr)) ::
              (_th, (Tstruct _dword noattr)) ::
              (_vh, (Tstruct _dword noattr)) :: nil);
  fn_temps := ((_c, tdouble) :: (_w, tdouble) :: (_t'10, tdouble) ::
               (_t'9, tdouble) :: (_t'8, tdouble) :: (_t'7, tdouble) ::
               (_t'6, tdouble) :: (_t'5, tdouble) :: (_t'4, tdouble) ::
               (_t'3, tdouble) :: (_t'2, tdouble) :: (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'9
      (Efield
        (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
          (Tstruct _dword noattr)) _s tdouble))
    (Ssequence
      (Sset _t'10
        (Efield
          (Ederef (Etempvar _y (tptr (Tstruct _dword noattr)))
            (Tstruct _dword noattr)) _s tdouble))
      (Scall None
        (Evar _two_sum (Tfunction
                         ((tptr (Tstruct _dword noattr)) :: tdouble ::
                          tdouble :: nil) tvoid cc_default))
        ((Eaddrof (Evar _sh (Tstruct _dword noattr))
           (tptr (Tstruct _dword noattr))) :: (Etempvar _t'9 tdouble) ::
         (Etempvar _t'10 tdouble) :: nil))))
  (Ssequence
    (Ssequence
      (Sset _t'7
        (Efield
          (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
            (Tstruct _dword noattr)) _t tdouble))
      (Ssequence
        (Sset _t'8
          (Efield
            (Ederef (Etempvar _y (tptr (Tstruct _dword noattr)))
              (Tstruct _dword noattr)) _t tdouble))
        (Scall None
          (Evar _two_sum (Tfunction
                           ((tptr (Tstruct _dword noattr)) :: tdouble ::
                            tdouble :: nil) tvoid cc_default))
          ((Eaddrof (Evar _th (Tstruct _dword noattr))
             (tptr (Tstruct _dword noattr))) :: (Etempvar _t'7 tdouble) ::
           (Etempvar _t'8 tdouble) :: nil))))
    (Ssequence
      (Ssequence
        (Sset _t'5 (Efield (Evar _sh (Tstruct _dword noattr)) _t tdouble))
        (Ssequence
          (Sset _t'6 (Efield (Evar _th (Tstruct _dword noattr)) _s tdouble))
          (Sset _c
            (Ebinop Oadd (Etempvar _t'5 tdouble) (Etempvar _t'6 tdouble)
              tdouble))))
      (Ssequence
        (Ssequence
          (Sset _t'4 (Efield (Evar _sh (Tstruct _dword noattr)) _s tdouble))
          (Scall None
            (Evar _fast_2sum (Tfunction
                               ((tptr (Tstruct _dword noattr)) :: tdouble ::
                                tdouble :: nil) tvoid cc_default))
            ((Eaddrof (Evar _vh (Tstruct _dword noattr))
               (tptr (Tstruct _dword noattr))) :: (Etempvar _t'4 tdouble) ::
             (Etempvar _c tdouble) :: nil)))
        (Ssequence
          (Ssequence
            (Sset _t'2
              (Efield (Evar _th (Tstruct _dword noattr)) _t tdouble))
            (Ssequence
              (Sset _t'3
                (Efield (Evar _vh (Tstruct _dword noattr)) _t tdouble))
              (Sset _w
                (Ebinop Oadd (Etempvar _t'2 tdouble) (Etempvar _t'3 tdouble)
                  tdouble))))
          (Ssequence
            (Sset _t'1
              (Efield (Evar _vh (Tstruct _dword noattr)) _s tdouble))
            (Scall None
              (Evar _fast_2sum (Tfunction
                                 ((tptr (Tstruct _dword noattr)) ::
                                  tdouble :: tdouble :: nil) tvoid
                                 cc_default))
              ((Etempvar _st (tptr (Tstruct _dword noattr))) ::
               (Etempvar _t'1 tdouble) :: (Etempvar _w tdouble) :: nil))))))))
|}.

Definition f_dw_plus_dw2_guarded := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _dword noattr))) ::
                (_x, (tptr (Tstruct _dword noattr))) ::
                (_y, (tptr (Tstruct _dword noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _dw_plus_dw_check (Tfunction
                                ((tptr (Tstruct _dword noattr)) ::
                                 (tptr (Tstruct _dword noattr)) :: nil) tint
                                cc_default))
      ((Etempvar _x (tptr (Tstruct _dword noattr))) ::
       (Etempvar _y (tptr (Tstruct _dword noattr))) :: nil))
    (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
      (Scall None (Evar _exit (Tfunction (tint :: nil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip))
  (Scall None
    (Evar _dw_plus_dw2 (Tfunction
                         ((tptr (Tstruct _dword noattr)) ::
                          (tptr (Tstruct _dword noattr)) ::
                          (tptr (Tstruct _dword noattr)) :: nil) tvoid
                         cc_default))
    ((Etempvar _st (tptr (Tstruct _dword noattr))) ::
     (Etempvar _x (tptr (Tstruct _dword noattr))) ::
     (Etempvar _y (tptr (Tstruct _dword noattr))) :: nil)))
|}.

Definition f_dw_mult_fp9 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_zh, (tptr (Tstruct _dword noattr))) ::
                (_x, (tptr (Tstruct _dword noattr))) :: (_y, tdouble) :: nil);
  fn_vars := ((_ch, (Tstruct _dword noattr)) :: nil);
  fn_temps := ((_c3, tdouble) :: (_t'1, tdouble) :: (_t'5, tdouble) ::
               (_t'4, tdouble) :: (_t'3, tdouble) :: (_t'2, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'5
      (Efield
        (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
          (Tstruct _dword noattr)) _s tdouble))
    (Scall None
      (Evar _fast_2mult (Tfunction
                          ((tptr (Tstruct _dword noattr)) :: tdouble ::
                           tdouble :: nil) tvoid cc_default))
      ((Eaddrof (Evar _ch (Tstruct _dword noattr))
         (tptr (Tstruct _dword noattr))) :: (Etempvar _t'5 tdouble) ::
       (Etempvar _y tdouble) :: nil)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
              (Tstruct _dword noattr)) _t tdouble))
        (Ssequence
          (Sset _t'4 (Efield (Evar _ch (Tstruct _dword noattr)) _t tdouble))
          (Scall (Some _t'1)
            (Evar _fma (Tfunction (tdouble :: tdouble :: tdouble :: nil)
                         tdouble cc_default))
            ((Etempvar _t'3 tdouble) :: (Etempvar _y tdouble) ::
             (Etempvar _t'4 tdouble) :: nil))))
      (Sset _c3 (Etempvar _t'1 tdouble)))
    (Ssequence
      (Sset _t'2 (Efield (Evar _ch (Tstruct _dword noattr)) _s tdouble))
      (Scall None
        (Evar _fast_2sum (Tfunction
                           ((tptr (Tstruct _dword noattr)) :: tdouble ::
                            tdouble :: nil) tvoid cc_default))
        ((Etempvar _zh (tptr (Tstruct _dword noattr))) ::
         (Etempvar _t'2 tdouble) :: (Etempvar _c3 tdouble) :: nil)))))
|}.

Definition f_dw_mult_fp9_guarded := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _dword noattr))) ::
                (_x, (tptr (Tstruct _dword noattr))) :: (_y, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _dw_mult_fp_check (Tfunction
                                ((tptr (Tstruct _dword noattr)) :: tdouble ::
                                 nil) tint cc_default))
      ((Etempvar _x (tptr (Tstruct _dword noattr))) ::
       (Etempvar _y tdouble) :: nil))
    (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
      (Scall None (Evar _exit (Tfunction (tint :: nil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip))
  (Scall None
    (Evar _dw_mult_fp9 (Tfunction
                         ((tptr (Tstruct _dword noattr)) ::
                          (tptr (Tstruct _dword noattr)) :: tdouble :: nil)
                         tvoid cc_default))
    ((Etempvar _st (tptr (Tstruct _dword noattr))) ::
     (Etempvar _x (tptr (Tstruct _dword noattr))) :: (Etempvar _y tdouble) ::
     nil)))
|}.

Definition f_dw_mult_dw12 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_zh, (tptr (Tstruct _dword noattr))) ::
                (_x, (tptr (Tstruct _dword noattr))) ::
                (_y, (tptr (Tstruct _dword noattr))) :: nil);
  fn_vars := ((_ch, (Tstruct _dword noattr)) :: nil);
  fn_temps := ((_t0, tdouble) :: (_t1, tdouble) :: (_c2, tdouble) ::
               (_c3, tdouble) :: (_t'2, tdouble) :: (_t'1, tdouble) ::
               (_t'12, tdouble) :: (_t'11, tdouble) :: (_t'10, tdouble) ::
               (_t'9, tdouble) :: (_t'8, tdouble) :: (_t'7, tdouble) ::
               (_t'6, tdouble) :: (_t'5, tdouble) :: (_t'4, tdouble) ::
               (_t'3, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'11
      (Efield
        (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
          (Tstruct _dword noattr)) _s tdouble))
    (Ssequence
      (Sset _t'12
        (Efield
          (Ederef (Etempvar _y (tptr (Tstruct _dword noattr)))
            (Tstruct _dword noattr)) _s tdouble))
      (Scall None
        (Evar _fast_2mult (Tfunction
                            ((tptr (Tstruct _dword noattr)) :: tdouble ::
                             tdouble :: nil) tvoid cc_default))
        ((Eaddrof (Evar _ch (Tstruct _dword noattr))
           (tptr (Tstruct _dword noattr))) :: (Etempvar _t'11 tdouble) ::
         (Etempvar _t'12 tdouble) :: nil))))
  (Ssequence
    (Ssequence
      (Sset _t'9
        (Efield
          (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
            (Tstruct _dword noattr)) _t tdouble))
      (Ssequence
        (Sset _t'10
          (Efield
            (Ederef (Etempvar _y (tptr (Tstruct _dword noattr)))
              (Tstruct _dword noattr)) _t tdouble))
        (Sset _t0
          (Ebinop Omul (Etempvar _t'9 tdouble) (Etempvar _t'10 tdouble)
            tdouble))))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'7
            (Efield
              (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                (Tstruct _dword noattr)) _s tdouble))
          (Ssequence
            (Sset _t'8
              (Efield
                (Ederef (Etempvar _y (tptr (Tstruct _dword noattr)))
                  (Tstruct _dword noattr)) _t tdouble))
            (Scall (Some _t'1)
              (Evar _fma (Tfunction (tdouble :: tdouble :: tdouble :: nil)
                           tdouble cc_default))
              ((Etempvar _t'7 tdouble) :: (Etempvar _t'8 tdouble) ::
               (Etempvar _t0 tdouble) :: nil))))
        (Sset _t1 (Etempvar _t'1 tdouble)))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                  (Tstruct _dword noattr)) _t tdouble))
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _y (tptr (Tstruct _dword noattr)))
                    (Tstruct _dword noattr)) _s tdouble))
              (Scall (Some _t'2)
                (Evar _fma (Tfunction (tdouble :: tdouble :: tdouble :: nil)
                             tdouble cc_default))
                ((Etempvar _t'5 tdouble) :: (Etempvar _t'6 tdouble) ::
                 (Etempvar _t1 tdouble) :: nil))))
          (Sset _c2 (Etempvar _t'2 tdouble)))
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Efield (Evar _ch (Tstruct _dword noattr)) _t tdouble))
            (Sset _c3
              (Ebinop Oadd (Etempvar _t'4 tdouble) (Etempvar _c2 tdouble)
                tdouble)))
          (Ssequence
            (Sset _t'3
              (Efield (Evar _ch (Tstruct _dword noattr)) _s tdouble))
            (Scall None
              (Evar _fast_2sum (Tfunction
                                 ((tptr (Tstruct _dword noattr)) ::
                                  tdouble :: tdouble :: nil) tvoid
                                 cc_default))
              ((Etempvar _zh (tptr (Tstruct _dword noattr))) ::
               (Etempvar _t'3 tdouble) :: (Etempvar _c3 tdouble) :: nil))))))))
|}.

Definition f_dw_div_dw18 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_z, (tptr (Tstruct _dword noattr))) ::
                (_x, (tptr (Tstruct _dword noattr))) ::
                (_y, (tptr (Tstruct _dword noattr))) :: nil);
  fn_vars := ((_e, (Tstruct _dword noattr)) ::
              (_delta, (Tstruct _dword noattr)) ::
              (_m, (Tstruct _dword noattr)) :: nil);
  fn_temps := ((_th, tdouble) :: (_rh, tdouble) :: (_rl, tdouble) ::
               (_t'1, tdouble) :: (_t'4, tdouble) :: (_t'3, tdouble) ::
               (_t'2, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'4
      (Efield
        (Ederef (Etempvar _y (tptr (Tstruct _dword noattr)))
          (Tstruct _dword noattr)) _s tdouble))
    (Sset _th
      (Ebinop Odiv
        (Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble)
        (Etempvar _t'4 tdouble) tdouble)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _y (tptr (Tstruct _dword noattr)))
              (Tstruct _dword noattr)) _s tdouble))
        (Scall (Some _t'1)
          (Evar _fma (Tfunction (tdouble :: tdouble :: tdouble :: nil)
                       tdouble cc_default))
          ((Eunop Oneg (Etempvar _t'3 tdouble) tdouble) ::
           (Etempvar _th tdouble) ::
           (Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble) ::
           nil)))
      (Sset _rh (Etempvar _t'1 tdouble)))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _y (tptr (Tstruct _dword noattr)))
              (Tstruct _dword noattr)) _t tdouble))
        (Sset _rl
          (Eunop Oneg
            (Ebinop Omul (Etempvar _t'2 tdouble) (Etempvar _th tdouble)
              tdouble) tdouble)))
      (Ssequence
        (Scall None
          (Evar _fast_2sum (Tfunction
                             ((tptr (Tstruct _dword noattr)) :: tdouble ::
                              tdouble :: nil) tvoid cc_default))
          ((Eaddrof (Evar _e (Tstruct _dword noattr))
             (tptr (Tstruct _dword noattr))) :: (Etempvar _rh tdouble) ::
           (Etempvar _rl tdouble) :: nil))
        (Ssequence
          (Scall None
            (Evar _dw_mult_fp9 (Tfunction
                                 ((tptr (Tstruct _dword noattr)) ::
                                  (tptr (Tstruct _dword noattr)) ::
                                  tdouble :: nil) tvoid cc_default))
            ((Eaddrof (Evar _delta (Tstruct _dword noattr))
               (tptr (Tstruct _dword noattr))) ::
             (Eaddrof (Evar _e (Tstruct _dword noattr))
               (tptr (Tstruct _dword noattr))) :: (Etempvar _th tdouble) ::
             nil))
          (Ssequence
            (Scall None
              (Evar _dw_plus_fp (Tfunction
                                  ((tptr (Tstruct _dword noattr)) ::
                                   (tptr (Tstruct _dword noattr)) ::
                                   tdouble :: nil) tvoid cc_default))
              ((Eaddrof (Evar _m (Tstruct _dword noattr))
                 (tptr (Tstruct _dword noattr))) ::
               (Eaddrof (Evar _delta (Tstruct _dword noattr))
                 (tptr (Tstruct _dword noattr))) :: (Etempvar _th tdouble) ::
               nil))
            (Scall None
              (Evar _dw_mult_dw12 (Tfunction
                                    ((tptr (Tstruct _dword noattr)) ::
                                     (tptr (Tstruct _dword noattr)) ::
                                     (tptr (Tstruct _dword noattr)) :: nil)
                                    tvoid cc_default))
              ((Etempvar _z (tptr (Tstruct _dword noattr))) ::
               (Etempvar _x (tptr (Tstruct _dword noattr))) ::
               (Eaddrof (Evar _m (Tstruct _dword noattr))
                 (tptr (Tstruct _dword noattr))) :: nil))))))))
|}.

Definition composites : list composite_definition :=
(Composite _dword Struct
   (Member_plain _s tdouble :: Member_plain _t tdouble :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tvoid) :: nil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tvoid) :: nil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr tvoid) :: nil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tulong :: nil)
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tlong :: nil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tulong :: nil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tlong :: nil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tulong :: nil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tulong :: tint :: nil) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Xlong :: nil) AST.Xlong cc_default))
     (tulong :: nil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Xint16unsigned :: nil)
                     AST.Xint16unsigned cc_default)) (tushort :: nil) tushort
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Xsingle :: nil) AST.Xsingle cc_default))
     (tfloat :: nil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: tulong :: nil) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Xbool :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tbool :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tschar) :: tint :: nil) tint
     cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
     cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___builtin_cls,
   Gfun(External (EF_builtin "__builtin_cls"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tint :: nil) tint cc_default)) ::
 (___builtin_clsl,
   Gfun(External (EF_builtin "__builtin_clsl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tlong :: nil) tint cc_default)) ::
 (___builtin_clsll,
   Gfun(External (EF_builtin "__builtin_clsll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tlong :: nil) tint cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_fma,
   Gfun(External (EF_external "fma"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (_two_sum, Gfun(Internal f_two_sum)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Xint :: nil) AST.Xvoid cc_default))
     (tint :: nil) tvoid cc_default)) ::
 (_fast2_sum_check,
   Gfun(External (EF_external "fast2_sum_check"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xint
                     cc_default)) (tdouble :: tdouble :: nil) tint
     cc_default)) ::
 (_two_sum_check,
   Gfun(External (EF_external "two_sum_check"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xint
                     cc_default)) (tdouble :: tdouble :: nil) tint
     cc_default)) ::
 (_fast2_mult_check,
   Gfun(External (EF_external "fast2_mult_check"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xint
                     cc_default)) (tdouble :: tdouble :: nil) tint
     cc_default)) ::
 (_dw_plus_dw_check,
   Gfun(External (EF_external "dw_plus_dw_check"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xint
                     cc_default))
     ((tptr (Tstruct _dword noattr)) :: (tptr (Tstruct _dword noattr)) ::
      nil) tint cc_default)) ::
 (_dw_plus_fp_check,
   Gfun(External (EF_external "dw_plus_fp_check"
                   (mksignature (AST.Xptr :: AST.Xfloat :: nil) AST.Xint
                     cc_default))
     ((tptr (Tstruct _dword noattr)) :: tdouble :: nil) tint cc_default)) ::
 (_dw_mult_fp_check,
   Gfun(External (EF_external "dw_mult_fp_check"
                   (mksignature (AST.Xptr :: AST.Xfloat :: nil) AST.Xint
                     cc_default))
     ((tptr (Tstruct _dword noattr)) :: tdouble :: nil) tint cc_default)) ::
 (_two_sum_guarded, Gfun(Internal f_two_sum_guarded)) ::
 (_fast_2sum, Gfun(Internal f_fast_2sum)) ::
 (_fast_2sum_guarded, Gfun(Internal f_fast_2sum_guarded)) ::
 (_fast_2mult, Gfun(Internal f_fast_2mult)) ::
 (_fast_2mult_guarded, Gfun(Internal f_fast_2mult_guarded)) ::
 (_dw_plus_fp, Gfun(Internal f_dw_plus_fp)) ::
 (_dw_plus_fp_guarded, Gfun(Internal f_dw_plus_fp_guarded)) ::
 (_dw_plus_dw1, Gfun(Internal f_dw_plus_dw1)) ::
 (_dw_plus_dw2, Gfun(Internal f_dw_plus_dw2)) ::
 (_dw_plus_dw2_guarded, Gfun(Internal f_dw_plus_dw2_guarded)) ::
 (_dw_mult_fp9, Gfun(Internal f_dw_mult_fp9)) ::
 (_dw_mult_fp9_guarded, Gfun(Internal f_dw_mult_fp9_guarded)) ::
 (_dw_mult_dw12, Gfun(Internal f_dw_mult_dw12)) ::
 (_dw_div_dw18, Gfun(Internal f_dw_div_dw18)) :: nil).

Definition public_idents : list ident :=
(_dw_div_dw18 :: _dw_mult_dw12 :: _dw_mult_fp9_guarded :: _dw_mult_fp9 ::
 _dw_plus_dw2_guarded :: _dw_plus_dw2 :: _dw_plus_dw1 ::
 _dw_plus_fp_guarded :: _dw_plus_fp :: _fast_2mult_guarded :: _fast_2mult ::
 _fast_2sum_guarded :: _fast_2sum :: _two_sum_guarded :: _dw_mult_fp_check ::
 _dw_plus_fp_check :: _dw_plus_dw_check :: _fast2_mult_check ::
 _two_sum_check :: _fast2_sum_check :: _exit :: _two_sum :: _fma ::
 ___builtin_debug :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_clsll :: ___builtin_clsl :: ___builtin_cls ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


