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
  Definition source_file := "dd_lib/fp_utils.c".
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
Definition _b : ident := $"b".
Definition _dw_div_dw_check : ident := $"dw_div_dw_check".
Definition _dw_div_fp_check : ident := $"dw_div_fp_check".
Definition _dw_mult_dw_check : ident := $"dw_mult_dw_check".
Definition _dw_mult_fp_check : ident := $"dw_mult_fp_check".
Definition _dw_plus_dw_check : ident := $"dw_plus_dw_check".
Definition _dw_plus_fp_check : ident := $"dw_plus_fp_check".
Definition _dw_plus_fp_input_check : ident := $"dw_plus_fp_input_check".
Definition _dword : ident := $"dword".
Definition _dword_finite_check : ident := $"dword_finite_check".
Definition _dwx : ident := $"dwx".
Definition _dwy : ident := $"dwy".
Definition _fabs : ident := $"fabs".
Definition _fast2_mult_acc_check : ident := $"fast2_mult_acc_check".
Definition _fast2_mult_check : ident := $"fast2_mult_check".
Definition _fast2_sum_check : ident := $"fast2_sum_check".
Definition _fin : ident := $"fin".
Definition _fin_diff : ident := $"fin_diff".
Definition _fin_s : ident := $"fin_s".
Definition _fin_sum : ident := $"fin_sum".
Definition _fin_t : ident := $"fin_t".
Definition _fin_xh : ident := $"fin_xh".
Definition _fin_xl : ident := $"fin_xl".
Definition _fin_y : ident := $"fin_y".
Definition _fin_yh : ident := $"fin_yh".
Definition _fin_yl : ident := $"fin_yl".
Definition _isfinite_double : ident := $"isfinite_double".
Definition _ldexp : ident := $"ldexp".
Definition _main : ident := $"main".
Definition _prod_bnd : ident := $"prod_bnd".
Definition _q : ident := $"q".
Definition _q_omega : ident := $"q_omega".
Definition _q_plo : ident := $"q_plo".
Definition _q_prod : ident := $"q_prod".
Definition _q_yhi : ident := $"q_yhi".
Definition _q_ylo : ident := $"q_ylo".
Definition _qt_hi : ident := $"qt_hi".
Definition _s : ident := $"s".
Definition _t : ident := $"t".
Definition _thresh : ident := $"thresh".
Definition _two_sum_check : ident := $"two_sum_check".
Definition _x : ident := $"x".
Definition _xh_bnd : ident := $"xh_bnd".
Definition _xh_hi : ident := $"xh_hi".
Definition _xh_lo : ident := $"xh_lo".
Definition _y : ident := $"y".
Definition _y_bnd : ident := $"y_bnd".
Definition _yh_bnd : ident := $"yh_bnd".
Definition _yh_hi : ident := $"yh_hi".
Definition _yh_lo : ident := $"yh_lo".
Definition _z : ident := $"z".
Definition _zx : ident := $"zx".
Definition _zy : ident := $"zy".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'18 : ident := 145%positive.
Definition _t'19 : ident := 146%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'20 : ident := 147%positive.
Definition _t'21 : ident := 148%positive.
Definition _t'22 : ident := 149%positive.
Definition _t'23 : ident := 150%positive.
Definition _t'24 : ident := 151%positive.
Definition _t'25 : ident := 152%positive.
Definition _t'26 : ident := 153%positive.
Definition _t'27 : ident := 154%positive.
Definition _t'28 : ident := 155%positive.
Definition _t'29 : ident := 156%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'30 : ident := 157%positive.
Definition _t'31 : ident := 158%positive.
Definition _t'32 : ident := 159%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition f_isfinite_double := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oeq
                 (Ebinop Osub (Etempvar _x tdouble) (Etempvar _x tdouble)
                   tdouble)
                 (Econst_float (Float.of_bits (Int64.repr 0)) tdouble) tint)))
|}.

Definition f_fast2_mult_check := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, tdouble) :: (_y, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := ((_z, tdouble) :: (_thresh, tdouble) :: (_fin, tint) ::
               (_zx, tint) :: (_zy, tint) :: (_t'9, tdouble) ::
               (_t'8, tint) :: (_t'7, tint) :: (_t'6, tint) ::
               (_t'5, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Sset _z (Ebinop Omul (Etempvar _x tdouble) (Etempvar _y tdouble) tdouble))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _ldexp (Tfunction (tdouble :: tint :: nil) tdouble cc_default))
        ((Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble) ::
         (Econst_int (Int.repr 53) tint) :: nil))
      (Sset _thresh
        (Ebinop Omul
          (Econst_float (Float.of_bits (Int64.repr 4503599627370496)) tdouble)
          (Etempvar _t'1 tdouble) tdouble)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
          ((Etempvar _z tdouble) :: nil))
        (Sset _fin (Etempvar _t'2 tint)))
      (Ssequence
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _x tdouble)
                         (Econst_float (Float.of_bits (Int64.repr 0)) tdouble)
                         tint)
            (Ssequence
              (Scall (Some _t'4)
                (Evar _isfinite_double (Tfunction (tdouble :: nil) tint
                                         cc_default))
                ((Etempvar _y tdouble) :: nil))
              (Sset _t'3 (Ecast (Etempvar _t'4 tint) tbool)))
            (Sset _t'3 (Econst_int (Int.repr 0) tint)))
          (Sset _zx (Etempvar _t'3 tint)))
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _y tdouble)
                           (Econst_float (Float.of_bits (Int64.repr 0)) tdouble)
                           tint)
              (Ssequence
                (Scall (Some _t'6)
                  (Evar _isfinite_double (Tfunction (tdouble :: nil) tint
                                           cc_default))
                  ((Etempvar _x tdouble) :: nil))
                (Sset _t'5 (Ecast (Etempvar _t'6 tint) tbool)))
              (Sset _t'5 (Econst_int (Int.repr 0) tint)))
            (Sset _zy (Etempvar _t'5 tint)))
          (Ssequence
            (Sifthenelse (Etempvar _fin tint)
              (Ssequence
                (Sifthenelse (Etempvar _zx tint)
                  (Sset _t'8 (Econst_int (Int.repr 1) tint))
                  (Sset _t'8 (Ecast (Etempvar _zy tint) tbool)))
                (Sifthenelse (Etempvar _t'8 tint)
                  (Sset _t'7 (Ecast (Econst_int (Int.repr 1) tint) tbool))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'9)
                        (Evar _fabs (Tfunction (tdouble :: nil) tdouble
                                      cc_default))
                        ((Etempvar _z tdouble) :: nil))
                      (Sset _t'7
                        (Ecast
                          (Ebinop Olt (Etempvar _thresh tdouble)
                            (Etempvar _t'9 tdouble) tint) tbool)))
                    (Sset _t'7 (Ecast (Etempvar _t'7 tint) tbool)))))
              (Sset _t'7 (Econst_int (Int.repr 0) tint)))
            (Sreturn (Some (Etempvar _t'7 tint)))))))))
|}.

Definition f_fast2_mult_acc_check := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, tdouble) :: (_y, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
    ((Ebinop Omul (Etempvar _x tdouble) (Etempvar _y tdouble) tdouble) ::
     nil))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition f_fast2_sum_check := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, tdouble) :: (_b, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := ((_s, tdouble) :: (_fin, tint) :: (_t'4, tdouble) ::
               (_t'3, tdouble) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _s (Ebinop Oadd (Etempvar _a tdouble) (Etempvar _b tdouble) tdouble))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
        ((Etempvar _s tdouble) :: nil))
      (Sset _fin (Etempvar _t'1 tint)))
    (Ssequence
      (Sifthenelse (Etempvar _fin tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _fabs (Tfunction (tdouble :: nil) tdouble cc_default))
              ((Etempvar _b tdouble) :: nil))
            (Scall (Some _t'4)
              (Evar _fabs (Tfunction (tdouble :: nil) tdouble cc_default))
              ((Etempvar _a tdouble) :: nil)))
          (Sset _t'2
            (Ecast
              (Ebinop Ole (Etempvar _t'3 tdouble) (Etempvar _t'4 tdouble)
                tint) tbool)))
        (Sset _t'2 (Econst_int (Int.repr 0) tint)))
      (Sreturn (Some (Etempvar _t'2 tint))))))
|}.

Definition f_two_sum_check := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, tdouble) :: (_b, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := ((_fin_sum, tint) :: (_fin_diff, tint) :: (_t'5, tdouble) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
      ((Ebinop Oadd (Etempvar _a tdouble) (Etempvar _b tdouble) tdouble) ::
       nil))
    (Sset _fin_sum (Etempvar _t'1 tint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
        ((Ebinop Osub (Etempvar _a tdouble) (Etempvar _b tdouble) tdouble) ::
         nil))
      (Sset _fin_diff (Etempvar _t'2 tint)))
    (Ssequence
      (Ssequence
        (Sifthenelse (Etempvar _fin_sum tint)
          (Sset _t'3 (Ecast (Etempvar _fin_diff tint) tbool))
          (Sset _t'3 (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar _t'3 tint)
          (Ssequence
            (Scall (Some _t'5)
              (Evar _fabs (Tfunction (tdouble :: nil) tdouble cc_default))
              ((Etempvar _b tdouble) :: nil))
            (Sset _t'4
              (Ecast
                (Ebinop Olt (Etempvar _t'5 tdouble)
                  (Econst_float (Float.of_bits (Int64.repr 9218868437227405311)) tdouble)
                  tint) tbool)))
          (Sset _t'4 (Econst_int (Int.repr 0) tint))))
      (Sreturn (Some (Etempvar _t'4 tint))))))
|}.

Definition f_dw_plus_dw_check := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _dword noattr))) ::
                (_y, (tptr (Tstruct _dword noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_fin_xh, tint) :: (_fin_xl, tint) :: (_fin_yh, tint) ::
               (_fin_yl, tint) :: (_dwx, tint) :: (_dwy, tint) ::
               (_q_omega, tdouble) :: (_xh_bnd, tint) :: (_yh_bnd, tint) ::
               (_t'14, tint) :: (_t'13, tint) :: (_t'12, tint) ::
               (_t'11, tdouble) :: (_t'10, tdouble) :: (_t'9, tdouble) ::
               (_t'8, tint) :: (_t'7, tint) :: (_t'6, tint) ::
               (_t'5, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: (_t'26, tdouble) ::
               (_t'25, tdouble) :: (_t'24, tdouble) :: (_t'23, tdouble) ::
               (_t'22, tdouble) :: (_t'21, tdouble) :: (_t'20, tdouble) ::
               (_t'19, tdouble) :: (_t'18, tdouble) :: (_t'17, tdouble) ::
               (_t'16, tdouble) :: (_t'15, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'26
        (Efield
          (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
            (Tstruct _dword noattr)) _s tdouble))
      (Scall (Some _t'1)
        (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
        ((Etempvar _t'26 tdouble) :: nil)))
    (Sset _fin_xh (Etempvar _t'1 tint)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'25
          (Efield
            (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
              (Tstruct _dword noattr)) _t tdouble))
        (Scall (Some _t'2)
          (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
          ((Etempvar _t'25 tdouble) :: nil)))
      (Sset _fin_xl (Etempvar _t'2 tint)))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'24
            (Efield
              (Ederef (Etempvar _y (tptr (Tstruct _dword noattr)))
                (Tstruct _dword noattr)) _s tdouble))
          (Scall (Some _t'3)
            (Evar _isfinite_double (Tfunction (tdouble :: nil) tint
                                     cc_default))
            ((Etempvar _t'24 tdouble) :: nil)))
        (Sset _fin_yh (Etempvar _t'3 tint)))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'23
              (Efield
                (Ederef (Etempvar _y (tptr (Tstruct _dword noattr)))
                  (Tstruct _dword noattr)) _t tdouble))
            (Scall (Some _t'4)
              (Evar _isfinite_double (Tfunction (tdouble :: nil) tint
                                       cc_default))
              ((Etempvar _t'23 tdouble) :: nil)))
          (Sset _fin_yl (Etempvar _t'4 tint)))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sifthenelse (Etempvar _fin_xh tint)
                (Sset _t'5 (Ecast (Etempvar _fin_xl tint) tbool))
                (Sset _t'5 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'5 tint)
                (Ssequence
                  (Sset _t'20
                    (Efield
                      (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                        (Tstruct _dword noattr)) _s tdouble))
                  (Ssequence
                    (Sset _t'21
                      (Efield
                        (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                          (Tstruct _dword noattr)) _t tdouble))
                    (Ssequence
                      (Sset _t'22
                        (Efield
                          (Ederef
                            (Etempvar _x (tptr (Tstruct _dword noattr)))
                            (Tstruct _dword noattr)) _s tdouble))
                      (Sset _t'6
                        (Ecast
                          (Ebinop Oeq
                            (Ebinop Oadd (Etempvar _t'20 tdouble)
                              (Etempvar _t'21 tdouble) tdouble)
                            (Etempvar _t'22 tdouble) tint) tbool)))))
                (Sset _t'6 (Econst_int (Int.repr 0) tint))))
            (Sset _dwx (Etempvar _t'6 tint)))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sifthenelse (Etempvar _fin_yh tint)
                  (Sset _t'7 (Ecast (Etempvar _fin_yl tint) tbool))
                  (Sset _t'7 (Econst_int (Int.repr 0) tint)))
                (Sifthenelse (Etempvar _t'7 tint)
                  (Ssequence
                    (Sset _t'17
                      (Efield
                        (Ederef (Etempvar _y (tptr (Tstruct _dword noattr)))
                          (Tstruct _dword noattr)) _s tdouble))
                    (Ssequence
                      (Sset _t'18
                        (Efield
                          (Ederef
                            (Etempvar _y (tptr (Tstruct _dword noattr)))
                            (Tstruct _dword noattr)) _t tdouble))
                      (Ssequence
                        (Sset _t'19
                          (Efield
                            (Ederef
                              (Etempvar _y (tptr (Tstruct _dword noattr)))
                              (Tstruct _dword noattr)) _s tdouble))
                        (Sset _t'8
                          (Ecast
                            (Ebinop Oeq
                              (Ebinop Oadd (Etempvar _t'17 tdouble)
                                (Etempvar _t'18 tdouble) tdouble)
                              (Etempvar _t'19 tdouble) tint) tbool)))))
                  (Sset _t'8 (Econst_int (Int.repr 0) tint))))
              (Sset _dwy (Etempvar _t'8 tint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'9)
                  (Evar _ldexp (Tfunction (tdouble :: tint :: nil) tdouble
                                 cc_default))
                  ((Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble) ::
                   (Econst_int (Int.repr 1022) tint) :: nil))
                (Sset _q_omega (Etempvar _t'9 tdouble)))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'16
                      (Efield
                        (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                          (Tstruct _dword noattr)) _s tdouble))
                    (Scall (Some _t'10)
                      (Evar _fabs (Tfunction (tdouble :: nil) tdouble
                                    cc_default))
                      ((Etempvar _t'16 tdouble) :: nil)))
                  (Sset _xh_bnd
                    (Ebinop Ole (Etempvar _t'10 tdouble)
                      (Etempvar _q_omega tdouble) tint)))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sset _t'15
                        (Efield
                          (Ederef
                            (Etempvar _y (tptr (Tstruct _dword noattr)))
                            (Tstruct _dword noattr)) _s tdouble))
                      (Scall (Some _t'11)
                        (Evar _fabs (Tfunction (tdouble :: nil) tdouble
                                      cc_default))
                        ((Etempvar _t'15 tdouble) :: nil)))
                    (Sset _yh_bnd
                      (Ebinop Ole (Etempvar _t'11 tdouble)
                        (Etempvar _q_omega tdouble) tint)))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sifthenelse (Etempvar _dwx tint)
                          (Sset _t'12 (Ecast (Etempvar _dwy tint) tbool))
                          (Sset _t'12 (Econst_int (Int.repr 0) tint)))
                        (Sifthenelse (Etempvar _t'12 tint)
                          (Sset _t'13 (Ecast (Etempvar _xh_bnd tint) tbool))
                          (Sset _t'13 (Econst_int (Int.repr 0) tint))))
                      (Sifthenelse (Etempvar _t'13 tint)
                        (Sset _t'14 (Ecast (Etempvar _yh_bnd tint) tbool))
                        (Sset _t'14 (Econst_int (Int.repr 0) tint))))
                    (Sreturn (Some (Etempvar _t'14 tint)))))))))))))
|}.

Definition f_dw_mult_fp_check := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _dword noattr))) :: (_y, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := ((_fin_xh, tint) :: (_fin_xl, tint) :: (_fin_y, tint) ::
               (_dwx, tint) :: (_z, tdouble) :: (_q_prod, tdouble) ::
               (_prod_bnd, tint) :: (_t'9, tint) :: (_t'8, tint) ::
               (_t'7, tdouble) :: (_t'6, tdouble) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'15, tdouble) :: (_t'14, tdouble) ::
               (_t'13, tdouble) :: (_t'12, tdouble) :: (_t'11, tdouble) ::
               (_t'10, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'15
        (Efield
          (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
            (Tstruct _dword noattr)) _s tdouble))
      (Scall (Some _t'1)
        (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
        ((Etempvar _t'15 tdouble) :: nil)))
    (Sset _fin_xh (Etempvar _t'1 tint)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'14
          (Efield
            (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
              (Tstruct _dword noattr)) _t tdouble))
        (Scall (Some _t'2)
          (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
          ((Etempvar _t'14 tdouble) :: nil)))
      (Sset _fin_xl (Etempvar _t'2 tint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
          ((Etempvar _y tdouble) :: nil))
        (Sset _fin_y (Etempvar _t'3 tint)))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sifthenelse (Etempvar _fin_xh tint)
              (Sset _t'4 (Ecast (Etempvar _fin_xl tint) tbool))
              (Sset _t'4 (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar _t'4 tint)
              (Ssequence
                (Sset _t'11
                  (Efield
                    (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                      (Tstruct _dword noattr)) _s tdouble))
                (Ssequence
                  (Sset _t'12
                    (Efield
                      (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                        (Tstruct _dword noattr)) _t tdouble))
                  (Ssequence
                    (Sset _t'13
                      (Efield
                        (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                          (Tstruct _dword noattr)) _s tdouble))
                    (Sset _t'5
                      (Ecast
                        (Ebinop Oeq
                          (Ebinop Oadd (Etempvar _t'11 tdouble)
                            (Etempvar _t'12 tdouble) tdouble)
                          (Etempvar _t'13 tdouble) tint) tbool)))))
              (Sset _t'5 (Econst_int (Int.repr 0) tint))))
          (Sset _dwx (Etempvar _t'5 tint)))
        (Ssequence
          (Ssequence
            (Sset _t'10
              (Efield
                (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                  (Tstruct _dword noattr)) _s tdouble))
            (Sset _z
              (Ebinop Omul (Etempvar _t'10 tdouble) (Etempvar _y tdouble)
                tdouble)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'6)
                (Evar _ldexp (Tfunction (tdouble :: tint :: nil) tdouble
                               cc_default))
                ((Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble) ::
                 (Econst_int (Int.repr 1023) tint) :: nil))
              (Sset _q_prod (Etempvar _t'6 tdouble)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'7)
                  (Evar _fabs (Tfunction (tdouble :: nil) tdouble cc_default))
                  ((Etempvar _z tdouble) :: nil))
                (Sset _prod_bnd
                  (Ebinop Olt (Etempvar _t'7 tdouble)
                    (Etempvar _q_prod tdouble) tint)))
              (Ssequence
                (Ssequence
                  (Sifthenelse (Etempvar _dwx tint)
                    (Sset _t'8 (Ecast (Etempvar _fin_y tint) tbool))
                    (Sset _t'8 (Econst_int (Int.repr 0) tint)))
                  (Sifthenelse (Etempvar _t'8 tint)
                    (Sset _t'9 (Ecast (Etempvar _prod_bnd tint) tbool))
                    (Sset _t'9 (Econst_int (Int.repr 0) tint))))
                (Sreturn (Some (Etempvar _t'9 tint)))))))))))
|}.

Definition f_dw_mult_dw_check := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _dword noattr))) ::
                (_y, (tptr (Tstruct _dword noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_fin_xh, tint) :: (_fin_xl, tint) :: (_fin_yh, tint) ::
               (_fin_yl, tint) :: (_dwx, tint) :: (_dwy, tint) ::
               (_z, tdouble) :: (_q_prod, tdouble) :: (_prod_bnd, tint) ::
               (_t'12, tint) :: (_t'11, tint) :: (_t'10, tdouble) ::
               (_t'9, tdouble) :: (_t'8, tint) :: (_t'7, tint) ::
               (_t'6, tint) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'24, tdouble) :: (_t'23, tdouble) :: (_t'22, tdouble) ::
               (_t'21, tdouble) :: (_t'20, tdouble) :: (_t'19, tdouble) ::
               (_t'18, tdouble) :: (_t'17, tdouble) :: (_t'16, tdouble) ::
               (_t'15, tdouble) :: (_t'14, tdouble) :: (_t'13, tdouble) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'24
        (Efield
          (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
            (Tstruct _dword noattr)) _s tdouble))
      (Scall (Some _t'1)
        (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
        ((Etempvar _t'24 tdouble) :: nil)))
    (Sset _fin_xh (Etempvar _t'1 tint)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'23
          (Efield
            (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
              (Tstruct _dword noattr)) _t tdouble))
        (Scall (Some _t'2)
          (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
          ((Etempvar _t'23 tdouble) :: nil)))
      (Sset _fin_xl (Etempvar _t'2 tint)))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'22
            (Efield
              (Ederef (Etempvar _y (tptr (Tstruct _dword noattr)))
                (Tstruct _dword noattr)) _s tdouble))
          (Scall (Some _t'3)
            (Evar _isfinite_double (Tfunction (tdouble :: nil) tint
                                     cc_default))
            ((Etempvar _t'22 tdouble) :: nil)))
        (Sset _fin_yh (Etempvar _t'3 tint)))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'21
              (Efield
                (Ederef (Etempvar _y (tptr (Tstruct _dword noattr)))
                  (Tstruct _dword noattr)) _t tdouble))
            (Scall (Some _t'4)
              (Evar _isfinite_double (Tfunction (tdouble :: nil) tint
                                       cc_default))
              ((Etempvar _t'21 tdouble) :: nil)))
          (Sset _fin_yl (Etempvar _t'4 tint)))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sifthenelse (Etempvar _fin_xh tint)
                (Sset _t'5 (Ecast (Etempvar _fin_xl tint) tbool))
                (Sset _t'5 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'5 tint)
                (Ssequence
                  (Sset _t'18
                    (Efield
                      (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                        (Tstruct _dword noattr)) _s tdouble))
                  (Ssequence
                    (Sset _t'19
                      (Efield
                        (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                          (Tstruct _dword noattr)) _t tdouble))
                    (Ssequence
                      (Sset _t'20
                        (Efield
                          (Ederef
                            (Etempvar _x (tptr (Tstruct _dword noattr)))
                            (Tstruct _dword noattr)) _s tdouble))
                      (Sset _t'6
                        (Ecast
                          (Ebinop Oeq
                            (Ebinop Oadd (Etempvar _t'18 tdouble)
                              (Etempvar _t'19 tdouble) tdouble)
                            (Etempvar _t'20 tdouble) tint) tbool)))))
                (Sset _t'6 (Econst_int (Int.repr 0) tint))))
            (Sset _dwx (Etempvar _t'6 tint)))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sifthenelse (Etempvar _fin_yh tint)
                  (Sset _t'7 (Ecast (Etempvar _fin_yl tint) tbool))
                  (Sset _t'7 (Econst_int (Int.repr 0) tint)))
                (Sifthenelse (Etempvar _t'7 tint)
                  (Ssequence
                    (Sset _t'15
                      (Efield
                        (Ederef (Etempvar _y (tptr (Tstruct _dword noattr)))
                          (Tstruct _dword noattr)) _s tdouble))
                    (Ssequence
                      (Sset _t'16
                        (Efield
                          (Ederef
                            (Etempvar _y (tptr (Tstruct _dword noattr)))
                            (Tstruct _dword noattr)) _t tdouble))
                      (Ssequence
                        (Sset _t'17
                          (Efield
                            (Ederef
                              (Etempvar _y (tptr (Tstruct _dword noattr)))
                              (Tstruct _dword noattr)) _s tdouble))
                        (Sset _t'8
                          (Ecast
                            (Ebinop Oeq
                              (Ebinop Oadd (Etempvar _t'15 tdouble)
                                (Etempvar _t'16 tdouble) tdouble)
                              (Etempvar _t'17 tdouble) tint) tbool)))))
                  (Sset _t'8 (Econst_int (Int.repr 0) tint))))
              (Sset _dwy (Etempvar _t'8 tint)))
            (Ssequence
              (Ssequence
                (Sset _t'13
                  (Efield
                    (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                      (Tstruct _dword noattr)) _s tdouble))
                (Ssequence
                  (Sset _t'14
                    (Efield
                      (Ederef (Etempvar _y (tptr (Tstruct _dword noattr)))
                        (Tstruct _dword noattr)) _s tdouble))
                  (Sset _z
                    (Ebinop Omul (Etempvar _t'13 tdouble)
                      (Etempvar _t'14 tdouble) tdouble))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'9)
                    (Evar _ldexp (Tfunction (tdouble :: tint :: nil) tdouble
                                   cc_default))
                    ((Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble) ::
                     (Econst_int (Int.repr 1023) tint) :: nil))
                  (Sset _q_prod (Etempvar _t'9 tdouble)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'10)
                      (Evar _fabs (Tfunction (tdouble :: nil) tdouble
                                    cc_default))
                      ((Etempvar _z tdouble) :: nil))
                    (Sset _prod_bnd
                      (Ebinop Olt (Etempvar _t'10 tdouble)
                        (Etempvar _q_prod tdouble) tint)))
                  (Ssequence
                    (Ssequence
                      (Sifthenelse (Etempvar _dwx tint)
                        (Sset _t'11 (Ecast (Etempvar _dwy tint) tbool))
                        (Sset _t'11 (Econst_int (Int.repr 0) tint)))
                      (Sifthenelse (Etempvar _t'11 tint)
                        (Sset _t'12 (Ecast (Etempvar _prod_bnd tint) tbool))
                        (Sset _t'12 (Econst_int (Int.repr 0) tint))))
                    (Sreturn (Some (Etempvar _t'12 tint)))))))))))))
|}.

Definition f_dw_div_fp_check := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _dword noattr))) :: (_y, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := ((_fin_xh, tint) :: (_fin_xl, tint) :: (_fin_y, tint) ::
               (_dwx, tint) :: (_q_omega, tdouble) :: (_q_plo, tdouble) ::
               (_xh_hi, tint) :: (_xh_lo, tint) :: (_q, tdouble) ::
               (_qt_hi, tint) :: (_t'14, tint) :: (_t'13, tint) ::
               (_t'12, tint) :: (_t'11, tint) :: (_t'10, tdouble) ::
               (_t'9, tdouble) :: (_t'8, tdouble) :: (_t'7, tdouble) ::
               (_t'6, tdouble) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'22, tdouble) :: (_t'21, tdouble) :: (_t'20, tdouble) ::
               (_t'19, tdouble) :: (_t'18, tdouble) :: (_t'17, tdouble) ::
               (_t'16, tdouble) :: (_t'15, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'22
        (Efield
          (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
            (Tstruct _dword noattr)) _s tdouble))
      (Scall (Some _t'1)
        (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
        ((Etempvar _t'22 tdouble) :: nil)))
    (Sset _fin_xh (Etempvar _t'1 tint)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'21
          (Efield
            (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
              (Tstruct _dword noattr)) _t tdouble))
        (Scall (Some _t'2)
          (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
          ((Etempvar _t'21 tdouble) :: nil)))
      (Sset _fin_xl (Etempvar _t'2 tint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
          ((Etempvar _y tdouble) :: nil))
        (Sset _fin_y (Etempvar _t'3 tint)))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sifthenelse (Etempvar _fin_xh tint)
              (Sset _t'4 (Ecast (Etempvar _fin_xl tint) tbool))
              (Sset _t'4 (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar _t'4 tint)
              (Ssequence
                (Sset _t'18
                  (Efield
                    (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                      (Tstruct _dword noattr)) _s tdouble))
                (Ssequence
                  (Sset _t'19
                    (Efield
                      (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                        (Tstruct _dword noattr)) _t tdouble))
                  (Ssequence
                    (Sset _t'20
                      (Efield
                        (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                          (Tstruct _dword noattr)) _s tdouble))
                    (Sset _t'5
                      (Ecast
                        (Ebinop Oeq
                          (Ebinop Oadd (Etempvar _t'18 tdouble)
                            (Etempvar _t'19 tdouble) tdouble)
                          (Etempvar _t'20 tdouble) tint) tbool)))))
              (Sset _t'5 (Econst_int (Int.repr 0) tint))))
          (Sset _dwx (Etempvar _t'5 tint)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'6)
              (Evar _ldexp (Tfunction (tdouble :: tint :: nil) tdouble
                             cc_default))
              ((Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble) ::
               (Econst_int (Int.repr 1022) tint) :: nil))
            (Sset _q_omega (Etempvar _t'6 tdouble)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'7)
                (Evar _ldexp (Tfunction (tdouble :: tint :: nil) tdouble
                               cc_default))
                ((Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble) ::
                 (Eunop Oneg (Econst_int (Int.repr 968) tint) tint) :: nil))
              (Sset _q_plo (Etempvar _t'7 tdouble)))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'17
                    (Efield
                      (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                        (Tstruct _dword noattr)) _s tdouble))
                  (Scall (Some _t'8)
                    (Evar _fabs (Tfunction (tdouble :: nil) tdouble
                                  cc_default))
                    ((Etempvar _t'17 tdouble) :: nil)))
                (Sset _xh_hi
                  (Ebinop Ole (Etempvar _t'8 tdouble)
                    (Etempvar _q_omega tdouble) tint)))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'16
                      (Efield
                        (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                          (Tstruct _dword noattr)) _s tdouble))
                    (Scall (Some _t'9)
                      (Evar _fabs (Tfunction (tdouble :: nil) tdouble
                                    cc_default))
                      ((Etempvar _t'16 tdouble) :: nil)))
                  (Sset _xh_lo
                    (Ebinop Ole (Etempvar _q_plo tdouble)
                      (Etempvar _t'9 tdouble) tint)))
                (Ssequence
                  (Ssequence
                    (Sset _t'15
                      (Efield
                        (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                          (Tstruct _dword noattr)) _s tdouble))
                    (Sset _q
                      (Ebinop Odiv (Etempvar _t'15 tdouble)
                        (Etempvar _y tdouble) tdouble)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'10)
                        (Evar _fabs (Tfunction (tdouble :: nil) tdouble
                                      cc_default))
                        ((Etempvar _q tdouble) :: nil))
                      (Sset _qt_hi
                        (Ebinop Olt (Etempvar _t'10 tdouble)
                          (Etempvar _q_omega tdouble) tint)))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sifthenelse (Etempvar _dwx tint)
                              (Sset _t'11
                                (Ecast (Etempvar _fin_y tint) tbool))
                              (Sset _t'11 (Econst_int (Int.repr 0) tint)))
                            (Sifthenelse (Etempvar _t'11 tint)
                              (Sset _t'12
                                (Ecast (Etempvar _xh_hi tint) tbool))
                              (Sset _t'12 (Econst_int (Int.repr 0) tint))))
                          (Sifthenelse (Etempvar _t'12 tint)
                            (Sset _t'13 (Ecast (Etempvar _xh_lo tint) tbool))
                            (Sset _t'13 (Econst_int (Int.repr 0) tint))))
                        (Sifthenelse (Etempvar _t'13 tint)
                          (Sset _t'14 (Ecast (Etempvar _qt_hi tint) tbool))
                          (Sset _t'14 (Econst_int (Int.repr 0) tint))))
                      (Sreturn (Some (Etempvar _t'14 tint))))))))))))))
|}.

Definition f_dw_plus_fp_check := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _dword noattr))) :: (_y, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := ((_fin_xh, tint) :: (_fin_xl, tint) :: (_fin_y, tint) ::
               (_dwx, tint) :: (_q_omega, tdouble) :: (_xh_bnd, tint) ::
               (_y_bnd, tint) :: (_t'11, tint) :: (_t'10, tint) ::
               (_t'9, tint) :: (_t'8, tdouble) :: (_t'7, tdouble) ::
               (_t'6, tdouble) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'17, tdouble) :: (_t'16, tdouble) :: (_t'15, tdouble) ::
               (_t'14, tdouble) :: (_t'13, tdouble) :: (_t'12, tdouble) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'17
        (Efield
          (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
            (Tstruct _dword noattr)) _s tdouble))
      (Scall (Some _t'1)
        (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
        ((Etempvar _t'17 tdouble) :: nil)))
    (Sset _fin_xh (Etempvar _t'1 tint)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'16
          (Efield
            (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
              (Tstruct _dword noattr)) _t tdouble))
        (Scall (Some _t'2)
          (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
          ((Etempvar _t'16 tdouble) :: nil)))
      (Sset _fin_xl (Etempvar _t'2 tint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
          ((Etempvar _y tdouble) :: nil))
        (Sset _fin_y (Etempvar _t'3 tint)))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sifthenelse (Etempvar _fin_xh tint)
              (Sset _t'4 (Ecast (Etempvar _fin_xl tint) tbool))
              (Sset _t'4 (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar _t'4 tint)
              (Ssequence
                (Sset _t'13
                  (Efield
                    (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                      (Tstruct _dword noattr)) _s tdouble))
                (Ssequence
                  (Sset _t'14
                    (Efield
                      (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                        (Tstruct _dword noattr)) _t tdouble))
                  (Ssequence
                    (Sset _t'15
                      (Efield
                        (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                          (Tstruct _dword noattr)) _s tdouble))
                    (Sset _t'5
                      (Ecast
                        (Ebinop Oeq
                          (Ebinop Oadd (Etempvar _t'13 tdouble)
                            (Etempvar _t'14 tdouble) tdouble)
                          (Etempvar _t'15 tdouble) tint) tbool)))))
              (Sset _t'5 (Econst_int (Int.repr 0) tint))))
          (Sset _dwx (Etempvar _t'5 tint)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'6)
              (Evar _ldexp (Tfunction (tdouble :: tint :: nil) tdouble
                             cc_default))
              ((Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble) ::
               (Econst_int (Int.repr 1022) tint) :: nil))
            (Sset _q_omega (Etempvar _t'6 tdouble)))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'12
                  (Efield
                    (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                      (Tstruct _dword noattr)) _s tdouble))
                (Scall (Some _t'7)
                  (Evar _fabs (Tfunction (tdouble :: nil) tdouble cc_default))
                  ((Etempvar _t'12 tdouble) :: nil)))
              (Sset _xh_bnd
                (Ebinop Ole (Etempvar _t'7 tdouble)
                  (Etempvar _q_omega tdouble) tint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'8)
                  (Evar _fabs (Tfunction (tdouble :: nil) tdouble cc_default))
                  ((Etempvar _y tdouble) :: nil))
                (Sset _y_bnd
                  (Ebinop Ole (Etempvar _t'8 tdouble)
                    (Etempvar _q_omega tdouble) tint)))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sifthenelse (Etempvar _dwx tint)
                      (Sset _t'9 (Ecast (Etempvar _fin_y tint) tbool))
                      (Sset _t'9 (Econst_int (Int.repr 0) tint)))
                    (Sifthenelse (Etempvar _t'9 tint)
                      (Sset _t'10 (Ecast (Etempvar _xh_bnd tint) tbool))
                      (Sset _t'10 (Econst_int (Int.repr 0) tint))))
                  (Sifthenelse (Etempvar _t'10 tint)
                    (Sset _t'11 (Ecast (Etempvar _y_bnd tint) tbool))
                    (Sset _t'11 (Econst_int (Int.repr 0) tint))))
                (Sreturn (Some (Etempvar _t'11 tint)))))))))))
|}.

Definition f_dw_plus_fp_input_check := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _dword noattr))) :: (_y, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := ((_fin_xh, tint) :: (_fin_xl, tint) :: (_fin_y, tint) ::
               (_dwx, tint) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'11, tdouble) :: (_t'10, tdouble) ::
               (_t'9, tdouble) :: (_t'8, tdouble) :: (_t'7, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'11
        (Efield
          (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
            (Tstruct _dword noattr)) _s tdouble))
      (Scall (Some _t'1)
        (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
        ((Etempvar _t'11 tdouble) :: nil)))
    (Sset _fin_xh (Etempvar _t'1 tint)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'10
          (Efield
            (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
              (Tstruct _dword noattr)) _t tdouble))
        (Scall (Some _t'2)
          (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
          ((Etempvar _t'10 tdouble) :: nil)))
      (Sset _fin_xl (Etempvar _t'2 tint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
          ((Etempvar _y tdouble) :: nil))
        (Sset _fin_y (Etempvar _t'3 tint)))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sifthenelse (Etempvar _fin_xh tint)
              (Sset _t'4 (Ecast (Etempvar _fin_xl tint) tbool))
              (Sset _t'4 (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar _t'4 tint)
              (Ssequence
                (Sset _t'7
                  (Efield
                    (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                      (Tstruct _dword noattr)) _s tdouble))
                (Ssequence
                  (Sset _t'8
                    (Efield
                      (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                        (Tstruct _dword noattr)) _t tdouble))
                  (Ssequence
                    (Sset _t'9
                      (Efield
                        (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                          (Tstruct _dword noattr)) _s tdouble))
                    (Sset _t'5
                      (Ecast
                        (Ebinop Oeq
                          (Ebinop Oadd (Etempvar _t'7 tdouble)
                            (Etempvar _t'8 tdouble) tdouble)
                          (Etempvar _t'9 tdouble) tint) tbool)))))
              (Sset _t'5 (Econst_int (Int.repr 0) tint))))
          (Sset _dwx (Etempvar _t'5 tint)))
        (Ssequence
          (Sifthenelse (Etempvar _dwx tint)
            (Sset _t'6 (Ecast (Etempvar _fin_y tint) tbool))
            (Sset _t'6 (Econst_int (Int.repr 0) tint)))
          (Sreturn (Some (Etempvar _t'6 tint))))))))
|}.

Definition f_dword_finite_check := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _dword noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_fin_s, tint) :: (_fin_t, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'4, tdouble) :: (_t'3, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
            (Tstruct _dword noattr)) _s tdouble))
      (Scall (Some _t'1)
        (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
        ((Etempvar _t'4 tdouble) :: nil)))
    (Sset _fin_s (Etempvar _t'1 tint)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
              (Tstruct _dword noattr)) _t tdouble))
        (Scall (Some _t'2)
          (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
          ((Etempvar _t'3 tdouble) :: nil)))
      (Sset _fin_t (Etempvar _t'2 tint)))
    (Ssequence
      (Sifthenelse (Eunop Onotbool (Etempvar _fin_s tint) tint)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        Sskip)
      (Ssequence
        (Sifthenelse (Eunop Onotbool (Etempvar _fin_t tint) tint)
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
          Sskip)
        (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))
|}.

Definition f_dw_div_dw_check := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _dword noattr))) ::
                (_y, (tptr (Tstruct _dword noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_fin_xh, tint) :: (_fin_xl, tint) :: (_fin_yh, tint) ::
               (_fin_yl, tint) :: (_dwx, tint) :: (_dwy, tint) ::
               (_q_omega, tdouble) :: (_q_yhi, tdouble) ::
               (_q_ylo, tdouble) :: (_yh_hi, tint) :: (_yh_lo, tint) ::
               (_q, tdouble) :: (_qt_hi, tint) :: (_t'18, tint) ::
               (_t'17, tint) :: (_t'16, tint) :: (_t'15, tint) ::
               (_t'14, tdouble) :: (_t'13, tdouble) :: (_t'12, tdouble) ::
               (_t'11, tdouble) :: (_t'10, tdouble) :: (_t'9, tdouble) ::
               (_t'8, tint) :: (_t'7, tint) :: (_t'6, tint) ::
               (_t'5, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: (_t'32, tdouble) ::
               (_t'31, tdouble) :: (_t'30, tdouble) :: (_t'29, tdouble) ::
               (_t'28, tdouble) :: (_t'27, tdouble) :: (_t'26, tdouble) ::
               (_t'25, tdouble) :: (_t'24, tdouble) :: (_t'23, tdouble) ::
               (_t'22, tdouble) :: (_t'21, tdouble) :: (_t'20, tdouble) ::
               (_t'19, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'32
        (Efield
          (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
            (Tstruct _dword noattr)) _s tdouble))
      (Scall (Some _t'1)
        (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
        ((Etempvar _t'32 tdouble) :: nil)))
    (Sset _fin_xh (Etempvar _t'1 tint)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'31
          (Efield
            (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
              (Tstruct _dword noattr)) _t tdouble))
        (Scall (Some _t'2)
          (Evar _isfinite_double (Tfunction (tdouble :: nil) tint cc_default))
          ((Etempvar _t'31 tdouble) :: nil)))
      (Sset _fin_xl (Etempvar _t'2 tint)))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'30
            (Efield
              (Ederef (Etempvar _y (tptr (Tstruct _dword noattr)))
                (Tstruct _dword noattr)) _s tdouble))
          (Scall (Some _t'3)
            (Evar _isfinite_double (Tfunction (tdouble :: nil) tint
                                     cc_default))
            ((Etempvar _t'30 tdouble) :: nil)))
        (Sset _fin_yh (Etempvar _t'3 tint)))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'29
              (Efield
                (Ederef (Etempvar _y (tptr (Tstruct _dword noattr)))
                  (Tstruct _dword noattr)) _t tdouble))
            (Scall (Some _t'4)
              (Evar _isfinite_double (Tfunction (tdouble :: nil) tint
                                       cc_default))
              ((Etempvar _t'29 tdouble) :: nil)))
          (Sset _fin_yl (Etempvar _t'4 tint)))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sifthenelse (Etempvar _fin_xh tint)
                (Sset _t'5 (Ecast (Etempvar _fin_xl tint) tbool))
                (Sset _t'5 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'5 tint)
                (Ssequence
                  (Sset _t'26
                    (Efield
                      (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                        (Tstruct _dword noattr)) _s tdouble))
                  (Ssequence
                    (Sset _t'27
                      (Efield
                        (Ederef (Etempvar _x (tptr (Tstruct _dword noattr)))
                          (Tstruct _dword noattr)) _t tdouble))
                    (Ssequence
                      (Sset _t'28
                        (Efield
                          (Ederef
                            (Etempvar _x (tptr (Tstruct _dword noattr)))
                            (Tstruct _dword noattr)) _s tdouble))
                      (Sset _t'6
                        (Ecast
                          (Ebinop Oeq
                            (Ebinop Oadd (Etempvar _t'26 tdouble)
                              (Etempvar _t'27 tdouble) tdouble)
                            (Etempvar _t'28 tdouble) tint) tbool)))))
                (Sset _t'6 (Econst_int (Int.repr 0) tint))))
            (Sset _dwx (Etempvar _t'6 tint)))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sifthenelse (Etempvar _fin_yh tint)
                  (Sset _t'7 (Ecast (Etempvar _fin_yl tint) tbool))
                  (Sset _t'7 (Econst_int (Int.repr 0) tint)))
                (Sifthenelse (Etempvar _t'7 tint)
                  (Ssequence
                    (Sset _t'23
                      (Efield
                        (Ederef (Etempvar _y (tptr (Tstruct _dword noattr)))
                          (Tstruct _dword noattr)) _s tdouble))
                    (Ssequence
                      (Sset _t'24
                        (Efield
                          (Ederef
                            (Etempvar _y (tptr (Tstruct _dword noattr)))
                            (Tstruct _dword noattr)) _t tdouble))
                      (Ssequence
                        (Sset _t'25
                          (Efield
                            (Ederef
                              (Etempvar _y (tptr (Tstruct _dword noattr)))
                              (Tstruct _dword noattr)) _s tdouble))
                        (Sset _t'8
                          (Ecast
                            (Ebinop Oeq
                              (Ebinop Oadd (Etempvar _t'23 tdouble)
                                (Etempvar _t'24 tdouble) tdouble)
                              (Etempvar _t'25 tdouble) tint) tbool)))))
                  (Sset _t'8 (Econst_int (Int.repr 0) tint))))
              (Sset _dwy (Etempvar _t'8 tint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'9)
                  (Evar _ldexp (Tfunction (tdouble :: tint :: nil) tdouble
                                 cc_default))
                  ((Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble) ::
                   (Econst_int (Int.repr 1022) tint) :: nil))
                (Sset _q_omega (Etempvar _t'9 tdouble)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'10)
                    (Evar _ldexp (Tfunction (tdouble :: tint :: nil) tdouble
                                   cc_default))
                    ((Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble) ::
                     (Econst_int (Int.repr 966) tint) :: nil))
                  (Sset _q_yhi (Etempvar _t'10 tdouble)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'11)
                      (Evar _ldexp (Tfunction (tdouble :: tint :: nil)
                                     tdouble cc_default))
                      ((Econst_float (Float.of_bits (Int64.repr 4607182418800017408)) tdouble) ::
                       (Eunop Oneg (Econst_int (Int.repr 968) tint) tint) ::
                       nil))
                    (Sset _q_ylo (Etempvar _t'11 tdouble)))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'22
                          (Efield
                            (Ederef
                              (Etempvar _y (tptr (Tstruct _dword noattr)))
                              (Tstruct _dword noattr)) _s tdouble))
                        (Scall (Some _t'12)
                          (Evar _fabs (Tfunction (tdouble :: nil) tdouble
                                        cc_default))
                          ((Etempvar _t'22 tdouble) :: nil)))
                      (Sset _yh_hi
                        (Ebinop Ole (Etempvar _t'12 tdouble)
                          (Etempvar _q_yhi tdouble) tint)))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'21
                            (Efield
                              (Ederef
                                (Etempvar _y (tptr (Tstruct _dword noattr)))
                                (Tstruct _dword noattr)) _s tdouble))
                          (Scall (Some _t'13)
                            (Evar _fabs (Tfunction (tdouble :: nil) tdouble
                                          cc_default))
                            ((Etempvar _t'21 tdouble) :: nil)))
                        (Sset _yh_lo
                          (Ebinop Ole (Etempvar _q_ylo tdouble)
                            (Etempvar _t'13 tdouble) tint)))
                      (Ssequence
                        (Ssequence
                          (Sset _t'19
                            (Efield
                              (Ederef
                                (Etempvar _x (tptr (Tstruct _dword noattr)))
                                (Tstruct _dword noattr)) _s tdouble))
                          (Ssequence
                            (Sset _t'20
                              (Efield
                                (Ederef
                                  (Etempvar _y (tptr (Tstruct _dword noattr)))
                                  (Tstruct _dword noattr)) _s tdouble))
                            (Sset _q
                              (Ebinop Odiv (Etempvar _t'19 tdouble)
                                (Etempvar _t'20 tdouble) tdouble))))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'14)
                              (Evar _fabs (Tfunction (tdouble :: nil) tdouble
                                            cc_default))
                              ((Etempvar _q tdouble) :: nil))
                            (Sset _qt_hi
                              (Ebinop Olt (Etempvar _t'14 tdouble)
                                (Etempvar _q_omega tdouble) tint)))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sifthenelse (Etempvar _dwx tint)
                                    (Sset _t'15
                                      (Ecast (Etempvar _dwy tint) tbool))
                                    (Sset _t'15
                                      (Econst_int (Int.repr 0) tint)))
                                  (Sifthenelse (Etempvar _t'15 tint)
                                    (Sset _t'16
                                      (Ecast (Etempvar _yh_hi tint) tbool))
                                    (Sset _t'16
                                      (Econst_int (Int.repr 0) tint))))
                                (Sifthenelse (Etempvar _t'16 tint)
                                  (Sset _t'17
                                    (Ecast (Etempvar _yh_lo tint) tbool))
                                  (Sset _t'17 (Econst_int (Int.repr 0) tint))))
                              (Sifthenelse (Etempvar _t'17 tint)
                                (Sset _t'18
                                  (Ecast (Etempvar _qt_hi tint) tbool))
                                (Sset _t'18 (Econst_int (Int.repr 0) tint))))
                            (Sreturn (Some (Etempvar _t'18 tint)))))))))))))))))
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
 (_ldexp,
   Gfun(External (EF_external "ldexp"
                   (mksignature (AST.Xfloat :: AST.Xint :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tint :: nil) tdouble
     cc_default)) ::
 (_fabs,
   Gfun(External (EF_external "fabs"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (_isfinite_double, Gfun(Internal f_isfinite_double)) ::
 (_fast2_mult_check, Gfun(Internal f_fast2_mult_check)) ::
 (_fast2_mult_acc_check, Gfun(Internal f_fast2_mult_acc_check)) ::
 (_fast2_sum_check, Gfun(Internal f_fast2_sum_check)) ::
 (_two_sum_check, Gfun(Internal f_two_sum_check)) ::
 (_dw_plus_dw_check, Gfun(Internal f_dw_plus_dw_check)) ::
 (_dw_mult_fp_check, Gfun(Internal f_dw_mult_fp_check)) ::
 (_dw_mult_dw_check, Gfun(Internal f_dw_mult_dw_check)) ::
 (_dw_div_fp_check, Gfun(Internal f_dw_div_fp_check)) ::
 (_dw_plus_fp_check, Gfun(Internal f_dw_plus_fp_check)) ::
 (_dw_plus_fp_input_check, Gfun(Internal f_dw_plus_fp_input_check)) ::
 (_dword_finite_check, Gfun(Internal f_dword_finite_check)) ::
 (_dw_div_dw_check, Gfun(Internal f_dw_div_dw_check)) :: nil).

Definition public_idents : list ident :=
(_dw_div_dw_check :: _dword_finite_check :: _dw_plus_fp_input_check ::
 _dw_plus_fp_check :: _dw_div_fp_check :: _dw_mult_dw_check ::
 _dw_mult_fp_check :: _dw_plus_dw_check :: _two_sum_check ::
 _fast2_sum_check :: _fast2_mult_acc_check :: _fast2_mult_check ::
 _isfinite_double :: _fabs :: _ldexp :: ___builtin_debug ::
 ___builtin_fmin :: ___builtin_fmax :: ___builtin_fnmsub ::
 ___builtin_fnmadd :: ___builtin_fmsub :: ___builtin_fmadd ::
 ___builtin_clsll :: ___builtin_clsl :: ___builtin_cls ::
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


