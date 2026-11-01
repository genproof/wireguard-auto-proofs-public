From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.15".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "harness/ae_split_chacha20.c".
  Definition normalized := true.
End Info.

Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
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
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
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
Definition _any_bytes : ident := $"any_bytes".
Definition _b : ident := $"b".
Definition _bytes : ident := $"bytes".
Definition _bytes_eq : ident := $"bytes_eq".
Definition _chacha20_crypt : ident := $"chacha20_crypt".
Definition _chacha_crypt : ident := $"chacha_crypt".
Definition _chacha_init : ident := $"chacha_init".
Definition _chacha_init_consts : ident := $"chacha_init_consts".
Definition _chacha_state : ident := $"chacha_state".
Definition _done : ident := $"done".
Definition _dst : ident := $"dst".
Definition _get_unaligned_le32 : ident := $"get_unaligned_le32".
Definition _gp_assert : ident := $"gp_assert".
Definition _i : ident := $"i".
Definition _iv : ident := $"iv".
Definition _key : ident := $"key".
Definition _len : ident := $"len".
Definition _main : ident := $"main".
Definition _many : ident := $"many".
Definition _max : ident := $"max".
Definition _message : ident := $"message".
Definition _n : ident := $"n".
Definition _nondet_bytes : ident := $"nondet_bytes".
Definition _nondet_size : ident := $"nondet_size".
Definition _nondet_u32 : ident := $"nondet_u32".
Definition _nondet_u8 : ident := $"nondet_u8".
Definition _one : ident := $"one".
Definition _p : ident := $"p".
Definition _pieces : ident := $"pieces".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _src : ident := $"src".
Definition _state : ident := $"state".
Definition _take : ident := $"take".
Definition _upto : ident := $"upto".
Definition _value : ident := $"value".
Definition _whole : ident := $"whole".
Definition _x : ident := $"x".
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

Definition f_get_unaligned_le32 := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, (tptr tuchar)) :: (_t'4, tuchar) :: (_t'3, tuchar) ::
               (_t'2, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _b (Ecast (Etempvar _p (tptr tvoid)) (tptr tuchar)))
  (Ssequence
    (Sset _t'1
      (Ederef
        (Ebinop Oadd (Etempvar _b (tptr tuchar))
          (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Etempvar _b (tptr tuchar))
            (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Etempvar _b (tptr tuchar))
              (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar))
        (Ssequence
          (Sset _t'4
            (Ederef
              (Ebinop Oadd (Etempvar _b (tptr tuchar))
                (Econst_int (Int.repr 3) tint) (tptr tuchar)) tuchar))
          (Sreturn (Some (Ebinop Oor
                           (Ebinop Oor
                             (Ebinop Oor (Ecast (Etempvar _t'1 tuchar) tuint)
                               (Ebinop Oshl
                                 (Ecast (Etempvar _t'2 tuchar) tuint)
                                 (Econst_int (Int.repr 8) tint) tuint) tuint)
                             (Ebinop Oshl
                               (Ecast (Etempvar _t'3 tuchar) tuint)
                               (Econst_int (Int.repr 16) tint) tuint) tuint)
                           (Ebinop Oshl (Ecast (Etempvar _t'4 tuchar) tuint)
                             (Econst_int (Int.repr 24) tint) tuint) tuint))))))))
|}.

Definition f_chacha_init_consts := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_state, (tptr (Tstruct _chacha_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _state (tptr (Tstruct _chacha_state noattr)))
            (Tstruct _chacha_state noattr)) _x (tarray tuint 16))
        (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
    (Econst_int (Int.repr 1634760805) tint))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _state (tptr (Tstruct _chacha_state noattr)))
              (Tstruct _chacha_state noattr)) _x (tarray tuint 16))
          (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint)
      (Econst_int (Int.repr 857760878) tint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _state (tptr (Tstruct _chacha_state noattr)))
                (Tstruct _chacha_state noattr)) _x (tarray tuint 16))
            (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint)
        (Econst_int (Int.repr 2036477234) tint))
      (Sassign
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _state (tptr (Tstruct _chacha_state noattr)))
                (Tstruct _chacha_state noattr)) _x (tarray tuint 16))
            (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint)
        (Econst_int (Int.repr 1797285236) tint)))))
|}.

Definition f_chacha_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_state, (tptr (Tstruct _chacha_state noattr))) ::
                (_key, (tptr tuint)) :: (_iv, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'4, tuint) :: (_t'3, tuint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: (_t'12, tuint) :: (_t'11, tuint) ::
               (_t'10, tuint) :: (_t'9, tuint) :: (_t'8, tuint) ::
               (_t'7, tuint) :: (_t'6, tuint) :: (_t'5, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _chacha_init_consts (Tfunction
                                ((tptr (Tstruct _chacha_state noattr)) ::
                                 nil) tvoid cc_default))
    ((Etempvar _state (tptr (Tstruct _chacha_state noattr))) :: nil))
  (Ssequence
    (Ssequence
      (Sset _t'12
        (Ederef
          (Ebinop Oadd (Etempvar _key (tptr tuint))
            (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
      (Sassign
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _state (tptr (Tstruct _chacha_state noattr)))
                (Tstruct _chacha_state noattr)) _x (tarray tuint 16))
            (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint)
        (Etempvar _t'12 tuint)))
    (Ssequence
      (Ssequence
        (Sset _t'11
          (Ederef
            (Ebinop Oadd (Etempvar _key (tptr tuint))
              (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint))
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef
                  (Etempvar _state (tptr (Tstruct _chacha_state noattr)))
                  (Tstruct _chacha_state noattr)) _x (tarray tuint 16))
              (Econst_int (Int.repr 5) tint) (tptr tuint)) tuint)
          (Etempvar _t'11 tuint)))
      (Ssequence
        (Ssequence
          (Sset _t'10
            (Ederef
              (Ebinop Oadd (Etempvar _key (tptr tuint))
                (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint))
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _chacha_state noattr)))
                    (Tstruct _chacha_state noattr)) _x (tarray tuint 16))
                (Econst_int (Int.repr 6) tint) (tptr tuint)) tuint)
            (Etempvar _t'10 tuint)))
        (Ssequence
          (Ssequence
            (Sset _t'9
              (Ederef
                (Ebinop Oadd (Etempvar _key (tptr tuint))
                  (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint))
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _state (tptr (Tstruct _chacha_state noattr)))
                      (Tstruct _chacha_state noattr)) _x (tarray tuint 16))
                  (Econst_int (Int.repr 7) tint) (tptr tuint)) tuint)
              (Etempvar _t'9 tuint)))
          (Ssequence
            (Ssequence
              (Sset _t'8
                (Ederef
                  (Ebinop Oadd (Etempvar _key (tptr tuint))
                    (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint))
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _state (tptr (Tstruct _chacha_state noattr)))
                        (Tstruct _chacha_state noattr)) _x (tarray tuint 16))
                    (Econst_int (Int.repr 8) tint) (tptr tuint)) tuint)
                (Etempvar _t'8 tuint)))
            (Ssequence
              (Ssequence
                (Sset _t'7
                  (Ederef
                    (Ebinop Oadd (Etempvar _key (tptr tuint))
                      (Econst_int (Int.repr 5) tint) (tptr tuint)) tuint))
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _state (tptr (Tstruct _chacha_state noattr)))
                          (Tstruct _chacha_state noattr)) _x
                        (tarray tuint 16)) (Econst_int (Int.repr 9) tint)
                      (tptr tuint)) tuint) (Etempvar _t'7 tuint)))
              (Ssequence
                (Ssequence
                  (Sset _t'6
                    (Ederef
                      (Ebinop Oadd (Etempvar _key (tptr tuint))
                        (Econst_int (Int.repr 6) tint) (tptr tuint)) tuint))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _state (tptr (Tstruct _chacha_state noattr)))
                            (Tstruct _chacha_state noattr)) _x
                          (tarray tuint 16)) (Econst_int (Int.repr 10) tint)
                        (tptr tuint)) tuint) (Etempvar _t'6 tuint)))
                (Ssequence
                  (Ssequence
                    (Sset _t'5
                      (Ederef
                        (Ebinop Oadd (Etempvar _key (tptr tuint))
                          (Econst_int (Int.repr 7) tint) (tptr tuint)) tuint))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _state (tptr (Tstruct _chacha_state noattr)))
                              (Tstruct _chacha_state noattr)) _x
                            (tarray tuint 16))
                          (Econst_int (Int.repr 11) tint) (tptr tuint))
                        tuint) (Etempvar _t'5 tuint)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'1)
                        (Evar _get_unaligned_le32 (Tfunction
                                                    ((tptr tvoid) :: nil)
                                                    tuint cc_default))
                        ((Ebinop Oadd (Etempvar _iv (tptr tuchar))
                           (Econst_int (Int.repr 0) tint) (tptr tuchar)) ::
                         nil))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _state (tptr (Tstruct _chacha_state noattr)))
                                (Tstruct _chacha_state noattr)) _x
                              (tarray tuint 16))
                            (Econst_int (Int.repr 12) tint) (tptr tuint))
                          tuint) (Etempvar _t'1 tuint)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'2)
                          (Evar _get_unaligned_le32 (Tfunction
                                                      ((tptr tvoid) :: nil)
                                                      tuint cc_default))
                          ((Ebinop Oadd (Etempvar _iv (tptr tuchar))
                             (Econst_int (Int.repr 4) tint) (tptr tuchar)) ::
                           nil))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _state (tptr (Tstruct _chacha_state noattr)))
                                  (Tstruct _chacha_state noattr)) _x
                                (tarray tuint 16))
                              (Econst_int (Int.repr 13) tint) (tptr tuint))
                            tuint) (Etempvar _t'2 tuint)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'3)
                            (Evar _get_unaligned_le32 (Tfunction
                                                        ((tptr tvoid) :: nil)
                                                        tuint cc_default))
                            ((Ebinop Oadd (Etempvar _iv (tptr tuchar))
                               (Econst_int (Int.repr 8) tint) (tptr tuchar)) ::
                             nil))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _state (tptr (Tstruct _chacha_state noattr)))
                                    (Tstruct _chacha_state noattr)) _x
                                  (tarray tuint 16))
                                (Econst_int (Int.repr 14) tint) (tptr tuint))
                              tuint) (Etempvar _t'3 tuint)))
                        (Ssequence
                          (Scall (Some _t'4)
                            (Evar _get_unaligned_le32 (Tfunction
                                                        ((tptr tvoid) :: nil)
                                                        tuint cc_default))
                            ((Ebinop Oadd (Etempvar _iv (tptr tuchar))
                               (Econst_int (Int.repr 12) tint) (tptr tuchar)) ::
                             nil))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _state (tptr (Tstruct _chacha_state noattr)))
                                    (Tstruct _chacha_state noattr)) _x
                                  (tarray tuint 16))
                                (Econst_int (Int.repr 15) tint) (tptr tuint))
                              tuint) (Etempvar _t'4 tuint)))))))))))))))
|}.

Definition f_chacha20_crypt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_state, (tptr (Tstruct _chacha_state noattr))) ::
                (_dst, (tptr tuchar)) :: (_src, (tptr tuchar)) ::
                (_bytes, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _chacha_crypt (Tfunction
                        ((tptr (Tstruct _chacha_state noattr)) ::
                         (tptr tuchar) :: (tptr tuchar) :: tulong :: tint ::
                         nil) tvoid cc_default))
  ((Etempvar _state (tptr (Tstruct _chacha_state noattr))) ::
   (Etempvar _dst (tptr tuchar)) :: (Etempvar _src (tptr tuchar)) ::
   (Etempvar _bytes tulong) :: (Econst_int (Int.repr 20) tint) :: nil))
|}.

Definition f_upto := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_max, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_value, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _nondet_size (Tfunction nil tulong cc_default))
      nil)
    (Sset _value (Etempvar _t'1 tulong)))
  (Ssequence
    (Sifthenelse (Ebinop Olt (Etempvar _value tulong) (Etempvar _max tulong)
                   tint)
      (Sset _t'2 (Ecast (Etempvar _value tulong) tulong))
      (Sset _t'2 (Ecast (Etempvar _max tulong) tulong)))
    (Sreturn (Some (Etempvar _t'2 tulong)))))
|}.

Definition f_any_bytes := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_bytes, (tptr tuchar)) :: (_t'2, tint) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _quickproof_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                 cc_default)) ((Etempvar _n tulong) :: nil))
    (Sset _bytes (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop One (Etempvar _bytes (tptr tuchar))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sset _t'2
          (Ecast
            (Ebinop One (Etempvar _n tulong) (Econst_int (Int.repr 0) tint)
              tint) tbool))
        (Sset _t'2 (Econst_int (Int.repr 0) tint)))
      (Sifthenelse (Etempvar _t'2 tint)
        (Scall None
          (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                tvoid cc_default))
          ((Etempvar _bytes (tptr tuchar)) :: (Etempvar _n tulong) :: nil))
        Sskip))
    (Sreturn (Some (Etempvar _bytes (tptr tuchar))))))
|}.

Definition f_bytes_eq := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tuchar)) :: (_b, (tptr tuchar)) :: (_n, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_t'2, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tulong) (Etempvar _n tulong)
                       tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'1
            (Ederef
              (Ebinop Oadd (Etempvar _a (tptr tuchar)) (Etempvar _i tulong)
                (tptr tuchar)) tuchar))
          (Ssequence
            (Sset _t'2
              (Ederef
                (Ebinop Oadd (Etempvar _b (tptr tuchar)) (Etempvar _i tulong)
                  (tptr tuchar)) tuchar))
            (Sifthenelse (Ebinop One (Etempvar _t'1 tuchar)
                           (Etempvar _t'2 tuchar) tint)
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
              Sskip))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
          tulong))))
  (Sreturn (Some (Econst_int (Int.repr 1) tint))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_key, (tarray tuint 8)) :: (_iv, (tarray tuchar 16)) ::
              (_one, (Tstruct _chacha_state noattr)) ::
              (_many, (Tstruct _chacha_state noattr)) :: nil);
  fn_temps := ((_i, tulong) :: (_len, tulong) :: (_message, (tptr tuchar)) ::
               (_whole, (tptr tuchar)) :: (_pieces, (tptr tuchar)) ::
               (_done, tulong) :: (_take, tulong) :: (_t'10, tint) ::
               (_t'9, tuchar) :: (_t'8, tulong) :: (_t'7, tint) ::
               (_t'6, tint) :: (_t'5, (tptr tvoid)) ::
               (_t'4, (tptr tvoid)) :: (_t'3, (tptr tuchar)) ::
               (_t'2, tulong) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                         (Econst_int (Int.repr 8) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Scall (Some _t'1)
              (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _key (tarray tuint 8))
                  (Etempvar _i tulong) (tptr tuint)) tuint)
              (Etempvar _t'1 tuint))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
            tulong))))
    (Ssequence
      (Scall None
        (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil) tvoid
                              cc_default))
        ((Evar _iv (tarray tuchar 16)) ::
         (Esizeof (tarray tuchar 16) tulong) :: nil))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _upto (Tfunction (tulong :: nil) tulong cc_default))
            ((Econst_long (Int64.repr 9223372036854775807) tlong) :: nil))
          (Sset _len (Etempvar _t'2 tulong)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _any_bytes (Tfunction (tulong :: nil) (tptr tuchar)
                                 cc_default))
              ((Etempvar _len tulong) :: nil))
            (Sset _message (Etempvar _t'3 (tptr tuchar))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'4)
                (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                           (tptr tvoid) cc_default))
                ((Etempvar _len tulong) :: nil))
              (Sset _whole (Etempvar _t'4 (tptr tvoid))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'5)
                  (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                             (tptr tvoid) cc_default))
                  ((Etempvar _len tulong) :: nil))
                (Sset _pieces (Etempvar _t'5 (tptr tvoid))))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sifthenelse (Ebinop Oeq
                                   (Etempvar _message (tptr tuchar))
                                   (Ecast (Econst_int (Int.repr 0) tint)
                                     (tptr tvoid)) tint)
                      (Sset _t'6 (Econst_int (Int.repr 1) tint))
                      (Sset _t'6
                        (Ecast
                          (Ebinop Oeq (Etempvar _whole (tptr tuchar))
                            (Ecast (Econst_int (Int.repr 0) tint)
                              (tptr tvoid)) tint) tbool)))
                    (Sifthenelse (Etempvar _t'6 tint)
                      (Sset _t'7 (Econst_int (Int.repr 1) tint))
                      (Sset _t'7
                        (Ecast
                          (Ebinop Oeq (Etempvar _pieces (tptr tuchar))
                            (Ecast (Econst_int (Int.repr 0) tint)
                              (tptr tvoid)) tint) tbool))))
                  (Sifthenelse (Etempvar _t'7 tint)
                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                    Sskip))
                (Ssequence
                  (Scall None
                    (Evar _chacha_init (Tfunction
                                         ((tptr (Tstruct _chacha_state noattr)) ::
                                          (tptr tuint) :: (tptr tuchar) ::
                                          nil) tvoid cc_default))
                    ((Eaddrof (Evar _one (Tstruct _chacha_state noattr))
                       (tptr (Tstruct _chacha_state noattr))) ::
                     (Evar _key (tarray tuint 8)) ::
                     (Evar _iv (tarray tuchar 16)) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _chacha20_crypt (Tfunction
                                              ((tptr (Tstruct _chacha_state noattr)) ::
                                               (tptr tuchar) ::
                                               (tptr tuchar) :: tulong ::
                                               nil) tvoid cc_default))
                      ((Eaddrof (Evar _one (Tstruct _chacha_state noattr))
                         (tptr (Tstruct _chacha_state noattr))) ::
                       (Etempvar _whole (tptr tuchar)) ::
                       (Etempvar _message (tptr tuchar)) ::
                       (Etempvar _len tulong) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _chacha_init (Tfunction
                                             ((tptr (Tstruct _chacha_state noattr)) ::
                                              (tptr tuint) ::
                                              (tptr tuchar) :: nil) tvoid
                                             cc_default))
                        ((Eaddrof (Evar _many (Tstruct _chacha_state noattr))
                           (tptr (Tstruct _chacha_state noattr))) ::
                         (Evar _key (tarray tuint 8)) ::
                         (Evar _iv (tarray tuchar 16)) :: nil))
                      (Ssequence
                        (Sset _done
                          (Ecast (Econst_int (Int.repr 0) tint) tulong))
                        (Ssequence
                          (Swhile
                            (Ebinop Olt (Etempvar _done tulong)
                              (Etempvar _len tulong) tint)
                            (Ssequence
                              (Sset _take
                                (Ebinop Osub (Etempvar _len tulong)
                                  (Etempvar _done tulong) tulong))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'9)
                                    (Evar _nondet_u8 (Tfunction nil tuchar
                                                       cc_default)) nil)
                                  (Sifthenelse (Ebinop One
                                                 (Etempvar _t'9 tuchar)
                                                 (Econst_int (Int.repr 0) tint)
                                                 tint)
                                    (Ssequence
                                      (Scall (Some _t'8)
                                        (Evar _upto (Tfunction
                                                      (tulong :: nil) tulong
                                                      cc_default))
                                        ((Ebinop Odiv (Etempvar _take tulong)
                                           (Econst_int (Int.repr 64) tint)
                                           tulong) :: nil))
                                      (Sset _take
                                        (Ebinop Omul
                                          (Econst_int (Int.repr 64) tint)
                                          (Etempvar _t'8 tulong) tulong)))
                                    Sskip))
                                (Ssequence
                                  (Scall None
                                    (Evar _chacha20_crypt (Tfunction
                                                            ((tptr (Tstruct _chacha_state noattr)) ::
                                                             (tptr tuchar) ::
                                                             (tptr tuchar) ::
                                                             tulong :: nil)
                                                            tvoid cc_default))
                                    ((Eaddrof
                                       (Evar _many (Tstruct _chacha_state noattr))
                                       (tptr (Tstruct _chacha_state noattr))) ::
                                     (Ebinop Oadd
                                       (Etempvar _pieces (tptr tuchar))
                                       (Etempvar _done tulong) (tptr tuchar)) ::
                                     (Ebinop Oadd
                                       (Etempvar _message (tptr tuchar))
                                       (Etempvar _done tulong) (tptr tuchar)) ::
                                     (Etempvar _take tulong) :: nil))
                                  (Sset _done
                                    (Ebinop Oadd (Etempvar _done tulong)
                                      (Etempvar _take tulong) tulong))))))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'10)
                                (Evar _bytes_eq (Tfunction
                                                  ((tptr tuchar) ::
                                                   (tptr tuchar) :: tulong ::
                                                   nil) tint cc_default))
                                ((Etempvar _whole (tptr tuchar)) ::
                                 (Etempvar _pieces (tptr tuchar)) ::
                                 (Etempvar _len tulong) :: nil))
                              (Scall None
                                (Evar _gp_assert (Tfunction (tint :: nil)
                                                   tvoid cc_default))
                                ((Etempvar _t'10 tint) :: nil)))
                            (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _chacha_state Struct
   (Member_plain _x (tarray tuint 16) :: nil)
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
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
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
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint16unsigned
                     cc_default)) ((tptr tushort) :: nil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tuint) :: nil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Xptr :: AST.Xint16unsigned :: nil)
                     AST.Xvoid cc_default))
     ((tptr tushort) :: tushort :: nil) tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tuint) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_nondet_u8,
   Gfun(External (EF_external "nondet_u8"
                   (mksignature nil AST.Xint8unsigned cc_default)) nil tuchar
     cc_default)) ::
 (_nondet_u32,
   Gfun(External (EF_external "nondet_u32"
                   (mksignature nil AST.Xint cc_default)) nil tuint
     cc_default)) ::
 (_nondet_size,
   Gfun(External (EF_external "nondet_size"
                   (mksignature nil AST.Xlong cc_default)) nil tulong
     cc_default)) ::
 (_nondet_bytes,
   Gfun(External (EF_external "nondet_bytes"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xvoid
                     cc_default)) ((tptr tuchar) :: tulong :: nil) tvoid
     cc_default)) ::
 (_gp_assert,
   Gfun(External (EF_external "gp_assert"
                   (mksignature (AST.Xint :: nil) AST.Xvoid cc_default))
     (tint :: nil) tvoid cc_default)) ::
 (_quickproof_malloc,
   Gfun(External (EF_external "quickproof_malloc"
                   (mksignature (AST.Xlong :: nil) AST.Xptr cc_default))
     (tulong :: nil) (tptr tvoid) cc_default)) ::
 (_get_unaligned_le32, Gfun(Internal f_get_unaligned_le32)) ::
 (_chacha_init_consts, Gfun(Internal f_chacha_init_consts)) ::
 (_chacha_init, Gfun(Internal f_chacha_init)) ::
 (_chacha_crypt,
   Gfun(External (EF_external "chacha_crypt"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xptr :: AST.Xlong ::
                      AST.Xint :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _chacha_state noattr)) :: (tptr tuchar) ::
      (tptr tuchar) :: tulong :: tint :: nil) tvoid cc_default)) ::
 (_chacha20_crypt, Gfun(Internal f_chacha20_crypt)) ::
 (_upto, Gfun(Internal f_upto)) ::
 (_any_bytes, Gfun(Internal f_any_bytes)) ::
 (_bytes_eq, Gfun(Internal f_bytes_eq)) :: (_main, Gfun(Internal f_main)) ::
 nil).

Definition public_idents : list ident :=
(_main :: _chacha_crypt :: _quickproof_malloc :: _gp_assert ::
 _nondet_bytes :: _nondet_size :: _nondet_u32 :: _nondet_u8 ::
 ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


