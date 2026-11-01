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
  Definition source_file := "harness/x_prim_x25519.c".
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
Definition _b : ident := $"b".
Definition _base : ident := $"base".
Definition _bytes_copy : ident := $"bytes_copy".
Definition _bytes_eq : ident := $"bytes_eq".
Definition _bytes_zero : ident := $"bytes_zero".
Definition _c : ident := $"c".
Definition _check_failed : ident := $"check_failed".
Definition _curve25519 : ident := $"curve25519".
Definition _curve25519_generate_public : ident := $"curve25519_generate_public".
Definition _curve25519_generic : ident := $"curve25519_generic".
Definition _d : ident := $"d".
Definition _e : ident := $"e".
Definition _f : ident := $"f".
Definition _i : ident := $"i".
Definition _in : ident := $"in".
Definition _j : ident := $"j".
Definition _k121665 : ident := $"k121665".
Definition _m : ident := $"m".
Definition _main : ident := $"main".
Definition _n : ident := $"n".
Definition _nondet_bytes : ident := $"nondet_bytes".
Definition _o : ident := $"o".
Definition _out : ident := $"out".
Definition _p : ident := $"p".
Definition _p0 : ident := $"p0".
Definition _q : ident := $"q".
Definition _quickproof_free : ident := $"quickproof_free".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _r : ident := $"r".
Definition _ref : ident := $"ref".
Definition _ref_x25519 : ident := $"ref_x25519".
Definition _rx_add : ident := $"rx_add".
Definition _rx_car : ident := $"rx_car".
Definition _rx_inv : ident := $"rx_inv".
Definition _rx_mul : ident := $"rx_mul".
Definition _rx_pack : ident := $"rx_pack".
Definition _rx_sel : ident := $"rx_sel".
Definition _rx_sub : ident := $"rx_sub".
Definition _rx_unpack : ident := $"rx_unpack".
Definition _s : ident := $"s".
Definition _s0 : ident := $"s0".
Definition _t : ident := $"t".
Definition _x : ident := $"x".
Definition _z : ident := $"z".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition f_check_failed := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_p, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Sassign (Ederef (Etempvar _p (tptr tint)) tint)
    (Econst_int (Int.repr 0) tint)))
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

Definition f_bytes_zero := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tuchar)) :: (_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_t'1, tuchar) :: nil);
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
          (Sifthenelse (Ebinop One (Etempvar _t'1 tuchar)
                         (Econst_int (Int.repr 0) tint) tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
            Sskip)))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
          tulong))))
  (Sreturn (Some (Econst_int (Int.repr 1) tint))))
|}.

Definition f_bytes_copy := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_d, (tptr tuchar)) :: (_s, (tptr tuchar)) :: (_n, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_t'1, tuchar) :: nil);
  fn_body :=
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
            (Ebinop Oadd (Etempvar _s (tptr tuchar)) (Etempvar _i tulong)
              (tptr tuchar)) tuchar))
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _d (tptr tuchar)) (Etempvar _i tulong)
              (tptr tuchar)) tuchar) (Etempvar _t'1 tuchar))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
        tulong))))
|}.

Definition f_rx_car := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr tlong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_c, tlong) :: (_t'5, tlong) :: (_t'4, tlong) ::
               (_t'3, tlong) :: (_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                     (Econst_int (Int.repr 16) tint) tint)
        Sskip
        Sbreak)
      (Ssequence
        (Ssequence
          (Sset _t'5
            (Ederef
              (Ebinop Oadd (Etempvar _o (tptr tlong)) (Etempvar _i tint)
                (tptr tlong)) tlong))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _o (tptr tlong)) (Etempvar _i tint)
                (tptr tlong)) tlong)
            (Ebinop Oadd (Etempvar _t'5 tlong)
              (Ebinop Oshl (Ecast (Econst_int (Int.repr 1) tint) tlong)
                (Econst_int (Int.repr 16) tint) tlong) tlong)))
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Ederef
                (Ebinop Oadd (Etempvar _o (tptr tlong)) (Etempvar _i tint)
                  (tptr tlong)) tlong))
            (Sset _c
              (Ebinop Oshr (Etempvar _t'4 tlong)
                (Econst_int (Int.repr 16) tint) tlong)))
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Econst_int (Int.repr 15) tint) tint)
              (Ssequence
                (Sset _t'3
                  (Ederef
                    (Ebinop Oadd (Etempvar _o (tptr tlong))
                      (Ebinop Oadd (Etempvar _i tint)
                        (Econst_int (Int.repr 1) tint) tint) (tptr tlong))
                    tlong))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _o (tptr tlong))
                      (Ebinop Oadd (Etempvar _i tint)
                        (Econst_int (Int.repr 1) tint) tint) (tptr tlong))
                    tlong)
                  (Ebinop Oadd (Etempvar _t'3 tlong)
                    (Ebinop Osub (Etempvar _c tlong)
                      (Econst_int (Int.repr 1) tint) tlong) tlong)))
              (Ssequence
                (Sset _t'2
                  (Ederef
                    (Ebinop Oadd (Etempvar _o (tptr tlong))
                      (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _o (tptr tlong))
                      (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
                  (Ebinop Oadd (Etempvar _t'2 tlong)
                    (Ebinop Omul (Econst_int (Int.repr 38) tint)
                      (Ebinop Osub (Etempvar _c tlong)
                        (Econst_int (Int.repr 1) tint) tlong) tlong) tlong))))
            (Ssequence
              (Sset _t'1
                (Ederef
                  (Ebinop Oadd (Etempvar _o (tptr tlong)) (Etempvar _i tint)
                    (tptr tlong)) tlong))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _o (tptr tlong)) (Etempvar _i tint)
                    (tptr tlong)) tlong)
                (Ebinop Osub (Etempvar _t'1 tlong)
                  (Ebinop Omul (Etempvar _c tlong)
                    (Econst_int (Int.repr 65536) tint) tlong) tlong)))))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_rx_sel := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tlong)) :: (_q, (tptr tlong)) :: (_b, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t, tlong) :: (_c, tlong) :: (_i, tint) :: (_t'4, tlong) ::
               (_t'3, tlong) :: (_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Sset _c
    (Eunop Onotint
      (Ebinop Osub (Ecast (Etempvar _b tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong) tlong))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 16) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Ederef
                (Ebinop Oadd (Etempvar _p (tptr tlong)) (Etempvar _i tint)
                  (tptr tlong)) tlong))
            (Ssequence
              (Sset _t'4
                (Ederef
                  (Ebinop Oadd (Etempvar _q (tptr tlong)) (Etempvar _i tint)
                    (tptr tlong)) tlong))
              (Sset _t
                (Ebinop Oand (Etempvar _c tlong)
                  (Ebinop Oxor (Etempvar _t'3 tlong) (Etempvar _t'4 tlong)
                    tlong) tlong))))
          (Ssequence
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd (Etempvar _p (tptr tlong)) (Etempvar _i tint)
                    (tptr tlong)) tlong))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _p (tptr tlong)) (Etempvar _i tint)
                    (tptr tlong)) tlong)
                (Ebinop Oxor (Etempvar _t'2 tlong) (Etempvar _t tlong) tlong)))
            (Ssequence
              (Sset _t'1
                (Ederef
                  (Ebinop Oadd (Etempvar _q (tptr tlong)) (Etempvar _i tint)
                    (tptr tlong)) tlong))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _q (tptr tlong)) (Etempvar _i tint)
                    (tptr tlong)) tlong)
                (Ebinop Oxor (Etempvar _t'1 tlong) (Etempvar _t tlong) tlong))))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))))
|}.

Definition f_rx_pack := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr tuchar)) :: (_n, (tptr tlong)) :: nil);
  fn_vars := ((_m, (tarray tlong 16)) :: (_t, (tarray tlong 16)) :: nil);
  fn_temps := ((_i, tint) :: (_j, tint) :: (_b, tint) :: (_t'11, tlong) ::
               (_t'10, tlong) :: (_t'9, tlong) :: (_t'8, tlong) ::
               (_t'7, tlong) :: (_t'6, tlong) :: (_t'5, tlong) ::
               (_t'4, tlong) :: (_t'3, tlong) :: (_t'2, tlong) ::
               (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 16) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'11
            (Ederef
              (Ebinop Oadd (Etempvar _n (tptr tlong)) (Etempvar _i tint)
                (tptr tlong)) tlong))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _t (tarray tlong 16)) (Etempvar _i tint)
                (tptr tlong)) tlong) (Etempvar _t'11 tlong))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Scall None
      (Evar _rx_car (Tfunction ((tptr tlong) :: nil) tvoid cc_default))
      ((Evar _t (tarray tlong 16)) :: nil))
    (Ssequence
      (Scall None
        (Evar _rx_car (Tfunction ((tptr tlong) :: nil) tvoid cc_default))
        ((Evar _t (tarray tlong 16)) :: nil))
      (Ssequence
        (Scall None
          (Evar _rx_car (Tfunction ((tptr tlong) :: nil) tvoid cc_default))
          ((Evar _t (tarray tlong 16)) :: nil))
        (Ssequence
          (Ssequence
            (Sset _j (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                               (Econst_int (Int.repr 2) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Ssequence
                    (Sset _t'10
                      (Ederef
                        (Ebinop Oadd (Evar _t (tarray tlong 16))
                          (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _m (tarray tlong 16))
                          (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
                      (Ebinop Osub (Etempvar _t'10 tlong)
                        (Econst_int (Int.repr 65517) tint) tlong)))
                  (Ssequence
                    (Ssequence
                      (Sset _i (Econst_int (Int.repr 1) tint))
                      (Sloop
                        (Ssequence
                          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                         (Econst_int (Int.repr 15) tint)
                                         tint)
                            Sskip
                            Sbreak)
                          (Ssequence
                            (Ssequence
                              (Sset _t'8
                                (Ederef
                                  (Ebinop Oadd (Evar _t (tarray tlong 16))
                                    (Etempvar _i tint) (tptr tlong)) tlong))
                              (Ssequence
                                (Sset _t'9
                                  (Ederef
                                    (Ebinop Oadd (Evar _m (tarray tlong 16))
                                      (Ebinop Osub (Etempvar _i tint)
                                        (Econst_int (Int.repr 1) tint) tint)
                                      (tptr tlong)) tlong))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd (Evar _m (tarray tlong 16))
                                      (Etempvar _i tint) (tptr tlong)) tlong)
                                  (Ebinop Osub
                                    (Ebinop Osub (Etempvar _t'8 tlong)
                                      (Econst_int (Int.repr 65535) tint)
                                      tlong)
                                    (Ebinop Oand
                                      (Ebinop Oshr (Etempvar _t'9 tlong)
                                        (Econst_int (Int.repr 16) tint)
                                        tlong) (Econst_int (Int.repr 1) tint)
                                      tlong) tlong))))
                            (Ssequence
                              (Sset _t'7
                                (Ederef
                                  (Ebinop Oadd (Evar _m (tarray tlong 16))
                                    (Ebinop Osub (Etempvar _i tint)
                                      (Econst_int (Int.repr 1) tint) tint)
                                    (tptr tlong)) tlong))
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd (Evar _m (tarray tlong 16))
                                    (Ebinop Osub (Etempvar _i tint)
                                      (Econst_int (Int.repr 1) tint) tint)
                                    (tptr tlong)) tlong)
                                (Ebinop Oand (Etempvar _t'7 tlong)
                                  (Econst_int (Int.repr 65535) tint) tlong)))))
                        (Sset _i
                          (Ebinop Oadd (Etempvar _i tint)
                            (Econst_int (Int.repr 1) tint) tint))))
                    (Ssequence
                      (Ssequence
                        (Sset _t'5
                          (Ederef
                            (Ebinop Oadd (Evar _t (tarray tlong 16))
                              (Econst_int (Int.repr 15) tint) (tptr tlong))
                            tlong))
                        (Ssequence
                          (Sset _t'6
                            (Ederef
                              (Ebinop Oadd (Evar _m (tarray tlong 16))
                                (Econst_int (Int.repr 14) tint) (tptr tlong))
                              tlong))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Evar _m (tarray tlong 16))
                                (Econst_int (Int.repr 15) tint) (tptr tlong))
                              tlong)
                            (Ebinop Osub
                              (Ebinop Osub (Etempvar _t'5 tlong)
                                (Econst_int (Int.repr 32767) tint) tlong)
                              (Ebinop Oand
                                (Ebinop Oshr (Etempvar _t'6 tlong)
                                  (Econst_int (Int.repr 16) tint) tlong)
                                (Econst_int (Int.repr 1) tint) tlong) tlong))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'4
                            (Ederef
                              (Ebinop Oadd (Evar _m (tarray tlong 16))
                                (Econst_int (Int.repr 15) tint) (tptr tlong))
                              tlong))
                          (Sset _b
                            (Ecast
                              (Ebinop Oand
                                (Ebinop Oshr (Etempvar _t'4 tlong)
                                  (Econst_int (Int.repr 16) tint) tlong)
                                (Econst_int (Int.repr 1) tint) tlong) tint)))
                        (Ssequence
                          (Ssequence
                            (Sset _t'3
                              (Ederef
                                (Ebinop Oadd (Evar _m (tarray tlong 16))
                                  (Econst_int (Int.repr 14) tint)
                                  (tptr tlong)) tlong))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Evar _m (tarray tlong 16))
                                  (Econst_int (Int.repr 14) tint)
                                  (tptr tlong)) tlong)
                              (Ebinop Oand (Etempvar _t'3 tlong)
                                (Econst_int (Int.repr 65535) tint) tlong)))
                          (Scall None
                            (Evar _rx_sel (Tfunction
                                            ((tptr tlong) :: (tptr tlong) ::
                                             tint :: nil) tvoid cc_default))
                            ((Evar _t (tarray tlong 16)) ::
                             (Evar _m (tarray tlong 16)) ::
                             (Ebinop Osub (Econst_int (Int.repr 1) tint)
                               (Etempvar _b tint) tint) :: nil))))))))
              (Sset _j
                (Ebinop Oadd (Etempvar _j tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Econst_int (Int.repr 16) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Ssequence
                    (Sset _t'2
                      (Ederef
                        (Ebinop Oadd (Evar _t (tarray tlong 16))
                          (Etempvar _i tint) (tptr tlong)) tlong))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Etempvar _o (tptr tuchar))
                          (Ebinop Omul (Econst_int (Int.repr 2) tint)
                            (Etempvar _i tint) tint) (tptr tuchar)) tuchar)
                      (Ecast
                        (Ebinop Oand (Etempvar _t'2 tlong)
                          (Econst_int (Int.repr 255) tint) tlong) tuchar)))
                  (Ssequence
                    (Sset _t'1
                      (Ederef
                        (Ebinop Oadd (Evar _t (tarray tlong 16))
                          (Etempvar _i tint) (tptr tlong)) tlong))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Etempvar _o (tptr tuchar))
                          (Ebinop Oadd
                            (Ebinop Omul (Econst_int (Int.repr 2) tint)
                              (Etempvar _i tint) tint)
                            (Econst_int (Int.repr 1) tint) tint)
                          (tptr tuchar)) tuchar)
                      (Ecast
                        (Ebinop Oshr (Etempvar _t'1 tlong)
                          (Econst_int (Int.repr 8) tint) tlong) tuchar)))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint)))))))))
|}.

Definition f_rx_unpack := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr tlong)) :: (_n, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'3, tuchar) :: (_t'2, tuchar) ::
               (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 16) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'2
            (Ederef
              (Ebinop Oadd (Etempvar _n (tptr tuchar))
                (Ebinop Omul (Econst_int (Int.repr 2) tint)
                  (Etempvar _i tint) tint) (tptr tuchar)) tuchar))
          (Ssequence
            (Sset _t'3
              (Ederef
                (Ebinop Oadd (Etempvar _n (tptr tuchar))
                  (Ebinop Oadd
                    (Ebinop Omul (Econst_int (Int.repr 2) tint)
                      (Etempvar _i tint) tint) (Econst_int (Int.repr 1) tint)
                    tint) (tptr tuchar)) tuchar))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _o (tptr tlong)) (Etempvar _i tint)
                  (tptr tlong)) tlong)
              (Ebinop Oadd (Etempvar _t'2 tuchar)
                (Ebinop Oshl (Ecast (Etempvar _t'3 tuchar) tlong)
                  (Econst_int (Int.repr 8) tint) tlong) tlong)))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Sset _t'1
      (Ederef
        (Ebinop Oadd (Etempvar _o (tptr tlong))
          (Econst_int (Int.repr 15) tint) (tptr tlong)) tlong))
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar _o (tptr tlong))
          (Econst_int (Int.repr 15) tint) (tptr tlong)) tlong)
      (Ebinop Oand (Etempvar _t'1 tlong) (Econst_int (Int.repr 32767) tint)
        tlong))))
|}.

Definition f_rx_add := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr tlong)) :: (_a, (tptr tlong)) ::
                (_b, (tptr tlong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                     (Econst_int (Int.repr 16) tint) tint)
        Sskip
        Sbreak)
      (Ssequence
        (Sset _t'1
          (Ederef
            (Ebinop Oadd (Etempvar _a (tptr tlong)) (Etempvar _i tint)
              (tptr tlong)) tlong))
        (Ssequence
          (Sset _t'2
            (Ederef
              (Ebinop Oadd (Etempvar _b (tptr tlong)) (Etempvar _i tint)
                (tptr tlong)) tlong))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _o (tptr tlong)) (Etempvar _i tint)
                (tptr tlong)) tlong)
            (Ebinop Oadd (Etempvar _t'1 tlong) (Etempvar _t'2 tlong) tlong)))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_rx_sub := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr tlong)) :: (_a, (tptr tlong)) ::
                (_b, (tptr tlong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                     (Econst_int (Int.repr 16) tint) tint)
        Sskip
        Sbreak)
      (Ssequence
        (Sset _t'1
          (Ederef
            (Ebinop Oadd (Etempvar _a (tptr tlong)) (Etempvar _i tint)
              (tptr tlong)) tlong))
        (Ssequence
          (Sset _t'2
            (Ederef
              (Ebinop Oadd (Etempvar _b (tptr tlong)) (Etempvar _i tint)
                (tptr tlong)) tlong))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _o (tptr tlong)) (Etempvar _i tint)
                (tptr tlong)) tlong)
            (Ebinop Osub (Etempvar _t'1 tlong) (Etempvar _t'2 tlong) tlong)))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_rx_mul := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr tlong)) :: (_a, (tptr tlong)) ::
                (_b, (tptr tlong)) :: nil);
  fn_vars := ((_t, (tarray tlong 31)) :: nil);
  fn_temps := ((_i, tint) :: (_j, tint) :: (_t'6, tlong) :: (_t'5, tlong) ::
               (_t'4, tlong) :: (_t'3, tlong) :: (_t'2, tlong) ::
               (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 31) tint) tint)
          Sskip
          Sbreak)
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _t (tarray tlong 31)) (Etempvar _i tint)
              (tptr tlong)) tlong) (Econst_int (Int.repr 0) tint)))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                         (Econst_int (Int.repr 16) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _j (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                               (Econst_int (Int.repr 16) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _t'4
                    (Ederef
                      (Ebinop Oadd (Evar _t (tarray tlong 31))
                        (Ebinop Oadd (Etempvar _i tint) (Etempvar _j tint)
                          tint) (tptr tlong)) tlong))
                  (Ssequence
                    (Sset _t'5
                      (Ederef
                        (Ebinop Oadd (Etempvar _a (tptr tlong))
                          (Etempvar _i tint) (tptr tlong)) tlong))
                    (Ssequence
                      (Sset _t'6
                        (Ederef
                          (Ebinop Oadd (Etempvar _b (tptr tlong))
                            (Etempvar _j tint) (tptr tlong)) tlong))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _t (tarray tlong 31))
                            (Ebinop Oadd (Etempvar _i tint)
                              (Etempvar _j tint) tint) (tptr tlong)) tlong)
                        (Ebinop Oadd (Etempvar _t'4 tlong)
                          (Ebinop Omul (Etempvar _t'5 tlong)
                            (Etempvar _t'6 tlong) tlong) tlong))))))
              (Sset _j
                (Ebinop Oadd (Etempvar _j tint)
                  (Econst_int (Int.repr 1) tint) tint)))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Econst_int (Int.repr 15) tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd (Evar _t (tarray tlong 31)) (Etempvar _i tint)
                    (tptr tlong)) tlong))
              (Ssequence
                (Sset _t'3
                  (Ederef
                    (Ebinop Oadd (Evar _t (tarray tlong 31))
                      (Ebinop Oadd (Etempvar _i tint)
                        (Econst_int (Int.repr 16) tint) tint) (tptr tlong))
                    tlong))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _t (tarray tlong 31))
                      (Etempvar _i tint) (tptr tlong)) tlong)
                  (Ebinop Oadd (Etempvar _t'2 tlong)
                    (Ebinop Omul (Econst_int (Int.repr 38) tint)
                      (Etempvar _t'3 tlong) tlong) tlong)))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Econst_int (Int.repr 16) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _t'1
                  (Ederef
                    (Ebinop Oadd (Evar _t (tarray tlong 31))
                      (Etempvar _i tint) (tptr tlong)) tlong))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _o (tptr tlong))
                      (Etempvar _i tint) (tptr tlong)) tlong)
                  (Etempvar _t'1 tlong))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Ssequence
          (Scall None
            (Evar _rx_car (Tfunction ((tptr tlong) :: nil) tvoid cc_default))
            ((Etempvar _o (tptr tlong)) :: nil))
          (Scall None
            (Evar _rx_car (Tfunction ((tptr tlong) :: nil) tvoid cc_default))
            ((Etempvar _o (tptr tlong)) :: nil)))))))
|}.

Definition f_rx_inv := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr tlong)) :: (_in, (tptr tlong)) :: nil);
  fn_vars := ((_c, (tarray tlong 16)) :: nil);
  fn_temps := ((_a, tint) :: (_t'1, tint) :: (_t'3, tlong) ::
               (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _a (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _a tint)
                       (Econst_int (Int.repr 16) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'3
            (Ederef
              (Ebinop Oadd (Etempvar _in (tptr tlong)) (Etempvar _a tint)
                (tptr tlong)) tlong))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _c (tarray tlong 16)) (Etempvar _a tint)
                (tptr tlong)) tlong) (Etempvar _t'3 tlong))))
      (Sset _a
        (Ebinop Oadd (Etempvar _a tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Ssequence
      (Sset _a (Econst_int (Int.repr 253) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Oge (Etempvar _a tint)
                         (Econst_int (Int.repr 0) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Scall None
              (Evar _rx_mul (Tfunction
                              ((tptr tlong) :: (tptr tlong) ::
                               (tptr tlong) :: nil) tvoid cc_default))
              ((Evar _c (tarray tlong 16)) :: (Evar _c (tarray tlong 16)) ::
               (Evar _c (tarray tlong 16)) :: nil))
            (Ssequence
              (Sifthenelse (Ebinop One (Etempvar _a tint)
                             (Econst_int (Int.repr 2) tint) tint)
                (Sset _t'1
                  (Ecast
                    (Ebinop One (Etempvar _a tint)
                      (Econst_int (Int.repr 4) tint) tint) tbool))
                (Sset _t'1 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'1 tint)
                (Scall None
                  (Evar _rx_mul (Tfunction
                                  ((tptr tlong) :: (tptr tlong) ::
                                   (tptr tlong) :: nil) tvoid cc_default))
                  ((Evar _c (tarray tlong 16)) ::
                   (Evar _c (tarray tlong 16)) ::
                   (Etempvar _in (tptr tlong)) :: nil))
                Sskip))))
        (Sset _a
          (Ebinop Osub (Etempvar _a tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Sset _a (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _a tint)
                         (Econst_int (Int.repr 16) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _t'2
              (Ederef
                (Ebinop Oadd (Evar _c (tarray tlong 16)) (Etempvar _a tint)
                  (tptr tlong)) tlong))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _o (tptr tlong)) (Etempvar _a tint)
                  (tptr tlong)) tlong) (Etempvar _t'2 tlong))))
        (Sset _a
          (Ebinop Oadd (Etempvar _a tint) (Econst_int (Int.repr 1) tint)
            tint))))))
|}.

Definition v_k121665 := {|
  gvar_info := (tarray tlong 16);
  gvar_init := (Init_int64 (Int64.repr 56129) :: Init_int64 (Int64.repr 1) ::
                Init_space 112 :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_ref_x25519 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_q, (tptr tuchar)) :: (_n, (tptr tuchar)) ::
                (_p, (tptr tuchar)) :: nil);
  fn_vars := ((_z, (tarray tuchar 32)) :: (_x, (tarray tlong 16)) ::
              (_a, (tarray tlong 16)) :: (_b, (tarray tlong 16)) ::
              (_c, (tarray tlong 16)) :: (_d, (tarray tlong 16)) ::
              (_e, (tarray tlong 16)) :: (_f, (tarray tlong 16)) :: nil);
  fn_temps := ((_i, tint) :: (_r, tint) :: (_t'3, tlong) :: (_t'2, tlong) ::
               (_t'1, tlong) :: (_t'8, tuchar) :: (_t'7, tuchar) ::
               (_t'6, tuchar) :: (_t'5, tlong) :: (_t'4, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 31) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'8
            (Ederef
              (Ebinop Oadd (Etempvar _n (tptr tuchar)) (Etempvar _i tint)
                (tptr tuchar)) tuchar))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _z (tarray tuchar 32)) (Etempvar _i tint)
                (tptr tuchar)) tuchar) (Etempvar _t'8 tuchar))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Ssequence
      (Sset _t'7
        (Ederef
          (Ebinop Oadd (Etempvar _n (tptr tuchar))
            (Econst_int (Int.repr 31) tint) (tptr tuchar)) tuchar))
      (Sassign
        (Ederef
          (Ebinop Oadd (Evar _z (tarray tuchar 32))
            (Econst_int (Int.repr 31) tint) (tptr tuchar)) tuchar)
        (Ebinop Oor
          (Ebinop Oand (Etempvar _t'7 tuchar)
            (Econst_int (Int.repr 127) tint) tint)
          (Econst_int (Int.repr 64) tint) tint)))
    (Ssequence
      (Ssequence
        (Sset _t'6
          (Ederef
            (Ebinop Oadd (Evar _z (tarray tuchar 32))
              (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar))
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _z (tarray tuchar 32))
              (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
          (Ebinop Oand (Etempvar _t'6 tuchar)
            (Econst_int (Int.repr 248) tint) tint)))
      (Ssequence
        (Scall None
          (Evar _rx_unpack (Tfunction ((tptr tlong) :: (tptr tuchar) :: nil)
                             tvoid cc_default))
          ((Evar _x (tarray tlong 16)) :: (Etempvar _p (tptr tuchar)) :: nil))
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Econst_int (Int.repr 16) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Ssequence
                    (Sset _t'5
                      (Ederef
                        (Ebinop Oadd (Evar _x (tarray tlong 16))
                          (Etempvar _i tint) (tptr tlong)) tlong))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _b (tarray tlong 16))
                          (Etempvar _i tint) (tptr tlong)) tlong)
                      (Etempvar _t'5 tlong)))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'1
                            (Ecast (Econst_int (Int.repr 0) tint) tlong))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Evar _c (tarray tlong 16))
                                (Etempvar _i tint) (tptr tlong)) tlong)
                            (Etempvar _t'1 tlong)))
                        (Sset _t'2 (Ecast (Etempvar _t'1 tlong) tlong)))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _a (tarray tlong 16))
                            (Etempvar _i tint) (tptr tlong)) tlong)
                        (Etempvar _t'2 tlong)))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _d (tarray tlong 16))
                          (Etempvar _i tint) (tptr tlong)) tlong)
                      (Etempvar _t'2 tlong)))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'3 (Ecast (Econst_int (Int.repr 1) tint) tlong))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _d (tarray tlong 16))
                      (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
                  (Etempvar _t'3 tlong)))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _a (tarray tlong 16))
                    (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
                (Etempvar _t'3 tlong)))
            (Ssequence
              (Ssequence
                (Sset _i (Econst_int (Int.repr 254) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Oge (Etempvar _i tint)
                                   (Econst_int (Int.repr 0) tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Ssequence
                        (Sset _t'4
                          (Ederef
                            (Ebinop Oadd (Evar _z (tarray tuchar 32))
                              (Ebinop Oshr (Etempvar _i tint)
                                (Econst_int (Int.repr 3) tint) tint)
                              (tptr tuchar)) tuchar))
                        (Sset _r
                          (Ebinop Oand
                            (Ebinop Oshr (Etempvar _t'4 tuchar)
                              (Ebinop Oand (Etempvar _i tint)
                                (Econst_int (Int.repr 7) tint) tint) tint)
                            (Econst_int (Int.repr 1) tint) tint)))
                      (Ssequence
                        (Scall None
                          (Evar _rx_sel (Tfunction
                                          ((tptr tlong) :: (tptr tlong) ::
                                           tint :: nil) tvoid cc_default))
                          ((Evar _a (tarray tlong 16)) ::
                           (Evar _b (tarray tlong 16)) ::
                           (Etempvar _r tint) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _rx_sel (Tfunction
                                            ((tptr tlong) :: (tptr tlong) ::
                                             tint :: nil) tvoid cc_default))
                            ((Evar _c (tarray tlong 16)) ::
                             (Evar _d (tarray tlong 16)) ::
                             (Etempvar _r tint) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar _rx_add (Tfunction
                                              ((tptr tlong) ::
                                               (tptr tlong) ::
                                               (tptr tlong) :: nil) tvoid
                                              cc_default))
                              ((Evar _e (tarray tlong 16)) ::
                               (Evar _a (tarray tlong 16)) ::
                               (Evar _c (tarray tlong 16)) :: nil))
                            (Ssequence
                              (Scall None
                                (Evar _rx_sub (Tfunction
                                                ((tptr tlong) ::
                                                 (tptr tlong) ::
                                                 (tptr tlong) :: nil) tvoid
                                                cc_default))
                                ((Evar _a (tarray tlong 16)) ::
                                 (Evar _a (tarray tlong 16)) ::
                                 (Evar _c (tarray tlong 16)) :: nil))
                              (Ssequence
                                (Scall None
                                  (Evar _rx_add (Tfunction
                                                  ((tptr tlong) ::
                                                   (tptr tlong) ::
                                                   (tptr tlong) :: nil) tvoid
                                                  cc_default))
                                  ((Evar _c (tarray tlong 16)) ::
                                   (Evar _b (tarray tlong 16)) ::
                                   (Evar _d (tarray tlong 16)) :: nil))
                                (Ssequence
                                  (Scall None
                                    (Evar _rx_sub (Tfunction
                                                    ((tptr tlong) ::
                                                     (tptr tlong) ::
                                                     (tptr tlong) :: nil)
                                                    tvoid cc_default))
                                    ((Evar _b (tarray tlong 16)) ::
                                     (Evar _b (tarray tlong 16)) ::
                                     (Evar _d (tarray tlong 16)) :: nil))
                                  (Ssequence
                                    (Scall None
                                      (Evar _rx_mul (Tfunction
                                                      ((tptr tlong) ::
                                                       (tptr tlong) ::
                                                       (tptr tlong) :: nil)
                                                      tvoid cc_default))
                                      ((Evar _d (tarray tlong 16)) ::
                                       (Evar _e (tarray tlong 16)) ::
                                       (Evar _e (tarray tlong 16)) :: nil))
                                    (Ssequence
                                      (Scall None
                                        (Evar _rx_mul (Tfunction
                                                        ((tptr tlong) ::
                                                         (tptr tlong) ::
                                                         (tptr tlong) :: nil)
                                                        tvoid cc_default))
                                        ((Evar _f (tarray tlong 16)) ::
                                         (Evar _a (tarray tlong 16)) ::
                                         (Evar _a (tarray tlong 16)) :: nil))
                                      (Ssequence
                                        (Scall None
                                          (Evar _rx_mul (Tfunction
                                                          ((tptr tlong) ::
                                                           (tptr tlong) ::
                                                           (tptr tlong) ::
                                                           nil) tvoid
                                                          cc_default))
                                          ((Evar _a (tarray tlong 16)) ::
                                           (Evar _c (tarray tlong 16)) ::
                                           (Evar _a (tarray tlong 16)) ::
                                           nil))
                                        (Ssequence
                                          (Scall None
                                            (Evar _rx_mul (Tfunction
                                                            ((tptr tlong) ::
                                                             (tptr tlong) ::
                                                             (tptr tlong) ::
                                                             nil) tvoid
                                                            cc_default))
                                            ((Evar _c (tarray tlong 16)) ::
                                             (Evar _b (tarray tlong 16)) ::
                                             (Evar _e (tarray tlong 16)) ::
                                             nil))
                                          (Ssequence
                                            (Scall None
                                              (Evar _rx_add (Tfunction
                                                              ((tptr tlong) ::
                                                               (tptr tlong) ::
                                                               (tptr tlong) ::
                                                               nil) tvoid
                                                              cc_default))
                                              ((Evar _e (tarray tlong 16)) ::
                                               (Evar _a (tarray tlong 16)) ::
                                               (Evar _c (tarray tlong 16)) ::
                                               nil))
                                            (Ssequence
                                              (Scall None
                                                (Evar _rx_sub (Tfunction
                                                                ((tptr tlong) ::
                                                                 (tptr tlong) ::
                                                                 (tptr tlong) ::
                                                                 nil) tvoid
                                                                cc_default))
                                                ((Evar _a (tarray tlong 16)) ::
                                                 (Evar _a (tarray tlong 16)) ::
                                                 (Evar _c (tarray tlong 16)) ::
                                                 nil))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _rx_mul (Tfunction
                                                                  ((tptr tlong) ::
                                                                   (tptr tlong) ::
                                                                   (tptr tlong) ::
                                                                   nil) tvoid
                                                                  cc_default))
                                                  ((Evar _b (tarray tlong 16)) ::
                                                   (Evar _a (tarray tlong 16)) ::
                                                   (Evar _a (tarray tlong 16)) ::
                                                   nil))
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _rx_sub (Tfunction
                                                                    ((tptr tlong) ::
                                                                    (tptr tlong) ::
                                                                    (tptr tlong) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                    ((Evar _c (tarray tlong 16)) ::
                                                     (Evar _d (tarray tlong 16)) ::
                                                     (Evar _f (tarray tlong 16)) ::
                                                     nil))
                                                  (Ssequence
                                                    (Scall None
                                                      (Evar _rx_mul (Tfunction
                                                                    ((tptr tlong) ::
                                                                    (tptr tlong) ::
                                                                    (tptr tlong) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                      ((Evar _a (tarray tlong 16)) ::
                                                       (Evar _c (tarray tlong 16)) ::
                                                       (Evar _k121665 (tarray tlong 16)) ::
                                                       nil))
                                                    (Ssequence
                                                      (Scall None
                                                        (Evar _rx_add 
                                                        (Tfunction
                                                          ((tptr tlong) ::
                                                           (tptr tlong) ::
                                                           (tptr tlong) ::
                                                           nil) tvoid
                                                          cc_default))
                                                        ((Evar _a (tarray tlong 16)) ::
                                                         (Evar _a (tarray tlong 16)) ::
                                                         (Evar _d (tarray tlong 16)) ::
                                                         nil))
                                                      (Ssequence
                                                        (Scall None
                                                          (Evar _rx_mul 
                                                          (Tfunction
                                                            ((tptr tlong) ::
                                                             (tptr tlong) ::
                                                             (tptr tlong) ::
                                                             nil) tvoid
                                                            cc_default))
                                                          ((Evar _c (tarray tlong 16)) ::
                                                           (Evar _c (tarray tlong 16)) ::
                                                           (Evar _a (tarray tlong 16)) ::
                                                           nil))
                                                        (Ssequence
                                                          (Scall None
                                                            (Evar _rx_mul 
                                                            (Tfunction
                                                              ((tptr tlong) ::
                                                               (tptr tlong) ::
                                                               (tptr tlong) ::
                                                               nil) tvoid
                                                              cc_default))
                                                            ((Evar _a (tarray tlong 16)) ::
                                                             (Evar _d (tarray tlong 16)) ::
                                                             (Evar _f (tarray tlong 16)) ::
                                                             nil))
                                                          (Ssequence
                                                            (Scall None
                                                              (Evar _rx_mul 
                                                              (Tfunction
                                                                ((tptr tlong) ::
                                                                 (tptr tlong) ::
                                                                 (tptr tlong) ::
                                                                 nil) tvoid
                                                                cc_default))
                                                              ((Evar _d (tarray tlong 16)) ::
                                                               (Evar _b (tarray tlong 16)) ::
                                                               (Evar _x (tarray tlong 16)) ::
                                                               nil))
                                                            (Ssequence
                                                              (Scall None
                                                                (Evar _rx_mul 
                                                                (Tfunction
                                                                  ((tptr tlong) ::
                                                                   (tptr tlong) ::
                                                                   (tptr tlong) ::
                                                                   nil) tvoid
                                                                  cc_default))
                                                                ((Evar _b (tarray tlong 16)) ::
                                                                 (Evar _e (tarray tlong 16)) ::
                                                                 (Evar _e (tarray tlong 16)) ::
                                                                 nil))
                                                              (Ssequence
                                                                (Scall None
                                                                  (Evar _rx_sel 
                                                                  (Tfunction
                                                                    ((tptr tlong) ::
                                                                    (tptr tlong) ::
                                                                    tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Evar _a (tarray tlong 16)) ::
                                                                   (Evar _b (tarray tlong 16)) ::
                                                                   (Etempvar _r tint) ::
                                                                   nil))
                                                                (Scall None
                                                                  (Evar _rx_sel 
                                                                  (Tfunction
                                                                    ((tptr tlong) ::
                                                                    (tptr tlong) ::
                                                                    tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Evar _c (tarray tlong 16)) ::
                                                                   (Evar _d (tarray tlong 16)) ::
                                                                   (Etempvar _r tint) ::
                                                                   nil)))))))))))))))))))))))))
                  (Sset _i
                    (Ebinop Osub (Etempvar _i tint)
                      (Econst_int (Int.repr 1) tint) tint))))
              (Ssequence
                (Scall None
                  (Evar _rx_inv (Tfunction
                                  ((tptr tlong) :: (tptr tlong) :: nil) tvoid
                                  cc_default))
                  ((Evar _c (tarray tlong 16)) ::
                   (Evar _c (tarray tlong 16)) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _rx_mul (Tfunction
                                    ((tptr tlong) :: (tptr tlong) ::
                                     (tptr tlong) :: nil) tvoid cc_default))
                    ((Evar _a (tarray tlong 16)) ::
                     (Evar _a (tarray tlong 16)) ::
                     (Evar _c (tarray tlong 16)) :: nil))
                  (Scall None
                    (Evar _rx_pack (Tfunction
                                     ((tptr tuchar) :: (tptr tlong) :: nil)
                                     tvoid cc_default))
                    ((Etempvar _q (tptr tuchar)) ::
                     (Evar _a (tarray tlong 16)) :: nil)))))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_s, (tarray tuchar 32)) :: (_p, (tarray tuchar 32)) ::
              (_s0, (tarray tuchar 32)) :: (_p0, (tarray tuchar 32)) ::
              (_ref, (tarray tuchar 32)) :: (_base, (tarray tuchar 32)) ::
              nil);
  fn_temps := ((_out, (tptr tuchar)) :: (_r, tbool) :: (_i, tint) ::
               (_t'17, tint) :: (_t'16, tint) :: (_t'15, tint) ::
               (_t'14, tint) :: (_t'13, tint) :: (_t'12, tint) ::
               (_t'11, tint) :: (_t'10, tint) :: (_t'9, tint) ::
               (_t'8, tbool) :: (_t'7, tint) :: (_t'6, tint) ::
               (_t'5, tint) :: (_t'4, tbool) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _quickproof_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                   cc_default))
        ((Econst_int (Int.repr 32) tint) :: nil))
      (Sset _out (Etempvar _t'1 (tptr tvoid))))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _out (tptr tuchar))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        Sskip)
      (Ssequence
        (Scall None
          (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                tvoid cc_default))
          ((Evar _s (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
           nil))
        (Ssequence
          (Scall None
            (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                  tvoid cc_default))
            ((Evar _p (tarray tuchar 32)) ::
             (Econst_int (Int.repr 32) tint) :: nil))
          (Ssequence
            (Scall None
              (Evar _bytes_copy (Tfunction
                                  ((tptr tuchar) :: (tptr tuchar) ::
                                   tulong :: nil) tvoid cc_default))
              ((Evar _s0 (tarray tuchar 32)) ::
               (Evar _s (tarray tuchar 32)) ::
               (Econst_int (Int.repr 32) tint) :: nil))
            (Ssequence
              (Scall None
                (Evar _bytes_copy (Tfunction
                                    ((tptr tuchar) :: (tptr tuchar) ::
                                     tulong :: nil) tvoid cc_default))
                ((Evar _p0 (tarray tuchar 32)) ::
                 (Evar _p (tarray tuchar 32)) ::
                 (Econst_int (Int.repr 32) tint) :: nil))
              (Ssequence
                (Ssequence
                  (Sset _i (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                     (Econst_int (Int.repr 32) tint) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Sifthenelse (Ebinop Oeq (Etempvar _i tint)
                                       (Econst_int (Int.repr 0) tint) tint)
                          (Sset _t'2
                            (Ecast (Econst_int (Int.repr 9) tint) tint))
                          (Sset _t'2
                            (Ecast (Econst_int (Int.repr 0) tint) tint)))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Evar _base (tarray tuchar 32))
                              (Etempvar _i tint) (tptr tuchar)) tuchar)
                          (Etempvar _t'2 tint))))
                    (Sset _i
                      (Ebinop Oadd (Etempvar _i tint)
                        (Econst_int (Int.repr 1) tint) tint))))
                (Ssequence
                  (Scall None
                    (Evar _ref_x25519 (Tfunction
                                        ((tptr tuchar) :: (tptr tuchar) ::
                                         (tptr tuchar) :: nil) tvoid
                                        cc_default))
                    ((Evar _ref (tarray tuchar 32)) ::
                     (Evar _s (tarray tuchar 32)) ::
                     (Evar _p (tarray tuchar 32)) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _curve25519_generic (Tfunction
                                                  ((tptr tuchar) ::
                                                   (tptr tuchar) ::
                                                   (tptr tuchar) :: nil)
                                                  tvoid cc_default))
                      ((Etempvar _out (tptr tuchar)) ::
                       (Evar _s (tarray tuchar 32)) ::
                       (Evar _p (tarray tuchar 32)) :: nil))
                    (Ssequence
                      (Sloop
                        (Ssequence
                          (Scall (Some _t'3)
                            (Evar _bytes_eq (Tfunction
                                              ((tptr tuchar) ::
                                               (tptr tuchar) :: tulong ::
                                               nil) tint cc_default))
                            ((Etempvar _out (tptr tuchar)) ::
                             (Evar _ref (tarray tuchar 32)) ::
                             (Econst_int (Int.repr 32) tint) :: nil))
                          (Sifthenelse (Eunop Onotbool (Etempvar _t'3 tint)
                                         tint)
                            (Scall None
                              (Evar _check_failed (Tfunction nil tvoid
                                                    cc_default)) nil)
                            Sskip))
                        Sbreak)
                      (Ssequence
                        (Scall None
                          (Evar _nondet_bytes (Tfunction
                                                ((tptr tuchar) :: tulong ::
                                                 nil) tvoid cc_default))
                          ((Etempvar _out (tptr tuchar)) ::
                           (Econst_int (Int.repr 32) tint) :: nil))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'4)
                              (Evar _curve25519 (Tfunction
                                                  ((tptr tuchar) ::
                                                   (tptr tuchar) ::
                                                   (tptr tuchar) :: nil)
                                                  tbool cc_default))
                              ((Etempvar _out (tptr tuchar)) ::
                               (Evar _s (tarray tuchar 32)) ::
                               (Evar _p (tarray tuchar 32)) :: nil))
                            (Sset _r (Ecast (Etempvar _t'4 tbool) tbool)))
                          (Ssequence
                            (Sloop
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'5)
                                    (Evar _bytes_eq (Tfunction
                                                      ((tptr tuchar) ::
                                                       (tptr tuchar) ::
                                                       tulong :: nil) tint
                                                      cc_default))
                                    ((Etempvar _out (tptr tuchar)) ::
                                     (Evar _ref (tarray tuchar 32)) ::
                                     (Econst_int (Int.repr 32) tint) :: nil))
                                  (Sifthenelse (Etempvar _t'5 tint)
                                    (Ssequence
                                      (Scall (Some _t'7)
                                        (Evar _bytes_zero (Tfunction
                                                            ((tptr tuchar) ::
                                                             tulong :: nil)
                                                            tint cc_default))
                                        ((Evar _ref (tarray tuchar 32)) ::
                                         (Econst_int (Int.repr 32) tint) ::
                                         nil))
                                      (Sset _t'6
                                        (Ecast
                                          (Ebinop Oeq (Etempvar _r tbool)
                                            (Eunop Onotbool
                                              (Etempvar _t'7 tint) tint)
                                            tint) tbool)))
                                    (Sset _t'6
                                      (Econst_int (Int.repr 0) tint))))
                                (Sifthenelse (Eunop Onotbool
                                               (Etempvar _t'6 tint) tint)
                                  (Scall None
                                    (Evar _check_failed (Tfunction nil tvoid
                                                          cc_default)) nil)
                                  Sskip))
                              Sbreak)
                            (Ssequence
                              (Scall None
                                (Evar _nondet_bytes (Tfunction
                                                      ((tptr tuchar) ::
                                                       tulong :: nil) tvoid
                                                      cc_default))
                                ((Etempvar _out (tptr tuchar)) ::
                                 (Econst_int (Int.repr 32) tint) :: nil))
                              (Ssequence
                                (Scall None
                                  (Evar _bytes_copy (Tfunction
                                                      ((tptr tuchar) ::
                                                       (tptr tuchar) ::
                                                       tulong :: nil) tvoid
                                                      cc_default))
                                  ((Evar _ref (tarray tuchar 32)) ::
                                   (Etempvar _out (tptr tuchar)) ::
                                   (Econst_int (Int.repr 32) tint) :: nil))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'8)
                                      (Evar _curve25519_generate_public 
                                      (Tfunction
                                        ((tptr tuchar) :: (tptr tuchar) ::
                                         nil) tbool cc_default))
                                      ((Etempvar _out (tptr tuchar)) ::
                                       (Evar _s (tarray tuchar 32)) :: nil))
                                    (Sset _r
                                      (Ecast (Etempvar _t'8 tbool) tbool)))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'14)
                                        (Evar _bytes_zero (Tfunction
                                                            ((tptr tuchar) ::
                                                             tulong :: nil)
                                                            tint cc_default))
                                        ((Evar _s (tarray tuchar 32)) ::
                                         (Econst_int (Int.repr 32) tint) ::
                                         nil))
                                      (Sifthenelse (Etempvar _t'14 tint)
                                        (Sloop
                                          (Ssequence
                                            (Sifthenelse (Eunop Onotbool
                                                           (Etempvar _r tbool)
                                                           tint)
                                              (Ssequence
                                                (Scall (Some _t'10)
                                                  (Evar _bytes_eq (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                  ((Etempvar _out (tptr tuchar)) ::
                                                   (Evar _ref (tarray tuchar 32)) ::
                                                   (Econst_int (Int.repr 32) tint) ::
                                                   nil))
                                                (Sset _t'9
                                                  (Ecast
                                                    (Etempvar _t'10 tint)
                                                    tbool)))
                                              (Sset _t'9
                                                (Econst_int (Int.repr 0) tint)))
                                            (Sifthenelse (Eunop Onotbool
                                                           (Etempvar _t'9 tint)
                                                           tint)
                                              (Scall None
                                                (Evar _check_failed (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                nil)
                                              Sskip))
                                          Sbreak)
                                        (Ssequence
                                          (Scall None
                                            (Evar _ref_x25519 (Tfunction
                                                                ((tptr tuchar) ::
                                                                 (tptr tuchar) ::
                                                                 (tptr tuchar) ::
                                                                 nil) tvoid
                                                                cc_default))
                                            ((Evar _ref (tarray tuchar 32)) ::
                                             (Evar _s (tarray tuchar 32)) ::
                                             (Evar _base (tarray tuchar 32)) ::
                                             nil))
                                          (Sloop
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'11)
                                                  (Evar _bytes_eq (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                  ((Etempvar _out (tptr tuchar)) ::
                                                   (Evar _ref (tarray tuchar 32)) ::
                                                   (Econst_int (Int.repr 32) tint) ::
                                                   nil))
                                                (Sifthenelse (Etempvar _t'11 tint)
                                                  (Ssequence
                                                    (Scall (Some _t'13)
                                                      (Evar _bytes_zero 
                                                      (Tfunction
                                                        ((tptr tuchar) ::
                                                         tulong :: nil) tint
                                                        cc_default))
                                                      ((Evar _ref (tarray tuchar 32)) ::
                                                       (Econst_int (Int.repr 32) tint) ::
                                                       nil))
                                                    (Sset _t'12
                                                      (Ecast
                                                        (Ebinop Oeq
                                                          (Etempvar _r tbool)
                                                          (Eunop Onotbool
                                                            (Etempvar _t'13 tint)
                                                            tint) tint)
                                                        tbool)))
                                                  (Sset _t'12
                                                    (Econst_int (Int.repr 0) tint))))
                                              (Sifthenelse (Eunop Onotbool
                                                             (Etempvar _t'12 tint)
                                                             tint)
                                                (Scall None
                                                  (Evar _check_failed 
                                                  (Tfunction nil tvoid
                                                    cc_default)) nil)
                                                Sskip))
                                            Sbreak))))
                                    (Ssequence
                                      (Sloop
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'15)
                                              (Evar _bytes_eq (Tfunction
                                                                ((tptr tuchar) ::
                                                                 (tptr tuchar) ::
                                                                 tulong ::
                                                                 nil) tint
                                                                cc_default))
                                              ((Evar _s (tarray tuchar 32)) ::
                                               (Evar _s0 (tarray tuchar 32)) ::
                                               (Econst_int (Int.repr 32) tint) ::
                                               nil))
                                            (Sifthenelse (Etempvar _t'15 tint)
                                              (Ssequence
                                                (Scall (Some _t'17)
                                                  (Evar _bytes_eq (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                  ((Evar _p (tarray tuchar 32)) ::
                                                   (Evar _p0 (tarray tuchar 32)) ::
                                                   (Econst_int (Int.repr 32) tint) ::
                                                   nil))
                                                (Sset _t'16
                                                  (Ecast
                                                    (Etempvar _t'17 tint)
                                                    tbool)))
                                              (Sset _t'16
                                                (Econst_int (Int.repr 0) tint))))
                                          (Sifthenelse (Eunop Onotbool
                                                         (Etempvar _t'16 tint)
                                                         tint)
                                            (Scall None
                                              (Evar _check_failed (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                              nil)
                                            Sskip))
                                        Sbreak)
                                      (Ssequence
                                        (Scall None
                                          (Evar _quickproof_free (Tfunction
                                                                   ((tptr tvoid) ::
                                                                    nil)
                                                                   tvoid
                                                                   cc_default))
                                          ((Etempvar _out (tptr tuchar)) ::
                                           nil))
                                        (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
nil.

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
 (_nondet_bytes,
   Gfun(External (EF_external "nondet_bytes"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xvoid
                     cc_default)) ((tptr tuchar) :: tulong :: nil) tvoid
     cc_default)) ::
 (_quickproof_malloc,
   Gfun(External (EF_external "quickproof_malloc"
                   (mksignature (AST.Xlong :: nil) AST.Xptr cc_default))
     (tulong :: nil) (tptr tvoid) cc_default)) ::
 (_quickproof_free,
   Gfun(External (EF_external "quickproof_free"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (_curve25519_generic,
   Gfun(External (EF_external "curve25519_generic"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xptr :: nil)
                     AST.Xvoid cc_default))
     ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) :: nil) tvoid
     cc_default)) ::
 (_curve25519,
   Gfun(External (EF_external "curve25519"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xptr :: nil)
                     AST.Xbool cc_default))
     ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) :: nil) tbool
     cc_default)) ::
 (_curve25519_generate_public,
   Gfun(External (EF_external "curve25519_generate_public"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xbool
                     cc_default)) ((tptr tuchar) :: (tptr tuchar) :: nil)
     tbool cc_default)) :: (_check_failed, Gfun(Internal f_check_failed)) ::
 (_bytes_eq, Gfun(Internal f_bytes_eq)) ::
 (_bytes_zero, Gfun(Internal f_bytes_zero)) ::
 (_bytes_copy, Gfun(Internal f_bytes_copy)) ::
 (_rx_car, Gfun(Internal f_rx_car)) :: (_rx_sel, Gfun(Internal f_rx_sel)) ::
 (_rx_pack, Gfun(Internal f_rx_pack)) ::
 (_rx_unpack, Gfun(Internal f_rx_unpack)) ::
 (_rx_add, Gfun(Internal f_rx_add)) :: (_rx_sub, Gfun(Internal f_rx_sub)) ::
 (_rx_mul, Gfun(Internal f_rx_mul)) :: (_rx_inv, Gfun(Internal f_rx_inv)) ::
 (_k121665, Gvar v_k121665) :: (_ref_x25519, Gfun(Internal f_ref_x25519)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _curve25519_generate_public :: _curve25519 ::
 _curve25519_generic :: _quickproof_free :: _quickproof_malloc ::
 _nondet_bytes :: ___builtin_debug :: ___builtin_write32_reversed ::
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


