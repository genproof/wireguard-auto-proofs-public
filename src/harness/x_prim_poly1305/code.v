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
  Definition source_file := "harness/x_prim_poly1305.c".
  Definition normalized := true.
End Info.

Definition __anon_ef6b4645c220 : ident := $"_anon_ef6b4645c220".
Definition __anon_43224dacc2cf : ident := $"_anon_43224dacc2cf".
Definition __anon_472b2db33f49 : ident := $"_anon_472b2db33f49".
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
Definition _buf : ident := $"buf".
Definition _buflen : ident := $"buflen".
Definition _bytes_copy : ident := $"bytes_copy".
Definition _bytes_eq : ident := $"bytes_eq".
Definition _bytes_zero : ident := $"bytes_zero".
Definition _c : ident := $"c".
Definition _check_failed : ident := $"check_failed".
Definition _copy : ident := $"copy".
Definition _core_r : ident := $"core_r".
Definition _d : ident := $"d".
Definition _draw_size : ident := $"draw_size".
Definition _g : ident := $"g".
Definition _h : ident := $"h".
Definition _h64 : ident := $"h64".
Definition _i : ident := $"i".
Definition _j : ident := $"j".
Definition _key : ident := $"key".
Definition _key0 : ident := $"key0".
Definition _len : ident := $"len".
Definition _m : ident := $"m".
Definition _main : ident := $"main".
Definition _x_prim_poly1305__minusp : ident := $"x_prim_poly1305__minusp".
Definition _msg : ident := $"msg".
Definition _n : ident := $"n".
Definition _nondet_bytes : ident := $"nondet_bytes".
Definition _nondet_size : ident := $"nondet_size".
Definition _opaque_r : ident := $"opaque_r".
Definition _out : ident := $"out".
Definition _p : ident := $"p".
Definition _poly1305_block_state : ident := $"poly1305_block_state".
Definition _poly1305_core_key : ident := $"poly1305_core_key".
Definition _poly1305_desc_ctx : ident := $"poly1305_desc_ctx".
Definition _poly1305_final : ident := $"poly1305_final".
Definition _poly1305_init : ident := $"poly1305_init".
Definition _poly1305_key : ident := $"poly1305_key".
Definition _poly1305_state : ident := $"poly1305_state".
Definition _poly1305_update : ident := $"poly1305_update".
Definition _pos : ident := $"pos".
Definition _precomputed_s : ident := $"precomputed_s".
Definition _quickproof_free : ident := $"quickproof_free".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _r : ident := $"r".
Definition _r64 : ident := $"r64".
Definition _ref : ident := $"ref".
Definition _ref_poly1305 : ident := $"ref_poly1305".
Definition _rp_add : ident := $"rp_add".
Definition _rp_block : ident := $"rp_block".
Definition _rp_final : ident := $"rp_final".
Definition _rp_init : ident := $"rp_init".
Definition _rp_mul : ident := $"rp_mul".
Definition _rpoly : ident := $"rpoly".
Definition _s : ident := $"s".
Definition _state : ident := $"state".
Definition _tag : ident := $"tag".
Definition _u : ident := $"u".
Definition _x : ident := $"x".
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

Definition f_draw_size := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_n, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _nondet_size (Tfunction nil tulong cc_default))
      nil)
    (Sset _n (Etempvar _t'1 tulong)))
  (Ssequence
    (Sifthenelse (Ebinop Ole (Etempvar _n tulong)
                   (Econst_long (Int64.repr (-1)) tulong) tint)
      (Sset _t'2 (Ecast (Etempvar _n tulong) tulong))
      (Sset _t'2
        (Ecast
          (Ebinop Omod (Etempvar _n tulong)
            (Econst_long (Int64.repr (-1)) tulong) tulong) tulong)))
    (Sreturn (Some (Etempvar _t'2 tulong)))))
|}.

Definition f_rp_add := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr tuint)) :: (_c, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_u, tuint) :: (_j, tint) :: (_t'2, tuint) :: (_t'1, tuint) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _u (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _j (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                       (Econst_int (Int.repr 17) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Ederef
                (Ebinop Oadd (Etempvar _h (tptr tuint)) (Etempvar _j tint)
                  (tptr tuint)) tuint))
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd (Etempvar _c (tptr tuint)) (Etempvar _j tint)
                    (tptr tuint)) tuint))
              (Sset _u
                (Ebinop Oadd (Etempvar _u tuint)
                  (Ebinop Oadd (Etempvar _t'1 tuint) (Etempvar _t'2 tuint)
                    tuint) tuint))))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _h (tptr tuint)) (Etempvar _j tint)
                  (tptr tuint)) tuint)
              (Ebinop Oand (Etempvar _u tuint)
                (Econst_int (Int.repr 255) tint) tuint))
            (Sset _u
              (Ebinop Oshr (Etempvar _u tuint) (Econst_int (Int.repr 8) tint)
                tuint)))))
      (Sset _j
        (Ebinop Oadd (Etempvar _j tint) (Econst_int (Int.repr 1) tint) tint)))))
|}.

Definition f_rp_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _rpoly noattr))) ::
                (_key, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_j, tint) :: (_t'9, tuchar) :: (_t'8, tuchar) ::
               (_t'7, tuint) :: (_t'6, tuint) :: (_t'5, tuint) ::
               (_t'4, tuint) :: (_t'3, tuint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _j (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                       (Econst_int (Int.repr 17) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                    (Tstruct _rpoly noattr)) _r (tarray tuint 17))
                (Etempvar _j tint) (tptr tuint)) tuint)
            (Econst_int (Int.repr 0) tint))
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                    (Tstruct _rpoly noattr)) _h (tarray tuint 17))
                (Etempvar _j tint) (tptr tuint)) tuint)
            (Econst_int (Int.repr 0) tint))))
      (Sset _j
        (Ebinop Oadd (Etempvar _j tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Ssequence
      (Sset _j (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                         (Econst_int (Int.repr 16) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Ssequence
              (Sset _t'9
                (Ederef
                  (Ebinop Oadd (Etempvar _key (tptr tuchar))
                    (Etempvar _j tint) (tptr tuchar)) tuchar))
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                        (Tstruct _rpoly noattr)) _r (tarray tuint 17))
                    (Etempvar _j tint) (tptr tuint)) tuint)
                (Etempvar _t'9 tuchar)))
            (Ssequence
              (Sset _t'8
                (Ederef
                  (Ebinop Oadd (Etempvar _key (tptr tuchar))
                    (Ebinop Oadd (Econst_int (Int.repr 16) tint)
                      (Etempvar _j tint) tint) (tptr tuchar)) tuchar))
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                        (Tstruct _rpoly noattr)) _s (tarray tuchar 16))
                    (Etempvar _j tint) (tptr tuchar)) tuchar)
                (Etempvar _t'8 tuchar)))))
        (Sset _j
          (Ebinop Oadd (Etempvar _j tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Ssequence
        (Sset _t'7
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                  (Tstruct _rpoly noattr)) _r (tarray tuint 17))
              (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint))
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                  (Tstruct _rpoly noattr)) _r (tarray tuint 17))
              (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint)
          (Ebinop Oand (Etempvar _t'7 tuint) (Econst_int (Int.repr 15) tint)
            tuint)))
      (Ssequence
        (Ssequence
          (Sset _t'6
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                    (Tstruct _rpoly noattr)) _r (tarray tuint 17))
                (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint))
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                    (Tstruct _rpoly noattr)) _r (tarray tuint 17))
                (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint)
            (Ebinop Oand (Etempvar _t'6 tuint)
              (Econst_int (Int.repr 252) tint) tuint)))
        (Ssequence
          (Ssequence
            (Sset _t'5
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                      (Tstruct _rpoly noattr)) _r (tarray tuint 17))
                  (Econst_int (Int.repr 7) tint) (tptr tuint)) tuint))
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                      (Tstruct _rpoly noattr)) _r (tarray tuint 17))
                  (Econst_int (Int.repr 7) tint) (tptr tuint)) tuint)
              (Ebinop Oand (Etempvar _t'5 tuint)
                (Econst_int (Int.repr 15) tint) tuint)))
          (Ssequence
            (Ssequence
              (Sset _t'4
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                        (Tstruct _rpoly noattr)) _r (tarray tuint 17))
                    (Econst_int (Int.repr 8) tint) (tptr tuint)) tuint))
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                        (Tstruct _rpoly noattr)) _r (tarray tuint 17))
                    (Econst_int (Int.repr 8) tint) (tptr tuint)) tuint)
                (Ebinop Oand (Etempvar _t'4 tuint)
                  (Econst_int (Int.repr 252) tint) tuint)))
            (Ssequence
              (Ssequence
                (Sset _t'3
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                          (Tstruct _rpoly noattr)) _r (tarray tuint 17))
                      (Econst_int (Int.repr 11) tint) (tptr tuint)) tuint))
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                          (Tstruct _rpoly noattr)) _r (tarray tuint 17))
                      (Econst_int (Int.repr 11) tint) (tptr tuint)) tuint)
                  (Ebinop Oand (Etempvar _t'3 tuint)
                    (Econst_int (Int.repr 15) tint) tuint)))
              (Ssequence
                (Ssequence
                  (Sset _t'2
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                            (Tstruct _rpoly noattr)) _r (tarray tuint 17))
                        (Econst_int (Int.repr 12) tint) (tptr tuint)) tuint))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                            (Tstruct _rpoly noattr)) _r (tarray tuint 17))
                        (Econst_int (Int.repr 12) tint) (tptr tuint)) tuint)
                    (Ebinop Oand (Etempvar _t'2 tuint)
                      (Econst_int (Int.repr 252) tint) tuint)))
                (Ssequence
                  (Sset _t'1
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                            (Tstruct _rpoly noattr)) _r (tarray tuint 17))
                        (Econst_int (Int.repr 15) tint) (tptr tuint)) tuint))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                            (Tstruct _rpoly noattr)) _r (tarray tuint 17))
                        (Econst_int (Int.repr 15) tint) (tptr tuint)) tuint)
                    (Ebinop Oand (Etempvar _t'1 tuint)
                      (Econst_int (Int.repr 15) tint) tuint)))))))))))
|}.

Definition f_rp_mul := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _rpoly noattr))) :: (_c, (tptr tuint)) ::
                nil);
  fn_vars := ((_x, (tarray tuint 17)) :: nil);
  fn_temps := ((_u, tuint) :: (_i, tint) :: (_j, tint) :: (_t'1, tuint) ::
               (_t'10, tuint) :: (_t'9, tuint) :: (_t'8, tuint) ::
               (_t'7, tuint) :: (_t'6, tuint) :: (_t'5, tuint) ::
               (_t'4, tuint) :: (_t'3, tuint) :: (_t'2, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _rp_add (Tfunction ((tptr tuint) :: (tptr tuint) :: nil) tvoid
                    cc_default))
    ((Efield
       (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
         (Tstruct _rpoly noattr)) _h (tarray tuint 17)) ::
     (Etempvar _c (tptr tuint)) :: nil))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                         (Econst_int (Int.repr 17) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _x (tarray tuint 17)) (Etempvar _i tint)
                  (tptr tuint)) tuint) (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sset _j (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                                 (Econst_int (Int.repr 17) tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sifthenelse (Ebinop Ole (Etempvar _j tint)
                                   (Etempvar _i tint) tint)
                      (Ssequence
                        (Sset _t'10
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                                  (Tstruct _rpoly noattr)) _r
                                (tarray tuint 17))
                              (Ebinop Osub (Etempvar _i tint)
                                (Etempvar _j tint) tint) (tptr tuint)) tuint))
                        (Sset _t'1 (Ecast (Etempvar _t'10 tuint) tuint)))
                      (Ssequence
                        (Sset _t'9
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                                  (Tstruct _rpoly noattr)) _r
                                (tarray tuint 17))
                              (Ebinop Osub
                                (Ebinop Oadd (Etempvar _i tint)
                                  (Econst_int (Int.repr 17) tint) tint)
                                (Etempvar _j tint) tint) (tptr tuint)) tuint))
                        (Sset _t'1
                          (Ecast
                            (Ebinop Omul (Econst_int (Int.repr 320) tint)
                              (Etempvar _t'9 tuint) tuint) tuint))))
                    (Ssequence
                      (Sset _t'7
                        (Ederef
                          (Ebinop Oadd (Evar _x (tarray tuint 17))
                            (Etempvar _i tint) (tptr tuint)) tuint))
                      (Ssequence
                        (Sset _t'8
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                                  (Tstruct _rpoly noattr)) _h
                                (tarray tuint 17)) (Etempvar _j tint)
                              (tptr tuint)) tuint))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Evar _x (tarray tuint 17))
                              (Etempvar _i tint) (tptr tuint)) tuint)
                          (Ebinop Oadd (Etempvar _t'7 tuint)
                            (Ebinop Omul (Etempvar _t'8 tuint)
                              (Etempvar _t'1 tuint) tuint) tuint))))))
                (Sset _j
                  (Ebinop Oadd (Etempvar _j tint)
                    (Econst_int (Int.repr 1) tint) tint))))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Econst_int (Int.repr 17) tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _t'6
                (Ederef
                  (Ebinop Oadd (Evar _x (tarray tuint 17)) (Etempvar _i tint)
                    (tptr tuint)) tuint))
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                        (Tstruct _rpoly noattr)) _h (tarray tuint 17))
                    (Etempvar _i tint) (tptr tuint)) tuint)
                (Etempvar _t'6 tuint))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Ssequence
        (Sset _u (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Ssequence
            (Sset _j (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                               (Econst_int (Int.repr 16) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Ssequence
                    (Sset _t'5
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                              (Tstruct _rpoly noattr)) _h (tarray tuint 17))
                          (Etempvar _j tint) (tptr tuint)) tuint))
                    (Sset _u
                      (Ebinop Oadd (Etempvar _u tuint) (Etempvar _t'5 tuint)
                        tuint)))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                              (Tstruct _rpoly noattr)) _h (tarray tuint 17))
                          (Etempvar _j tint) (tptr tuint)) tuint)
                      (Ebinop Oand (Etempvar _u tuint)
                        (Econst_int (Int.repr 255) tint) tuint))
                    (Sset _u
                      (Ebinop Oshr (Etempvar _u tuint)
                        (Econst_int (Int.repr 8) tint) tuint)))))
              (Sset _j
                (Ebinop Oadd (Etempvar _j tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Ssequence
              (Sset _t'4
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                        (Tstruct _rpoly noattr)) _h (tarray tuint 17))
                    (Econst_int (Int.repr 16) tint) (tptr tuint)) tuint))
              (Sset _u
                (Ebinop Oadd (Etempvar _u tuint) (Etempvar _t'4 tuint) tuint)))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                        (Tstruct _rpoly noattr)) _h (tarray tuint 17))
                    (Econst_int (Int.repr 16) tint) (tptr tuint)) tuint)
                (Ebinop Oand (Etempvar _u tuint)
                  (Econst_int (Int.repr 3) tint) tuint))
              (Ssequence
                (Sset _u
                  (Ebinop Omul (Econst_int (Int.repr 5) tint)
                    (Ebinop Oshr (Etempvar _u tuint)
                      (Econst_int (Int.repr 2) tint) tuint) tuint))
                (Ssequence
                  (Ssequence
                    (Sset _j (Econst_int (Int.repr 0) tint))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                                       (Econst_int (Int.repr 16) tint) tint)
                          Sskip
                          Sbreak)
                        (Ssequence
                          (Ssequence
                            (Sset _t'3
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                                      (Tstruct _rpoly noattr)) _h
                                    (tarray tuint 17)) (Etempvar _j tint)
                                  (tptr tuint)) tuint))
                            (Sset _u
                              (Ebinop Oadd (Etempvar _u tuint)
                                (Etempvar _t'3 tuint) tuint)))
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                                      (Tstruct _rpoly noattr)) _h
                                    (tarray tuint 17)) (Etempvar _j tint)
                                  (tptr tuint)) tuint)
                              (Ebinop Oand (Etempvar _u tuint)
                                (Econst_int (Int.repr 255) tint) tuint))
                            (Sset _u
                              (Ebinop Oshr (Etempvar _u tuint)
                                (Econst_int (Int.repr 8) tint) tuint)))))
                      (Sset _j
                        (Ebinop Oadd (Etempvar _j tint)
                          (Econst_int (Int.repr 1) tint) tint))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'2
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                                (Tstruct _rpoly noattr)) _h
                              (tarray tuint 17))
                            (Econst_int (Int.repr 16) tint) (tptr tuint))
                          tuint))
                      (Sset _u
                        (Ebinop Oadd (Etempvar _u tuint)
                          (Etempvar _t'2 tuint) tuint)))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                              (Tstruct _rpoly noattr)) _h (tarray tuint 17))
                          (Econst_int (Int.repr 16) tint) (tptr tuint))
                        tuint) (Etempvar _u tuint))))))))))))
|}.

Definition f_rp_block := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _rpoly noattr))) ::
                (_m, (tptr tuchar)) :: nil);
  fn_vars := ((_c, (tarray tuint 17)) :: nil);
  fn_temps := ((_j, tint) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _j (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                       (Econst_int (Int.repr 16) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'1
            (Ederef
              (Ebinop Oadd (Etempvar _m (tptr tuchar)) (Etempvar _j tint)
                (tptr tuchar)) tuchar))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _c (tarray tuint 17)) (Etempvar _j tint)
                (tptr tuint)) tuint) (Etempvar _t'1 tuchar))))
      (Sset _j
        (Ebinop Oadd (Etempvar _j tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Evar _c (tarray tuint 17))
          (Econst_int (Int.repr 16) tint) (tptr tuint)) tuint)
      (Econst_int (Int.repr 1) tint))
    (Scall None
      (Evar _rp_mul (Tfunction
                      ((tptr (Tstruct _rpoly noattr)) :: (tptr tuint) :: nil)
                      tvoid cc_default))
      ((Etempvar _p (tptr (Tstruct _rpoly noattr))) ::
       (Evar _c (tarray tuint 17)) :: nil))))
|}.

Definition v_x_prim_poly1305__minusp := {|
  gvar_info := (tarray tuint 17);
  gvar_init := (Init_int32 (Int.repr 5) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 252) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_rp_final := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _rpoly noattr))) ::
                (_out, (tptr tuchar)) :: nil);
  fn_vars := ((_g, (tarray tuint 17)) :: (_c, (tarray tuint 17)) :: nil);
  fn_temps := ((_s, tuint) :: (_j, tint) :: (_t'7, tuint) :: (_t'6, tuint) ::
               (_t'5, tuint) :: (_t'4, tuint) :: (_t'3, tuint) ::
               (_t'2, tuchar) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _j (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                       (Econst_int (Int.repr 17) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'7
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                    (Tstruct _rpoly noattr)) _h (tarray tuint 17))
                (Etempvar _j tint) (tptr tuint)) tuint))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _g (tarray tuint 17)) (Etempvar _j tint)
                (tptr tuint)) tuint) (Etempvar _t'7 tuint))))
      (Sset _j
        (Ebinop Oadd (Etempvar _j tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Scall None
      (Evar _rp_add (Tfunction ((tptr tuint) :: (tptr tuint) :: nil) tvoid
                      cc_default))
      ((Efield
         (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
           (Tstruct _rpoly noattr)) _h (tarray tuint 17)) ::
       (Evar _x_prim_poly1305__minusp (tarray tuint 17)) :: nil))
    (Ssequence
      (Ssequence
        (Sset _t'6
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                  (Tstruct _rpoly noattr)) _h (tarray tuint 17))
              (Econst_int (Int.repr 16) tint) (tptr tuint)) tuint))
        (Sset _s
          (Eunop Oneg
            (Ebinop Oshr (Etempvar _t'6 tuint) (Econst_int (Int.repr 7) tint)
              tuint) tuint)))
      (Ssequence
        (Ssequence
          (Sset _j (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                             (Econst_int (Int.repr 17) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _t'3
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                          (Tstruct _rpoly noattr)) _h (tarray tuint 17))
                      (Etempvar _j tint) (tptr tuint)) tuint))
                (Ssequence
                  (Sset _t'4
                    (Ederef
                      (Ebinop Oadd (Evar _g (tarray tuint 17))
                        (Etempvar _j tint) (tptr tuint)) tuint))
                  (Ssequence
                    (Sset _t'5
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                              (Tstruct _rpoly noattr)) _h (tarray tuint 17))
                          (Etempvar _j tint) (tptr tuint)) tuint))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                              (Tstruct _rpoly noattr)) _h (tarray tuint 17))
                          (Etempvar _j tint) (tptr tuint)) tuint)
                      (Ebinop Oxor (Etempvar _t'3 tuint)
                        (Ebinop Oand (Etempvar _s tuint)
                          (Ebinop Oxor (Etempvar _t'4 tuint)
                            (Etempvar _t'5 tuint) tuint) tuint) tuint))))))
            (Sset _j
              (Ebinop Oadd (Etempvar _j tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Ssequence
          (Ssequence
            (Sset _j (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                               (Econst_int (Int.repr 16) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _t'2
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                            (Tstruct _rpoly noattr)) _s (tarray tuchar 16))
                        (Etempvar _j tint) (tptr tuchar)) tuchar))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Evar _c (tarray tuint 17))
                        (Etempvar _j tint) (tptr tuint)) tuint)
                    (Etempvar _t'2 tuchar))))
              (Sset _j
                (Ebinop Oadd (Etempvar _j tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _c (tarray tuint 17))
                  (Econst_int (Int.repr 16) tint) (tptr tuint)) tuint)
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Scall None
                (Evar _rp_add (Tfunction
                                ((tptr tuint) :: (tptr tuint) :: nil) tvoid
                                cc_default))
                ((Efield
                   (Ederef (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                     (Tstruct _rpoly noattr)) _h (tarray tuint 17)) ::
                 (Evar _c (tarray tuint 17)) :: nil))
              (Ssequence
                (Sset _j (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                                   (Econst_int (Int.repr 16) tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Sset _t'1
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _p (tptr (Tstruct _rpoly noattr)))
                                (Tstruct _rpoly noattr)) _h
                              (tarray tuint 17)) (Etempvar _j tint)
                            (tptr tuint)) tuint))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _out (tptr tuchar))
                            (Etempvar _j tint) (tptr tuchar)) tuchar)
                        (Ecast (Etempvar _t'1 tuint) tuchar))))
                  (Sset _j
                    (Ebinop Oadd (Etempvar _j tint)
                      (Econst_int (Int.repr 1) tint) tint)))))))))))
|}.

Definition f_ref_poly1305 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) :: (_key, (tptr tuchar)) ::
                (_m, (tptr tuchar)) :: (_len, tulong) :: nil);
  fn_vars := ((_p, (Tstruct _rpoly noattr)) :: (_c, (tarray tuint 17)) ::
              nil);
  fn_temps := ((_pos, tulong) :: (_j, tulong) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _pos (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Ssequence
    (Scall None
      (Evar _rp_init (Tfunction
                       ((tptr (Tstruct _rpoly noattr)) :: (tptr tuchar) ::
                        nil) tvoid cc_default))
      ((Eaddrof (Evar _p (Tstruct _rpoly noattr))
         (tptr (Tstruct _rpoly noattr))) :: (Etempvar _key (tptr tuchar)) ::
       nil))
    (Ssequence
      (Swhile
        (Ebinop Oge
          (Ebinop Osub (Etempvar _len tulong) (Etempvar _pos tulong) tulong)
          (Econst_int (Int.repr 16) tint) tint)
        (Ssequence
          (Scall None
            (Evar _rp_block (Tfunction
                              ((tptr (Tstruct _rpoly noattr)) ::
                               (tptr tuchar) :: nil) tvoid cc_default))
            ((Eaddrof (Evar _p (Tstruct _rpoly noattr))
               (tptr (Tstruct _rpoly noattr))) ::
             (Ebinop Oadd (Etempvar _m (tptr tuchar)) (Etempvar _pos tulong)
               (tptr tuchar)) :: nil))
          (Sset _pos
            (Ebinop Oadd (Etempvar _pos tulong)
              (Econst_int (Int.repr 16) tint) tulong))))
      (Ssequence
        (Sifthenelse (Ebinop Ogt
                       (Ebinop Osub (Etempvar _len tulong)
                         (Etempvar _pos tulong) tulong)
                       (Econst_int (Int.repr 0) tint) tint)
          (Ssequence
            (Ssequence
              (Sset _j (Ecast (Econst_int (Int.repr 0) tint) tulong))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _j tulong)
                                 (Econst_int (Int.repr 17) tint) tint)
                    Sskip
                    Sbreak)
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Evar _c (tarray tuint 17))
                        (Etempvar _j tulong) (tptr tuint)) tuint)
                    (Econst_int (Int.repr 0) tint)))
                (Sset _j
                  (Ebinop Oadd (Etempvar _j tulong)
                    (Econst_int (Int.repr 1) tint) tulong))))
            (Ssequence
              (Ssequence
                (Sset _j (Ecast (Econst_int (Int.repr 0) tint) tulong))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _j tulong)
                                   (Ebinop Osub (Etempvar _len tulong)
                                     (Etempvar _pos tulong) tulong) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Sset _t'1
                        (Ederef
                          (Ebinop Oadd (Etempvar _m (tptr tuchar))
                            (Ebinop Oadd (Etempvar _pos tulong)
                              (Etempvar _j tulong) tulong) (tptr tuchar))
                          tuchar))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _c (tarray tuint 17))
                            (Etempvar _j tulong) (tptr tuint)) tuint)
                        (Etempvar _t'1 tuchar))))
                  (Sset _j
                    (Ebinop Oadd (Etempvar _j tulong)
                      (Econst_int (Int.repr 1) tint) tulong))))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _c (tarray tuint 17))
                      (Ebinop Osub (Etempvar _len tulong)
                        (Etempvar _pos tulong) tulong) (tptr tuint)) tuint)
                  (Econst_int (Int.repr 1) tint))
                (Scall None
                  (Evar _rp_mul (Tfunction
                                  ((tptr (Tstruct _rpoly noattr)) ::
                                   (tptr tuint) :: nil) tvoid cc_default))
                  ((Eaddrof (Evar _p (Tstruct _rpoly noattr))
                     (tptr (Tstruct _rpoly noattr))) ::
                   (Evar _c (tarray tuint 17)) :: nil)))))
          Sskip)
        (Scall None
          (Evar _rp_final (Tfunction
                            ((tptr (Tstruct _rpoly noattr)) ::
                             (tptr tuchar) :: nil) tvoid cc_default))
          ((Eaddrof (Evar _p (Tstruct _rpoly noattr))
             (tptr (Tstruct _rpoly noattr))) ::
           (Etempvar _out (tptr tuchar)) :: nil))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_d, (Tstruct _poly1305_desc_ctx noattr)) ::
              (_key, (tarray tuchar 32)) :: (_key0, (tarray tuchar 32)) ::
              (_ref, (tarray tuchar 16)) :: nil);
  fn_temps := ((_msg, (tptr tuchar)) :: (_copy, (tptr tuchar)) ::
               (_tag, (tptr tuchar)) :: (_n, tulong) :: (_pos, tulong) ::
               (_i, tulong) :: (_c, tulong) :: (_t'14, tint) ::
               (_t'13, tint) :: (_t'12, tint) :: (_t'11, tint) ::
               (_t'10, tint) :: (_t'9, tint) :: (_t'8, tint) ::
               (_t'7, tulong) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, (tptr tvoid)) :: (_t'3, (tptr tvoid)) ::
               (_t'2, (tptr tvoid)) :: (_t'1, tulong) :: (_t'19, tuint) ::
               (_t'18, tuint) :: (_t'17, tuint) :: (_t'16, tuint) ::
               (_t'15, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall None
      (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil) tvoid
                            cc_default))
      ((Evar _key (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
       nil))
    (Ssequence
      (Scall None
        (Evar _bytes_copy (Tfunction
                            ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                            tvoid cc_default))
        ((Evar _key0 (tarray tuchar 32)) :: (Evar _key (tarray tuchar 32)) ::
         (Econst_int (Int.repr 32) tint) :: nil))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _draw_size (Tfunction nil tulong cc_default)) nil)
          (Sset _n (Etempvar _t'1 tulong)))
        (Ssequence
          (Sifthenelse (Ebinop Ogt (Etempvar _n tulong)
                         (Econst_long (Int64.repr 9223372036854775807) tlong)
                         tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
            Sskip)
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                           (tptr tvoid) cc_default))
                ((Etempvar _n tulong) :: nil))
              (Sset _msg (Etempvar _t'2 (tptr tvoid))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                             (tptr tvoid) cc_default))
                  ((Etempvar _n tulong) :: nil))
                (Sset _copy (Etempvar _t'3 (tptr tvoid))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                               (tptr tvoid) cc_default))
                    ((Econst_int (Int.repr 16) tint) :: nil))
                  (Sset _tag (Etempvar _t'4 (tptr tvoid))))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sifthenelse (Ebinop Oeq (Etempvar _msg (tptr tuchar))
                                     (Ecast (Econst_int (Int.repr 0) tint)
                                       (tptr tvoid)) tint)
                        (Sset _t'5 (Econst_int (Int.repr 1) tint))
                        (Sset _t'5
                          (Ecast
                            (Ebinop Oeq (Etempvar _copy (tptr tuchar))
                              (Ecast (Econst_int (Int.repr 0) tint)
                                (tptr tvoid)) tint) tbool)))
                      (Sifthenelse (Etempvar _t'5 tint)
                        (Sset _t'6 (Econst_int (Int.repr 1) tint))
                        (Sset _t'6
                          (Ecast
                            (Ebinop Oeq (Etempvar _tag (tptr tuchar))
                              (Ecast (Econst_int (Int.repr 0) tint)
                                (tptr tvoid)) tint) tbool))))
                    (Sifthenelse (Etempvar _t'6 tint)
                      (Ssequence
                        (Scall None
                          (Evar _quickproof_free (Tfunction
                                                   ((tptr tvoid) :: nil)
                                                   tvoid cc_default))
                          ((Etempvar _msg (tptr tuchar)) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _quickproof_free (Tfunction
                                                     ((tptr tvoid) :: nil)
                                                     tvoid cc_default))
                            ((Etempvar _copy (tptr tuchar)) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar _quickproof_free (Tfunction
                                                       ((tptr tvoid) :: nil)
                                                       tvoid cc_default))
                              ((Etempvar _tag (tptr tuchar)) :: nil))
                            (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
                      Sskip))
                  (Ssequence
                    (Scall None
                      (Evar _nondet_bytes (Tfunction
                                            ((tptr tuchar) :: tulong :: nil)
                                            tvoid cc_default))
                      ((Etempvar _msg (tptr tuchar)) ::
                       (Etempvar _n tulong) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _bytes_copy (Tfunction
                                            ((tptr tuchar) ::
                                             (tptr tuchar) :: tulong :: nil)
                                            tvoid cc_default))
                        ((Etempvar _copy (tptr tuchar)) ::
                         (Etempvar _msg (tptr tuchar)) ::
                         (Etempvar _n tulong) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _poly1305_init (Tfunction
                                                 ((tptr (Tstruct _poly1305_desc_ctx noattr)) ::
                                                  (tptr tuchar) :: nil) tvoid
                                                 cc_default))
                          ((Eaddrof
                             (Evar _d (Tstruct _poly1305_desc_ctx noattr))
                             (tptr (Tstruct _poly1305_desc_ctx noattr))) ::
                           (Evar _key (tarray tuchar 32)) :: nil))
                        (Ssequence
                          (Sset _pos
                            (Ecast (Econst_int (Int.repr 0) tint) tulong))
                          (Ssequence
                            (Swhile
                              (Ebinop Olt (Etempvar _pos tulong)
                                (Etempvar _n tulong) tint)
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'7)
                                    (Evar _nondet_size (Tfunction nil tulong
                                                         cc_default)) nil)
                                  (Sset _c (Etempvar _t'7 tulong)))
                                (Ssequence
                                  (Sifthenelse (Ebinop Ogt
                                                 (Etempvar _c tulong)
                                                 (Ebinop Osub
                                                   (Etempvar _n tulong)
                                                   (Etempvar _pos tulong)
                                                   tulong) tint)
                                    (Sset _c
                                      (Ebinop Osub (Etempvar _n tulong)
                                        (Etempvar _pos tulong) tulong))
                                    Sskip)
                                  (Ssequence
                                    (Scall None
                                      (Evar _poly1305_update (Tfunction
                                                               ((tptr (Tstruct _poly1305_desc_ctx noattr)) ::
                                                                (tptr tuchar) ::
                                                                tulong ::
                                                                nil) tvoid
                                                               cc_default))
                                      ((Eaddrof
                                         (Evar _d (Tstruct _poly1305_desc_ctx noattr))
                                         (tptr (Tstruct _poly1305_desc_ctx noattr))) ::
                                       (Ebinop Oadd
                                         (Etempvar _msg (tptr tuchar))
                                         (Etempvar _pos tulong)
                                         (tptr tuchar)) ::
                                       (Etempvar _c tulong) :: nil))
                                    (Sset _pos
                                      (Ebinop Oadd (Etempvar _pos tulong)
                                        (Etempvar _c tulong) tulong))))))
                            (Ssequence
                              (Scall None
                                (Evar _poly1305_final (Tfunction
                                                        ((tptr (Tstruct _poly1305_desc_ctx noattr)) ::
                                                         (tptr tuchar) ::
                                                         nil) tvoid
                                                        cc_default))
                                ((Eaddrof
                                   (Evar _d (Tstruct _poly1305_desc_ctx noattr))
                                   (tptr (Tstruct _poly1305_desc_ctx noattr))) ::
                                 (Etempvar _tag (tptr tuchar)) :: nil))
                              (Ssequence
                                (Scall None
                                  (Evar _ref_poly1305 (Tfunction
                                                        ((tptr tuchar) ::
                                                         (tptr tuchar) ::
                                                         (tptr tuchar) ::
                                                         tulong :: nil) tvoid
                                                        cc_default))
                                  ((Evar _ref (tarray tuchar 16)) ::
                                   (Evar _key (tarray tuchar 32)) ::
                                   (Etempvar _msg (tptr tuchar)) ::
                                   (Etempvar _n tulong) :: nil))
                                (Ssequence
                                  (Sloop
                                    (Ssequence
                                      (Scall (Some _t'8)
                                        (Evar _bytes_eq (Tfunction
                                                          ((tptr tuchar) ::
                                                           (tptr tuchar) ::
                                                           tulong :: nil)
                                                          tint cc_default))
                                        ((Etempvar _tag (tptr tuchar)) ::
                                         (Evar _ref (tarray tuchar 16)) ::
                                         (Econst_int (Int.repr 16) tint) ::
                                         nil))
                                      (Sifthenelse (Eunop Onotbool
                                                     (Etempvar _t'8 tint)
                                                     tint)
                                        (Scall None
                                          (Evar _check_failed (Tfunction nil
                                                                tvoid
                                                                cc_default))
                                          nil)
                                        Sskip))
                                    Sbreak)
                                  (Ssequence
                                    (Sloop
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'9)
                                            (Evar _bytes_zero (Tfunction
                                                                ((tptr tuchar) ::
                                                                 tulong ::
                                                                 nil) tint
                                                                cc_default))
                                            ((Efield
                                               (Evar _d (Tstruct _poly1305_desc_ctx noattr))
                                               _buf (tarray tuchar 16)) ::
                                             (Econst_int (Int.repr 16) tint) ::
                                             nil))
                                          (Sifthenelse (Etempvar _t'9 tint)
                                            (Ssequence
                                              (Sset _t'19
                                                (Efield
                                                  (Evar _d (Tstruct _poly1305_desc_ctx noattr))
                                                  _buflen tuint))
                                              (Sset _t'10
                                                (Ecast
                                                  (Ebinop Oeq
                                                    (Etempvar _t'19 tuint)
                                                    (Econst_int (Int.repr 0) tint)
                                                    tint) tbool)))
                                            (Sset _t'10
                                              (Econst_int (Int.repr 0) tint))))
                                        (Sifthenelse (Eunop Onotbool
                                                       (Etempvar _t'10 tint)
                                                       tint)
                                          (Scall None
                                            (Evar _check_failed (Tfunction
                                                                  nil tvoid
                                                                  cc_default))
                                            nil)
                                          Sskip))
                                      Sbreak)
                                    (Ssequence
                                      (Ssequence
                                        (Sset _i
                                          (Ecast
                                            (Econst_int (Int.repr 0) tint)
                                            tulong))
                                        (Sloop
                                          (Ssequence
                                            (Sifthenelse (Ebinop Olt
                                                           (Etempvar _i tulong)
                                                           (Econst_int (Int.repr 4) tint)
                                                           tint)
                                              Sskip
                                              Sbreak)
                                            (Sloop
                                              (Ssequence
                                                (Sset _t'18
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Efield
                                                        (Evar _d (Tstruct _poly1305_desc_ctx noattr))
                                                        _s (tarray tuint 4))
                                                      (Etempvar _i tulong)
                                                      (tptr tuint)) tuint))
                                                (Sifthenelse (Eunop Onotbool
                                                               (Ebinop Oeq
                                                                 (Etempvar _t'18 tuint)
                                                                 (Econst_int (Int.repr 0) tint)
                                                                 tint) tint)
                                                  (Scall None
                                                    (Evar _check_failed 
                                                    (Tfunction nil tvoid
                                                      cc_default)) nil)
                                                  Sskip))
                                              Sbreak))
                                          (Sset _i
                                            (Ebinop Oadd (Etempvar _i tulong)
                                              (Econst_int (Int.repr 1) tint)
                                              tulong))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _i
                                            (Ecast
                                              (Econst_int (Int.repr 0) tint)
                                              tulong))
                                          (Sloop
                                            (Ssequence
                                              (Sifthenelse (Ebinop Olt
                                                             (Etempvar _i tulong)
                                                             (Econst_int (Int.repr 5) tint)
                                                             tint)
                                                Sskip
                                                Sbreak)
                                              (Sloop
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'16
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Efield
                                                            (Efield
                                                              (Efield
                                                                (Efield
                                                                  (Evar _d (Tstruct _poly1305_desc_ctx noattr))
                                                                  _state
                                                                  (Tstruct _poly1305_block_state noattr))
                                                                _h
                                                                (Tstruct _poly1305_state noattr))
                                                              18727075383868559167%positive
                                                              (Tunion __anon_43224dacc2cf noattr))
                                                            _h
                                                            (tarray tuint 5))
                                                          (Etempvar _i tulong)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Sifthenelse (Ebinop Oeq
                                                                   (Etempvar _t'16 tuint)
                                                                   (Econst_int (Int.repr 0) tint)
                                                                   tint)
                                                      (Ssequence
                                                        (Sset _t'17
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Efield
                                                                (Efield
                                                                  (Efield
                                                                    (Efield
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _d (Tstruct _poly1305_desc_ctx noattr))
                                                                    _state
                                                                    (Tstruct _poly1305_block_state noattr))
                                                                    18727075383868559167%positive
                                                                    (Tunion __anon_472b2db33f49 noattr))
                                                                    _core_r
                                                                    (Tstruct _poly1305_core_key noattr))
                                                                    _key
                                                                    (Tstruct _poly1305_key noattr))
                                                                  18727075383868559167%positive
                                                                  (Tunion __anon_ef6b4645c220 noattr))
                                                                _r
                                                                (tarray tuint 5))
                                                              (Etempvar _i tulong)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Sset _t'11
                                                          (Ecast
                                                            (Ebinop Oeq
                                                              (Etempvar _t'17 tuint)
                                                              (Econst_int (Int.repr 0) tint)
                                                              tint) tbool)))
                                                      (Sset _t'11
                                                        (Econst_int (Int.repr 0) tint))))
                                                  (Sifthenelse (Eunop Onotbool
                                                                 (Etempvar _t'11 tint)
                                                                 tint)
                                                    (Scall None
                                                      (Evar _check_failed 
                                                      (Tfunction nil tvoid
                                                        cc_default)) nil)
                                                    Sskip))
                                                Sbreak))
                                            (Sset _i
                                              (Ebinop Oadd
                                                (Etempvar _i tulong)
                                                (Econst_int (Int.repr 1) tint)
                                                tulong))))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _i
                                              (Ecast
                                                (Econst_int (Int.repr 0) tint)
                                                tulong))
                                            (Sloop
                                              (Ssequence
                                                (Sifthenelse (Ebinop Olt
                                                               (Etempvar _i tulong)
                                                               (Econst_int (Int.repr 4) tint)
                                                               tint)
                                                  Sskip
                                                  Sbreak)
                                                (Sloop
                                                  (Ssequence
                                                    (Sset _t'15
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Efield
                                                            (Efield
                                                              (Efield
                                                                (Efield
                                                                  (Efield
                                                                    (Efield
                                                                    (Evar _d (Tstruct _poly1305_desc_ctx noattr))
                                                                    _state
                                                                    (Tstruct _poly1305_block_state noattr))
                                                                    18727075383868559167%positive
                                                                    (Tunion __anon_472b2db33f49 noattr))
                                                                  _core_r
                                                                  (Tstruct _poly1305_core_key noattr))
                                                                _precomputed_s
                                                                (Tstruct _poly1305_key noattr))
                                                              18727075383868559167%positive
                                                              (Tunion __anon_ef6b4645c220 noattr))
                                                            _r
                                                            (tarray tuint 5))
                                                          (Etempvar _i tulong)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Sifthenelse (Eunop Onotbool
                                                                   (Ebinop Oeq
                                                                    (Etempvar _t'15 tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                   tint)
                                                      (Scall None
                                                        (Evar _check_failed 
                                                        (Tfunction nil tvoid
                                                          cc_default)) nil)
                                                      Sskip))
                                                  Sbreak))
                                              (Sset _i
                                                (Ebinop Oadd
                                                  (Etempvar _i tulong)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tulong))))
                                          (Ssequence
                                            (Sloop
                                              (Ssequence
                                                (Ssequence
                                                  (Scall (Some _t'12)
                                                    (Evar _bytes_eq (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                    ((Etempvar _msg (tptr tuchar)) ::
                                                     (Etempvar _copy (tptr tuchar)) ::
                                                     (Etempvar _n tulong) ::
                                                     nil))
                                                  (Sifthenelse (Etempvar _t'12 tint)
                                                    (Ssequence
                                                      (Scall (Some _t'14)
                                                        (Evar _bytes_eq 
                                                        (Tfunction
                                                          ((tptr tuchar) ::
                                                           (tptr tuchar) ::
                                                           tulong :: nil)
                                                          tint cc_default))
                                                        ((Evar _key (tarray tuchar 32)) ::
                                                         (Evar _key0 (tarray tuchar 32)) ::
                                                         (Econst_int (Int.repr 32) tint) ::
                                                         nil))
                                                      (Sset _t'13
                                                        (Ecast
                                                          (Etempvar _t'14 tint)
                                                          tbool)))
                                                    (Sset _t'13
                                                      (Econst_int (Int.repr 0) tint))))
                                                (Sifthenelse (Eunop Onotbool
                                                               (Etempvar _t'13 tint)
                                                               tint)
                                                  (Scall None
                                                    (Evar _check_failed 
                                                    (Tfunction nil tvoid
                                                      cc_default)) nil)
                                                  Sskip))
                                              Sbreak)
                                            (Ssequence
                                              (Scall None
                                                (Evar _quickproof_free 
                                                (Tfunction
                                                  ((tptr tvoid) :: nil) tvoid
                                                  cc_default))
                                                ((Etempvar _msg (tptr tuchar)) ::
                                                 nil))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _quickproof_free 
                                                  (Tfunction
                                                    ((tptr tvoid) :: nil)
                                                    tvoid cc_default))
                                                  ((Etempvar _copy (tptr tuchar)) ::
                                                   nil))
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _quickproof_free 
                                                    (Tfunction
                                                      ((tptr tvoid) :: nil)
                                                      tvoid cc_default))
                                                    ((Etempvar _tag (tptr tuchar)) ::
                                                     nil))
                                                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _rpoly Struct
   (Member_plain _r (tarray tuint 17) :: Member_plain _h (tarray tuint 17) ::
    Member_plain _s (tarray tuchar 16) :: nil)
   noattr ::
 Composite __anon_ef6b4645c220 Union
   (Member_plain _r (tarray tuint 5) ::
    Member_plain _r64 (tarray tulong 3) :: nil)
   noattr ::
 Composite _poly1305_key Struct
   (Member_plain 18727075383868559167%positive (Tunion __anon_ef6b4645c220 noattr) :: nil)
   noattr ::
 Composite _poly1305_core_key Struct
   (Member_plain _key (Tstruct _poly1305_key noattr) ::
    Member_plain _precomputed_s (Tstruct _poly1305_key noattr) :: nil)
   noattr ::
 Composite __anon_43224dacc2cf Union
   (Member_plain _h (tarray tuint 5) ::
    Member_plain _h64 (tarray tulong 3) :: nil)
   noattr ::
 Composite _poly1305_state Struct
   (Member_plain 18727075383868559167%positive (Tunion __anon_43224dacc2cf noattr) :: nil)
   noattr ::
 Composite __anon_472b2db33f49 Union
   (Member_plain _opaque_r (tarray (Tstruct _poly1305_key noattr) 1) ::
    Member_plain _core_r (Tstruct _poly1305_core_key noattr) :: nil)
   noattr ::
 Composite _poly1305_block_state Struct
   (Member_plain _h (Tstruct _poly1305_state noattr) ::
    Member_plain 18727075383868559167%positive (Tunion __anon_472b2db33f49 noattr) :: nil)
   noattr ::
 Composite _poly1305_desc_ctx Struct
   (Member_plain _buf (tarray tuchar 16) :: Member_plain _buflen tuint ::
    Member_plain _s (tarray tuint 4) ::
    Member_plain _state (Tstruct _poly1305_block_state noattr) :: nil)
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
 (_nondet_size,
   Gfun(External (EF_external "nondet_size"
                   (mksignature nil AST.Xlong cc_default)) nil tulong
     cc_default)) ::
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
 (_check_failed, Gfun(Internal f_check_failed)) ::
 (_bytes_eq, Gfun(Internal f_bytes_eq)) ::
 (_bytes_zero, Gfun(Internal f_bytes_zero)) ::
 (_bytes_copy, Gfun(Internal f_bytes_copy)) ::
 (_draw_size, Gfun(Internal f_draw_size)) ::
 (_rp_add, Gfun(Internal f_rp_add)) ::
 (_rp_init, Gfun(Internal f_rp_init)) ::
 (_rp_mul, Gfun(Internal f_rp_mul)) ::
 (_rp_block, Gfun(Internal f_rp_block)) :: (_x_prim_poly1305__minusp, Gvar v_x_prim_poly1305__minusp) ::
 (_rp_final, Gfun(Internal f_rp_final)) ::
 (_ref_poly1305, Gfun(Internal f_ref_poly1305)) ::
 (_poly1305_init,
   Gfun(External (EF_external "poly1305_init"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default))
     ((tptr (Tstruct _poly1305_desc_ctx noattr)) :: (tptr tuchar) :: nil)
     tvoid cc_default)) ::
 (_poly1305_update,
   Gfun(External (EF_external "poly1305_update"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr (Tstruct _poly1305_desc_ctx noattr)) :: (tptr tuchar) ::
      tulong :: nil) tvoid cc_default)) ::
 (_poly1305_final,
   Gfun(External (EF_external "poly1305_final"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default))
     ((tptr (Tstruct _poly1305_desc_ctx noattr)) :: (tptr tuchar) :: nil)
     tvoid cc_default)) :: (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _poly1305_final :: _poly1305_update :: _poly1305_init ::
 _quickproof_free :: _quickproof_malloc :: _nondet_bytes :: _nondet_size ::
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


