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
  Definition source_file := "harness/x_prim_blake2s.c".
  Definition normalized := true.
End Info.

Definition _RB2S_IV : ident := $"RB2S_IV".
Definition _RB2S_SIGMA : ident := $"RB2S_SIGMA".
Definition ___blake2s_init : ident := $"__blake2s_init".
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
Definition _blake2s : ident := $"blake2s".
Definition _blake2s_ctx : ident := $"blake2s_ctx".
Definition _blake2s_final : ident := $"blake2s_final".
Definition _blake2s_init : ident := $"blake2s_init".
Definition _blake2s_init_key : ident := $"blake2s_init_key".
Definition _blake2s_update : ident := $"blake2s_update".
Definition _block : ident := $"block".
Definition _buf : ident := $"buf".
Definition _buflen : ident := $"buflen".
Definition _bytes_copy : ident := $"bytes_copy".
Definition _bytes_eq : ident := $"bytes_eq".
Definition _bytes_set : ident := $"bytes_set".
Definition _bytes_zero : ident := $"bytes_zero".
Definition _c : ident := $"c".
Definition _check_failed : ident := $"check_failed".
Definition _copy : ident := $"copy".
Definition _ctx : ident := $"ctx".
Definition _d : ident := $"d".
Definition _done : ident := $"done".
Definition _draw_size : ident := $"draw_size".
Definition _f : ident := $"f".
Definition _h : ident := $"h".
Definition _i : ident := $"i".
Definition _in : ident := $"in".
Definition _inlen : ident := $"inlen".
Definition _key : ident := $"key".
Definition _key_copy : ident := $"key_copy".
Definition _keylen : ident := $"keylen".
Definition _last : ident := $"last".
Definition _le32_load : ident := $"le32_load".
Definition _m : ident := $"m".
Definition _main : ident := $"main".
Definition _memcpy : ident := $"memcpy".
Definition _memset : ident := $"memset".
Definition _msg : ident := $"msg".
Definition _n : ident := $"n".
Definition _nondet_bytes : ident := $"nondet_bytes".
Definition _nondet_size : ident := $"nondet_size".
Definition _nondet_u8 : ident := $"nondet_u8".
Definition _out : ident := $"out".
Definition _out2 : ident := $"out2".
Definition _outlen : ident := $"outlen".
Definition _p : ident := $"p".
Definition _pos : ident := $"pos".
Definition _quickproof_free : ident := $"quickproof_free".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _r : ident := $"r".
Definition _rb2s_compress : ident := $"rb2s_compress".
Definition _rb2s_g : ident := $"rb2s_g".
Definition _rb2s_rotr : ident := $"rb2s_rotr".
Definition _ref : ident := $"ref".
Definition _ref_blake2s : ident := $"ref_blake2s".
Definition _s : ident := $"s".
Definition _t : ident := $"t".
Definition _total : ident := $"total".
Definition _v : ident := $"v".
Definition _x : ident := $"x".
Definition _y : ident := $"y".
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
Definition _t'33 : ident := 160%positive.
Definition _t'34 : ident := 161%positive.
Definition _t'35 : ident := 162%positive.
Definition _t'36 : ident := 163%positive.
Definition _t'37 : ident := 164%positive.
Definition _t'38 : ident := 165%positive.
Definition _t'39 : ident := 166%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'40 : ident := 167%positive.
Definition _t'41 : ident := 168%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition f___blake2s_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _blake2s_ctx noattr))) ::
                (_outlen, tulong) :: (_key, (tptr tvoid)) ::
                (_keylen, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
            (Tstruct _blake2s_ctx noattr)) _h (tarray tuint 8))
        (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
    (Ebinop Oxor (Econst_int (Int.repr 1779033703) tint)
      (Ebinop Oor
        (Ebinop Oor (Econst_int (Int.repr 16842752) tint)
          (Ebinop Oshl (Etempvar _keylen tulong)
            (Econst_int (Int.repr 8) tint) tulong) tulong)
        (Etempvar _outlen tulong) tulong) tulong))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
              (Tstruct _blake2s_ctx noattr)) _h (tarray tuint 8))
          (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint)
      (Econst_int (Int.repr (-1150833019)) tint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                (Tstruct _blake2s_ctx noattr)) _h (tarray tuint 8))
            (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint)
        (Econst_int (Int.repr 1013904242) tint))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                  (Tstruct _blake2s_ctx noattr)) _h (tarray tuint 8))
              (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint)
          (Econst_int (Int.repr (-1521486534)) tint))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                    (Tstruct _blake2s_ctx noattr)) _h (tarray tuint 8))
                (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint)
            (Econst_int (Int.repr 1359893119) tint))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                      (Tstruct _blake2s_ctx noattr)) _h (tarray tuint 8))
                  (Econst_int (Int.repr 5) tint) (tptr tuint)) tuint)
              (Econst_int (Int.repr (-1694144372)) tint))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                        (Tstruct _blake2s_ctx noattr)) _h (tarray tuint 8))
                    (Econst_int (Int.repr 6) tint) (tptr tuint)) tuint)
                (Econst_int (Int.repr 528734635) tint))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                          (Tstruct _blake2s_ctx noattr)) _h (tarray tuint 8))
                      (Econst_int (Int.repr 7) tint) (tptr tuint)) tuint)
                  (Econst_int (Int.repr 1541459225) tint))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                            (Tstruct _blake2s_ctx noattr)) _t
                          (tarray tuint 2)) (Econst_int (Int.repr 0) tint)
                        (tptr tuint)) tuint) (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                              (Tstruct _blake2s_ctx noattr)) _t
                            (tarray tuint 2)) (Econst_int (Int.repr 1) tint)
                          (tptr tuint)) tuint)
                      (Econst_int (Int.repr 0) tint))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                                (Tstruct _blake2s_ctx noattr)) _f
                              (tarray tuint 2))
                            (Econst_int (Int.repr 0) tint) (tptr tuint))
                          tuint) (Econst_int (Int.repr 0) tint))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                                  (Tstruct _blake2s_ctx noattr)) _f
                                (tarray tuint 2))
                              (Econst_int (Int.repr 1) tint) (tptr tuint))
                            tuint) (Econst_int (Int.repr 0) tint))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                                (Tstruct _blake2s_ctx noattr)) _buflen tuint)
                            (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                                  (Tstruct _blake2s_ctx noattr)) _outlen
                                tuint) (Etempvar _outlen tulong))
                            (Sifthenelse (Etempvar _keylen tulong)
                              (Ssequence
                                (Scall None
                                  (Evar _memcpy (Tfunction
                                                  ((tptr tvoid) ::
                                                   (tptr tvoid) :: tulong ::
                                                   nil) (tptr tvoid)
                                                  cc_default))
                                  ((Efield
                                     (Ederef
                                       (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                                       (Tstruct _blake2s_ctx noattr)) _buf
                                     (tarray tuchar 64)) ::
                                   (Etempvar _key (tptr tvoid)) ::
                                   (Etempvar _keylen tulong) :: nil))
                                (Ssequence
                                  (Scall None
                                    (Evar _memset (Tfunction
                                                    ((tptr tvoid) :: tint ::
                                                     tulong :: nil)
                                                    (tptr tvoid) cc_default))
                                    ((Ebinop Oadd
                                       (Efield
                                         (Ederef
                                           (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                                           (Tstruct _blake2s_ctx noattr))
                                         _buf (tarray tuchar 64))
                                       (Etempvar _keylen tulong)
                                       (tptr tuchar)) ::
                                     (Econst_int (Int.repr 0) tint) ::
                                     (Ebinop Osub
                                       (Econst_int (Int.repr 64) tint)
                                       (Etempvar _keylen tulong) tulong) ::
                                     nil))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                                        (Tstruct _blake2s_ctx noattr))
                                      _buflen tuint)
                                    (Econst_int (Int.repr 64) tint))))
                              Sskip)))))))))))))))
|}.

Definition f_blake2s_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _blake2s_ctx noattr))) ::
                (_outlen, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar ___blake2s_init (Tfunction
                          ((tptr (Tstruct _blake2s_ctx noattr)) :: tulong ::
                           (tptr tvoid) :: tulong :: nil) tvoid cc_default))
  ((Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr))) ::
   (Etempvar _outlen tulong) ::
   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
   (Econst_int (Int.repr 0) tint) :: nil))
|}.

Definition f_blake2s_init_key := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _blake2s_ctx noattr))) ::
                (_outlen, tulong) :: (_key, (tptr tvoid)) ::
                (_keylen, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1 (Econst_int (Int.repr 0) tint))
  (Scall None
    (Evar ___blake2s_init (Tfunction
                            ((tptr (Tstruct _blake2s_ctx noattr)) ::
                             tulong :: (tptr tvoid) :: tulong :: nil) tvoid
                            cc_default))
    ((Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr))) ::
     (Etempvar _outlen tulong) :: (Etempvar _key (tptr tvoid)) ::
     (Etempvar _keylen tulong) :: nil)))
|}.

Definition f_blake2s := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr tuchar)) :: (_keylen, tulong) ::
                (_in, (tptr tuchar)) :: (_inlen, tulong) ::
                (_out, (tptr tuchar)) :: (_outlen, tulong) :: nil);
  fn_vars := ((_ctx, (Tstruct _blake2s_ctx noattr)) :: nil);
  fn_temps := ((_t'6, tint) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1 (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Scall None
      (Evar ___blake2s_init (Tfunction
                              ((tptr (Tstruct _blake2s_ctx noattr)) ::
                               tulong :: (tptr tvoid) :: tulong :: nil) tvoid
                              cc_default))
      ((Eaddrof (Evar _ctx (Tstruct _blake2s_ctx noattr))
         (tptr (Tstruct _blake2s_ctx noattr))) ::
       (Etempvar _outlen tulong) :: (Etempvar _key (tptr tuchar)) ::
       (Etempvar _keylen tulong) :: nil))
    (Ssequence
      (Scall None
        (Evar _blake2s_update (Tfunction
                                ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                 (tptr tuchar) :: tulong :: nil) tvoid
                                cc_default))
        ((Eaddrof (Evar _ctx (Tstruct _blake2s_ctx noattr))
           (tptr (Tstruct _blake2s_ctx noattr))) ::
         (Etempvar _in (tptr tuchar)) :: (Etempvar _inlen tulong) :: nil))
      (Scall None
        (Evar _blake2s_final (Tfunction
                               ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                (tptr tuchar) :: nil) tvoid cc_default))
        ((Eaddrof (Evar _ctx (Tstruct _blake2s_ctx noattr))
           (tptr (Tstruct _blake2s_ctx noattr))) ::
         (Etempvar _out (tptr tuchar)) :: nil)))))
|}.

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

Definition f_bytes_set := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_d, (tptr tuchar)) :: (_v, tuchar) :: (_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tulong) (Etempvar _n tulong)
                     tint)
        Sskip
        Sbreak)
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _d (tptr tuchar)) (Etempvar _i tulong)
            (tptr tuchar)) tuchar) (Etempvar _v tuchar)))
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

Definition f_le32_load := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'4, tuchar) :: (_t'3, tuchar) :: (_t'2, tuchar) ::
               (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Ederef
      (Ebinop Oadd (Etempvar _p (tptr tuchar)) (Econst_int (Int.repr 0) tint)
        (tptr tuchar)) tuchar))
  (Ssequence
    (Sset _t'2
      (Ederef
        (Ebinop Oadd (Etempvar _p (tptr tuchar))
          (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar))
    (Ssequence
      (Sset _t'3
        (Ederef
          (Ebinop Oadd (Etempvar _p (tptr tuchar))
            (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar))
      (Ssequence
        (Sset _t'4
          (Ederef
            (Ebinop Oadd (Etempvar _p (tptr tuchar))
              (Econst_int (Int.repr 3) tint) (tptr tuchar)) tuchar))
        (Sreturn (Some (Ebinop Oor
                         (Ebinop Oor
                           (Ebinop Oor (Ecast (Etempvar _t'1 tuchar) tuint)
                             (Ebinop Oshl
                               (Ecast (Etempvar _t'2 tuchar) tuint)
                               (Econst_int (Int.repr 8) tint) tuint) tuint)
                           (Ebinop Oshl (Ecast (Etempvar _t'3 tuchar) tuint)
                             (Econst_int (Int.repr 16) tint) tuint) tuint)
                         (Ebinop Oshl (Ecast (Etempvar _t'4 tuchar) tuint)
                           (Econst_int (Int.repr 24) tint) tuint) tuint)))))))
|}.

Definition v_RB2S_IV := {|
  gvar_info := (tarray tuint 8);
  gvar_init := (Init_int32 (Int.repr 1779033703) ::
                Init_int32 (Int.repr (-1150833019)) ::
                Init_int32 (Int.repr 1013904242) ::
                Init_int32 (Int.repr (-1521486534)) ::
                Init_int32 (Int.repr 1359893119) ::
                Init_int32 (Int.repr (-1694144372)) ::
                Init_int32 (Int.repr 528734635) ::
                Init_int32 (Int.repr 1541459225) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_RB2S_SIGMA := {|
  gvar_info := (tarray (tarray tuchar 16) 10);
  gvar_init := (Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 2) :: Init_int8 (Int.repr 3) ::
                Init_int8 (Int.repr 4) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 9) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 11) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 4) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 9) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 1) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 2) ::
                Init_int8 (Int.repr 11) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 5) :: Init_int8 (Int.repr 3) ::
                Init_int8 (Int.repr 11) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 5) :: Init_int8 (Int.repr 2) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 3) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 9) :: Init_int8 (Int.repr 4) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 9) ::
                Init_int8 (Int.repr 3) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 11) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 2) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 5) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 4) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 9) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 5) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 2) :: Init_int8 (Int.repr 4) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 11) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 3) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 2) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 11) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 3) ::
                Init_int8 (Int.repr 4) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 1) :: Init_int8 (Int.repr 9) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 1) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 4) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 3) ::
                Init_int8 (Int.repr 9) :: Init_int8 (Int.repr 2) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 11) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 11) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 3) :: Init_int8 (Int.repr 9) ::
                Init_int8 (Int.repr 5) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 4) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 2) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 9) ::
                Init_int8 (Int.repr 11) :: Init_int8 (Int.repr 3) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 2) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 1) :: Init_int8 (Int.repr 4) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 2) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 4) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 1) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 11) ::
                Init_int8 (Int.repr 9) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 3) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_rb2s_rotr := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_x, tuint) :: (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oor
                 (Ebinop Oshr (Etempvar _x tuint) (Etempvar _n tuint) tuint)
                 (Ebinop Oshl (Etempvar _x tuint)
                   (Ebinop Osub (Econst_int (Int.repr 32) tint)
                     (Etempvar _n tuint) tuint) tuint) tuint)))
|}.

Definition f_rb2s_g := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr tuint)) :: (_a, tint) :: (_b, tint) ::
                (_c, tint) :: (_d, tint) :: (_x, tuint) :: (_y, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'4, tuint) :: (_t'3, tuint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: (_t'20, tuint) :: (_t'19, tuint) ::
               (_t'18, tuint) :: (_t'17, tuint) :: (_t'16, tuint) ::
               (_t'15, tuint) :: (_t'14, tuint) :: (_t'13, tuint) ::
               (_t'12, tuint) :: (_t'11, tuint) :: (_t'10, tuint) ::
               (_t'9, tuint) :: (_t'8, tuint) :: (_t'7, tuint) ::
               (_t'6, tuint) :: (_t'5, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'19
      (Ederef
        (Ebinop Oadd (Etempvar _v (tptr tuint)) (Etempvar _a tint)
          (tptr tuint)) tuint))
    (Ssequence
      (Sset _t'20
        (Ederef
          (Ebinop Oadd (Etempvar _v (tptr tuint)) (Etempvar _b tint)
            (tptr tuint)) tuint))
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _v (tptr tuint)) (Etempvar _a tint)
            (tptr tuint)) tuint)
        (Ebinop Oadd
          (Ebinop Oadd (Etempvar _t'19 tuint) (Etempvar _t'20 tuint) tuint)
          (Etempvar _x tuint) tuint))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'17
          (Ederef
            (Ebinop Oadd (Etempvar _v (tptr tuint)) (Etempvar _d tint)
              (tptr tuint)) tuint))
        (Ssequence
          (Sset _t'18
            (Ederef
              (Ebinop Oadd (Etempvar _v (tptr tuint)) (Etempvar _a tint)
                (tptr tuint)) tuint))
          (Scall (Some _t'1)
            (Evar _rb2s_rotr (Tfunction (tuint :: tuint :: nil) tuint
                               cc_default))
            ((Ebinop Oxor (Etempvar _t'17 tuint) (Etempvar _t'18 tuint)
               tuint) :: (Econst_int (Int.repr 16) tint) :: nil))))
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _v (tptr tuint)) (Etempvar _d tint)
            (tptr tuint)) tuint) (Etempvar _t'1 tuint)))
    (Ssequence
      (Ssequence
        (Sset _t'15
          (Ederef
            (Ebinop Oadd (Etempvar _v (tptr tuint)) (Etempvar _c tint)
              (tptr tuint)) tuint))
        (Ssequence
          (Sset _t'16
            (Ederef
              (Ebinop Oadd (Etempvar _v (tptr tuint)) (Etempvar _d tint)
                (tptr tuint)) tuint))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _v (tptr tuint)) (Etempvar _c tint)
                (tptr tuint)) tuint)
            (Ebinop Oadd (Etempvar _t'15 tuint) (Etempvar _t'16 tuint) tuint))))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'13
              (Ederef
                (Ebinop Oadd (Etempvar _v (tptr tuint)) (Etempvar _b tint)
                  (tptr tuint)) tuint))
            (Ssequence
              (Sset _t'14
                (Ederef
                  (Ebinop Oadd (Etempvar _v (tptr tuint)) (Etempvar _c tint)
                    (tptr tuint)) tuint))
              (Scall (Some _t'2)
                (Evar _rb2s_rotr (Tfunction (tuint :: tuint :: nil) tuint
                                   cc_default))
                ((Ebinop Oxor (Etempvar _t'13 tuint) (Etempvar _t'14 tuint)
                   tuint) :: (Econst_int (Int.repr 12) tint) :: nil))))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _v (tptr tuint)) (Etempvar _b tint)
                (tptr tuint)) tuint) (Etempvar _t'2 tuint)))
        (Ssequence
          (Ssequence
            (Sset _t'11
              (Ederef
                (Ebinop Oadd (Etempvar _v (tptr tuint)) (Etempvar _a tint)
                  (tptr tuint)) tuint))
            (Ssequence
              (Sset _t'12
                (Ederef
                  (Ebinop Oadd (Etempvar _v (tptr tuint)) (Etempvar _b tint)
                    (tptr tuint)) tuint))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _v (tptr tuint)) (Etempvar _a tint)
                    (tptr tuint)) tuint)
                (Ebinop Oadd
                  (Ebinop Oadd (Etempvar _t'11 tuint) (Etempvar _t'12 tuint)
                    tuint) (Etempvar _y tuint) tuint))))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'9
                  (Ederef
                    (Ebinop Oadd (Etempvar _v (tptr tuint))
                      (Etempvar _d tint) (tptr tuint)) tuint))
                (Ssequence
                  (Sset _t'10
                    (Ederef
                      (Ebinop Oadd (Etempvar _v (tptr tuint))
                        (Etempvar _a tint) (tptr tuint)) tuint))
                  (Scall (Some _t'3)
                    (Evar _rb2s_rotr (Tfunction (tuint :: tuint :: nil) tuint
                                       cc_default))
                    ((Ebinop Oxor (Etempvar _t'9 tuint)
                       (Etempvar _t'10 tuint) tuint) ::
                     (Econst_int (Int.repr 8) tint) :: nil))))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _v (tptr tuint)) (Etempvar _d tint)
                    (tptr tuint)) tuint) (Etempvar _t'3 tuint)))
            (Ssequence
              (Ssequence
                (Sset _t'7
                  (Ederef
                    (Ebinop Oadd (Etempvar _v (tptr tuint))
                      (Etempvar _c tint) (tptr tuint)) tuint))
                (Ssequence
                  (Sset _t'8
                    (Ederef
                      (Ebinop Oadd (Etempvar _v (tptr tuint))
                        (Etempvar _d tint) (tptr tuint)) tuint))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _v (tptr tuint))
                        (Etempvar _c tint) (tptr tuint)) tuint)
                    (Ebinop Oadd (Etempvar _t'7 tuint) (Etempvar _t'8 tuint)
                      tuint))))
              (Ssequence
                (Ssequence
                  (Sset _t'5
                    (Ederef
                      (Ebinop Oadd (Etempvar _v (tptr tuint))
                        (Etempvar _b tint) (tptr tuint)) tuint))
                  (Ssequence
                    (Sset _t'6
                      (Ederef
                        (Ebinop Oadd (Etempvar _v (tptr tuint))
                          (Etempvar _c tint) (tptr tuint)) tuint))
                    (Scall (Some _t'4)
                      (Evar _rb2s_rotr (Tfunction (tuint :: tuint :: nil)
                                         tuint cc_default))
                      ((Ebinop Oxor (Etempvar _t'5 tuint)
                         (Etempvar _t'6 tuint) tuint) ::
                       (Econst_int (Int.repr 7) tint) :: nil))))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _v (tptr tuint))
                      (Etempvar _b tint) (tptr tuint)) tuint)
                  (Etempvar _t'4 tuint))))))))))
|}.

Definition f_rb2s_compress := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr tuint)) :: (_block, (tptr tuchar)) ::
                (_t, tulong) :: (_last, tint) :: nil);
  fn_vars := ((_m, (tarray tuint 16)) :: (_v, (tarray tuint 16)) :: nil);
  fn_temps := ((_i, tint) :: (_r, tint) :: (_s, (tptr tuchar)) ::
               (_t'1, tuint) :: (_t'41, tuint) :: (_t'40, tuint) ::
               (_t'39, tuint) :: (_t'38, tuint) :: (_t'37, tuint) ::
               (_t'36, tuint) :: (_t'35, tuchar) :: (_t'34, tuint) ::
               (_t'33, tuchar) :: (_t'32, tuint) :: (_t'31, tuchar) ::
               (_t'30, tuint) :: (_t'29, tuchar) :: (_t'28, tuint) ::
               (_t'27, tuchar) :: (_t'26, tuint) :: (_t'25, tuchar) ::
               (_t'24, tuint) :: (_t'23, tuchar) :: (_t'22, tuint) ::
               (_t'21, tuchar) :: (_t'20, tuint) :: (_t'19, tuchar) ::
               (_t'18, tuint) :: (_t'17, tuchar) :: (_t'16, tuint) ::
               (_t'15, tuchar) :: (_t'14, tuint) :: (_t'13, tuchar) ::
               (_t'12, tuint) :: (_t'11, tuchar) :: (_t'10, tuint) ::
               (_t'9, tuchar) :: (_t'8, tuint) :: (_t'7, tuchar) ::
               (_t'6, tuint) :: (_t'5, tuchar) :: (_t'4, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: nil);
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
          (Scall (Some _t'1)
            (Evar _le32_load (Tfunction ((tptr tuchar) :: nil) tuint
                               cc_default))
            ((Ebinop Oadd (Etempvar _block (tptr tuchar))
               (Ebinop Omul (Econst_int (Int.repr 4) tint) (Etempvar _i tint)
                 tint) (tptr tuchar)) :: nil))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _m (tarray tuint 16)) (Etempvar _i tint)
                (tptr tuint)) tuint) (Etempvar _t'1 tuint))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                         (Econst_int (Int.repr 8) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Ssequence
              (Sset _t'41
                (Ederef
                  (Ebinop Oadd (Etempvar _h (tptr tuint)) (Etempvar _i tint)
                    (tptr tuint)) tuint))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _v (tarray tuint 16)) (Etempvar _i tint)
                    (tptr tuint)) tuint) (Etempvar _t'41 tuint)))
            (Ssequence
              (Sset _t'40
                (Ederef
                  (Ebinop Oadd (Evar _RB2S_IV (tarray tuint 8))
                    (Etempvar _i tint) (tptr tuint)) tuint))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _v (tarray tuint 16))
                    (Ebinop Oadd (Etempvar _i tint)
                      (Econst_int (Int.repr 8) tint) tint) (tptr tuint))
                  tuint) (Etempvar _t'40 tuint)))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Ssequence
        (Sset _t'39
          (Ederef
            (Ebinop Oadd (Evar _v (tarray tuint 16))
              (Econst_int (Int.repr 12) tint) (tptr tuint)) tuint))
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _v (tarray tuint 16))
              (Econst_int (Int.repr 12) tint) (tptr tuint)) tuint)
          (Ebinop Oxor (Etempvar _t'39 tuint)
            (Ecast (Etempvar _t tulong) tuint) tuint)))
      (Ssequence
        (Ssequence
          (Sset _t'38
            (Ederef
              (Ebinop Oadd (Evar _v (tarray tuint 16))
                (Econst_int (Int.repr 13) tint) (tptr tuint)) tuint))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _v (tarray tuint 16))
                (Econst_int (Int.repr 13) tint) (tptr tuint)) tuint)
            (Ebinop Oxor (Etempvar _t'38 tuint)
              (Ecast
                (Ebinop Oshr (Etempvar _t tulong)
                  (Econst_int (Int.repr 32) tint) tulong) tuint) tuint)))
        (Ssequence
          (Sifthenelse (Etempvar _last tint)
            (Ssequence
              (Sset _t'37
                (Ederef
                  (Ebinop Oadd (Evar _v (tarray tuint 16))
                    (Econst_int (Int.repr 14) tint) (tptr tuint)) tuint))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _v (tarray tuint 16))
                    (Econst_int (Int.repr 14) tint) (tptr tuint)) tuint)
                (Eunop Onotint (Etempvar _t'37 tuint) tuint)))
            Sskip)
          (Ssequence
            (Ssequence
              (Sset _r (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _r tint)
                                 (Econst_int (Int.repr 10) tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _s
                      (Ederef
                        (Ebinop Oadd
                          (Evar _RB2S_SIGMA (tarray (tarray tuchar 16) 10))
                          (Etempvar _r tint) (tptr (tarray tuchar 16)))
                        (tarray tuchar 16)))
                    (Ssequence
                      (Ssequence
                        (Sset _t'33
                          (Ederef
                            (Ebinop Oadd (Etempvar _s (tptr tuchar))
                              (Econst_int (Int.repr 0) tint) (tptr tuchar))
                            tuchar))
                        (Ssequence
                          (Sset _t'34
                            (Ederef
                              (Ebinop Oadd (Evar _m (tarray tuint 16))
                                (Etempvar _t'33 tuchar) (tptr tuint)) tuint))
                          (Ssequence
                            (Sset _t'35
                              (Ederef
                                (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                  (Econst_int (Int.repr 1) tint)
                                  (tptr tuchar)) tuchar))
                            (Ssequence
                              (Sset _t'36
                                (Ederef
                                  (Ebinop Oadd (Evar _m (tarray tuint 16))
                                    (Etempvar _t'35 tuchar) (tptr tuint))
                                  tuint))
                              (Scall None
                                (Evar _rb2s_g (Tfunction
                                                ((tptr tuint) :: tint ::
                                                 tint :: tint :: tint ::
                                                 tuint :: tuint :: nil) tvoid
                                                cc_default))
                                ((Evar _v (tarray tuint 16)) ::
                                 (Econst_int (Int.repr 0) tint) ::
                                 (Econst_int (Int.repr 4) tint) ::
                                 (Econst_int (Int.repr 8) tint) ::
                                 (Econst_int (Int.repr 12) tint) ::
                                 (Etempvar _t'34 tuint) ::
                                 (Etempvar _t'36 tuint) :: nil))))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'29
                            (Ederef
                              (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                (Econst_int (Int.repr 2) tint) (tptr tuchar))
                              tuchar))
                          (Ssequence
                            (Sset _t'30
                              (Ederef
                                (Ebinop Oadd (Evar _m (tarray tuint 16))
                                  (Etempvar _t'29 tuchar) (tptr tuint))
                                tuint))
                            (Ssequence
                              (Sset _t'31
                                (Ederef
                                  (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                    (Econst_int (Int.repr 3) tint)
                                    (tptr tuchar)) tuchar))
                              (Ssequence
                                (Sset _t'32
                                  (Ederef
                                    (Ebinop Oadd (Evar _m (tarray tuint 16))
                                      (Etempvar _t'31 tuchar) (tptr tuint))
                                    tuint))
                                (Scall None
                                  (Evar _rb2s_g (Tfunction
                                                  ((tptr tuint) :: tint ::
                                                   tint :: tint :: tint ::
                                                   tuint :: tuint :: nil)
                                                  tvoid cc_default))
                                  ((Evar _v (tarray tuint 16)) ::
                                   (Econst_int (Int.repr 1) tint) ::
                                   (Econst_int (Int.repr 5) tint) ::
                                   (Econst_int (Int.repr 9) tint) ::
                                   (Econst_int (Int.repr 13) tint) ::
                                   (Etempvar _t'30 tuint) ::
                                   (Etempvar _t'32 tuint) :: nil))))))
                        (Ssequence
                          (Ssequence
                            (Sset _t'25
                              (Ederef
                                (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                  (Econst_int (Int.repr 4) tint)
                                  (tptr tuchar)) tuchar))
                            (Ssequence
                              (Sset _t'26
                                (Ederef
                                  (Ebinop Oadd (Evar _m (tarray tuint 16))
                                    (Etempvar _t'25 tuchar) (tptr tuint))
                                  tuint))
                              (Ssequence
                                (Sset _t'27
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                      (Econst_int (Int.repr 5) tint)
                                      (tptr tuchar)) tuchar))
                                (Ssequence
                                  (Sset _t'28
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _m (tarray tuint 16))
                                        (Etempvar _t'27 tuchar) (tptr tuint))
                                      tuint))
                                  (Scall None
                                    (Evar _rb2s_g (Tfunction
                                                    ((tptr tuint) :: tint ::
                                                     tint :: tint :: tint ::
                                                     tuint :: tuint :: nil)
                                                    tvoid cc_default))
                                    ((Evar _v (tarray tuint 16)) ::
                                     (Econst_int (Int.repr 2) tint) ::
                                     (Econst_int (Int.repr 6) tint) ::
                                     (Econst_int (Int.repr 10) tint) ::
                                     (Econst_int (Int.repr 14) tint) ::
                                     (Etempvar _t'26 tuint) ::
                                     (Etempvar _t'28 tuint) :: nil))))))
                          (Ssequence
                            (Ssequence
                              (Sset _t'21
                                (Ederef
                                  (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                    (Econst_int (Int.repr 6) tint)
                                    (tptr tuchar)) tuchar))
                              (Ssequence
                                (Sset _t'22
                                  (Ederef
                                    (Ebinop Oadd (Evar _m (tarray tuint 16))
                                      (Etempvar _t'21 tuchar) (tptr tuint))
                                    tuint))
                                (Ssequence
                                  (Sset _t'23
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _s (tptr tuchar))
                                        (Econst_int (Int.repr 7) tint)
                                        (tptr tuchar)) tuchar))
                                  (Ssequence
                                    (Sset _t'24
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _m (tarray tuint 16))
                                          (Etempvar _t'23 tuchar)
                                          (tptr tuint)) tuint))
                                    (Scall None
                                      (Evar _rb2s_g (Tfunction
                                                      ((tptr tuint) ::
                                                       tint :: tint ::
                                                       tint :: tint ::
                                                       tuint :: tuint :: nil)
                                                      tvoid cc_default))
                                      ((Evar _v (tarray tuint 16)) ::
                                       (Econst_int (Int.repr 3) tint) ::
                                       (Econst_int (Int.repr 7) tint) ::
                                       (Econst_int (Int.repr 11) tint) ::
                                       (Econst_int (Int.repr 15) tint) ::
                                       (Etempvar _t'22 tuint) ::
                                       (Etempvar _t'24 tuint) :: nil))))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'17
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                      (Econst_int (Int.repr 8) tint)
                                      (tptr tuchar)) tuchar))
                                (Ssequence
                                  (Sset _t'18
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _m (tarray tuint 16))
                                        (Etempvar _t'17 tuchar) (tptr tuint))
                                      tuint))
                                  (Ssequence
                                    (Sset _t'19
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _s (tptr tuchar))
                                          (Econst_int (Int.repr 9) tint)
                                          (tptr tuchar)) tuchar))
                                    (Ssequence
                                      (Sset _t'20
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _m (tarray tuint 16))
                                            (Etempvar _t'19 tuchar)
                                            (tptr tuint)) tuint))
                                      (Scall None
                                        (Evar _rb2s_g (Tfunction
                                                        ((tptr tuint) ::
                                                         tint :: tint ::
                                                         tint :: tint ::
                                                         tuint :: tuint ::
                                                         nil) tvoid
                                                        cc_default))
                                        ((Evar _v (tarray tuint 16)) ::
                                         (Econst_int (Int.repr 0) tint) ::
                                         (Econst_int (Int.repr 5) tint) ::
                                         (Econst_int (Int.repr 10) tint) ::
                                         (Econst_int (Int.repr 15) tint) ::
                                         (Etempvar _t'18 tuint) ::
                                         (Etempvar _t'20 tuint) :: nil))))))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'13
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _s (tptr tuchar))
                                        (Econst_int (Int.repr 10) tint)
                                        (tptr tuchar)) tuchar))
                                  (Ssequence
                                    (Sset _t'14
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _m (tarray tuint 16))
                                          (Etempvar _t'13 tuchar)
                                          (tptr tuint)) tuint))
                                    (Ssequence
                                      (Sset _t'15
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _s (tptr tuchar))
                                            (Econst_int (Int.repr 11) tint)
                                            (tptr tuchar)) tuchar))
                                      (Ssequence
                                        (Sset _t'16
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _m (tarray tuint 16))
                                              (Etempvar _t'15 tuchar)
                                              (tptr tuint)) tuint))
                                        (Scall None
                                          (Evar _rb2s_g (Tfunction
                                                          ((tptr tuint) ::
                                                           tint :: tint ::
                                                           tint :: tint ::
                                                           tuint :: tuint ::
                                                           nil) tvoid
                                                          cc_default))
                                          ((Evar _v (tarray tuint 16)) ::
                                           (Econst_int (Int.repr 1) tint) ::
                                           (Econst_int (Int.repr 6) tint) ::
                                           (Econst_int (Int.repr 11) tint) ::
                                           (Econst_int (Int.repr 12) tint) ::
                                           (Etempvar _t'14 tuint) ::
                                           (Etempvar _t'16 tuint) :: nil))))))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'9
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _s (tptr tuchar))
                                          (Econst_int (Int.repr 12) tint)
                                          (tptr tuchar)) tuchar))
                                    (Ssequence
                                      (Sset _t'10
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _m (tarray tuint 16))
                                            (Etempvar _t'9 tuchar)
                                            (tptr tuint)) tuint))
                                      (Ssequence
                                        (Sset _t'11
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _s (tptr tuchar))
                                              (Econst_int (Int.repr 13) tint)
                                              (tptr tuchar)) tuchar))
                                        (Ssequence
                                          (Sset _t'12
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _m (tarray tuint 16))
                                                (Etempvar _t'11 tuchar)
                                                (tptr tuint)) tuint))
                                          (Scall None
                                            (Evar _rb2s_g (Tfunction
                                                            ((tptr tuint) ::
                                                             tint :: tint ::
                                                             tint :: tint ::
                                                             tuint ::
                                                             tuint :: nil)
                                                            tvoid cc_default))
                                            ((Evar _v (tarray tuint 16)) ::
                                             (Econst_int (Int.repr 2) tint) ::
                                             (Econst_int (Int.repr 7) tint) ::
                                             (Econst_int (Int.repr 8) tint) ::
                                             (Econst_int (Int.repr 13) tint) ::
                                             (Etempvar _t'10 tuint) ::
                                             (Etempvar _t'12 tuint) :: nil))))))
                                  (Ssequence
                                    (Sset _t'5
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _s (tptr tuchar))
                                          (Econst_int (Int.repr 14) tint)
                                          (tptr tuchar)) tuchar))
                                    (Ssequence
                                      (Sset _t'6
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _m (tarray tuint 16))
                                            (Etempvar _t'5 tuchar)
                                            (tptr tuint)) tuint))
                                      (Ssequence
                                        (Sset _t'7
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _s (tptr tuchar))
                                              (Econst_int (Int.repr 15) tint)
                                              (tptr tuchar)) tuchar))
                                        (Ssequence
                                          (Sset _t'8
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _m (tarray tuint 16))
                                                (Etempvar _t'7 tuchar)
                                                (tptr tuint)) tuint))
                                          (Scall None
                                            (Evar _rb2s_g (Tfunction
                                                            ((tptr tuint) ::
                                                             tint :: tint ::
                                                             tint :: tint ::
                                                             tuint ::
                                                             tuint :: nil)
                                                            tvoid cc_default))
                                            ((Evar _v (tarray tuint 16)) ::
                                             (Econst_int (Int.repr 3) tint) ::
                                             (Econst_int (Int.repr 4) tint) ::
                                             (Econst_int (Int.repr 9) tint) ::
                                             (Econst_int (Int.repr 14) tint) ::
                                             (Etempvar _t'6 tuint) ::
                                             (Etempvar _t'8 tuint) :: nil)))))))))))))))
                (Sset _r
                  (Ebinop Oadd (Etempvar _r tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Econst_int (Int.repr 8) tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _t'2
                      (Ederef
                        (Ebinop Oadd (Etempvar _h (tptr tuint))
                          (Etempvar _i tint) (tptr tuint)) tuint))
                    (Ssequence
                      (Sset _t'3
                        (Ederef
                          (Ebinop Oadd (Evar _v (tarray tuint 16))
                            (Etempvar _i tint) (tptr tuint)) tuint))
                      (Ssequence
                        (Sset _t'4
                          (Ederef
                            (Ebinop Oadd (Evar _v (tarray tuint 16))
                              (Ebinop Oadd (Etempvar _i tint)
                                (Econst_int (Int.repr 8) tint) tint)
                              (tptr tuint)) tuint))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _h (tptr tuint))
                              (Etempvar _i tint) (tptr tuint)) tuint)
                          (Ebinop Oxor (Etempvar _t'2 tuint)
                            (Ebinop Oxor (Etempvar _t'3 tuint)
                              (Etempvar _t'4 tuint) tuint) tuint))))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))))))))
|}.

Definition f_ref_blake2s := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) :: (_outlen, tulong) ::
                (_key, (tptr tuchar)) :: (_keylen, tulong) ::
                (_in, (tptr tuchar)) :: (_inlen, tulong) :: nil);
  fn_vars := ((_h, (tarray tuint 8)) :: (_block, (tarray tuchar 64)) :: nil);
  fn_temps := ((_total, tulong) :: (_done, tulong) :: (_pos, tulong) ::
               (_i, tint) :: (_t'2, tint) :: (_t'1, tint) :: (_t'5, tuint) ::
               (_t'4, tuint) :: (_t'3, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sifthenelse (Ebinop Ogt (Etempvar _keylen tulong)
                   (Econst_int (Int.repr 0) tint) tint)
      (Sset _t'1 (Ecast (Econst_int (Int.repr 64) tint) tint))
      (Sset _t'1 (Ecast (Econst_int (Int.repr 0) tint) tint)))
    (Sset _total
      (Ebinop Oadd (Etempvar _t'1 tint)
        (Ecast (Etempvar _inlen tulong) tulong) tulong)))
  (Ssequence
    (Sset _done (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Ssequence
      (Sset _pos (Ecast (Econst_int (Int.repr 0) tint) tulong))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Econst_int (Int.repr 8) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _t'5
                  (Ederef
                    (Ebinop Oadd (Evar _RB2S_IV (tarray tuint 8))
                      (Etempvar _i tint) (tptr tuint)) tuint))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _h (tarray tuint 8))
                      (Etempvar _i tint) (tptr tuint)) tuint)
                  (Etempvar _t'5 tuint))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Ederef
                (Ebinop Oadd (Evar _h (tarray tuint 8))
                  (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _h (tarray tuint 8))
                  (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
              (Ebinop Oxor (Etempvar _t'4 tuint)
                (Ebinop Oxor
                  (Ebinop Oxor (Econst_int (Int.repr 16842752) tuint)
                    (Ebinop Oshl (Ecast (Etempvar _keylen tulong) tuint)
                      (Econst_int (Int.repr 8) tint) tuint) tuint)
                  (Ecast (Etempvar _outlen tulong) tuint) tuint) tuint)))
          (Ssequence
            (Sifthenelse (Ebinop Ogt (Etempvar _keylen tulong)
                           (Econst_int (Int.repr 0) tint) tint)
              (Ssequence
                (Scall None
                  (Evar _bytes_set (Tfunction
                                     ((tptr tuchar) :: tuchar :: tulong ::
                                      nil) tvoid cc_default))
                  ((Evar _block (tarray tuchar 64)) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 64) tint) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _bytes_copy (Tfunction
                                        ((tptr tuchar) :: (tptr tuchar) ::
                                         tulong :: nil) tvoid cc_default))
                    ((Evar _block (tarray tuchar 64)) ::
                     (Etempvar _key (tptr tuchar)) ::
                     (Etempvar _keylen tulong) :: nil))
                  (Ssequence
                    (Sset _done
                      (Ecast (Econst_int (Int.repr 64) tint) tulong))
                    (Scall None
                      (Evar _rb2s_compress (Tfunction
                                             ((tptr tuint) ::
                                              (tptr tuchar) :: tulong ::
                                              tint :: nil) tvoid cc_default))
                      ((Evar _h (tarray tuint 8)) ::
                       (Evar _block (tarray tuchar 64)) ::
                       (Etempvar _done tulong) ::
                       (Ebinop Oeq (Etempvar _inlen tulong)
                         (Econst_int (Int.repr 0) tint) tint) :: nil)))))
              Sskip)
            (Ssequence
              (Ssequence
                (Sifthenelse (Ebinop Oeq (Etempvar _keylen tulong)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Sset _t'2 (Econst_int (Int.repr 1) tint))
                  (Sset _t'2
                    (Ecast
                      (Ebinop Ogt (Etempvar _inlen tulong)
                        (Econst_int (Int.repr 0) tint) tint) tbool)))
                (Sifthenelse (Etempvar _t'2 tint)
                  (Ssequence
                    (Swhile
                      (Ebinop Ogt
                        (Ebinop Osub (Etempvar _inlen tulong)
                          (Etempvar _pos tulong) tulong)
                        (Econst_int (Int.repr 64) tint) tint)
                      (Ssequence
                        (Scall None
                          (Evar _bytes_copy (Tfunction
                                              ((tptr tuchar) ::
                                               (tptr tuchar) :: tulong ::
                                               nil) tvoid cc_default))
                          ((Evar _block (tarray tuchar 64)) ::
                           (Ebinop Oadd (Etempvar _in (tptr tuchar))
                             (Etempvar _pos tulong) (tptr tuchar)) ::
                           (Econst_int (Int.repr 64) tint) :: nil))
                        (Ssequence
                          (Sset _pos
                            (Ebinop Oadd (Etempvar _pos tulong)
                              (Econst_int (Int.repr 64) tint) tulong))
                          (Ssequence
                            (Sset _done
                              (Ebinop Oadd (Etempvar _done tulong)
                                (Econst_int (Int.repr 64) tint) tulong))
                            (Scall None
                              (Evar _rb2s_compress (Tfunction
                                                     ((tptr tuint) ::
                                                      (tptr tuchar) ::
                                                      tulong :: tint :: nil)
                                                     tvoid cc_default))
                              ((Evar _h (tarray tuint 8)) ::
                               (Evar _block (tarray tuchar 64)) ::
                               (Etempvar _done tulong) ::
                               (Econst_int (Int.repr 0) tint) :: nil))))))
                    (Ssequence
                      (Scall None
                        (Evar _bytes_set (Tfunction
                                           ((tptr tuchar) :: tuchar ::
                                            tulong :: nil) tvoid cc_default))
                        ((Evar _block (tarray tuchar 64)) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Econst_int (Int.repr 64) tint) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _bytes_copy (Tfunction
                                              ((tptr tuchar) ::
                                               (tptr tuchar) :: tulong ::
                                               nil) tvoid cc_default))
                          ((Evar _block (tarray tuchar 64)) ::
                           (Ebinop Oadd (Etempvar _in (tptr tuchar))
                             (Etempvar _pos tulong) (tptr tuchar)) ::
                           (Ebinop Osub (Etempvar _inlen tulong)
                             (Etempvar _pos tulong) tulong) :: nil))
                        (Scall None
                          (Evar _rb2s_compress (Tfunction
                                                 ((tptr tuint) ::
                                                  (tptr tuchar) :: tulong ::
                                                  tint :: nil) tvoid
                                                 cc_default))
                          ((Evar _h (tarray tuint 8)) ::
                           (Evar _block (tarray tuchar 64)) ::
                           (Etempvar _total tulong) ::
                           (Econst_int (Int.repr 1) tint) :: nil)))))
                  Sskip))
              (Ssequence
                (Sset _i (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt
                                   (Ecast (Etempvar _i tint) tulong)
                                   (Etempvar _outlen tulong) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Sset _t'3
                        (Ederef
                          (Ebinop Oadd (Evar _h (tarray tuint 8))
                            (Ebinop Odiv (Etempvar _i tint)
                              (Econst_int (Int.repr 4) tint) tint)
                            (tptr tuint)) tuint))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _out (tptr tuchar))
                            (Etempvar _i tint) (tptr tuchar)) tuchar)
                        (Ecast
                          (Ebinop Oshr (Etempvar _t'3 tuint)
                            (Ebinop Omul (Econst_int (Int.repr 8) tint)
                              (Ebinop Omod (Etempvar _i tint)
                                (Econst_int (Int.repr 4) tint) tint) tint)
                            tuint) tuchar))))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tint)
                      (Econst_int (Int.repr 1) tint) tint)))))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_ctx, (Tstruct _blake2s_ctx noattr)) ::
              (_key, (tarray tuchar 32)) ::
              (_key_copy, (tarray tuchar 32)) :: nil);
  fn_temps := ((_keylen, tulong) :: (_outlen, tulong) :: (_n, tulong) ::
               (_pos, tulong) :: (_i, tulong) :: (_msg, (tptr tuchar)) ::
               (_copy, (tptr tuchar)) :: (_out, (tptr tuchar)) ::
               (_ref, (tptr tuchar)) :: (_out2, (tptr tuchar)) ::
               (_c, tulong) :: (_t'26, tint) :: (_t'25, tint) ::
               (_t'24, tint) :: (_t'23, tint) :: (_t'22, (tptr tvoid)) ::
               (_t'21, tint) :: (_t'20, tint) :: (_t'19, tint) ::
               (_t'18, tint) :: (_t'17, tint) :: (_t'16, tint) ::
               (_t'15, tint) :: (_t'14, tuchar) :: (_t'13, tulong) ::
               (_t'12, tint) :: (_t'11, tint) :: (_t'10, tint) ::
               (_t'9, tint) :: (_t'8, (tptr tvoid)) ::
               (_t'7, (tptr tvoid)) :: (_t'6, (tptr tvoid)) ::
               (_t'5, (tptr tvoid)) :: (_t'4, (tptr tvoid)) ::
               (_t'3, tulong) :: (_t'2, tuchar) :: (_t'1, tuchar) ::
               (_t'33, tuint) :: (_t'32, tuint) :: (_t'31, tuint) ::
               (_t'30, tuint) :: (_t'29, tuint) :: (_t'28, tuint) ::
               (_t'27, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1) (Evar _nondet_u8 (Tfunction nil tuchar cc_default))
        nil)
      (Sset _outlen
        (Ecast
          (Ebinop Oadd (Econst_int (Int.repr 1) tint)
            (Ebinop Omod (Etempvar _t'1 tuchar)
              (Econst_int (Int.repr 32) tint) tint) tint) tulong)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _nondet_u8 (Tfunction nil tuchar cc_default)) nil)
        (Sset _keylen
          (Ecast
            (Ebinop Omod (Etempvar _t'2 tuchar)
              (Econst_int (Int.repr 33) tint) tint) tulong)))
      (Ssequence
        (Scall None
          (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                tvoid cc_default))
          ((Evar _key (tarray tuchar 32)) ::
           (Econst_int (Int.repr 32) tint) :: nil))
        (Ssequence
          (Scall None
            (Evar _bytes_copy (Tfunction
                                ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                                 nil) tvoid cc_default))
            ((Evar _key_copy (tarray tuchar 32)) ::
             (Evar _key (tarray tuchar 32)) ::
             (Econst_int (Int.repr 32) tint) :: nil))
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _draw_size (Tfunction nil tulong cc_default)) nil)
              (Sset _n (Etempvar _t'3 tulong)))
            (Ssequence
              (Sifthenelse (Ebinop Ogt (Etempvar _n tulong)
                             (Econst_long (Int64.repr 9223372036854775807) tlong)
                             tint)
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                Sskip)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                               (tptr tvoid) cc_default))
                    ((Etempvar _n tulong) :: nil))
                  (Sset _msg (Etempvar _t'4 (tptr tvoid))))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'5)
                      (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                                 (tptr tvoid) cc_default))
                      ((Etempvar _n tulong) :: nil))
                    (Sset _copy (Etempvar _t'5 (tptr tvoid))))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'6)
                        (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                                   (tptr tvoid) cc_default))
                        ((Etempvar _outlen tulong) :: nil))
                      (Sset _out (Etempvar _t'6 (tptr tvoid))))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'7)
                          (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                                     (tptr tvoid) cc_default))
                          ((Etempvar _outlen tulong) :: nil))
                        (Sset _ref (Etempvar _t'7 (tptr tvoid))))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'8)
                            (Evar _quickproof_malloc (Tfunction
                                                       (tulong :: nil)
                                                       (tptr tvoid)
                                                       cc_default))
                            ((Etempvar _outlen tulong) :: nil))
                          (Sset _out2 (Etempvar _t'8 (tptr tvoid))))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sifthenelse (Ebinop Oeq
                                                 (Etempvar _msg (tptr tuchar))
                                                 (Ecast
                                                   (Econst_int (Int.repr 0) tint)
                                                   (tptr tvoid)) tint)
                                    (Sset _t'9
                                      (Econst_int (Int.repr 1) tint))
                                    (Sset _t'9
                                      (Ecast
                                        (Ebinop Oeq
                                          (Etempvar _copy (tptr tuchar))
                                          (Ecast
                                            (Econst_int (Int.repr 0) tint)
                                            (tptr tvoid)) tint) tbool)))
                                  (Sifthenelse (Etempvar _t'9 tint)
                                    (Sset _t'10
                                      (Econst_int (Int.repr 1) tint))
                                    (Sset _t'10
                                      (Ecast
                                        (Ebinop Oeq
                                          (Etempvar _out (tptr tuchar))
                                          (Ecast
                                            (Econst_int (Int.repr 0) tint)
                                            (tptr tvoid)) tint) tbool))))
                                (Sifthenelse (Etempvar _t'10 tint)
                                  (Sset _t'11 (Econst_int (Int.repr 1) tint))
                                  (Sset _t'11
                                    (Ecast
                                      (Ebinop Oeq
                                        (Etempvar _ref (tptr tuchar))
                                        (Ecast (Econst_int (Int.repr 0) tint)
                                          (tptr tvoid)) tint) tbool))))
                              (Sifthenelse (Etempvar _t'11 tint)
                                (Sset _t'12 (Econst_int (Int.repr 1) tint))
                                (Sset _t'12
                                  (Ecast
                                    (Ebinop Oeq
                                      (Etempvar _out2 (tptr tuchar))
                                      (Ecast (Econst_int (Int.repr 0) tint)
                                        (tptr tvoid)) tint) tbool))))
                            (Sifthenelse (Etempvar _t'12 tint)
                              (Ssequence
                                (Scall None
                                  (Evar _quickproof_free (Tfunction
                                                           ((tptr tvoid) ::
                                                            nil) tvoid
                                                           cc_default))
                                  ((Etempvar _msg (tptr tuchar)) :: nil))
                                (Ssequence
                                  (Scall None
                                    (Evar _quickproof_free (Tfunction
                                                             ((tptr tvoid) ::
                                                              nil) tvoid
                                                             cc_default))
                                    ((Etempvar _copy (tptr tuchar)) :: nil))
                                  (Ssequence
                                    (Scall None
                                      (Evar _quickproof_free (Tfunction
                                                               ((tptr tvoid) ::
                                                                nil) tvoid
                                                               cc_default))
                                      ((Etempvar _out (tptr tuchar)) :: nil))
                                    (Ssequence
                                      (Scall None
                                        (Evar _quickproof_free (Tfunction
                                                                 ((tptr tvoid) ::
                                                                  nil) tvoid
                                                                 cc_default))
                                        ((Etempvar _ref (tptr tuchar)) ::
                                         nil))
                                      (Ssequence
                                        (Scall None
                                          (Evar _quickproof_free (Tfunction
                                                                   ((tptr tvoid) ::
                                                                    nil)
                                                                   tvoid
                                                                   cc_default))
                                          ((Etempvar _out2 (tptr tuchar)) ::
                                           nil))
                                        (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))
                              Sskip))
                          (Ssequence
                            (Scall None
                              (Evar _nondet_bytes (Tfunction
                                                    ((tptr tuchar) ::
                                                     tulong :: nil) tvoid
                                                    cc_default))
                              ((Etempvar _msg (tptr tuchar)) ::
                               (Etempvar _n tulong) :: nil))
                            (Ssequence
                              (Scall None
                                (Evar _bytes_copy (Tfunction
                                                    ((tptr tuchar) ::
                                                     (tptr tuchar) ::
                                                     tulong :: nil) tvoid
                                                    cc_default))
                                ((Etempvar _copy (tptr tuchar)) ::
                                 (Etempvar _msg (tptr tuchar)) ::
                                 (Etempvar _n tulong) :: nil))
                              (Ssequence
                                (Sifthenelse (Ebinop Ogt
                                               (Etempvar _keylen tulong)
                                               (Econst_int (Int.repr 0) tint)
                                               tint)
                                  (Scall None
                                    (Evar _blake2s_init_key (Tfunction
                                                              ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                                               tulong ::
                                                               (tptr tvoid) ::
                                                               tulong :: nil)
                                                              tvoid
                                                              cc_default))
                                    ((Eaddrof
                                       (Evar _ctx (Tstruct _blake2s_ctx noattr))
                                       (tptr (Tstruct _blake2s_ctx noattr))) ::
                                     (Etempvar _outlen tulong) ::
                                     (Evar _key (tarray tuchar 32)) ::
                                     (Etempvar _keylen tulong) :: nil))
                                  (Scall None
                                    (Evar _blake2s_init (Tfunction
                                                          ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                                           tulong :: nil)
                                                          tvoid cc_default))
                                    ((Eaddrof
                                       (Evar _ctx (Tstruct _blake2s_ctx noattr))
                                       (tptr (Tstruct _blake2s_ctx noattr))) ::
                                     (Etempvar _outlen tulong) :: nil)))
                                (Ssequence
                                  (Sset _pos
                                    (Ecast (Econst_int (Int.repr 0) tint)
                                      tulong))
                                  (Ssequence
                                    (Swhile
                                      (Ebinop Olt (Etempvar _pos tulong)
                                        (Etempvar _n tulong) tint)
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'13)
                                            (Evar _nondet_size (Tfunction nil
                                                                 tulong
                                                                 cc_default))
                                            nil)
                                          (Sset _c (Etempvar _t'13 tulong)))
                                        (Ssequence
                                          (Sifthenelse (Ebinop Ogt
                                                         (Etempvar _c tulong)
                                                         (Ebinop Osub
                                                           (Etempvar _n tulong)
                                                           (Etempvar _pos tulong)
                                                           tulong) tint)
                                            (Sset _c
                                              (Ebinop Osub
                                                (Etempvar _n tulong)
                                                (Etempvar _pos tulong)
                                                tulong))
                                            Sskip)
                                          (Ssequence
                                            (Scall None
                                              (Evar _blake2s_update (Tfunction
                                                                    ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                              ((Eaddrof
                                                 (Evar _ctx (Tstruct _blake2s_ctx noattr))
                                                 (tptr (Tstruct _blake2s_ctx noattr))) ::
                                               (Ebinop Oadd
                                                 (Etempvar _msg (tptr tuchar))
                                                 (Etempvar _pos tulong)
                                                 (tptr tuchar)) ::
                                               (Etempvar _c tulong) :: nil))
                                            (Sset _pos
                                              (Ebinop Oadd
                                                (Etempvar _pos tulong)
                                                (Etempvar _c tulong) tulong))))))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'14)
                                          (Evar _nondet_u8 (Tfunction nil
                                                             tuchar
                                                             cc_default))
                                          nil)
                                        (Sifthenelse (Ebinop Oand
                                                       (Etempvar _t'14 tuchar)
                                                       (Econst_int (Int.repr 1) tint)
                                                       tint)
                                          (Scall None
                                            (Evar _blake2s_update (Tfunction
                                                                    ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                            ((Eaddrof
                                               (Evar _ctx (Tstruct _blake2s_ctx noattr))
                                               (tptr (Tstruct _blake2s_ctx noattr))) ::
                                             (Etempvar _msg (tptr tuchar)) ::
                                             (Econst_int (Int.repr 0) tint) ::
                                             nil))
                                          Sskip))
                                      (Ssequence
                                        (Scall None
                                          (Evar _blake2s_final (Tfunction
                                                                 ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                                                  (tptr tuchar) ::
                                                                  nil) tvoid
                                                                 cc_default))
                                          ((Eaddrof
                                             (Evar _ctx (Tstruct _blake2s_ctx noattr))
                                             (tptr (Tstruct _blake2s_ctx noattr))) ::
                                           (Etempvar _out (tptr tuchar)) ::
                                           nil))
                                        (Ssequence
                                          (Scall None
                                            (Evar _ref_blake2s (Tfunction
                                                                 ((tptr tuchar) ::
                                                                  tulong ::
                                                                  (tptr tuchar) ::
                                                                  tulong ::
                                                                  (tptr tuchar) ::
                                                                  tulong ::
                                                                  nil) tvoid
                                                                 cc_default))
                                            ((Etempvar _ref (tptr tuchar)) ::
                                             (Etempvar _outlen tulong) ::
                                             (Evar _key (tarray tuchar 32)) ::
                                             (Etempvar _keylen tulong) ::
                                             (Etempvar _msg (tptr tuchar)) ::
                                             (Etempvar _n tulong) :: nil))
                                          (Ssequence
                                            (Sloop
                                              (Ssequence
                                                (Scall (Some _t'15)
                                                  (Evar _bytes_eq (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                  ((Etempvar _out (tptr tuchar)) ::
                                                   (Etempvar _ref (tptr tuchar)) ::
                                                   (Etempvar _outlen tulong) ::
                                                   nil))
                                                (Sifthenelse (Eunop Onotbool
                                                               (Etempvar _t'15 tint)
                                                               tint)
                                                  (Scall None
                                                    (Evar _check_failed 
                                                    (Tfunction nil tvoid
                                                      cc_default)) nil)
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
                                                                   (Econst_int (Int.repr 8) tint)
                                                                   tint)
                                                      Sskip
                                                      Sbreak)
                                                    (Sloop
                                                      (Ssequence
                                                        (Sset _t'33
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Efield
                                                                (Evar _ctx (Tstruct _blake2s_ctx noattr))
                                                                _h
                                                                (tarray tuint 8))
                                                              (Etempvar _i tulong)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Sifthenelse 
                                                          (Eunop Onotbool
                                                            (Ebinop Oeq
                                                              (Etempvar _t'33 tuint)
                                                              (Econst_int (Int.repr 0) tint)
                                                              tint) tint)
                                                          (Scall None
                                                            (Evar _check_failed 
                                                            (Tfunction nil
                                                              tvoid
                                                              cc_default))
                                                            nil)
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
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'31
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Efield
                                                                  (Evar _ctx (Tstruct _blake2s_ctx noattr))
                                                                  _t
                                                                  (tarray tuint 2))
                                                                (Econst_int (Int.repr 0) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Sifthenelse 
                                                            (Ebinop Oeq
                                                              (Etempvar _t'31 tuint)
                                                              (Econst_int (Int.repr 0) tint)
                                                              tint)
                                                            (Ssequence
                                                              (Sset _t'32
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _ctx (Tstruct _blake2s_ctx noattr))
                                                                    _t
                                                                    (tarray tuint 2))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Sset _t'16
                                                                (Ecast
                                                                  (Ebinop Oeq
                                                                    (Etempvar _t'32 tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                  tbool)))
                                                            (Sset _t'16
                                                              (Econst_int (Int.repr 0) tint))))
                                                        (Sifthenelse (Etempvar _t'16 tint)
                                                          (Ssequence
                                                            (Sset _t'30
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Efield
                                                                    (Evar _ctx (Tstruct _blake2s_ctx noattr))
                                                                    _f
                                                                    (tarray tuint 2))
                                                                  (Econst_int (Int.repr 0) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Sset _t'17
                                                              (Ecast
                                                                (Ebinop Oeq
                                                                  (Etempvar _t'30 tuint)
                                                                  (Econst_int (Int.repr 0) tint)
                                                                  tint)
                                                                tbool)))
                                                          (Sset _t'17
                                                            (Econst_int (Int.repr 0) tint))))
                                                      (Sifthenelse (Etempvar _t'17 tint)
                                                        (Ssequence
                                                          (Sset _t'29
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Efield
                                                                  (Evar _ctx (Tstruct _blake2s_ctx noattr))
                                                                  _f
                                                                  (tarray tuint 2))
                                                                (Econst_int (Int.repr 1) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Sset _t'18
                                                            (Ecast
                                                              (Ebinop Oeq
                                                                (Etempvar _t'29 tuint)
                                                                (Econst_int (Int.repr 0) tint)
                                                                tint) tbool)))
                                                        (Sset _t'18
                                                          (Econst_int (Int.repr 0) tint))))
                                                    (Sifthenelse (Eunop Onotbool
                                                                   (Etempvar _t'18 tint)
                                                                   tint)
                                                      (Scall None
                                                        (Evar _check_failed 
                                                        (Tfunction nil tvoid
                                                          cc_default)) nil)
                                                      Sskip))
                                                  Sbreak)
                                                (Ssequence
                                                  (Sloop
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Scall (Some _t'19)
                                                            (Evar _bytes_zero 
                                                            (Tfunction
                                                              ((tptr tuchar) ::
                                                               tulong :: nil)
                                                              tint
                                                              cc_default))
                                                            ((Efield
                                                               (Evar _ctx (Tstruct _blake2s_ctx noattr))
                                                               _buf
                                                               (tarray tuchar 64)) ::
                                                             (Econst_int (Int.repr 64) tint) ::
                                                             nil))
                                                          (Sifthenelse (Etempvar _t'19 tint)
                                                            (Ssequence
                                                              (Sset _t'28
                                                                (Efield
                                                                  (Evar _ctx (Tstruct _blake2s_ctx noattr))
                                                                  _buflen
                                                                  tuint))
                                                              (Sset _t'20
                                                                (Ecast
                                                                  (Ebinop Oeq
                                                                    (Etempvar _t'28 tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                  tbool)))
                                                            (Sset _t'20
                                                              (Econst_int (Int.repr 0) tint))))
                                                        (Sifthenelse (Etempvar _t'20 tint)
                                                          (Ssequence
                                                            (Sset _t'27
                                                              (Efield
                                                                (Evar _ctx (Tstruct _blake2s_ctx noattr))
                                                                _outlen
                                                                tuint))
                                                            (Sset _t'21
                                                              (Ecast
                                                                (Ebinop Oeq
                                                                  (Etempvar _t'27 tuint)
                                                                  (Econst_int (Int.repr 0) tint)
                                                                  tint)
                                                                tbool)))
                                                          (Sset _t'21
                                                            (Econst_int (Int.repr 0) tint))))
                                                      (Sifthenelse (Eunop Onotbool
                                                                    (Etempvar _t'21 tint)
                                                                    tint)
                                                        (Scall None
                                                          (Evar _check_failed 
                                                          (Tfunction nil
                                                            tvoid cc_default))
                                                          nil)
                                                        Sskip))
                                                    Sbreak)
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop Ogt
                                                                    (Etempvar _keylen tulong)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                        (Sset _t'22
                                                          (Ecast
                                                            (Evar _key (tarray tuchar 32))
                                                            (tptr tvoid)))
                                                        (Sset _t'22
                                                          (Ecast
                                                            (Ecast
                                                              (Econst_int (Int.repr 0) tint)
                                                              (tptr tvoid))
                                                            (tptr tvoid))))
                                                      (Scall None
                                                        (Evar _blake2s 
                                                        (Tfunction
                                                          ((tptr tuchar) ::
                                                           tulong ::
                                                           (tptr tuchar) ::
                                                           tulong ::
                                                           (tptr tuchar) ::
                                                           tulong :: nil)
                                                          tvoid cc_default))
                                                        ((Etempvar _t'22 (tptr tvoid)) ::
                                                         (Etempvar _keylen tulong) ::
                                                         (Etempvar _msg (tptr tuchar)) ::
                                                         (Etempvar _n tulong) ::
                                                         (Etempvar _out2 (tptr tuchar)) ::
                                                         (Etempvar _outlen tulong) ::
                                                         nil)))
                                                    (Ssequence
                                                      (Sloop
                                                        (Ssequence
                                                          (Scall (Some _t'23)
                                                            (Evar _bytes_eq 
                                                            (Tfunction
                                                              ((tptr tuchar) ::
                                                               (tptr tuchar) ::
                                                               tulong :: nil)
                                                              tint
                                                              cc_default))
                                                            ((Etempvar _out2 (tptr tuchar)) ::
                                                             (Etempvar _ref (tptr tuchar)) ::
                                                             (Etempvar _outlen tulong) ::
                                                             nil))
                                                          (Sifthenelse 
                                                            (Eunop Onotbool
                                                              (Etempvar _t'23 tint)
                                                              tint)
                                                            (Scall None
                                                              (Evar _check_failed 
                                                              (Tfunction nil
                                                                tvoid
                                                                cc_default))
                                                              nil)
                                                            Sskip))
                                                        Sbreak)
                                                      (Ssequence
                                                        (Sloop
                                                          (Ssequence
                                                            (Ssequence
                                                              (Scall (Some _t'24)
                                                                (Evar _bytes_eq 
                                                                (Tfunction
                                                                  ((tptr tuchar) ::
                                                                   (tptr tuchar) ::
                                                                   tulong ::
                                                                   nil) tint
                                                                  cc_default))
                                                                ((Etempvar _msg (tptr tuchar)) ::
                                                                 (Etempvar _copy (tptr tuchar)) ::
                                                                 (Etempvar _n tulong) ::
                                                                 nil))
                                                              (Sifthenelse (Etempvar _t'24 tint)
                                                                (Ssequence
                                                                  (Scall (Some _t'26)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Evar _key (tarray tuchar 32)) ::
                                                                    (Evar _key_copy (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                  (Sset _t'25
                                                                    (Ecast
                                                                    (Etempvar _t'26 tint)
                                                                    tbool)))
                                                                (Sset _t'25
                                                                  (Econst_int (Int.repr 0) tint))))
                                                            (Sifthenelse 
                                                              (Eunop Onotbool
                                                                (Etempvar _t'25 tint)
                                                                tint)
                                                              (Scall None
                                                                (Evar _check_failed 
                                                                (Tfunction
                                                                  nil tvoid
                                                                  cc_default))
                                                                nil)
                                                              Sskip))
                                                          Sbreak)
                                                        (Ssequence
                                                          (Scall None
                                                            (Evar _quickproof_free 
                                                            (Tfunction
                                                              ((tptr tvoid) ::
                                                               nil) tvoid
                                                              cc_default))
                                                            ((Etempvar _msg (tptr tuchar)) ::
                                                             nil))
                                                          (Ssequence
                                                            (Scall None
                                                              (Evar _quickproof_free 
                                                              (Tfunction
                                                                ((tptr tvoid) ::
                                                                 nil) tvoid
                                                                cc_default))
                                                              ((Etempvar _copy (tptr tuchar)) ::
                                                               nil))
                                                            (Ssequence
                                                              (Scall None
                                                                (Evar _quickproof_free 
                                                                (Tfunction
                                                                  ((tptr tvoid) ::
                                                                   nil) tvoid
                                                                  cc_default))
                                                                ((Etempvar _out (tptr tuchar)) ::
                                                                 nil))
                                                              (Ssequence
                                                                (Scall None
                                                                  (Evar _quickproof_free 
                                                                  (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Etempvar _ref (tptr tuchar)) ::
                                                                   nil))
                                                                (Ssequence
                                                                  (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _out2 (tptr tuchar)) ::
                                                                    nil))
                                                                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))))))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _blake2s_ctx Struct
   (Member_plain _h (tarray tuint 8) :: Member_plain _t (tarray tuint 2) ::
    Member_plain _f (tarray tuint 2) ::
    Member_plain _buf (tarray tuchar 64) :: Member_plain _buflen tuint ::
    Member_plain _outlen tuint :: nil)
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
 (_nondet_size,
   Gfun(External (EF_external "nondet_size"
                   (mksignature nil AST.Xlong cc_default)) nil tulong
     cc_default)) ::
 (_nondet_bytes,
   Gfun(External (EF_external "nondet_bytes"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xvoid
                     cc_default)) ((tptr tuchar) :: tulong :: nil) tvoid
     cc_default)) ::
 (_memcpy,
   Gfun(External (EF_external "memcpy"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xlong :: nil)
                     AST.Xptr cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil) (tptr tvoid)
     cc_default)) ::
 (_memset,
   Gfun(External (EF_external "memset"
                   (mksignature (AST.Xptr :: AST.Xint :: AST.Xlong :: nil)
                     AST.Xptr cc_default))
     ((tptr tvoid) :: tint :: tulong :: nil) (tptr tvoid) cc_default)) ::
 (_quickproof_malloc,
   Gfun(External (EF_external "quickproof_malloc"
                   (mksignature (AST.Xlong :: nil) AST.Xptr cc_default))
     (tulong :: nil) (tptr tvoid) cc_default)) ::
 (_quickproof_free,
   Gfun(External (EF_external "quickproof_free"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___blake2s_init, Gfun(Internal f___blake2s_init)) ::
 (_blake2s_init, Gfun(Internal f_blake2s_init)) ::
 (_blake2s_init_key, Gfun(Internal f_blake2s_init_key)) ::
 (_blake2s_update,
   Gfun(External (EF_external "blake2s_update"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr (Tstruct _blake2s_ctx noattr)) :: (tptr tuchar) :: tulong :: nil)
     tvoid cc_default)) ::
 (_blake2s_final,
   Gfun(External (EF_external "blake2s_final"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default))
     ((tptr (Tstruct _blake2s_ctx noattr)) :: (tptr tuchar) :: nil) tvoid
     cc_default)) :: (_blake2s, Gfun(Internal f_blake2s)) ::
 (_check_failed, Gfun(Internal f_check_failed)) ::
 (_bytes_eq, Gfun(Internal f_bytes_eq)) ::
 (_bytes_zero, Gfun(Internal f_bytes_zero)) ::
 (_bytes_copy, Gfun(Internal f_bytes_copy)) ::
 (_bytes_set, Gfun(Internal f_bytes_set)) ::
 (_draw_size, Gfun(Internal f_draw_size)) ::
 (_le32_load, Gfun(Internal f_le32_load)) :: (_RB2S_IV, Gvar v_RB2S_IV) ::
 (_RB2S_SIGMA, Gvar v_RB2S_SIGMA) ::
 (_rb2s_rotr, Gfun(Internal f_rb2s_rotr)) ::
 (_rb2s_g, Gfun(Internal f_rb2s_g)) ::
 (_rb2s_compress, Gfun(Internal f_rb2s_compress)) ::
 (_ref_blake2s, Gfun(Internal f_ref_blake2s)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _blake2s_final :: _blake2s_update :: _quickproof_free ::
 _quickproof_malloc :: _memset :: _memcpy :: _nondet_bytes :: _nondet_size ::
 _nondet_u8 :: ___builtin_debug :: ___builtin_write32_reversed ::
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


