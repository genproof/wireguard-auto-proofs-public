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
  Definition source_file := "lib/crypto/poly1305-donna32.c".
  Definition normalized := true.
End Info.

Definition __anon_ef6b4645c220 : ident := $"_anon_ef6b4645c220".
Definition __anon_43224dacc2cf : ident := $"_anon_43224dacc2cf".
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
Definition _b : ident := $"b".
Definition _c : ident := $"c".
Definition _d0 : ident := $"d0".
Definition _d1 : ident := $"d1".
Definition _d2 : ident := $"d2".
Definition _d3 : ident := $"d3".
Definition _d4 : ident := $"d4".
Definition _dst : ident := $"dst".
Definition _f : ident := $"f".
Definition _g0 : ident := $"g0".
Definition _g1 : ident := $"g1".
Definition _g2 : ident := $"g2".
Definition _g3 : ident := $"g3".
Definition _g4 : ident := $"g4".
Definition _get_unaligned_le32 : ident := $"get_unaligned_le32".
Definition _h : ident := $"h".
Definition _h0 : ident := $"h0".
Definition _h1 : ident := $"h1".
Definition _h2 : ident := $"h2".
Definition _h3 : ident := $"h3".
Definition _h4 : ident := $"h4".
Definition _h64 : ident := $"h64".
Definition _hibit : ident := $"hibit".
Definition _input : ident := $"input".
Definition _key : ident := $"key".
Definition _mac : ident := $"mac".
Definition _main : ident := $"main".
Definition _mask : ident := $"mask".
Definition _nblocks : ident := $"nblocks".
Definition _nonce : ident := $"nonce".
Definition _p : ident := $"p".
Definition _poly1305_core_blocks : ident := $"poly1305_core_blocks".
Definition _poly1305_core_emit : ident := $"poly1305_core_emit".
Definition _poly1305_core_key : ident := $"poly1305_core_key".
Definition _poly1305_core_setkey : ident := $"poly1305_core_setkey".
Definition _poly1305_key : ident := $"poly1305_key".
Definition _poly1305_state : ident := $"poly1305_state".
Definition _precomputed_s : ident := $"precomputed_s".
Definition _put_unaligned_le32 : ident := $"put_unaligned_le32".
Definition _r : ident := $"r".
Definition _r0 : ident := $"r0".
Definition _r1 : ident := $"r1".
Definition _r2 : ident := $"r2".
Definition _r3 : ident := $"r3".
Definition _r4 : ident := $"r4".
Definition _r64 : ident := $"r64".
Definition _raw_key : ident := $"raw_key".
Definition _s1 : ident := $"s1".
Definition _s2 : ident := $"s2".
Definition _s3 : ident := $"s3".
Definition _s4 : ident := $"s4".
Definition _src : ident := $"src".
Definition _state : ident := $"state".
Definition _v : ident := $"v".
Definition _t'1 : ident := 128%positive.
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

Definition f_put_unaligned_le32 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, tuint) :: (_p, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, (tptr tuchar)) :: nil);
  fn_body :=
(Ssequence
  (Sset _b (Ecast (Etempvar _p (tptr tvoid)) (tptr tuchar)))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar _b (tptr tuchar))
          (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
      (Ecast (Etempvar _v tuint) tuchar))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _b (tptr tuchar))
            (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar)
        (Ecast
          (Ebinop Oshr (Etempvar _v tuint) (Econst_int (Int.repr 8) tint)
            tuint) tuchar))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _b (tptr tuchar))
              (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar)
          (Ecast
            (Ebinop Oshr (Etempvar _v tuint) (Econst_int (Int.repr 16) tint)
              tuint) tuchar))
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _b (tptr tuchar))
              (Econst_int (Int.repr 3) tint) (tptr tuchar)) tuchar)
          (Ecast
            (Ebinop Oshr (Etempvar _v tuint) (Econst_int (Int.repr 24) tint)
              tuint) tuchar))))))
|}.

Definition f_poly1305_core_setkey := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr (Tstruct _poly1305_core_key noattr))) ::
                (_raw_key, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tuint) :: (_t'4, tuint) :: (_t'3, tuint) ::
               (_t'2, tuint) :: (_t'1, tuint) :: (_t'9, tuint) ::
               (_t'8, tuint) :: (_t'7, tuint) :: (_t'6, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_unaligned_le32 (Tfunction ((tptr tvoid) :: nil) tuint
                                  cc_default))
      ((Ebinop Oadd (Etempvar _raw_key (tptr tuchar))
         (Econst_int (Int.repr 0) tint) (tptr tuchar)) :: nil))
    (Sassign
      (Ederef
        (Ebinop Oadd
          (Efield
            (Efield
              (Efield
                (Ederef
                  (Etempvar _key (tptr (Tstruct _poly1305_core_key noattr)))
                  (Tstruct _poly1305_core_key noattr)) _key
                (Tstruct _poly1305_key noattr)) 18727075383868559167%positive
              (Tunion __anon_ef6b4645c220 noattr)) _r (tarray tuint 5))
          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
      (Ebinop Oand (Etempvar _t'1 tuint)
        (Econst_int (Int.repr 67108863) tint) tuint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _get_unaligned_le32 (Tfunction ((tptr tvoid) :: nil) tuint
                                    cc_default))
        ((Ebinop Oadd (Etempvar _raw_key (tptr tuchar))
           (Econst_int (Int.repr 3) tint) (tptr tuchar)) :: nil))
      (Sassign
        (Ederef
          (Ebinop Oadd
            (Efield
              (Efield
                (Efield
                  (Ederef
                    (Etempvar _key (tptr (Tstruct _poly1305_core_key noattr)))
                    (Tstruct _poly1305_core_key noattr)) _key
                  (Tstruct _poly1305_key noattr))
                18727075383868559167%positive (Tunion __anon_ef6b4645c220 noattr)) _r
              (tarray tuint 5)) (Econst_int (Int.repr 1) tint) (tptr tuint))
          tuint)
        (Ebinop Oand
          (Ebinop Oshr (Etempvar _t'2 tuint) (Econst_int (Int.repr 2) tint)
            tuint) (Econst_int (Int.repr 67108611) tint) tuint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _get_unaligned_le32 (Tfunction ((tptr tvoid) :: nil) tuint
                                      cc_default))
          ((Ebinop Oadd (Etempvar _raw_key (tptr tuchar))
             (Econst_int (Int.repr 6) tint) (tptr tuchar)) :: nil))
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield
                (Efield
                  (Efield
                    (Ederef
                      (Etempvar _key (tptr (Tstruct _poly1305_core_key noattr)))
                      (Tstruct _poly1305_core_key noattr)) _key
                    (Tstruct _poly1305_key noattr))
                  18727075383868559167%positive (Tunion __anon_ef6b4645c220 noattr)) _r
                (tarray tuint 5)) (Econst_int (Int.repr 2) tint)
              (tptr tuint)) tuint)
          (Ebinop Oand
            (Ebinop Oshr (Etempvar _t'3 tuint) (Econst_int (Int.repr 4) tint)
              tuint) (Econst_int (Int.repr 67092735) tint) tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _get_unaligned_le32 (Tfunction ((tptr tvoid) :: nil) tuint
                                        cc_default))
            ((Ebinop Oadd (Etempvar _raw_key (tptr tuchar))
               (Econst_int (Int.repr 9) tint) (tptr tuchar)) :: nil))
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Efield
                    (Efield
                      (Ederef
                        (Etempvar _key (tptr (Tstruct _poly1305_core_key noattr)))
                        (Tstruct _poly1305_core_key noattr)) _key
                      (Tstruct _poly1305_key noattr))
                    18727075383868559167%positive (Tunion __anon_ef6b4645c220 noattr)) _r
                  (tarray tuint 5)) (Econst_int (Int.repr 3) tint)
                (tptr tuint)) tuint)
            (Ebinop Oand
              (Ebinop Oshr (Etempvar _t'4 tuint)
                (Econst_int (Int.repr 6) tint) tuint)
              (Econst_int (Int.repr 66076671) tint) tuint)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'5)
              (Evar _get_unaligned_le32 (Tfunction ((tptr tvoid) :: nil)
                                          tuint cc_default))
              ((Ebinop Oadd (Etempvar _raw_key (tptr tuchar))
                 (Econst_int (Int.repr 12) tint) (tptr tuchar)) :: nil))
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Efield
                      (Efield
                        (Ederef
                          (Etempvar _key (tptr (Tstruct _poly1305_core_key noattr)))
                          (Tstruct _poly1305_core_key noattr)) _key
                        (Tstruct _poly1305_key noattr))
                      18727075383868559167%positive (Tunion __anon_ef6b4645c220 noattr)) _r
                    (tarray tuint 5)) (Econst_int (Int.repr 4) tint)
                  (tptr tuint)) tuint)
              (Ebinop Oand
                (Ebinop Oshr (Etempvar _t'5 tuint)
                  (Econst_int (Int.repr 8) tint) tuint)
                (Econst_int (Int.repr 1048575) tint) tuint)))
          (Ssequence
            (Ssequence
              (Sset _t'9
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Efield
                        (Efield
                          (Ederef
                            (Etempvar _key (tptr (Tstruct _poly1305_core_key noattr)))
                            (Tstruct _poly1305_core_key noattr)) _key
                          (Tstruct _poly1305_key noattr))
                        18727075383868559167%positive (Tunion __anon_ef6b4645c220 noattr))
                      _r (tarray tuint 5)) (Econst_int (Int.repr 1) tint)
                    (tptr tuint)) tuint))
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Efield
                        (Efield
                          (Ederef
                            (Etempvar _key (tptr (Tstruct _poly1305_core_key noattr)))
                            (Tstruct _poly1305_core_key noattr))
                          _precomputed_s (Tstruct _poly1305_key noattr))
                        18727075383868559167%positive (Tunion __anon_ef6b4645c220 noattr))
                      _r (tarray tuint 5)) (Econst_int (Int.repr 0) tint)
                    (tptr tuint)) tuint)
                (Ebinop Omul (Etempvar _t'9 tuint)
                  (Econst_int (Int.repr 5) tint) tuint)))
            (Ssequence
              (Ssequence
                (Sset _t'8
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Efield
                          (Efield
                            (Ederef
                              (Etempvar _key (tptr (Tstruct _poly1305_core_key noattr)))
                              (Tstruct _poly1305_core_key noattr)) _key
                            (Tstruct _poly1305_key noattr))
                          18727075383868559167%positive
                          (Tunion __anon_ef6b4645c220 noattr)) _r (tarray tuint 5))
                      (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint))
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Efield
                          (Efield
                            (Ederef
                              (Etempvar _key (tptr (Tstruct _poly1305_core_key noattr)))
                              (Tstruct _poly1305_core_key noattr))
                            _precomputed_s (Tstruct _poly1305_key noattr))
                          18727075383868559167%positive
                          (Tunion __anon_ef6b4645c220 noattr)) _r (tarray tuint 5))
                      (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint)
                  (Ebinop Omul (Etempvar _t'8 tuint)
                    (Econst_int (Int.repr 5) tint) tuint)))
              (Ssequence
                (Ssequence
                  (Sset _t'7
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Efield
                            (Efield
                              (Ederef
                                (Etempvar _key (tptr (Tstruct _poly1305_core_key noattr)))
                                (Tstruct _poly1305_core_key noattr)) _key
                              (Tstruct _poly1305_key noattr))
                            18727075383868559167%positive
                            (Tunion __anon_ef6b4645c220 noattr)) _r (tarray tuint 5))
                        (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Efield
                            (Efield
                              (Ederef
                                (Etempvar _key (tptr (Tstruct _poly1305_core_key noattr)))
                                (Tstruct _poly1305_core_key noattr))
                              _precomputed_s (Tstruct _poly1305_key noattr))
                            18727075383868559167%positive
                            (Tunion __anon_ef6b4645c220 noattr)) _r (tarray tuint 5))
                        (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint)
                    (Ebinop Omul (Etempvar _t'7 tuint)
                      (Econst_int (Int.repr 5) tint) tuint)))
                (Ssequence
                  (Sset _t'6
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Efield
                            (Efield
                              (Ederef
                                (Etempvar _key (tptr (Tstruct _poly1305_core_key noattr)))
                                (Tstruct _poly1305_core_key noattr)) _key
                              (Tstruct _poly1305_key noattr))
                            18727075383868559167%positive
                            (Tunion __anon_ef6b4645c220 noattr)) _r (tarray tuint 5))
                        (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Efield
                            (Efield
                              (Ederef
                                (Etempvar _key (tptr (Tstruct _poly1305_core_key noattr)))
                                (Tstruct _poly1305_core_key noattr))
                              _precomputed_s (Tstruct _poly1305_key noattr))
                            18727075383868559167%positive
                            (Tunion __anon_ef6b4645c220 noattr)) _r (tarray tuint 5))
                        (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint)
                    (Ebinop Omul (Etempvar _t'6 tuint)
                      (Econst_int (Int.repr 5) tint) tuint)))))))))))
|}.

Definition f_poly1305_core_blocks := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_state, (tptr (Tstruct _poly1305_state noattr))) ::
                (_key, (tptr (Tstruct _poly1305_core_key noattr))) ::
                (_src, (tptr tvoid)) :: (_nblocks, tuint) ::
                (_hibit, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_input, (tptr tuchar)) :: (_r0, tuint) :: (_r1, tuint) ::
               (_r2, tuint) :: (_r3, tuint) :: (_r4, tuint) ::
               (_s1, tuint) :: (_s2, tuint) :: (_s3, tuint) ::
               (_s4, tuint) :: (_h0, tuint) :: (_h1, tuint) ::
               (_h2, tuint) :: (_h3, tuint) :: (_h4, tuint) ::
               (_d0, tulong) :: (_d1, tulong) :: (_d2, tulong) ::
               (_d3, tulong) :: (_d4, tulong) :: (_c, tuint) ::
               (_t'6, tuint) :: (_t'5, tuint) :: (_t'4, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _input (Etempvar _src (tptr tvoid)))
  (Ssequence
    (Sifthenelse (Eunop Onotbool (Etempvar _nblocks tuint) tint)
      (Sreturn None)
      Sskip)
    (Ssequence
      (Sset _hibit
        (Ebinop Oshl (Etempvar _hibit tuint) (Econst_int (Int.repr 24) tint)
          tuint))
      (Ssequence
        (Sset _r0
          (Ederef
            (Ebinop Oadd
              (Efield
                (Efield
                  (Efield
                    (Ederef
                      (Etempvar _key (tptr (Tstruct _poly1305_core_key noattr)))
                      (Tstruct _poly1305_core_key noattr)) _key
                    (Tstruct _poly1305_key noattr))
                  18727075383868559167%positive (Tunion __anon_ef6b4645c220 noattr)) _r
                (tarray tuint 5)) (Econst_int (Int.repr 0) tint)
              (tptr tuint)) tuint))
        (Ssequence
          (Sset _r1
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Efield
                    (Efield
                      (Ederef
                        (Etempvar _key (tptr (Tstruct _poly1305_core_key noattr)))
                        (Tstruct _poly1305_core_key noattr)) _key
                      (Tstruct _poly1305_key noattr))
                    18727075383868559167%positive (Tunion __anon_ef6b4645c220 noattr)) _r
                  (tarray tuint 5)) (Econst_int (Int.repr 1) tint)
                (tptr tuint)) tuint))
          (Ssequence
            (Sset _r2
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Efield
                      (Efield
                        (Ederef
                          (Etempvar _key (tptr (Tstruct _poly1305_core_key noattr)))
                          (Tstruct _poly1305_core_key noattr)) _key
                        (Tstruct _poly1305_key noattr))
                      18727075383868559167%positive (Tunion __anon_ef6b4645c220 noattr)) _r
                    (tarray tuint 5)) (Econst_int (Int.repr 2) tint)
                  (tptr tuint)) tuint))
            (Ssequence
              (Sset _r3
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Efield
                        (Efield
                          (Ederef
                            (Etempvar _key (tptr (Tstruct _poly1305_core_key noattr)))
                            (Tstruct _poly1305_core_key noattr)) _key
                          (Tstruct _poly1305_key noattr))
                        18727075383868559167%positive (Tunion __anon_ef6b4645c220 noattr))
                      _r (tarray tuint 5)) (Econst_int (Int.repr 3) tint)
                    (tptr tuint)) tuint))
              (Ssequence
                (Sset _r4
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Efield
                          (Efield
                            (Ederef
                              (Etempvar _key (tptr (Tstruct _poly1305_core_key noattr)))
                              (Tstruct _poly1305_core_key noattr)) _key
                            (Tstruct _poly1305_key noattr))
                          18727075383868559167%positive
                          (Tunion __anon_ef6b4645c220 noattr)) _r (tarray tuint 5))
                      (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint))
                (Ssequence
                  (Sset _s1
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Efield
                            (Efield
                              (Ederef
                                (Etempvar _key (tptr (Tstruct _poly1305_core_key noattr)))
                                (Tstruct _poly1305_core_key noattr))
                              _precomputed_s (Tstruct _poly1305_key noattr))
                            18727075383868559167%positive
                            (Tunion __anon_ef6b4645c220 noattr)) _r (tarray tuint 5))
                        (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
                  (Ssequence
                    (Sset _s2
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Efield
                              (Efield
                                (Ederef
                                  (Etempvar _key (tptr (Tstruct _poly1305_core_key noattr)))
                                  (Tstruct _poly1305_core_key noattr))
                                _precomputed_s
                                (Tstruct _poly1305_key noattr))
                              18727075383868559167%positive
                              (Tunion __anon_ef6b4645c220 noattr)) _r (tarray tuint 5))
                          (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint))
                    (Ssequence
                      (Sset _s3
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Efield
                                (Efield
                                  (Ederef
                                    (Etempvar _key (tptr (Tstruct _poly1305_core_key noattr)))
                                    (Tstruct _poly1305_core_key noattr))
                                  _precomputed_s
                                  (Tstruct _poly1305_key noattr))
                                18727075383868559167%positive
                                (Tunion __anon_ef6b4645c220 noattr)) _r (tarray tuint 5))
                            (Econst_int (Int.repr 2) tint) (tptr tuint))
                          tuint))
                      (Ssequence
                        (Sset _s4
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Efield
                                  (Efield
                                    (Ederef
                                      (Etempvar _key (tptr (Tstruct _poly1305_core_key noattr)))
                                      (Tstruct _poly1305_core_key noattr))
                                    _precomputed_s
                                    (Tstruct _poly1305_key noattr))
                                  18727075383868559167%positive
                                  (Tunion __anon_ef6b4645c220 noattr)) _r (tarray tuint 5))
                              (Econst_int (Int.repr 3) tint) (tptr tuint))
                            tuint))
                        (Ssequence
                          (Sset _h0
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Efield
                                    (Ederef
                                      (Etempvar _state (tptr (Tstruct _poly1305_state noattr)))
                                      (Tstruct _poly1305_state noattr))
                                    18727075383868559167%positive
                                    (Tunion __anon_43224dacc2cf noattr)) _h
                                  (tarray tuint 5))
                                (Econst_int (Int.repr 0) tint) (tptr tuint))
                              tuint))
                          (Ssequence
                            (Sset _h1
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Efield
                                      (Ederef
                                        (Etempvar _state (tptr (Tstruct _poly1305_state noattr)))
                                        (Tstruct _poly1305_state noattr))
                                      18727075383868559167%positive
                                      (Tunion __anon_43224dacc2cf noattr)) _h
                                    (tarray tuint 5))
                                  (Econst_int (Int.repr 1) tint)
                                  (tptr tuint)) tuint))
                            (Ssequence
                              (Sset _h2
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Efield
                                        (Ederef
                                          (Etempvar _state (tptr (Tstruct _poly1305_state noattr)))
                                          (Tstruct _poly1305_state noattr))
                                        18727075383868559167%positive
                                        (Tunion __anon_43224dacc2cf noattr)) _h
                                      (tarray tuint 5))
                                    (Econst_int (Int.repr 2) tint)
                                    (tptr tuint)) tuint))
                              (Ssequence
                                (Sset _h3
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Efield
                                          (Ederef
                                            (Etempvar _state (tptr (Tstruct _poly1305_state noattr)))
                                            (Tstruct _poly1305_state noattr))
                                          18727075383868559167%positive
                                          (Tunion __anon_43224dacc2cf noattr)) _h
                                        (tarray tuint 5))
                                      (Econst_int (Int.repr 3) tint)
                                      (tptr tuint)) tuint))
                                (Ssequence
                                  (Sset _h4
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Efield
                                            (Ederef
                                              (Etempvar _state (tptr (Tstruct _poly1305_state noattr)))
                                              (Tstruct _poly1305_state noattr))
                                            18727075383868559167%positive
                                            (Tunion __anon_43224dacc2cf noattr)) _h
                                          (tarray tuint 5))
                                        (Econst_int (Int.repr 4) tint)
                                        (tptr tuint)) tuint))
                                  (Ssequence
                                    (Sloop
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'2)
                                            (Evar _get_unaligned_le32 
                                            (Tfunction ((tptr tvoid) :: nil)
                                              tuint cc_default))
                                            ((Ebinop Oadd
                                               (Etempvar _input (tptr tuchar))
                                               (Econst_int (Int.repr 0) tint)
                                               (tptr tuchar)) :: nil))
                                          (Sset _h0
                                            (Ebinop Oadd (Etempvar _h0 tuint)
                                              (Ebinop Oand
                                                (Etempvar _t'2 tuint)
                                                (Econst_int (Int.repr 67108863) tint)
                                                tuint) tuint)))
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'3)
                                              (Evar _get_unaligned_le32 
                                              (Tfunction
                                                ((tptr tvoid) :: nil) tuint
                                                cc_default))
                                              ((Ebinop Oadd
                                                 (Etempvar _input (tptr tuchar))
                                                 (Econst_int (Int.repr 3) tint)
                                                 (tptr tuchar)) :: nil))
                                            (Sset _h1
                                              (Ebinop Oadd
                                                (Etempvar _h1 tuint)
                                                (Ebinop Oand
                                                  (Ebinop Oshr
                                                    (Etempvar _t'3 tuint)
                                                    (Econst_int (Int.repr 2) tint)
                                                    tuint)
                                                  (Econst_int (Int.repr 67108863) tint)
                                                  tuint) tuint)))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'4)
                                                (Evar _get_unaligned_le32 
                                                (Tfunction
                                                  ((tptr tvoid) :: nil) tuint
                                                  cc_default))
                                                ((Ebinop Oadd
                                                   (Etempvar _input (tptr tuchar))
                                                   (Econst_int (Int.repr 6) tint)
                                                   (tptr tuchar)) :: nil))
                                              (Sset _h2
                                                (Ebinop Oadd
                                                  (Etempvar _h2 tuint)
                                                  (Ebinop Oand
                                                    (Ebinop Oshr
                                                      (Etempvar _t'4 tuint)
                                                      (Econst_int (Int.repr 4) tint)
                                                      tuint)
                                                    (Econst_int (Int.repr 67108863) tint)
                                                    tuint) tuint)))
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'5)
                                                  (Evar _get_unaligned_le32 
                                                  (Tfunction
                                                    ((tptr tvoid) :: nil)
                                                    tuint cc_default))
                                                  ((Ebinop Oadd
                                                     (Etempvar _input (tptr tuchar))
                                                     (Econst_int (Int.repr 9) tint)
                                                     (tptr tuchar)) :: nil))
                                                (Sset _h3
                                                  (Ebinop Oadd
                                                    (Etempvar _h3 tuint)
                                                    (Ebinop Oand
                                                      (Ebinop Oshr
                                                        (Etempvar _t'5 tuint)
                                                        (Econst_int (Int.repr 6) tint)
                                                        tuint)
                                                      (Econst_int (Int.repr 67108863) tint)
                                                      tuint) tuint)))
                                              (Ssequence
                                                (Ssequence
                                                  (Scall (Some _t'6)
                                                    (Evar _get_unaligned_le32 
                                                    (Tfunction
                                                      ((tptr tvoid) :: nil)
                                                      tuint cc_default))
                                                    ((Ebinop Oadd
                                                       (Etempvar _input (tptr tuchar))
                                                       (Econst_int (Int.repr 12) tint)
                                                       (tptr tuchar)) :: nil))
                                                  (Sset _h4
                                                    (Ebinop Oadd
                                                      (Etempvar _h4 tuint)
                                                      (Ebinop Oor
                                                        (Ebinop Oshr
                                                          (Etempvar _t'6 tuint)
                                                          (Econst_int (Int.repr 8) tint)
                                                          tuint)
                                                        (Etempvar _hibit tuint)
                                                        tuint) tuint)))
                                                (Ssequence
                                                  (Sset _d0
                                                    (Ebinop Oadd
                                                      (Ebinop Oadd
                                                        (Ebinop Oadd
                                                          (Ebinop Oadd
                                                            (Ebinop Omul
                                                              (Ecast
                                                                (Etempvar _h0 tuint)
                                                                tulong)
                                                              (Etempvar _r0 tuint)
                                                              tulong)
                                                            (Ebinop Omul
                                                              (Ecast
                                                                (Etempvar _h1 tuint)
                                                                tulong)
                                                              (Etempvar _s4 tuint)
                                                              tulong) tulong)
                                                          (Ebinop Omul
                                                            (Ecast
                                                              (Etempvar _h2 tuint)
                                                              tulong)
                                                            (Etempvar _s3 tuint)
                                                            tulong) tulong)
                                                        (Ebinop Omul
                                                          (Ecast
                                                            (Etempvar _h3 tuint)
                                                            tulong)
                                                          (Etempvar _s2 tuint)
                                                          tulong) tulong)
                                                      (Ebinop Omul
                                                        (Ecast
                                                          (Etempvar _h4 tuint)
                                                          tulong)
                                                        (Etempvar _s1 tuint)
                                                        tulong) tulong))
                                                  (Ssequence
                                                    (Sset _d1
                                                      (Ebinop Oadd
                                                        (Ebinop Oadd
                                                          (Ebinop Oadd
                                                            (Ebinop Oadd
                                                              (Ebinop Omul
                                                                (Ecast
                                                                  (Etempvar _h0 tuint)
                                                                  tulong)
                                                                (Etempvar _r1 tuint)
                                                                tulong)
                                                              (Ebinop Omul
                                                                (Ecast
                                                                  (Etempvar _h1 tuint)
                                                                  tulong)
                                                                (Etempvar _r0 tuint)
                                                                tulong)
                                                              tulong)
                                                            (Ebinop Omul
                                                              (Ecast
                                                                (Etempvar _h2 tuint)
                                                                tulong)
                                                              (Etempvar _s4 tuint)
                                                              tulong) tulong)
                                                          (Ebinop Omul
                                                            (Ecast
                                                              (Etempvar _h3 tuint)
                                                              tulong)
                                                            (Etempvar _s3 tuint)
                                                            tulong) tulong)
                                                        (Ebinop Omul
                                                          (Ecast
                                                            (Etempvar _h4 tuint)
                                                            tulong)
                                                          (Etempvar _s2 tuint)
                                                          tulong) tulong))
                                                    (Ssequence
                                                      (Sset _d2
                                                        (Ebinop Oadd
                                                          (Ebinop Oadd
                                                            (Ebinop Oadd
                                                              (Ebinop Oadd
                                                                (Ebinop Omul
                                                                  (Ecast
                                                                    (Etempvar _h0 tuint)
                                                                    tulong)
                                                                  (Etempvar _r2 tuint)
                                                                  tulong)
                                                                (Ebinop Omul
                                                                  (Ecast
                                                                    (Etempvar _h1 tuint)
                                                                    tulong)
                                                                  (Etempvar _r1 tuint)
                                                                  tulong)
                                                                tulong)
                                                              (Ebinop Omul
                                                                (Ecast
                                                                  (Etempvar _h2 tuint)
                                                                  tulong)
                                                                (Etempvar _r0 tuint)
                                                                tulong)
                                                              tulong)
                                                            (Ebinop Omul
                                                              (Ecast
                                                                (Etempvar _h3 tuint)
                                                                tulong)
                                                              (Etempvar _s4 tuint)
                                                              tulong) tulong)
                                                          (Ebinop Omul
                                                            (Ecast
                                                              (Etempvar _h4 tuint)
                                                              tulong)
                                                            (Etempvar _s3 tuint)
                                                            tulong) tulong))
                                                      (Ssequence
                                                        (Sset _d3
                                                          (Ebinop Oadd
                                                            (Ebinop Oadd
                                                              (Ebinop Oadd
                                                                (Ebinop Oadd
                                                                  (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _h0 tuint)
                                                                    tulong)
                                                                    (Etempvar _r3 tuint)
                                                                    tulong)
                                                                  (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _h1 tuint)
                                                                    tulong)
                                                                    (Etempvar _r2 tuint)
                                                                    tulong)
                                                                  tulong)
                                                                (Ebinop Omul
                                                                  (Ecast
                                                                    (Etempvar _h2 tuint)
                                                                    tulong)
                                                                  (Etempvar _r1 tuint)
                                                                  tulong)
                                                                tulong)
                                                              (Ebinop Omul
                                                                (Ecast
                                                                  (Etempvar _h3 tuint)
                                                                  tulong)
                                                                (Etempvar _r0 tuint)
                                                                tulong)
                                                              tulong)
                                                            (Ebinop Omul
                                                              (Ecast
                                                                (Etempvar _h4 tuint)
                                                                tulong)
                                                              (Etempvar _s4 tuint)
                                                              tulong) tulong))
                                                        (Ssequence
                                                          (Sset _d4
                                                            (Ebinop Oadd
                                                              (Ebinop Oadd
                                                                (Ebinop Oadd
                                                                  (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _h0 tuint)
                                                                    tulong)
                                                                    (Etempvar _r4 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _h1 tuint)
                                                                    tulong)
                                                                    (Etempvar _r3 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                  (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _h2 tuint)
                                                                    tulong)
                                                                    (Etempvar _r2 tuint)
                                                                    tulong)
                                                                  tulong)
                                                                (Ebinop Omul
                                                                  (Ecast
                                                                    (Etempvar _h3 tuint)
                                                                    tulong)
                                                                  (Etempvar _r1 tuint)
                                                                  tulong)
                                                                tulong)
                                                              (Ebinop Omul
                                                                (Ecast
                                                                  (Etempvar _h4 tuint)
                                                                  tulong)
                                                                (Etempvar _r0 tuint)
                                                                tulong)
                                                              tulong))
                                                          (Ssequence
                                                            (Sset _c
                                                              (Ecast
                                                                (Ebinop Oshr
                                                                  (Etempvar _d0 tulong)
                                                                  (Econst_int (Int.repr 26) tint)
                                                                  tulong)
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _h0
                                                                (Ebinop Oand
                                                                  (Ecast
                                                                    (Etempvar _d0 tulong)
                                                                    tuint)
                                                                  (Econst_int (Int.repr 67108863) tint)
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _d1
                                                                  (Ebinop Oadd
                                                                    (Etempvar _d1 tulong)
                                                                    (Etempvar _c tuint)
                                                                    tulong))
                                                                (Ssequence
                                                                  (Sset _c
                                                                    (Ecast
                                                                    (Ebinop Oshr
                                                                    (Etempvar _d1 tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong)
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _h1
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _d1 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _d2
                                                                    (Ebinop Oadd
                                                                    (Etempvar _d2 tulong)
                                                                    (Etempvar _c tuint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _c
                                                                    (Ecast
                                                                    (Ebinop Oshr
                                                                    (Etempvar _d2 tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _h2
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _d2 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _d3
                                                                    (Ebinop Oadd
                                                                    (Etempvar _d3 tulong)
                                                                    (Etempvar _c tuint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _c
                                                                    (Ecast
                                                                    (Ebinop Oshr
                                                                    (Etempvar _d3 tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _h3
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _d3 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _d4
                                                                    (Ebinop Oadd
                                                                    (Etempvar _d4 tulong)
                                                                    (Etempvar _c tuint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _c
                                                                    (Ecast
                                                                    (Ebinop Oshr
                                                                    (Etempvar _d4 tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _h4
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _d4 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _h0
                                                                    (Ebinop Oadd
                                                                    (Etempvar _h0 tuint)
                                                                    (Ebinop Omul
                                                                    (Etempvar _c tuint)
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _c
                                                                    (Ebinop Oshr
                                                                    (Etempvar _h0 tuint)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _h0
                                                                    (Ebinop Oand
                                                                    (Etempvar _h0 tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _h1
                                                                    (Ebinop Oadd
                                                                    (Etempvar _h1 tuint)
                                                                    (Etempvar _c tuint)
                                                                    tuint))
                                                                    (Sset _input
                                                                    (Ebinop Oadd
                                                                    (Etempvar _input (tptr tuchar))
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    (tptr tuchar)))))))))))))))))))))))))))))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'1
                                            (Ecast
                                              (Ebinop Osub
                                                (Etempvar _nblocks tuint)
                                                (Econst_int (Int.repr 1) tint)
                                                tuint) tuint))
                                          (Sset _nblocks
                                            (Etempvar _t'1 tuint)))
                                        (Sifthenelse (Etempvar _t'1 tuint)
                                          Sskip
                                          Sbreak)))
                                    (Ssequence
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Efield
                                                (Ederef
                                                  (Etempvar _state (tptr (Tstruct _poly1305_state noattr)))
                                                  (Tstruct _poly1305_state noattr))
                                                18727075383868559167%positive
                                                (Tunion __anon_43224dacc2cf noattr)) _h
                                              (tarray tuint 5))
                                            (Econst_int (Int.repr 0) tint)
                                            (tptr tuint)) tuint)
                                        (Etempvar _h0 tuint))
                                      (Ssequence
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _state (tptr (Tstruct _poly1305_state noattr)))
                                                    (Tstruct _poly1305_state noattr))
                                                  18727075383868559167%positive
                                                  (Tunion __anon_43224dacc2cf noattr)) _h
                                                (tarray tuint 5))
                                              (Econst_int (Int.repr 1) tint)
                                              (tptr tuint)) tuint)
                                          (Etempvar _h1 tuint))
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _state (tptr (Tstruct _poly1305_state noattr)))
                                                      (Tstruct _poly1305_state noattr))
                                                    18727075383868559167%positive
                                                    (Tunion __anon_43224dacc2cf noattr)) _h
                                                  (tarray tuint 5))
                                                (Econst_int (Int.repr 2) tint)
                                                (tptr tuint)) tuint)
                                            (Etempvar _h2 tuint))
                                          (Ssequence
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Efield
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _state (tptr (Tstruct _poly1305_state noattr)))
                                                        (Tstruct _poly1305_state noattr))
                                                      18727075383868559167%positive
                                                      (Tunion __anon_43224dacc2cf noattr))
                                                    _h (tarray tuint 5))
                                                  (Econst_int (Int.repr 3) tint)
                                                  (tptr tuint)) tuint)
                                              (Etempvar _h3 tuint))
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Efield
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _state (tptr (Tstruct _poly1305_state noattr)))
                                                        (Tstruct _poly1305_state noattr))
                                                      18727075383868559167%positive
                                                      (Tunion __anon_43224dacc2cf noattr))
                                                    _h (tarray tuint 5))
                                                  (Econst_int (Int.repr 4) tint)
                                                  (tptr tuint)) tuint)
                                              (Etempvar _h4 tuint))))))))))))))))))))))))
|}.

Definition f_poly1305_core_emit := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_state, (tptr (Tstruct _poly1305_state noattr))) ::
                (_nonce, (tptr tuint)) :: (_dst, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_mac, (tptr tuchar)) :: (_h0, tuint) :: (_h1, tuint) ::
               (_h2, tuint) :: (_h3, tuint) :: (_h4, tuint) :: (_c, tuint) ::
               (_g0, tuint) :: (_g1, tuint) :: (_g2, tuint) ::
               (_g3, tuint) :: (_g4, tuint) :: (_f, tulong) ::
               (_mask, tuint) :: (_t'4, tuint) :: (_t'3, tuint) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _mac (Etempvar _dst (tptr tvoid)))
  (Ssequence
    (Sset _h0
      (Ederef
        (Ebinop Oadd
          (Efield
            (Efield
              (Ederef
                (Etempvar _state (tptr (Tstruct _poly1305_state noattr)))
                (Tstruct _poly1305_state noattr))
              18727075383868559167%positive (Tunion __anon_43224dacc2cf noattr)) _h
            (tarray tuint 5)) (Econst_int (Int.repr 0) tint) (tptr tuint))
        tuint))
    (Ssequence
      (Sset _h1
        (Ederef
          (Ebinop Oadd
            (Efield
              (Efield
                (Ederef
                  (Etempvar _state (tptr (Tstruct _poly1305_state noattr)))
                  (Tstruct _poly1305_state noattr))
                18727075383868559167%positive (Tunion __anon_43224dacc2cf noattr)) _h
              (tarray tuint 5)) (Econst_int (Int.repr 1) tint) (tptr tuint))
          tuint))
      (Ssequence
        (Sset _h2
          (Ederef
            (Ebinop Oadd
              (Efield
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _poly1305_state noattr)))
                    (Tstruct _poly1305_state noattr))
                  18727075383868559167%positive (Tunion __anon_43224dacc2cf noattr)) _h
                (tarray tuint 5)) (Econst_int (Int.repr 2) tint)
              (tptr tuint)) tuint))
        (Ssequence
          (Sset _h3
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Efield
                    (Ederef
                      (Etempvar _state (tptr (Tstruct _poly1305_state noattr)))
                      (Tstruct _poly1305_state noattr))
                    18727075383868559167%positive (Tunion __anon_43224dacc2cf noattr)) _h
                  (tarray tuint 5)) (Econst_int (Int.repr 3) tint)
                (tptr tuint)) tuint))
          (Ssequence
            (Sset _h4
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Efield
                      (Ederef
                        (Etempvar _state (tptr (Tstruct _poly1305_state noattr)))
                        (Tstruct _poly1305_state noattr))
                      18727075383868559167%positive (Tunion __anon_43224dacc2cf noattr)) _h
                    (tarray tuint 5)) (Econst_int (Int.repr 4) tint)
                  (tptr tuint)) tuint))
            (Ssequence
              (Sset _c
                (Ebinop Oshr (Etempvar _h1 tuint)
                  (Econst_int (Int.repr 26) tint) tuint))
              (Ssequence
                (Sset _h1
                  (Ebinop Oand (Etempvar _h1 tuint)
                    (Econst_int (Int.repr 67108863) tint) tuint))
                (Ssequence
                  (Sset _h2
                    (Ebinop Oadd (Etempvar _h2 tuint) (Etempvar _c tuint)
                      tuint))
                  (Ssequence
                    (Sset _c
                      (Ebinop Oshr (Etempvar _h2 tuint)
                        (Econst_int (Int.repr 26) tint) tuint))
                    (Ssequence
                      (Sset _h2
                        (Ebinop Oand (Etempvar _h2 tuint)
                          (Econst_int (Int.repr 67108863) tint) tuint))
                      (Ssequence
                        (Sset _h3
                          (Ebinop Oadd (Etempvar _h3 tuint)
                            (Etempvar _c tuint) tuint))
                        (Ssequence
                          (Sset _c
                            (Ebinop Oshr (Etempvar _h3 tuint)
                              (Econst_int (Int.repr 26) tint) tuint))
                          (Ssequence
                            (Sset _h3
                              (Ebinop Oand (Etempvar _h3 tuint)
                                (Econst_int (Int.repr 67108863) tint) tuint))
                            (Ssequence
                              (Sset _h4
                                (Ebinop Oadd (Etempvar _h4 tuint)
                                  (Etempvar _c tuint) tuint))
                              (Ssequence
                                (Sset _c
                                  (Ebinop Oshr (Etempvar _h4 tuint)
                                    (Econst_int (Int.repr 26) tint) tuint))
                                (Ssequence
                                  (Sset _h4
                                    (Ebinop Oand (Etempvar _h4 tuint)
                                      (Econst_int (Int.repr 67108863) tint)
                                      tuint))
                                  (Ssequence
                                    (Sset _h0
                                      (Ebinop Oadd (Etempvar _h0 tuint)
                                        (Ebinop Omul (Etempvar _c tuint)
                                          (Econst_int (Int.repr 5) tint)
                                          tuint) tuint))
                                    (Ssequence
                                      (Sset _c
                                        (Ebinop Oshr (Etempvar _h0 tuint)
                                          (Econst_int (Int.repr 26) tint)
                                          tuint))
                                      (Ssequence
                                        (Sset _h0
                                          (Ebinop Oand (Etempvar _h0 tuint)
                                            (Econst_int (Int.repr 67108863) tint)
                                            tuint))
                                        (Ssequence
                                          (Sset _h1
                                            (Ebinop Oadd (Etempvar _h1 tuint)
                                              (Etempvar _c tuint) tuint))
                                          (Ssequence
                                            (Sset _g0
                                              (Ebinop Oadd
                                                (Etempvar _h0 tuint)
                                                (Econst_int (Int.repr 5) tint)
                                                tuint))
                                            (Ssequence
                                              (Sset _c
                                                (Ebinop Oshr
                                                  (Etempvar _g0 tuint)
                                                  (Econst_int (Int.repr 26) tint)
                                                  tuint))
                                              (Ssequence
                                                (Sset _g0
                                                  (Ebinop Oand
                                                    (Etempvar _g0 tuint)
                                                    (Econst_int (Int.repr 67108863) tint)
                                                    tuint))
                                                (Ssequence
                                                  (Sset _g1
                                                    (Ebinop Oadd
                                                      (Etempvar _h1 tuint)
                                                      (Etempvar _c tuint)
                                                      tuint))
                                                  (Ssequence
                                                    (Sset _c
                                                      (Ebinop Oshr
                                                        (Etempvar _g1 tuint)
                                                        (Econst_int (Int.repr 26) tint)
                                                        tuint))
                                                    (Ssequence
                                                      (Sset _g1
                                                        (Ebinop Oand
                                                          (Etempvar _g1 tuint)
                                                          (Econst_int (Int.repr 67108863) tint)
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _g2
                                                          (Ebinop Oadd
                                                            (Etempvar _h2 tuint)
                                                            (Etempvar _c tuint)
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _c
                                                            (Ebinop Oshr
                                                              (Etempvar _g2 tuint)
                                                              (Econst_int (Int.repr 26) tint)
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _g2
                                                              (Ebinop Oand
                                                                (Etempvar _g2 tuint)
                                                                (Econst_int (Int.repr 67108863) tint)
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _g3
                                                                (Ebinop Oadd
                                                                  (Etempvar _h3 tuint)
                                                                  (Etempvar _c tuint)
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _c
                                                                  (Ebinop Oshr
                                                                    (Etempvar _g3 tuint)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tuint))
                                                                (Ssequence
                                                                  (Sset _g3
                                                                    (Ebinop Oand
                                                                    (Etempvar _g3 tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _g4
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Ebinop Oadd
                                                                    (Etempvar _h4 tuint)
                                                                    (Etempvar _c tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Econst_long (Int64.repr 1) tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong)
                                                                    tulong)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _mask
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshr
                                                                    (Etempvar _g4 tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Omul
                                                                    (Esizeof tuint tulong)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _g0
                                                                    (Ebinop Oand
                                                                    (Etempvar _g0 tuint)
                                                                    (Etempvar _mask tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _g1
                                                                    (Ebinop Oand
                                                                    (Etempvar _g1 tuint)
                                                                    (Etempvar _mask tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _g2
                                                                    (Ebinop Oand
                                                                    (Etempvar _g2 tuint)
                                                                    (Etempvar _mask tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _g3
                                                                    (Ebinop Oand
                                                                    (Etempvar _g3 tuint)
                                                                    (Etempvar _mask tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _g4
                                                                    (Ebinop Oand
                                                                    (Etempvar _g4 tuint)
                                                                    (Etempvar _mask tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _mask
                                                                    (Eunop Onotint
                                                                    (Etempvar _mask tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _h0
                                                                    (Ebinop Oor
                                                                    (Ebinop Oand
                                                                    (Etempvar _h0 tuint)
                                                                    (Etempvar _mask tuint)
                                                                    tuint)
                                                                    (Etempvar _g0 tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _h1
                                                                    (Ebinop Oor
                                                                    (Ebinop Oand
                                                                    (Etempvar _h1 tuint)
                                                                    (Etempvar _mask tuint)
                                                                    tuint)
                                                                    (Etempvar _g1 tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _h2
                                                                    (Ebinop Oor
                                                                    (Ebinop Oand
                                                                    (Etempvar _h2 tuint)
                                                                    (Etempvar _mask tuint)
                                                                    tuint)
                                                                    (Etempvar _g2 tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _h3
                                                                    (Ebinop Oor
                                                                    (Ebinop Oand
                                                                    (Etempvar _h3 tuint)
                                                                    (Etempvar _mask tuint)
                                                                    tuint)
                                                                    (Etempvar _g3 tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _h4
                                                                    (Ebinop Oor
                                                                    (Ebinop Oand
                                                                    (Etempvar _h4 tuint)
                                                                    (Etempvar _mask tuint)
                                                                    tuint)
                                                                    (Etempvar _g4 tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _h0
                                                                    (Ebinop Oand
                                                                    (Ebinop Oor
                                                                    (Etempvar _h0 tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _h1 tuint)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr (-1)) tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _h1
                                                                    (Ebinop Oand
                                                                    (Ebinop Oor
                                                                    (Ebinop Oshr
                                                                    (Etempvar _h1 tuint)
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _h2 tuint)
                                                                    (Econst_int (Int.repr 20) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr (-1)) tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _h2
                                                                    (Ebinop Oand
                                                                    (Ebinop Oor
                                                                    (Ebinop Oshr
                                                                    (Etempvar _h2 tuint)
                                                                    (Econst_int (Int.repr 12) tint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _h3 tuint)
                                                                    (Econst_int (Int.repr 14) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr (-1)) tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _h3
                                                                    (Ebinop Oand
                                                                    (Ebinop Oor
                                                                    (Ebinop Oshr
                                                                    (Etempvar _h3 tuint)
                                                                    (Econst_int (Int.repr 18) tint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _h4 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr (-1)) tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _nonce (tptr tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'4
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _nonce (tptr tuint))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sset _f
                                                                    (Ebinop Oadd
                                                                    (Ecast
                                                                    (Etempvar _h0 tuint)
                                                                    tulong)
                                                                    (Etempvar _t'4 tuint)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Sset _h0
                                                                    (Ecast
                                                                    (Etempvar _f tulong)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'3
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _nonce (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sset _f
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ecast
                                                                    (Etempvar _h1 tuint)
                                                                    tulong)
                                                                    (Etempvar _t'3 tuint)
                                                                    tulong)
                                                                    (Ebinop Oshr
                                                                    (Etempvar _f tulong)
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    tulong)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Sset _h1
                                                                    (Ecast
                                                                    (Etempvar _f tulong)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'2
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _nonce (tptr tuint))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sset _f
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ecast
                                                                    (Etempvar _h2 tuint)
                                                                    tulong)
                                                                    (Etempvar _t'2 tuint)
                                                                    tulong)
                                                                    (Ebinop Oshr
                                                                    (Etempvar _f tulong)
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    tulong)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Sset _h2
                                                                    (Ecast
                                                                    (Etempvar _f tulong)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'1
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _nonce (tptr tuint))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sset _f
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ecast
                                                                    (Etempvar _h3 tuint)
                                                                    tulong)
                                                                    (Etempvar _t'1 tuint)
                                                                    tulong)
                                                                    (Ebinop Oshr
                                                                    (Etempvar _f tulong)
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    tulong)
                                                                    tulong)))
                                                                    (Sset _h3
                                                                    (Ecast
                                                                    (Etempvar _f tulong)
                                                                    tuint)))))))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _put_unaligned_le32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    (tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _h0 tuint) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _mac (tptr tuchar))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuchar)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _put_unaligned_le32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    (tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _h1 tuint) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _mac (tptr tuchar))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuchar)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _put_unaligned_le32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    (tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _h2 tuint) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _mac (tptr tuchar))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuchar)) ::
                                                                    nil))
                                                                    (Scall None
                                                                    (Evar _put_unaligned_le32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    (tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _h3 tuint) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _mac (tptr tuchar))
                                                                    (Econst_int (Int.repr 12) tint)
                                                                    (tptr tuchar)) ::
                                                                    nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))
|}.

Definition composites : list composite_definition :=
(Composite __anon_ef6b4645c220 Union
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
 (_get_unaligned_le32, Gfun(Internal f_get_unaligned_le32)) ::
 (_put_unaligned_le32, Gfun(Internal f_put_unaligned_le32)) ::
 (_poly1305_core_setkey, Gfun(Internal f_poly1305_core_setkey)) ::
 (_poly1305_core_blocks, Gfun(Internal f_poly1305_core_blocks)) ::
 (_poly1305_core_emit, Gfun(Internal f_poly1305_core_emit)) :: nil).

Definition public_idents : list ident :=
(_poly1305_core_emit :: _poly1305_core_blocks :: _poly1305_core_setkey ::
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


