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
  Definition source_file := "lib/crypto/poly1305.c".
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
Definition _b : ident := $"b".
Definition _buf : ident := $"buf".
Definition _buflen : ident := $"buflen".
Definition _bulk_len : ident := $"bulk_len".
Definition _core_r : ident := $"core_r".
Definition _desc : ident := $"desc".
Definition _digest : ident := $"digest".
Definition _dst : ident := $"dst".
Definition _get_unaligned_le32 : ident := $"get_unaligned_le32".
Definition _h : ident := $"h".
Definition _h64 : ident := $"h64".
Definition _key : ident := $"key".
Definition _l : ident := $"l".
Definition _len : ident := $"len".
Definition _main : ident := $"main".
Definition _memcpy : ident := $"memcpy".
Definition _memset : ident := $"memset".
Definition _nbytes : ident := $"nbytes".
Definition _nonce : ident := $"nonce".
Definition _opaque_r : ident := $"opaque_r".
Definition _p : ident := $"p".
Definition _padbit : ident := $"padbit".
Definition _poly1305_block_init_generic : ident := $"poly1305_block_init_generic".
Definition _poly1305_block_state : ident := $"poly1305_block_state".
Definition _poly1305_blocks_generic : ident := $"poly1305_blocks_generic".
Definition _poly1305_core_blocks : ident := $"poly1305_core_blocks".
Definition _poly1305_core_emit : ident := $"poly1305_core_emit".
Definition _poly1305_core_init : ident := $"poly1305_core_init".
Definition _poly1305_core_key : ident := $"poly1305_core_key".
Definition _poly1305_core_setkey : ident := $"poly1305_core_setkey".
Definition _poly1305_desc_ctx : ident := $"poly1305_desc_ctx".
Definition _poly1305_emit_generic : ident := $"poly1305_emit_generic".
Definition _poly1305_final : ident := $"poly1305_final".
Definition _poly1305_init : ident := $"poly1305_init".
Definition _poly1305_key : ident := $"poly1305_key".
Definition _poly1305_state : ident := $"poly1305_state".
Definition _poly1305_update : ident := $"poly1305_update".
Definition _precomputed_s : ident := $"precomputed_s".
Definition _r : ident := $"r".
Definition _r64 : ident := $"r64".
Definition _raw_key : ident := $"raw_key".
Definition _s : ident := $"s".
Definition _src : ident := $"src".
Definition _state : ident := $"state".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.

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

Definition f_poly1305_core_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_state, (tptr (Tstruct _poly1305_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _memset (Tfunction ((tptr tvoid) :: tint :: tulong :: nil)
                  (tptr tvoid) cc_default))
  ((Etempvar _state (tptr (Tstruct _poly1305_state noattr))) ::
   (Econst_int (Int.repr 0) tint) ::
   (Esizeof (Tstruct _poly1305_state noattr) tulong) :: nil))
|}.

Definition f_poly1305_block_init_generic := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_desc, (tptr (Tstruct _poly1305_block_state noattr))) ::
                (_raw_key, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _poly1305_core_init (Tfunction
                                ((tptr (Tstruct _poly1305_state noattr)) ::
                                 nil) tvoid cc_default))
    ((Eaddrof
       (Efield
         (Ederef
           (Etempvar _desc (tptr (Tstruct _poly1305_block_state noattr)))
           (Tstruct _poly1305_block_state noattr)) _h
         (Tstruct _poly1305_state noattr))
       (tptr (Tstruct _poly1305_state noattr))) :: nil))
  (Scall None
    (Evar _poly1305_core_setkey (Tfunction
                                  ((tptr (Tstruct _poly1305_core_key noattr)) ::
                                   (tptr tuchar) :: nil) tvoid cc_default))
    ((Eaddrof
       (Efield
         (Efield
           (Ederef
             (Etempvar _desc (tptr (Tstruct _poly1305_block_state noattr)))
             (Tstruct _poly1305_block_state noattr))
           18727075383868559167%positive (Tunion __anon_472b2db33f49 noattr)) _core_r
         (Tstruct _poly1305_core_key noattr))
       (tptr (Tstruct _poly1305_core_key noattr))) ::
     (Etempvar _raw_key (tptr tuchar)) :: nil)))
|}.

Definition f_poly1305_blocks_generic := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_state, (tptr (Tstruct _poly1305_block_state noattr))) ::
                (_src, (tptr tuchar)) :: (_len, tuint) :: (_padbit, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _poly1305_core_blocks (Tfunction
                                ((tptr (Tstruct _poly1305_state noattr)) ::
                                 (tptr (Tstruct _poly1305_core_key noattr)) ::
                                 (tptr tvoid) :: tuint :: tuint :: nil) tvoid
                                cc_default))
  ((Eaddrof
     (Efield
       (Ederef
         (Etempvar _state (tptr (Tstruct _poly1305_block_state noattr)))
         (Tstruct _poly1305_block_state noattr)) _h
       (Tstruct _poly1305_state noattr))
     (tptr (Tstruct _poly1305_state noattr))) ::
   (Eaddrof
     (Efield
       (Efield
         (Ederef
           (Etempvar _state (tptr (Tstruct _poly1305_block_state noattr)))
           (Tstruct _poly1305_block_state noattr))
         18727075383868559167%positive (Tunion __anon_472b2db33f49 noattr)) _core_r
       (Tstruct _poly1305_core_key noattr))
     (tptr (Tstruct _poly1305_core_key noattr))) ::
   (Etempvar _src (tptr tuchar)) ::
   (Ebinop Odiv (Etempvar _len tuint) (Econst_int (Int.repr 16) tint) tuint) ::
   (Etempvar _padbit tuint) :: nil))
|}.

Definition f_poly1305_emit_generic := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_state, (tptr (Tstruct _poly1305_state noattr))) ::
                (_digest, (tptr tuchar)) :: (_nonce, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _poly1305_core_emit (Tfunction
                              ((tptr (Tstruct _poly1305_state noattr)) ::
                               (tptr tuint) :: (tptr tvoid) :: nil) tvoid
                              cc_default))
  ((Etempvar _state (tptr (Tstruct _poly1305_state noattr))) ::
   (Etempvar _nonce (tptr tuint)) :: (Etempvar _digest (tptr tuchar)) :: nil))
|}.

Definition f_poly1305_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_desc, (tptr (Tstruct _poly1305_desc_ctx noattr))) ::
                (_key, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'4, tuint) :: (_t'3, tuint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_unaligned_le32 (Tfunction ((tptr tvoid) :: nil) tuint
                                  cc_default))
      ((Ebinop Oadd (Etempvar _key (tptr tuchar))
         (Econst_int (Int.repr 16) tint) (tptr tuchar)) :: nil))
    (Sassign
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef
              (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
              (Tstruct _poly1305_desc_ctx noattr)) _s (tarray tuint 4))
          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
      (Etempvar _t'1 tuint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _get_unaligned_le32 (Tfunction ((tptr tvoid) :: nil) tuint
                                    cc_default))
        ((Ebinop Oadd (Etempvar _key (tptr tuchar))
           (Econst_int (Int.repr 20) tint) (tptr tuchar)) :: nil))
      (Sassign
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef
                (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
                (Tstruct _poly1305_desc_ctx noattr)) _s (tarray tuint 4))
            (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint)
        (Etempvar _t'2 tuint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _get_unaligned_le32 (Tfunction ((tptr tvoid) :: nil) tuint
                                      cc_default))
          ((Ebinop Oadd (Etempvar _key (tptr tuchar))
             (Econst_int (Int.repr 24) tint) (tptr tuchar)) :: nil))
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef
                  (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
                  (Tstruct _poly1305_desc_ctx noattr)) _s (tarray tuint 4))
              (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint)
          (Etempvar _t'3 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _get_unaligned_le32 (Tfunction ((tptr tvoid) :: nil) tuint
                                        cc_default))
            ((Ebinop Oadd (Etempvar _key (tptr tuchar))
               (Econst_int (Int.repr 28) tint) (tptr tuchar)) :: nil))
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
                    (Tstruct _poly1305_desc_ctx noattr)) _s (tarray tuint 4))
                (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint)
            (Etempvar _t'4 tuint)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef
                (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
                (Tstruct _poly1305_desc_ctx noattr)) _buflen tuint)
            (Econst_int (Int.repr 0) tint))
          (Scall None
            (Evar _poly1305_block_init_generic (Tfunction
                                                 ((tptr (Tstruct _poly1305_block_state noattr)) ::
                                                  (tptr tuchar) :: nil) tvoid
                                                 cc_default))
            ((Eaddrof
               (Efield
                 (Ederef
                   (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
                   (Tstruct _poly1305_desc_ctx noattr)) _state
                 (Tstruct _poly1305_block_state noattr))
               (tptr (Tstruct _poly1305_block_state noattr))) ::
             (Etempvar _key (tptr tuchar)) :: nil)))))))
|}.

Definition f_poly1305_update := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_desc, (tptr (Tstruct _poly1305_desc_ctx noattr))) ::
                (_src, (tptr tuchar)) :: (_nbytes, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, tuint) :: (_bulk_len, tuint) :: (_t'1, tulong) ::
               (_t'7, tuint) :: (_t'6, tuint) :: (_t'5, tuint) ::
               (_t'4, tuint) :: (_t'3, tuint) :: (_t'2, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'4
      (Efield
        (Ederef (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
          (Tstruct _poly1305_desc_ctx noattr)) _buflen tuint))
    (Sifthenelse (Ebinop Oge (Etempvar _nbytes tulong)
                   (Ebinop Osub (Econst_int (Int.repr 16) tint)
                     (Etempvar _t'4 tuint) tuint) tint)
      (Ssequence
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef
                (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
                (Tstruct _poly1305_desc_ctx noattr)) _buflen tuint))
          (Sifthenelse (Etempvar _t'5 tuint)
            (Ssequence
              (Ssequence
                (Sset _t'7
                  (Efield
                    (Ederef
                      (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
                      (Tstruct _poly1305_desc_ctx noattr)) _buflen tuint))
                (Sset _l
                  (Ebinop Osub (Econst_int (Int.repr 16) tint)
                    (Etempvar _t'7 tuint) tuint)))
              (Ssequence
                (Ssequence
                  (Sset _t'6
                    (Efield
                      (Ederef
                        (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
                        (Tstruct _poly1305_desc_ctx noattr)) _buflen tuint))
                  (Scall None
                    (Evar _memcpy (Tfunction
                                    ((tptr tvoid) :: (tptr tvoid) ::
                                     tulong :: nil) (tptr tvoid) cc_default))
                    ((Ebinop Oadd
                       (Efield
                         (Ederef
                           (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
                           (Tstruct _poly1305_desc_ctx noattr)) _buf
                         (tarray tuchar 16)) (Etempvar _t'6 tuint)
                       (tptr tuchar)) :: (Etempvar _src (tptr tuchar)) ::
                     (Etempvar _l tuint) :: nil)))
                (Ssequence
                  (Sset _src
                    (Ebinop Oadd (Etempvar _src (tptr tuchar))
                      (Etempvar _l tuint) (tptr tuchar)))
                  (Ssequence
                    (Sset _nbytes
                      (Ebinop Osub (Etempvar _nbytes tulong)
                        (Etempvar _l tuint) tulong))
                    (Ssequence
                      (Scall None
                        (Evar _poly1305_blocks_generic (Tfunction
                                                         ((tptr (Tstruct _poly1305_block_state noattr)) ::
                                                          (tptr tuchar) ::
                                                          tuint :: tuint ::
                                                          nil) tvoid
                                                         cc_default))
                        ((Eaddrof
                           (Efield
                             (Ederef
                               (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
                               (Tstruct _poly1305_desc_ctx noattr)) _state
                             (Tstruct _poly1305_block_state noattr))
                           (tptr (Tstruct _poly1305_block_state noattr))) ::
                         (Efield
                           (Ederef
                             (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
                             (Tstruct _poly1305_desc_ctx noattr)) _buf
                           (tarray tuchar 16)) ::
                         (Econst_int (Int.repr 16) tint) ::
                         (Econst_int (Int.repr 1) tint) :: nil))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
                            (Tstruct _poly1305_desc_ctx noattr)) _buflen
                          tuint) (Econst_int (Int.repr 0) tint)))))))
            Sskip))
        (Swhile
          (Ebinop Oge (Etempvar _nbytes tulong)
            (Econst_int (Int.repr 16) tint) tint)
          (Ssequence
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _nbytes tulong)
                             (Eunop Onotint (Econst_int (Int.repr 0) tuint)
                               tuint) tint)
                (Sset _t'1 (Ecast (Etempvar _nbytes tulong) tulong))
                (Sset _t'1
                  (Ecast
                    (Eunop Onotint (Econst_int (Int.repr 0) tuint) tuint)
                    tulong)))
              (Sset _bulk_len
                (Ecast
                  (Ebinop Oand (Etempvar _t'1 tulong)
                    (Eunop Onotint
                      (Ebinop Osub (Econst_int (Int.repr 16) tint)
                        (Econst_int (Int.repr 1) tint) tint) tint) tulong)
                  tuint)))
            (Ssequence
              (Scall None
                (Evar _poly1305_blocks_generic (Tfunction
                                                 ((tptr (Tstruct _poly1305_block_state noattr)) ::
                                                  (tptr tuchar) :: tuint ::
                                                  tuint :: nil) tvoid
                                                 cc_default))
                ((Eaddrof
                   (Efield
                     (Ederef
                       (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
                       (Tstruct _poly1305_desc_ctx noattr)) _state
                     (Tstruct _poly1305_block_state noattr))
                   (tptr (Tstruct _poly1305_block_state noattr))) ::
                 (Etempvar _src (tptr tuchar)) ::
                 (Etempvar _bulk_len tuint) ::
                 (Econst_int (Int.repr 1) tint) :: nil))
              (Ssequence
                (Sset _src
                  (Ebinop Oadd (Etempvar _src (tptr tuchar))
                    (Etempvar _bulk_len tuint) (tptr tuchar)))
                (Sset _nbytes
                  (Ebinop Osub (Etempvar _nbytes tulong)
                    (Etempvar _bulk_len tuint) tulong)))))))
      Sskip))
  (Sifthenelse (Etempvar _nbytes tulong)
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef
              (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
              (Tstruct _poly1305_desc_ctx noattr)) _buflen tuint))
        (Scall None
          (Evar _memcpy (Tfunction
                          ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil)
                          (tptr tvoid) cc_default))
          ((Ebinop Oadd
             (Efield
               (Ederef
                 (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
                 (Tstruct _poly1305_desc_ctx noattr)) _buf
               (tarray tuchar 16)) (Etempvar _t'3 tuint) (tptr tuchar)) ::
           (Etempvar _src (tptr tuchar)) :: (Etempvar _nbytes tulong) :: nil)))
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef
              (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
              (Tstruct _poly1305_desc_ctx noattr)) _buflen tuint))
        (Sassign
          (Efield
            (Ederef
              (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
              (Tstruct _poly1305_desc_ctx noattr)) _buflen tuint)
          (Ebinop Oadd (Etempvar _t'2 tuint) (Etempvar _nbytes tulong)
            tulong))))
    Sskip))
|}.

Definition f_poly1305_final := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_desc, (tptr (Tstruct _poly1305_desc_ctx noattr))) ::
                (_dst, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tuint) :: (_t'4, tuint) :: (_t'3, tuint) ::
               (_t'2, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
          (Tstruct _poly1305_desc_ctx noattr)) _buflen tuint))
    (Sifthenelse (Etempvar _t'2 tuint)
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef
                  (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
                  (Tstruct _poly1305_desc_ctx noattr)) _buflen tuint))
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
                  (Tstruct _poly1305_desc_ctx noattr)) _buflen tuint)
              (Ebinop Oadd (Etempvar _t'1 tuint)
                (Econst_int (Int.repr 1) tint) tuint)))
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
                    (Tstruct _poly1305_desc_ctx noattr)) _buf
                  (tarray tuchar 16)) (Etempvar _t'1 tuint) (tptr tuchar))
              tuchar) (Econst_int (Int.repr 1) tint)))
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef
                  (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
                  (Tstruct _poly1305_desc_ctx noattr)) _buflen tuint))
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef
                    (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
                    (Tstruct _poly1305_desc_ctx noattr)) _buflen tuint))
              (Scall None
                (Evar _memset (Tfunction
                                ((tptr tvoid) :: tint :: tulong :: nil)
                                (tptr tvoid) cc_default))
                ((Ebinop Oadd
                   (Efield
                     (Ederef
                       (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
                       (Tstruct _poly1305_desc_ctx noattr)) _buf
                     (tarray tuchar 16)) (Etempvar _t'3 tuint) (tptr tuchar)) ::
                 (Econst_int (Int.repr 0) tint) ::
                 (Ebinop Osub (Econst_int (Int.repr 16) tint)
                   (Etempvar _t'4 tuint) tuint) :: nil))))
          (Scall None
            (Evar _poly1305_blocks_generic (Tfunction
                                             ((tptr (Tstruct _poly1305_block_state noattr)) ::
                                              (tptr tuchar) :: tuint ::
                                              tuint :: nil) tvoid cc_default))
            ((Eaddrof
               (Efield
                 (Ederef
                   (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
                   (Tstruct _poly1305_desc_ctx noattr)) _state
                 (Tstruct _poly1305_block_state noattr))
               (tptr (Tstruct _poly1305_block_state noattr))) ::
             (Efield
               (Ederef
                 (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
                 (Tstruct _poly1305_desc_ctx noattr)) _buf
               (tarray tuchar 16)) :: (Econst_int (Int.repr 16) tint) ::
             (Econst_int (Int.repr 0) tint) :: nil))))
      Sskip))
  (Ssequence
    (Scall None
      (Evar _poly1305_emit_generic (Tfunction
                                     ((tptr (Tstruct _poly1305_state noattr)) ::
                                      (tptr tuchar) :: (tptr tuint) :: nil)
                                     tvoid cc_default))
      ((Eaddrof
         (Efield
           (Efield
             (Ederef
               (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
               (Tstruct _poly1305_desc_ctx noattr)) _state
             (Tstruct _poly1305_block_state noattr)) _h
           (Tstruct _poly1305_state noattr))
         (tptr (Tstruct _poly1305_state noattr))) ::
       (Etempvar _dst (tptr tuchar)) ::
       (Efield
         (Ederef (Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr)))
           (Tstruct _poly1305_desc_ctx noattr)) _s (tarray tuint 4)) :: nil))
    (Scall None
      (Evar _memset (Tfunction ((tptr tvoid) :: tint :: tulong :: nil)
                      (tptr tvoid) cc_default))
      ((Etempvar _desc (tptr (Tstruct _poly1305_desc_ctx noattr))) ::
       (Econst_int (Int.repr 0) tint) ::
       (Esizeof (Tstruct _poly1305_desc_ctx noattr) tulong) :: nil))))
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
 (_get_unaligned_le32, Gfun(Internal f_get_unaligned_le32)) ::
 (_poly1305_core_setkey,
   Gfun(External (EF_external "poly1305_core_setkey"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default))
     ((tptr (Tstruct _poly1305_core_key noattr)) :: (tptr tuchar) :: nil)
     tvoid cc_default)) ::
 (_poly1305_core_init, Gfun(Internal f_poly1305_core_init)) ::
 (_poly1305_core_blocks,
   Gfun(External (EF_external "poly1305_core_blocks"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xptr :: AST.Xint ::
                      AST.Xint :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _poly1305_state noattr)) ::
      (tptr (Tstruct _poly1305_core_key noattr)) :: (tptr tvoid) :: tuint ::
      tuint :: nil) tvoid cc_default)) ::
 (_poly1305_core_emit,
   Gfun(External (EF_external "poly1305_core_emit"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xptr :: nil)
                     AST.Xvoid cc_default))
     ((tptr (Tstruct _poly1305_state noattr)) :: (tptr tuint) ::
      (tptr tvoid) :: nil) tvoid cc_default)) ::
 (_poly1305_block_init_generic, Gfun(Internal f_poly1305_block_init_generic)) ::
 (_poly1305_blocks_generic, Gfun(Internal f_poly1305_blocks_generic)) ::
 (_poly1305_emit_generic, Gfun(Internal f_poly1305_emit_generic)) ::
 (_poly1305_init, Gfun(Internal f_poly1305_init)) ::
 (_poly1305_update, Gfun(Internal f_poly1305_update)) ::
 (_poly1305_final, Gfun(Internal f_poly1305_final)) :: nil).

Definition public_idents : list ident :=
(_poly1305_final :: _poly1305_update :: _poly1305_init ::
 _poly1305_core_emit :: _poly1305_core_blocks :: _poly1305_core_setkey ::
 _memset :: _memcpy :: ___builtin_debug :: ___builtin_write32_reversed ::
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


