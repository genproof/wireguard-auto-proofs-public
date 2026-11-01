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
  Definition source_file := "harness/x_transport_order.c".
  Definition normalized := true.
End Info.

Definition _L : ident := $"L".
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
Definition ___gp_spinlock_t : ident := $"__gp_spinlock_t".
Definition _a : ident := $"a".
Definition _ad : ident := $"ad".
Definition _adlen : ident := $"adlen".
Definition _b : ident := $"b".
Definition _backtrack : ident := $"backtrack".
Definition _blk : ident := $"blk".
Definition _bytes_copy : ident := $"bytes_copy".
Definition _bytes_eq : ident := $"bytes_eq".
Definition _bytes_set : ident := $"bytes_set".
Definition _c : ident := $"c".
Definition _chacha20poly1305_decrypt : ident := $"chacha20poly1305_decrypt".
Definition _chacha20poly1305_encrypt : ident := $"chacha20poly1305_encrypt".
Definition _check_failed : ident := $"check_failed".
Definition _counter : ident := $"counter".
Definition _ct : ident := $"ct".
Definition _ctlen : ident := $"ctlen".
Definition _ctr : ident := $"ctr".
Definition _d : ident := $"d".
Definition _draw_nonce : ident := $"draw_nonce".
Definition _draw_size : ident := $"draw_size".
Definition _draw_steps : ident := $"draw_steps".
Definition _draw_u64 : ident := $"draw_u64".
Definition _dst : ident := $"dst".
Definition _enc_len : ident := $"enc_len".
Definition _g : ident := $"g".
Definition _h : ident := $"h".
Definition _have_auth : ident := $"have_auth".
Definition _hi : ident := $"hi".
Definition _i : ident := $"i".
Definition _in : ident := $"in".
Definition _j : ident := $"j".
Definition _key : ident := $"key".
Definition _kind : ident := $"kind".
Definition _l : ident := $"l".
Definition _last_nonce : ident := $"last_nonce".
Definition _le32_load : ident := $"le32_load".
Definition _le32_store : ident := $"le32_store".
Definition _le64_store : ident := $"le64_store".
Definition _len : ident := $"len".
Definition _lens : ident := $"lens".
Definition _lock : ident := $"lock".
Definition _m : ident := $"m".
Definition _main : ident := $"main".
Definition _x_transport_order__minusp : ident := $"x_transport_order__minusp".
Definition _n : ident := $"n".
Definition _next : ident := $"next".
Definition _noise_replay_counter : ident := $"noise_replay_counter".
Definition _nonce : ident := $"nonce".
Definition _nondet_bytes : ident := $"nondet_bytes".
Definition _nondet_size : ident := $"nondet_size".
Definition _nondet_u32 : ident := $"nondet_u32".
Definition _nondet_u8 : ident := $"nondet_u8".
Definition _ok : ident := $"ok".
Definition _out : ident := $"out".
Definition _p : ident := $"p".
Definition _pkt : ident := $"pkt".
Definition _pos : ident := $"pos".
Definition _pred : ident := $"pred".
Definition _pt : ident := $"pt".
Definition _pt_out : ident := $"pt_out".
Definition _quickproof_free : ident := $"quickproof_free".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _r : ident := $"r".
Definition _rc : ident := $"rc".
Definition _rc_init : ident := $"rc_init".
Definition _rc_qr : ident := $"rc_qr".
Definition _rc_rotl : ident := $"rc_rotl".
Definition _rc_rounds : ident := $"rc_rounds".
Definition _rc_same : ident := $"rc_same".
Definition _rc_setup : ident := $"rc_setup".
Definition _rc_snap : ident := $"rc_snap".
Definition _rc_take : ident := $"rc_take".
Definition _ref_aead_decrypt : ident := $"ref_aead_decrypt".
Definition _ref_aead_tag : ident := $"ref_aead_tag".
Definition _ref_chacha20_block : ident := $"ref_chacha20_block".
Definition _ref_chacha20_xor : ident := $"ref_chacha20_xor".
Definition _ref_ok : ident := $"ref_ok".
Definition _ref_pt : ident := $"ref_pt".
Definition _rp_add : ident := $"rp_add".
Definition _rp_block : ident := $"rp_block".
Definition _rp_final : ident := $"rp_final".
Definition _rp_init : ident := $"rp_init".
Definition _rp_mul : ident := $"rp_mul".
Definition _rp_padded : ident := $"rp_padded".
Definition _rpoly : ident := $"rpoly".
Definition _s : ident := $"s".
Definition _set : ident := $"set".
Definition _snap : ident := $"snap".
Definition _src : ident := $"src".
Definition _steps : ident := $"steps".
Definition _tag : ident := $"tag".
Definition _top : ident := $"top".
Definition _tot : ident := $"tot".
Definition _u : ident := $"u".
Definition _unused : ident := $"unused".
Definition _v : ident := $"v".
Definition _w12 : ident := $"w12".
Definition _w13 : ident := $"w13".
Definition _w14 : ident := $"w14".
Definition _w15 : ident := $"w15".
Definition _wacc : ident := $"wacc".
Definition _wg_counter_validate : ident := $"wg_counter_validate".
Definition _wm : ident := $"wm".
Definition _wm_accepts : ident := $"wm_accepts".
Definition _wm_commit : ident := $"wm_commit".
Definition _wm_free : ident := $"wm_free".
Definition _wm_init : ident := $"wm_init".
Definition _wmodel : ident := $"wmodel".
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

Definition f_draw_steps := {|
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

Definition f_draw_u64 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_hi, tulong) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _nondet_u32 (Tfunction nil tuint cc_default))
      nil)
    (Sset _hi (Ecast (Etempvar _t'1 tuint) tulong)))
  (Ssequence
    (Scall (Some _t'2) (Evar _nondet_u32 (Tfunction nil tuint cc_default))
      nil)
    (Sreturn (Some (Ebinop Oor
                     (Ebinop Oshl (Etempvar _hi tulong)
                       (Econst_int (Int.repr 32) tint) tulong)
                     (Etempvar _t'2 tuint) tulong)))))
|}.

Definition f_le32_store := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tuchar)) :: (_v, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd (Etempvar _p (tptr tuchar)) (Econst_int (Int.repr 0) tint)
        (tptr tuchar)) tuchar) (Ecast (Etempvar _v tuint) tuchar))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar _p (tptr tuchar))
          (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar)
      (Ecast
        (Ebinop Oshr (Etempvar _v tuint) (Econst_int (Int.repr 8) tint)
          tuint) tuchar))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _p (tptr tuchar))
            (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar)
        (Ecast
          (Ebinop Oshr (Etempvar _v tuint) (Econst_int (Int.repr 16) tint)
            tuint) tuchar))
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _p (tptr tuchar))
            (Econst_int (Int.repr 3) tint) (tptr tuchar)) tuchar)
        (Ecast
          (Ebinop Oshr (Etempvar _v tuint) (Econst_int (Int.repr 24) tint)
            tuint) tuchar)))))
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

Definition f_le64_store := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tuchar)) :: (_v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _le32_store (Tfunction ((tptr tuchar) :: tuint :: nil) tvoid
                        cc_default))
    ((Etempvar _p (tptr tuchar)) :: (Ecast (Etempvar _v tulong) tuint) ::
     nil))
  (Scall None
    (Evar _le32_store (Tfunction ((tptr tuchar) :: tuint :: nil) tvoid
                        cc_default))
    ((Ebinop Oadd (Etempvar _p (tptr tuchar)) (Econst_int (Int.repr 4) tint)
       (tptr tuchar)) ::
     (Ecast
       (Ebinop Oshr (Etempvar _v tulong) (Econst_int (Int.repr 32) tint)
         tulong) tuint) :: nil)))
|}.

Definition f_rc_rotl := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_x, tuint) :: (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oor
                 (Ebinop Oshl (Etempvar _x tuint) (Etempvar _n tuint) tuint)
                 (Ebinop Oshr (Etempvar _x tuint)
                   (Ebinop Osub (Econst_int (Int.repr 32) tint)
                     (Etempvar _n tuint) tuint) tuint) tuint)))
|}.

Definition f_rc_qr := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tuint)) :: (_a, tint) :: (_b, tint) ::
                (_c, tint) :: (_d, tint) :: nil);
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
        (Ebinop Oadd (Etempvar _x (tptr tuint)) (Etempvar _a tint)
          (tptr tuint)) tuint))
    (Ssequence
      (Sset _t'20
        (Ederef
          (Ebinop Oadd (Etempvar _x (tptr tuint)) (Etempvar _b tint)
            (tptr tuint)) tuint))
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _x (tptr tuint)) (Etempvar _a tint)
            (tptr tuint)) tuint)
        (Ebinop Oadd (Etempvar _t'19 tuint) (Etempvar _t'20 tuint) tuint))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'17
          (Ederef
            (Ebinop Oadd (Etempvar _x (tptr tuint)) (Etempvar _d tint)
              (tptr tuint)) tuint))
        (Ssequence
          (Sset _t'18
            (Ederef
              (Ebinop Oadd (Etempvar _x (tptr tuint)) (Etempvar _a tint)
                (tptr tuint)) tuint))
          (Scall (Some _t'1)
            (Evar _rc_rotl (Tfunction (tuint :: tuint :: nil) tuint
                             cc_default))
            ((Ebinop Oxor (Etempvar _t'17 tuint) (Etempvar _t'18 tuint)
               tuint) :: (Econst_int (Int.repr 16) tint) :: nil))))
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _x (tptr tuint)) (Etempvar _d tint)
            (tptr tuint)) tuint) (Etempvar _t'1 tuint)))
    (Ssequence
      (Ssequence
        (Sset _t'15
          (Ederef
            (Ebinop Oadd (Etempvar _x (tptr tuint)) (Etempvar _c tint)
              (tptr tuint)) tuint))
        (Ssequence
          (Sset _t'16
            (Ederef
              (Ebinop Oadd (Etempvar _x (tptr tuint)) (Etempvar _d tint)
                (tptr tuint)) tuint))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _x (tptr tuint)) (Etempvar _c tint)
                (tptr tuint)) tuint)
            (Ebinop Oadd (Etempvar _t'15 tuint) (Etempvar _t'16 tuint) tuint))))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'13
              (Ederef
                (Ebinop Oadd (Etempvar _x (tptr tuint)) (Etempvar _b tint)
                  (tptr tuint)) tuint))
            (Ssequence
              (Sset _t'14
                (Ederef
                  (Ebinop Oadd (Etempvar _x (tptr tuint)) (Etempvar _c tint)
                    (tptr tuint)) tuint))
              (Scall (Some _t'2)
                (Evar _rc_rotl (Tfunction (tuint :: tuint :: nil) tuint
                                 cc_default))
                ((Ebinop Oxor (Etempvar _t'13 tuint) (Etempvar _t'14 tuint)
                   tuint) :: (Econst_int (Int.repr 12) tint) :: nil))))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _x (tptr tuint)) (Etempvar _b tint)
                (tptr tuint)) tuint) (Etempvar _t'2 tuint)))
        (Ssequence
          (Ssequence
            (Sset _t'11
              (Ederef
                (Ebinop Oadd (Etempvar _x (tptr tuint)) (Etempvar _a tint)
                  (tptr tuint)) tuint))
            (Ssequence
              (Sset _t'12
                (Ederef
                  (Ebinop Oadd (Etempvar _x (tptr tuint)) (Etempvar _b tint)
                    (tptr tuint)) tuint))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _x (tptr tuint)) (Etempvar _a tint)
                    (tptr tuint)) tuint)
                (Ebinop Oadd (Etempvar _t'11 tuint) (Etempvar _t'12 tuint)
                  tuint))))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'9
                  (Ederef
                    (Ebinop Oadd (Etempvar _x (tptr tuint))
                      (Etempvar _d tint) (tptr tuint)) tuint))
                (Ssequence
                  (Sset _t'10
                    (Ederef
                      (Ebinop Oadd (Etempvar _x (tptr tuint))
                        (Etempvar _a tint) (tptr tuint)) tuint))
                  (Scall (Some _t'3)
                    (Evar _rc_rotl (Tfunction (tuint :: tuint :: nil) tuint
                                     cc_default))
                    ((Ebinop Oxor (Etempvar _t'9 tuint)
                       (Etempvar _t'10 tuint) tuint) ::
                     (Econst_int (Int.repr 8) tint) :: nil))))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _x (tptr tuint)) (Etempvar _d tint)
                    (tptr tuint)) tuint) (Etempvar _t'3 tuint)))
            (Ssequence
              (Ssequence
                (Sset _t'7
                  (Ederef
                    (Ebinop Oadd (Etempvar _x (tptr tuint))
                      (Etempvar _c tint) (tptr tuint)) tuint))
                (Ssequence
                  (Sset _t'8
                    (Ederef
                      (Ebinop Oadd (Etempvar _x (tptr tuint))
                        (Etempvar _d tint) (tptr tuint)) tuint))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _x (tptr tuint))
                        (Etempvar _c tint) (tptr tuint)) tuint)
                    (Ebinop Oadd (Etempvar _t'7 tuint) (Etempvar _t'8 tuint)
                      tuint))))
              (Ssequence
                (Ssequence
                  (Sset _t'5
                    (Ederef
                      (Ebinop Oadd (Etempvar _x (tptr tuint))
                        (Etempvar _b tint) (tptr tuint)) tuint))
                  (Ssequence
                    (Sset _t'6
                      (Ederef
                        (Ebinop Oadd (Etempvar _x (tptr tuint))
                          (Etempvar _c tint) (tptr tuint)) tuint))
                    (Scall (Some _t'4)
                      (Evar _rc_rotl (Tfunction (tuint :: tuint :: nil) tuint
                                       cc_default))
                      ((Ebinop Oxor (Etempvar _t'5 tuint)
                         (Etempvar _t'6 tuint) tuint) ::
                       (Econst_int (Int.repr 7) tint) :: nil))))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _x (tptr tuint))
                      (Etempvar _b tint) (tptr tuint)) tuint)
                  (Etempvar _t'4 tuint))))))))))
|}.

Definition f_rc_rounds := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                     (Econst_int (Int.repr 10) tint) tint)
        Sskip
        Sbreak)
      (Ssequence
        (Scall None
          (Evar _rc_qr (Tfunction
                         ((tptr tuint) :: tint :: tint :: tint :: tint ::
                          nil) tvoid cc_default))
          ((Etempvar _x (tptr tuint)) :: (Econst_int (Int.repr 0) tint) ::
           (Econst_int (Int.repr 4) tint) ::
           (Econst_int (Int.repr 8) tint) ::
           (Econst_int (Int.repr 12) tint) :: nil))
        (Ssequence
          (Scall None
            (Evar _rc_qr (Tfunction
                           ((tptr tuint) :: tint :: tint :: tint :: tint ::
                            nil) tvoid cc_default))
            ((Etempvar _x (tptr tuint)) :: (Econst_int (Int.repr 1) tint) ::
             (Econst_int (Int.repr 5) tint) ::
             (Econst_int (Int.repr 9) tint) ::
             (Econst_int (Int.repr 13) tint) :: nil))
          (Ssequence
            (Scall None
              (Evar _rc_qr (Tfunction
                             ((tptr tuint) :: tint :: tint :: tint :: tint ::
                              nil) tvoid cc_default))
              ((Etempvar _x (tptr tuint)) ::
               (Econst_int (Int.repr 2) tint) ::
               (Econst_int (Int.repr 6) tint) ::
               (Econst_int (Int.repr 10) tint) ::
               (Econst_int (Int.repr 14) tint) :: nil))
            (Ssequence
              (Scall None
                (Evar _rc_qr (Tfunction
                               ((tptr tuint) :: tint :: tint :: tint ::
                                tint :: nil) tvoid cc_default))
                ((Etempvar _x (tptr tuint)) ::
                 (Econst_int (Int.repr 3) tint) ::
                 (Econst_int (Int.repr 7) tint) ::
                 (Econst_int (Int.repr 11) tint) ::
                 (Econst_int (Int.repr 15) tint) :: nil))
              (Ssequence
                (Scall None
                  (Evar _rc_qr (Tfunction
                                 ((tptr tuint) :: tint :: tint :: tint ::
                                  tint :: nil) tvoid cc_default))
                  ((Etempvar _x (tptr tuint)) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 5) tint) ::
                   (Econst_int (Int.repr 10) tint) ::
                   (Econst_int (Int.repr 15) tint) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _rc_qr (Tfunction
                                   ((tptr tuint) :: tint :: tint :: tint ::
                                    tint :: nil) tvoid cc_default))
                    ((Etempvar _x (tptr tuint)) ::
                     (Econst_int (Int.repr 1) tint) ::
                     (Econst_int (Int.repr 6) tint) ::
                     (Econst_int (Int.repr 11) tint) ::
                     (Econst_int (Int.repr 12) tint) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _rc_qr (Tfunction
                                     ((tptr tuint) :: tint :: tint :: tint ::
                                      tint :: nil) tvoid cc_default))
                      ((Etempvar _x (tptr tuint)) ::
                       (Econst_int (Int.repr 2) tint) ::
                       (Econst_int (Int.repr 7) tint) ::
                       (Econst_int (Int.repr 8) tint) ::
                       (Econst_int (Int.repr 13) tint) :: nil))
                    (Scall None
                      (Evar _rc_qr (Tfunction
                                     ((tptr tuint) :: tint :: tint :: tint ::
                                      tint :: nil) tvoid cc_default))
                      ((Etempvar _x (tptr tuint)) ::
                       (Econst_int (Int.repr 3) tint) ::
                       (Econst_int (Int.repr 4) tint) ::
                       (Econst_int (Int.repr 9) tint) ::
                       (Econst_int (Int.repr 14) tint) :: nil))))))))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_rc_setup := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr tuint)) :: (_key, (tptr tuchar)) ::
                (_w12, tuint) :: (_w13, tuint) :: (_w14, tuint) ::
                (_w15, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd (Etempvar _s (tptr tuint)) (Econst_int (Int.repr 0) tint)
        (tptr tuint)) tuint) (Econst_int (Int.repr 1634760805) tuint))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar _s (tptr tuint))
          (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint)
      (Econst_int (Int.repr 857760878) tuint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _s (tptr tuint))
            (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint)
        (Econst_int (Int.repr 2036477234) tuint))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _s (tptr tuint))
              (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint)
          (Econst_int (Int.repr 1797285236) tuint))
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
                  (Scall (Some _t'1)
                    (Evar _le32_load (Tfunction ((tptr tuchar) :: nil) tuint
                                       cc_default))
                    ((Ebinop Oadd (Etempvar _key (tptr tuchar))
                       (Ebinop Omul (Econst_int (Int.repr 4) tint)
                         (Etempvar _i tint) tint) (tptr tuchar)) :: nil))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _s (tptr tuint))
                        (Ebinop Oadd (Econst_int (Int.repr 4) tint)
                          (Etempvar _i tint) tint) (tptr tuint)) tuint)
                    (Etempvar _t'1 tuint))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _s (tptr tuint))
                  (Econst_int (Int.repr 12) tint) (tptr tuint)) tuint)
              (Etempvar _w12 tuint))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _s (tptr tuint))
                    (Econst_int (Int.repr 13) tint) (tptr tuint)) tuint)
                (Etempvar _w13 tuint))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _s (tptr tuint))
                      (Econst_int (Int.repr 14) tint) (tptr tuint)) tuint)
                  (Etempvar _w14 tuint))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _s (tptr tuint))
                      (Econst_int (Int.repr 15) tint) (tptr tuint)) tuint)
                  (Etempvar _w15 tuint))))))))))
|}.

Definition f_ref_chacha20_block := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) :: (_key, (tptr tuchar)) ::
                (_ctr, tuint) :: (_n, tulong) :: nil);
  fn_vars := ((_s, (tarray tuint 16)) :: (_x, (tarray tuint 16)) :: nil);
  fn_temps := ((_i, tint) :: (_t'3, tuint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _rc_setup (Tfunction
                      ((tptr tuint) :: (tptr tuchar) :: tuint :: tuint ::
                       tuint :: tuint :: nil) tvoid cc_default))
    ((Evar _s (tarray tuint 16)) :: (Etempvar _key (tptr tuchar)) ::
     (Etempvar _ctr tuint) :: (Econst_int (Int.repr 0) tint) ::
     (Ecast (Etempvar _n tulong) tuint) ::
     (Ecast
       (Ebinop Oshr (Etempvar _n tulong) (Econst_int (Int.repr 32) tint)
         tulong) tuint) :: nil))
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
            (Sset _t'3
              (Ederef
                (Ebinop Oadd (Evar _s (tarray tuint 16)) (Etempvar _i tint)
                  (tptr tuint)) tuint))
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _x (tarray tuint 16)) (Etempvar _i tint)
                  (tptr tuint)) tuint) (Etempvar _t'3 tuint))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Scall None
        (Evar _rc_rounds (Tfunction ((tptr tuint) :: nil) tvoid cc_default))
        ((Evar _x (tarray tuint 16)) :: nil))
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
                  (Ebinop Oadd (Evar _x (tarray tuint 16)) (Etempvar _i tint)
                    (tptr tuint)) tuint))
              (Ssequence
                (Sset _t'2
                  (Ederef
                    (Ebinop Oadd (Evar _s (tarray tuint 16))
                      (Etempvar _i tint) (tptr tuint)) tuint))
                (Scall None
                  (Evar _le32_store (Tfunction
                                      ((tptr tuchar) :: tuint :: nil) tvoid
                                      cc_default))
                  ((Ebinop Oadd (Etempvar _out (tptr tuchar))
                     (Ebinop Omul (Econst_int (Int.repr 4) tint)
                       (Etempvar _i tint) tint) (tptr tuchar)) ::
                   (Ebinop Oadd (Etempvar _t'1 tuint) (Etempvar _t'2 tuint)
                     tuint) :: nil)))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint)))))))
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

Definition f_rp_padded := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _rpoly noattr))) ::
                (_in, (tptr tuchar)) :: (_len, tulong) :: nil);
  fn_vars := ((_b, (tarray tuchar 16)) :: nil);
  fn_temps := ((_pos, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _pos (Ecast (Econst_int (Int.repr 0) tint) tulong))
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
          ((Etempvar _p (tptr (Tstruct _rpoly noattr))) ::
           (Ebinop Oadd (Etempvar _in (tptr tuchar)) (Etempvar _pos tulong)
             (tptr tuchar)) :: nil))
        (Sset _pos
          (Ebinop Oadd (Etempvar _pos tulong) (Econst_int (Int.repr 16) tint)
            tulong))))
    (Sifthenelse (Ebinop Ogt
                   (Ebinop Osub (Etempvar _len tulong) (Etempvar _pos tulong)
                     tulong) (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Scall None
          (Evar _bytes_set (Tfunction
                             ((tptr tuchar) :: tuchar :: tulong :: nil) tvoid
                             cc_default))
          ((Evar _b (tarray tuchar 16)) :: (Econst_int (Int.repr 0) tint) ::
           (Econst_int (Int.repr 16) tint) :: nil))
        (Ssequence
          (Scall None
            (Evar _bytes_copy (Tfunction
                                ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                                 nil) tvoid cc_default))
            ((Evar _b (tarray tuchar 16)) ::
             (Ebinop Oadd (Etempvar _in (tptr tuchar)) (Etempvar _pos tulong)
               (tptr tuchar)) ::
             (Ebinop Osub (Etempvar _len tulong) (Etempvar _pos tulong)
               tulong) :: nil))
          (Scall None
            (Evar _rp_block (Tfunction
                              ((tptr (Tstruct _rpoly noattr)) ::
                               (tptr tuchar) :: nil) tvoid cc_default))
            ((Etempvar _p (tptr (Tstruct _rpoly noattr))) ::
             (Evar _b (tarray tuchar 16)) :: nil))))
      Sskip)))
|}.

Definition v_x_transport_order__minusp := {|
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
       (Evar _x_transport_order__minusp (tarray tuint 17)) :: nil))
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

Definition f_ref_aead_tag := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_tag, (tptr tuchar)) :: (_key, (tptr tuchar)) ::
                (_nonce, tulong) :: (_ad, (tptr tuchar)) ::
                (_adlen, tulong) :: (_ct, (tptr tuchar)) ::
                (_ctlen, tulong) :: nil);
  fn_vars := ((_p, (Tstruct _rpoly noattr)) :: (_blk, (tarray tuchar 64)) ::
              (_lens, (tarray tuchar 16)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _ref_chacha20_block (Tfunction
                                ((tptr tuchar) :: (tptr tuchar) :: tuint ::
                                 tulong :: nil) tvoid cc_default))
    ((Evar _blk (tarray tuchar 64)) :: (Etempvar _key (tptr tuchar)) ::
     (Econst_int (Int.repr 0) tint) :: (Etempvar _nonce tulong) :: nil))
  (Ssequence
    (Scall None
      (Evar _rp_init (Tfunction
                       ((tptr (Tstruct _rpoly noattr)) :: (tptr tuchar) ::
                        nil) tvoid cc_default))
      ((Eaddrof (Evar _p (Tstruct _rpoly noattr))
         (tptr (Tstruct _rpoly noattr))) :: (Evar _blk (tarray tuchar 64)) ::
       nil))
    (Ssequence
      (Scall None
        (Evar _rp_padded (Tfunction
                           ((tptr (Tstruct _rpoly noattr)) ::
                            (tptr tuchar) :: tulong :: nil) tvoid cc_default))
        ((Eaddrof (Evar _p (Tstruct _rpoly noattr))
           (tptr (Tstruct _rpoly noattr))) :: (Etempvar _ad (tptr tuchar)) ::
         (Etempvar _adlen tulong) :: nil))
      (Ssequence
        (Scall None
          (Evar _rp_padded (Tfunction
                             ((tptr (Tstruct _rpoly noattr)) ::
                              (tptr tuchar) :: tulong :: nil) tvoid
                             cc_default))
          ((Eaddrof (Evar _p (Tstruct _rpoly noattr))
             (tptr (Tstruct _rpoly noattr))) ::
           (Etempvar _ct (tptr tuchar)) :: (Etempvar _ctlen tulong) :: nil))
        (Ssequence
          (Scall None
            (Evar _le64_store (Tfunction ((tptr tuchar) :: tulong :: nil)
                                tvoid cc_default))
            ((Evar _lens (tarray tuchar 16)) ::
             (Ecast (Etempvar _adlen tulong) tulong) :: nil))
          (Ssequence
            (Scall None
              (Evar _le64_store (Tfunction ((tptr tuchar) :: tulong :: nil)
                                  tvoid cc_default))
              ((Ebinop Oadd (Evar _lens (tarray tuchar 16))
                 (Econst_int (Int.repr 8) tint) (tptr tuchar)) ::
               (Ecast (Etempvar _ctlen tulong) tulong) :: nil))
            (Ssequence
              (Scall None
                (Evar _rp_block (Tfunction
                                  ((tptr (Tstruct _rpoly noattr)) ::
                                   (tptr tuchar) :: nil) tvoid cc_default))
                ((Eaddrof (Evar _p (Tstruct _rpoly noattr))
                   (tptr (Tstruct _rpoly noattr))) ::
                 (Evar _lens (tarray tuchar 16)) :: nil))
              (Scall None
                (Evar _rp_final (Tfunction
                                  ((tptr (Tstruct _rpoly noattr)) ::
                                   (tptr tuchar) :: nil) tvoid cc_default))
                ((Eaddrof (Evar _p (Tstruct _rpoly noattr))
                   (tptr (Tstruct _rpoly noattr))) ::
                 (Etempvar _tag (tptr tuchar)) :: nil)))))))))
|}.

Definition f_ref_chacha20_xor := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr tuchar)) :: (_src, (tptr tuchar)) ::
                (_len, tulong) :: (_key, (tptr tuchar)) ::
                (_nonce, tulong) :: nil);
  fn_vars := ((_blk, (tarray tuchar 64)) :: nil);
  fn_temps := ((_pos, tulong) :: (_i, tulong) :: (_ctr, tuint) ::
               (_t'1, tint) :: (_t'3, tuchar) :: (_t'2, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _pos (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Ssequence
    (Sset _ctr (Econst_int (Int.repr 1) tint))
    (Swhile
      (Ebinop Olt (Etempvar _pos tulong) (Etempvar _len tulong) tint)
      (Ssequence
        (Scall None
          (Evar _ref_chacha20_block (Tfunction
                                      ((tptr tuchar) :: (tptr tuchar) ::
                                       tuint :: tulong :: nil) tvoid
                                      cc_default))
          ((Evar _blk (tarray tuchar 64)) :: (Etempvar _key (tptr tuchar)) ::
           (Etempvar _ctr tuint) :: (Etempvar _nonce tulong) :: nil))
        (Ssequence
          (Ssequence
            (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
            (Sloop
              (Ssequence
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                                 (Econst_int (Int.repr 64) tint) tint)
                    (Sset _t'1
                      (Ecast
                        (Ebinop Olt
                          (Ebinop Oadd (Etempvar _pos tulong)
                            (Etempvar _i tulong) tulong)
                          (Etempvar _len tulong) tint) tbool))
                    (Sset _t'1 (Econst_int (Int.repr 0) tint)))
                  (Sifthenelse (Etempvar _t'1 tint) Sskip Sbreak))
                (Ssequence
                  (Sset _t'2
                    (Ederef
                      (Ebinop Oadd (Etempvar _src (tptr tuchar))
                        (Ebinop Oadd (Etempvar _pos tulong)
                          (Etempvar _i tulong) tulong) (tptr tuchar)) tuchar))
                  (Ssequence
                    (Sset _t'3
                      (Ederef
                        (Ebinop Oadd (Evar _blk (tarray tuchar 64))
                          (Etempvar _i tulong) (tptr tuchar)) tuchar))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Etempvar _dst (tptr tuchar))
                          (Ebinop Oadd (Etempvar _pos tulong)
                            (Etempvar _i tulong) tulong) (tptr tuchar))
                        tuchar)
                      (Ebinop Oxor (Etempvar _t'2 tuchar)
                        (Etempvar _t'3 tuchar) tint)))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tulong)
                  (Econst_int (Int.repr 1) tint) tulong))))
          (Ssequence
            (Sset _pos
              (Ebinop Oadd (Etempvar _pos tulong) (Etempvar _i tulong)
                tulong))
            (Sset _ctr
              (Ebinop Oadd (Etempvar _ctr tuint)
                (Econst_int (Int.repr 1) tint) tuint))))))))
|}.

Definition f_ref_aead_decrypt := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr tuchar)) :: (_src, (tptr tuchar)) ::
                (_len, tulong) :: (_ad, (tptr tuchar)) :: (_adlen, tulong) ::
                (_nonce, tulong) :: (_key, (tptr tuchar)) :: nil);
  fn_vars := ((_tag, (tarray tuchar 16)) :: nil);
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Olt (Etempvar _len tulong)
                 (Econst_int (Int.repr 16) tint) tint)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
    Sskip)
  (Ssequence
    (Scall None
      (Evar _ref_aead_tag (Tfunction
                            ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                             (tptr tuchar) :: tulong :: (tptr tuchar) ::
                             tulong :: nil) tvoid cc_default))
      ((Evar _tag (tarray tuchar 16)) :: (Etempvar _key (tptr tuchar)) ::
       (Etempvar _nonce tulong) :: (Etempvar _ad (tptr tuchar)) ::
       (Etempvar _adlen tulong) :: (Etempvar _src (tptr tuchar)) ::
       (Ebinop Osub (Etempvar _len tulong) (Econst_int (Int.repr 16) tint)
         tulong) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _bytes_eq (Tfunction
                            ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                            tint cc_default))
          ((Evar _tag (tarray tuchar 16)) ::
           (Ebinop Osub
             (Ebinop Oadd (Etempvar _src (tptr tuchar))
               (Etempvar _len tulong) (tptr tuchar))
             (Econst_int (Int.repr 16) tint) (tptr tuchar)) ::
           (Econst_int (Int.repr 16) tint) :: nil))
        (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
          Sskip))
      (Ssequence
        (Scall None
          (Evar _ref_chacha20_xor (Tfunction
                                    ((tptr tuchar) :: (tptr tuchar) ::
                                     tulong :: (tptr tuchar) :: tulong ::
                                     nil) tvoid cc_default))
          ((Etempvar _dst (tptr tuchar)) :: (Etempvar _src (tptr tuchar)) ::
           (Ebinop Osub (Etempvar _len tulong)
             (Econst_int (Int.repr 16) tint) tulong) ::
           (Etempvar _key (tptr tuchar)) :: (Etempvar _nonce tulong) :: nil))
        (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))
|}.

Definition f_wm_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_m, (tptr (Tstruct _wmodel noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _m (tptr (Tstruct _wmodel noattr)))
        (Tstruct _wmodel noattr)) _set (tptr (Tstruct _wacc noattr)))
    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Sassign
    (Efield
      (Ederef (Etempvar _m (tptr (Tstruct _wmodel noattr)))
        (Tstruct _wmodel noattr)) _top tulong)
    (Econst_int (Int.repr 0) tint)))
|}.

Definition f_wm_accepts := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_m, (tptr (Tstruct _wmodel noattr))) :: (_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_a, (tptr (Tstruct _wacc noattr))) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'5, tulong) :: (_t'4, tulong) ::
               (_t'3, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _a
      (Efield
        (Ederef (Etempvar _m (tptr (Tstruct _wmodel noattr)))
          (Tstruct _wmodel noattr)) _set (tptr (Tstruct _wacc noattr))))
    (Sloop
      (Ssequence
        (Sifthenelse (Etempvar _a (tptr (Tstruct _wacc noattr)))
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _a (tptr (Tstruct _wacc noattr)))
                (Tstruct _wacc noattr)) _n tulong))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'5 tulong)
                         (Etempvar _n tulong) tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
            Sskip)))
      (Sset _a
        (Efield
          (Ederef (Etempvar _a (tptr (Tstruct _wacc noattr)))
            (Tstruct _wacc noattr)) _next (tptr (Tstruct _wacc noattr))))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _m (tptr (Tstruct _wmodel noattr)))
              (Tstruct _wmodel noattr)) _top tulong))
        (Sifthenelse (Ebinop Olt (Etempvar _t'4 tulong)
                       (Ebinop Oadd
                         (Ebinop Osub
                           (Ebinop Osub
                             (Econst_long (Int64.repr (-1)) tulong)
                             (Econst_long (Int64.repr 8128) tulong) tulong)
                           (Econst_int (Int.repr 1) tint) tulong)
                         (Econst_int (Int.repr 1) tint) tulong) tint)
          (Sset _t'1
            (Ecast
              (Ebinop Olt (Etempvar _n tulong)
                (Ebinop Osub
                  (Ebinop Osub (Econst_long (Int64.repr (-1)) tulong)
                    (Econst_long (Int64.repr 8128) tulong) tulong)
                  (Econst_int (Int.repr 1) tint) tulong) tint) tbool))
          (Sset _t'1 (Econst_int (Int.repr 0) tint))))
      (Sifthenelse (Etempvar _t'1 tint)
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _m (tptr (Tstruct _wmodel noattr)))
                (Tstruct _wmodel noattr)) _top tulong))
          (Sset _t'2
            (Ecast
              (Ebinop Oge
                (Ebinop Oadd
                  (Ebinop Oadd (Etempvar _n tulong)
                    (Econst_int (Int.repr 1) tint) tulong)
                  (Econst_long (Int64.repr 8128) tulong) tulong)
                (Etempvar _t'3 tulong) tint) tbool)))
        (Sset _t'2 (Econst_int (Int.repr 0) tint))))
    (Sreturn (Some (Etempvar _t'2 tint)))))
|}.

Definition f_wm_commit := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_m, (tptr (Tstruct _wmodel noattr))) :: (_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_a, (tptr (Tstruct _wacc noattr))) ::
               (_l, (tptr (tptr (Tstruct _wacc noattr)))) ::
               (_t'1, (tptr tvoid)) ::
               (_t'9, (tptr (Tstruct _wacc noattr))) :: (_t'8, tulong) ::
               (_t'7, (tptr (Tstruct _wacc noattr))) ::
               (_t'6, (tptr (Tstruct _wacc noattr))) ::
               (_t'5, (tptr (Tstruct _wacc noattr))) :: (_t'4, tulong) ::
               (_t'3, tulong) :: (_t'2, (tptr (Tstruct _wacc noattr))) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _quickproof_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                 cc_default))
      ((Esizeof (Tstruct _wacc noattr) tulong) :: nil))
    (Sset _a (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _a (tptr (Tstruct _wacc noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _a (tptr (Tstruct _wacc noattr)))
            (Tstruct _wacc noattr)) _n tulong) (Etempvar _n tulong))
      (Ssequence
        (Ssequence
          (Sset _t'9
            (Efield
              (Ederef (Etempvar _m (tptr (Tstruct _wmodel noattr)))
                (Tstruct _wmodel noattr)) _set (tptr (Tstruct _wacc noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _a (tptr (Tstruct _wacc noattr)))
                (Tstruct _wacc noattr)) _next (tptr (Tstruct _wacc noattr)))
            (Etempvar _t'9 (tptr (Tstruct _wacc noattr)))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _m (tptr (Tstruct _wmodel noattr)))
                (Tstruct _wmodel noattr)) _set (tptr (Tstruct _wacc noattr)))
            (Etempvar _a (tptr (Tstruct _wacc noattr))))
          (Ssequence
            (Ssequence
              (Sset _t'8
                (Efield
                  (Ederef (Etempvar _m (tptr (Tstruct _wmodel noattr)))
                    (Tstruct _wmodel noattr)) _top tulong))
              (Sifthenelse (Ebinop Ogt
                             (Ebinop Oadd (Etempvar _n tulong)
                               (Econst_int (Int.repr 1) tint) tulong)
                             (Etempvar _t'8 tulong) tint)
                (Sassign
                  (Efield
                    (Ederef (Etempvar _m (tptr (Tstruct _wmodel noattr)))
                      (Tstruct _wmodel noattr)) _top tulong)
                  (Ebinop Oadd (Etempvar _n tulong)
                    (Econst_int (Int.repr 1) tint) tulong))
                Sskip))
            (Ssequence
              (Ssequence
                (Sset _l
                  (Eaddrof
                    (Efield
                      (Ederef (Etempvar _m (tptr (Tstruct _wmodel noattr)))
                        (Tstruct _wmodel noattr)) _set
                      (tptr (Tstruct _wacc noattr)))
                    (tptr (tptr (Tstruct _wacc noattr)))))
                (Sloop
                  (Ssequence
                    (Ssequence
                      (Sset _t'7
                        (Ederef
                          (Etempvar _l (tptr (tptr (Tstruct _wacc noattr))))
                          (tptr (Tstruct _wacc noattr))))
                      (Sifthenelse (Etempvar _t'7 (tptr (Tstruct _wacc noattr)))
                        Sskip
                        Sbreak))
                    (Ssequence
                      (Sset _t'2
                        (Ederef
                          (Etempvar _l (tptr (tptr (Tstruct _wacc noattr))))
                          (tptr (Tstruct _wacc noattr))))
                      (Ssequence
                        (Sset _t'3
                          (Efield
                            (Ederef
                              (Etempvar _t'2 (tptr (Tstruct _wacc noattr)))
                              (Tstruct _wacc noattr)) _n tulong))
                        (Ssequence
                          (Sset _t'4
                            (Efield
                              (Ederef
                                (Etempvar _m (tptr (Tstruct _wmodel noattr)))
                                (Tstruct _wmodel noattr)) _top tulong))
                          (Sifthenelse (Ebinop Olt
                                         (Ebinop Oadd
                                           (Ebinop Oadd
                                             (Etempvar _t'3 tulong)
                                             (Econst_int (Int.repr 1) tint)
                                             tulong)
                                           (Econst_long (Int64.repr 8128) tulong)
                                           tulong) (Etempvar _t'4 tulong)
                                         tint)
                            (Ssequence
                              (Sset _a
                                (Ederef
                                  (Etempvar _l (tptr (tptr (Tstruct _wacc noattr))))
                                  (tptr (Tstruct _wacc noattr))))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'6
                                    (Efield
                                      (Ederef
                                        (Etempvar _a (tptr (Tstruct _wacc noattr)))
                                        (Tstruct _wacc noattr)) _next
                                      (tptr (Tstruct _wacc noattr))))
                                  (Sassign
                                    (Ederef
                                      (Etempvar _l (tptr (tptr (Tstruct _wacc noattr))))
                                      (tptr (Tstruct _wacc noattr)))
                                    (Etempvar _t'6 (tptr (Tstruct _wacc noattr)))))
                                (Scall None
                                  (Evar _quickproof_free (Tfunction
                                                           ((tptr tvoid) ::
                                                            nil) tvoid
                                                           cc_default))
                                  ((Etempvar _a (tptr (Tstruct _wacc noattr))) ::
                                   nil))))
                            (Ssequence
                              (Sset _t'5
                                (Ederef
                                  (Etempvar _l (tptr (tptr (Tstruct _wacc noattr))))
                                  (tptr (Tstruct _wacc noattr))))
                              (Sset _l
                                (Eaddrof
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'5 (tptr (Tstruct _wacc noattr)))
                                      (Tstruct _wacc noattr)) _next
                                    (tptr (Tstruct _wacc noattr)))
                                  (tptr (tptr (Tstruct _wacc noattr)))))))))))
                  Sskip))
              (Sreturn (Some (Econst_int (Int.repr 1) tint))))))))))
|}.

Definition f_wm_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_m, (tptr (Tstruct _wmodel noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_a, (tptr (Tstruct _wacc noattr))) ::
               (_t'3, (tptr (Tstruct _wacc noattr))) ::
               (_t'2, (tptr (Tstruct _wacc noattr))) ::
               (_t'1, (tptr (Tstruct _wacc noattr))) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _m (tptr (Tstruct _wmodel noattr)))
            (Tstruct _wmodel noattr)) _set (tptr (Tstruct _wacc noattr))))
      (Sifthenelse (Etempvar _t'3 (tptr (Tstruct _wacc noattr)))
        Sskip
        Sbreak))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _m (tptr (Tstruct _wmodel noattr)))
              (Tstruct _wmodel noattr)) _set (tptr (Tstruct _wacc noattr))))
        (Sset _a
          (Efield
            (Ederef (Etempvar _t'2 (tptr (Tstruct _wacc noattr)))
              (Tstruct _wacc noattr)) _next (tptr (Tstruct _wacc noattr)))))
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _m (tptr (Tstruct _wmodel noattr)))
                (Tstruct _wmodel noattr)) _set (tptr (Tstruct _wacc noattr))))
          (Scall None
            (Evar _quickproof_free (Tfunction ((tptr tvoid) :: nil) tvoid
                                     cc_default))
            ((Etempvar _t'1 (tptr (Tstruct _wacc noattr))) :: nil)))
        (Sassign
          (Efield
            (Ederef (Etempvar _m (tptr (Tstruct _wmodel noattr)))
              (Tstruct _wmodel noattr)) _set (tptr (Tstruct _wacc noattr)))
          (Etempvar _a (tptr (Tstruct _wacc noattr)))))))
  Sskip)
|}.

Definition f_rc_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct _noise_replay_counter noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _c (tptr (Tstruct _noise_replay_counter noattr)))
        (Tstruct _noise_replay_counter noattr)) _counter tulong)
    (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                       (Ebinop Odiv (Econst_int (Int.repr 8192) tint)
                         (Econst_int (Int.repr 64) tint) tint) tint)
          Sskip
          Sbreak)
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef
                  (Etempvar _c (tptr (Tstruct _noise_replay_counter noattr)))
                  (Tstruct _noise_replay_counter noattr)) _backtrack
                (tarray tulong 128)) (Etempvar _i tulong) (tptr tulong))
            tulong) (Econst_int (Int.repr 0) tint)))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
          tulong)))))
|}.

Definition f_rc_take := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _rc_snap noattr))) ::
                (_c, (tptr (Tstruct _noise_replay_counter noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _c (tptr (Tstruct _noise_replay_counter noattr)))
          (Tstruct _noise_replay_counter noattr)) _counter tulong))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _rc_snap noattr)))
          (Tstruct _rc_snap noattr)) _counter tulong) (Etempvar _t'2 tulong)))
  (Ssequence
    (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                       (Ebinop Odiv (Econst_int (Int.repr 8192) tint)
                         (Econst_int (Int.repr 64) tint) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'1
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _c (tptr (Tstruct _noise_replay_counter noattr)))
                    (Tstruct _noise_replay_counter noattr)) _backtrack
                  (tarray tulong 128)) (Etempvar _i tulong) (tptr tulong))
              tulong))
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _rc_snap noattr)))
                    (Tstruct _rc_snap noattr)) _backtrack
                  (tarray tulong 128)) (Etempvar _i tulong) (tptr tulong))
              tulong) (Etempvar _t'1 tulong))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
          tulong)))))
|}.

Definition f_rc_same := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _rc_snap noattr))) ::
                (_c, (tptr (Tstruct _noise_replay_counter noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_t'4, tulong) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'3
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _rc_snap noattr)))
          (Tstruct _rc_snap noattr)) _counter tulong))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _c (tptr (Tstruct _noise_replay_counter noattr)))
            (Tstruct _noise_replay_counter noattr)) _counter tulong))
      (Sifthenelse (Ebinop One (Etempvar _t'3 tulong) (Etempvar _t'4 tulong)
                     tint)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        Sskip)))
  (Ssequence
    (Ssequence
      (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                         (Ebinop Odiv (Econst_int (Int.repr 8192) tint)
                           (Econst_int (Int.repr 64) tint) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _t'1
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _s (tptr (Tstruct _rc_snap noattr)))
                      (Tstruct _rc_snap noattr)) _backtrack
                    (tarray tulong 128)) (Etempvar _i tulong) (tptr tulong))
                tulong))
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _c (tptr (Tstruct _noise_replay_counter noattr)))
                        (Tstruct _noise_replay_counter noattr)) _backtrack
                      (tarray tulong 128)) (Etempvar _i tulong)
                    (tptr tulong)) tulong))
              (Sifthenelse (Ebinop One (Etempvar _t'1 tulong)
                             (Etempvar _t'2 tulong) tint)
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                Sskip))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
            tulong))))
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))))
|}.

Definition f_draw_nonce := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_top, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'6, tulong) :: (_t'5, tuint) :: (_t'4, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1) (Evar _nondet_u8 (Tfunction nil tuchar cc_default)) nil)
  (Sswitch (Ebinop Omod (Etempvar _t'1 tuchar) (Econst_int (Int.repr 5) tint)
             tint)
    (LScons (Some 0)
      (Ssequence
        (Scall (Some _t'2)
          (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
        (Sreturn (Some (Ebinop Osub
                         (Ebinop Oadd (Etempvar _top tulong)
                           (Ecast
                             (Ebinop Omod (Etempvar _t'2 tuint)
                               (Econst_int (Int.repr 200) tint) tuint)
                             tulong) tulong) (Econst_int (Int.repr 100) tint)
                         tulong))))
      (LScons (Some 1)
        (Ssequence
          (Scall (Some _t'3)
            (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
          (Sreturn (Some (Ebinop Osub (Etempvar _top tulong)
                           (Ecast
                             (Ebinop Omod (Etempvar _t'3 tuint)
                               (Econst_int (Int.repr 9000) tint) tuint)
                             tulong) tulong))))
        (LScons (Some 2)
          (Ssequence
            (Scall (Some _t'4)
              (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
            (Sreturn (Some (Ebinop Osub
                             (Ebinop Oadd
                               (Ebinop Osub
                                 (Ebinop Osub
                                   (Econst_long (Int64.repr (-1)) tulong)
                                   (Econst_long (Int64.repr 8128) tulong)
                                   tulong) (Econst_int (Int.repr 1) tint)
                                 tulong)
                               (Ecast
                                 (Ebinop Omod (Etempvar _t'4 tuint)
                                   (Econst_int (Int.repr 8) tint) tuint)
                                 tulong) tulong)
                             (Econst_int (Int.repr 4) tint) tulong))))
          (LScons (Some 3)
            (Ssequence
              (Scall (Some _t'5)
                (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
              (Sreturn (Some (Ebinop Osub
                               (Ebinop Oadd
                                 (Ebinop Osub
                                   (Ebinop Osub (Etempvar _top tulong)
                                     (Econst_long (Int64.repr 8128) tulong)
                                     tulong) (Econst_int (Int.repr 1) tint)
                                   tulong)
                                 (Ecast
                                   (Ebinop Omod (Etempvar _t'5 tuint)
                                     (Econst_int (Int.repr 5) tint) tuint)
                                   tulong) tulong)
                               (Econst_int (Int.repr 2) tint) tulong))))
            (LScons None
              (Ssequence
                (Scall (Some _t'6)
                  (Evar _draw_u64 (Tfunction nil tulong cc_default)) nil)
                (Sreturn (Some (Etempvar _t'6 tulong))))
              LSnil)))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_rc, (Tstruct _noise_replay_counter noattr)) ::
              (_wm, (Tstruct _wmodel noattr)) ::
              (_snap, (Tstruct _rc_snap noattr)) ::
              (_key, (tarray tuchar 32)) :: nil);
  fn_temps := ((_last_nonce, tulong) :: (_have_auth, tint) ::
               (_steps, tulong) :: (_i, tulong) :: (_pkt, (tptr tuchar)) ::
               (_pt_out, (tptr tuchar)) :: (_ref_pt, (tptr tuchar)) ::
               (_L, tulong) :: (_enc_len, tulong) :: (_tot, tulong) ::
               (_j, tulong) :: (_nonce, tulong) :: (_kind, tint) ::
               (_ok, tint) :: (_ref_ok, tint) :: (_pt, (tptr tuchar)) ::
               (_pred, tint) :: (_r, tint) :: (_t'27, tint) ::
               (_t'26, tint) :: (_t'25, tbool) :: (_t'24, tint) ::
               (_t'23, tint) :: (_t'22, tint) :: (_t'21, tbool) ::
               (_t'20, tint) :: (_t'19, tint) :: (_t'18, tuchar) ::
               (_t'17, tulong) :: (_t'16, (tptr tvoid)) :: (_t'15, tuint) ::
               (_t'14, tulong) :: (_t'13, tulong) :: (_t'12, tint) ::
               (_t'11, tint) :: (_t'10, tint) :: (_t'9, (tptr tvoid)) ::
               (_t'8, tulong) :: (_t'7, (tptr tvoid)) :: (_t'6, tulong) ::
               (_t'5, (tptr tvoid)) :: (_t'4, tint) :: (_t'3, tulong) ::
               (_t'2, tuchar) :: (_t'1, tulong) :: (_t'31, tulong) ::
               (_t'30, tuchar) :: (_t'29, tulong) :: (_t'28, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _last_nonce (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Ssequence
      (Sset _have_auth (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Scall None
          (Evar _rc_init (Tfunction
                           ((tptr (Tstruct _noise_replay_counter noattr)) ::
                            nil) tvoid cc_default))
          ((Eaddrof (Evar _rc (Tstruct _noise_replay_counter noattr))
             (tptr (Tstruct _noise_replay_counter noattr))) :: nil))
        (Ssequence
          (Scall None
            (Evar _wm_init (Tfunction
                             ((tptr (Tstruct _wmodel noattr)) :: nil) tvoid
                             cc_default))
            ((Eaddrof (Evar _wm (Tstruct _wmodel noattr))
               (tptr (Tstruct _wmodel noattr))) :: nil))
          (Ssequence
            (Scall None
              (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                    tvoid cc_default))
              ((Evar _key (tarray tuchar 32)) ::
               (Econst_int (Int.repr 32) tint) :: nil))
            (Ssequence
              (Ssequence
                (Scall (Some _t'1)
                  (Evar _draw_steps (Tfunction nil tulong cc_default)) nil)
                (Sset _steps (Etempvar _t'1 tulong)))
              (Ssequence
                (Ssequence
                  (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                                     (Etempvar _steps tulong) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'2)
                            (Evar _nondet_u8 (Tfunction nil tuchar
                                               cc_default)) nil)
                          (Sset _kind
                            (Ebinop Omod (Etempvar _t'2 tuchar)
                              (Econst_int (Int.repr 4) tint) tint)))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'3)
                              (Evar _draw_size (Tfunction nil tulong
                                                 cc_default)) nil)
                            (Sset _L (Etempvar _t'3 tulong)))
                          (Ssequence
                            (Sifthenelse (Ebinop Ogt (Etempvar _L tulong)
                                           (Ebinop Osub
                                             (Econst_long (Int64.repr 9223372036854775807) tlong)
                                             (Econst_int (Int.repr 32) tint)
                                             tlong) tint)
                              Sbreak
                              Sskip)
                            (Ssequence
                              (Ssequence
                                (Sifthenelse (Ebinop Oeq
                                               (Etempvar _kind tint)
                                               (Econst_int (Int.repr 3) tint)
                                               tint)
                                  (Sset _t'4
                                    (Ecast
                                      (Ebinop Olt (Etempvar _L tulong)
                                        (Econst_int (Int.repr 16) tint) tint)
                                      tbool))
                                  (Sset _t'4 (Econst_int (Int.repr 0) tint)))
                                (Sifthenelse (Etempvar _t'4 tint)
                                  (Sset _enc_len (Etempvar _L tulong))
                                  (Sset _enc_len
                                    (Ebinop Oadd (Etempvar _L tulong)
                                      (Econst_int (Int.repr 16) tint) tulong))))
                              (Ssequence
                                (Sset _tot
                                  (Ebinop Oadd
                                    (Econst_int (Int.repr 16) tint)
                                    (Etempvar _enc_len tulong) tulong))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'5)
                                      (Evar _quickproof_malloc (Tfunction
                                                                 (tulong ::
                                                                  nil)
                                                                 (tptr tvoid)
                                                                 cc_default))
                                      ((Etempvar _tot tulong) :: nil))
                                    (Sset _pkt (Etempvar _t'5 (tptr tvoid))))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sifthenelse (Ebinop Oge
                                                       (Etempvar _enc_len tulong)
                                                       (Econst_int (Int.repr 16) tint)
                                                       tint)
                                          (Sset _t'6
                                            (Ecast
                                              (Ebinop Osub
                                                (Etempvar _enc_len tulong)
                                                (Econst_int (Int.repr 16) tint)
                                                tulong) tulong))
                                          (Sset _t'6
                                            (Ecast
                                              (Econst_int (Int.repr 0) tint)
                                              tulong)))
                                        (Scall (Some _t'7)
                                          (Evar _quickproof_malloc (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                          ((Etempvar _t'6 tulong) :: nil)))
                                      (Sset _pt_out
                                        (Etempvar _t'7 (tptr tvoid))))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sifthenelse (Ebinop Oge
                                                         (Etempvar _enc_len tulong)
                                                         (Econst_int (Int.repr 16) tint)
                                                         tint)
                                            (Sset _t'8
                                              (Ecast
                                                (Ebinop Osub
                                                  (Etempvar _enc_len tulong)
                                                  (Econst_int (Int.repr 16) tint)
                                                  tulong) tulong))
                                            (Sset _t'8
                                              (Ecast
                                                (Econst_int (Int.repr 0) tint)
                                                tulong)))
                                          (Scall (Some _t'9)
                                            (Evar _quickproof_malloc 
                                            (Tfunction (tulong :: nil)
                                              (tptr tvoid) cc_default))
                                            ((Etempvar _t'8 tulong) :: nil)))
                                        (Sset _ref_pt
                                          (Etempvar _t'9 (tptr tvoid))))
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sifthenelse (Ebinop Oeq
                                                           (Etempvar _pkt (tptr tuchar))
                                                           (Ecast
                                                             (Econst_int (Int.repr 0) tint)
                                                             (tptr tvoid))
                                                           tint)
                                              (Sset _t'10
                                                (Econst_int (Int.repr 1) tint))
                                              (Sset _t'10
                                                (Ecast
                                                  (Ebinop Oeq
                                                    (Etempvar _pt_out (tptr tuchar))
                                                    (Ecast
                                                      (Econst_int (Int.repr 0) tint)
                                                      (tptr tvoid)) tint)
                                                  tbool)))
                                            (Sifthenelse (Etempvar _t'10 tint)
                                              (Sset _t'11
                                                (Econst_int (Int.repr 1) tint))
                                              (Sset _t'11
                                                (Ecast
                                                  (Ebinop Oeq
                                                    (Etempvar _ref_pt (tptr tuchar))
                                                    (Ecast
                                                      (Econst_int (Int.repr 0) tint)
                                                      (tptr tvoid)) tint)
                                                  tbool))))
                                          (Sifthenelse (Etempvar _t'11 tint)
                                            (Ssequence
                                              (Scall None
                                                (Evar _quickproof_free 
                                                (Tfunction
                                                  ((tptr tvoid) :: nil) tvoid
                                                  cc_default))
                                                ((Etempvar _pkt (tptr tuchar)) ::
                                                 nil))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _quickproof_free 
                                                  (Tfunction
                                                    ((tptr tvoid) :: nil)
                                                    tvoid cc_default))
                                                  ((Etempvar _pt_out (tptr tuchar)) ::
                                                   nil))
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _quickproof_free 
                                                    (Tfunction
                                                      ((tptr tvoid) :: nil)
                                                      tvoid cc_default))
                                                    ((Etempvar _ref_pt (tptr tuchar)) ::
                                                     nil))
                                                  Sbreak)))
                                            Sskip))
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sifthenelse (Ebinop Oeq
                                                             (Etempvar _kind tint)
                                                             (Econst_int (Int.repr 2) tint)
                                                             tint)
                                                (Sset _t'12
                                                  (Ecast
                                                    (Etempvar _have_auth tint)
                                                    tbool))
                                                (Sset _t'12
                                                  (Econst_int (Int.repr 0) tint)))
                                              (Sifthenelse (Etempvar _t'12 tint)
                                                (Sset _t'13
                                                  (Ecast
                                                    (Etempvar _last_nonce tulong)
                                                    tulong))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'31
                                                      (Efield
                                                        (Evar _wm (Tstruct _wmodel noattr))
                                                        _top tulong))
                                                    (Scall (Some _t'14)
                                                      (Evar _draw_nonce 
                                                      (Tfunction
                                                        (tulong :: nil)
                                                        tulong cc_default))
                                                      ((Etempvar _t'31 tulong) ::
                                                       nil)))
                                                  (Sset _t'13
                                                    (Ecast
                                                      (Etempvar _t'14 tulong)
                                                      tulong)))))
                                            (Sset _nonce
                                              (Etempvar _t'13 tulong)))
                                          (Ssequence
                                            (Scall None
                                              (Evar _le32_store (Tfunction
                                                                  ((tptr tuchar) ::
                                                                   tuint ::
                                                                   nil) tvoid
                                                                  cc_default))
                                              ((Etempvar _pkt (tptr tuchar)) ::
                                               (Econst_int (Int.repr 4) tint) ::
                                               nil))
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'15)
                                                  (Evar _nondet_u32 (Tfunction
                                                                    nil tuint
                                                                    cc_default))
                                                  nil)
                                                (Scall None
                                                  (Evar _le32_store (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                  ((Ebinop Oadd
                                                     (Etempvar _pkt (tptr tuchar))
                                                     (Econst_int (Int.repr 4) tint)
                                                     (tptr tuchar)) ::
                                                   (Etempvar _t'15 tuint) ::
                                                   nil)))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _le64_store (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                  ((Ebinop Oadd
                                                     (Etempvar _pkt (tptr tuchar))
                                                     (Econst_int (Int.repr 8) tint)
                                                     (tptr tuchar)) ::
                                                   (Etempvar _nonce tulong) ::
                                                   nil))
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop Oeq
                                                                    (Etempvar _kind tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                        (Sset _t'19
                                                          (Econst_int (Int.repr 1) tint))
                                                        (Sset _t'19
                                                          (Ecast
                                                            (Ebinop Oeq
                                                              (Etempvar _kind tint)
                                                              (Econst_int (Int.repr 1) tint)
                                                              tint) tbool)))
                                                      (Sifthenelse (Etempvar _t'19 tint)
                                                        (Sset _t'20
                                                          (Econst_int (Int.repr 1) tint))
                                                        (Sset _t'20
                                                          (Ecast
                                                            (Ebinop Oeq
                                                              (Etempvar _kind tint)
                                                              (Econst_int (Int.repr 2) tint)
                                                              tint) tbool))))
                                                    (Sifthenelse (Etempvar _t'20 tint)
                                                      (Ssequence
                                                        (Ssequence
                                                          (Scall (Some _t'16)
                                                            (Evar _quickproof_malloc 
                                                            (Tfunction
                                                              (tulong :: nil)
                                                              (tptr tvoid)
                                                              cc_default))
                                                            ((Etempvar _L tulong) ::
                                                             nil))
                                                          (Sset _pt
                                                            (Etempvar _t'16 (tptr tvoid))))
                                                        (Ssequence
                                                          (Sifthenelse 
                                                            (Ebinop Oeq
                                                              (Etempvar _pt (tptr tuchar))
                                                              (Ecast
                                                                (Econst_int (Int.repr 0) tint)
                                                                (tptr tvoid))
                                                              tint)
                                                            (Ssequence
                                                              (Scall None
                                                                (Evar _quickproof_free 
                                                                (Tfunction
                                                                  ((tptr tvoid) ::
                                                                   nil) tvoid
                                                                  cc_default))
                                                                ((Etempvar _pkt (tptr tuchar)) ::
                                                                 nil))
                                                              (Ssequence
                                                                (Scall None
                                                                  (Evar _quickproof_free 
                                                                  (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Etempvar _pt_out (tptr tuchar)) ::
                                                                   nil))
                                                                (Ssequence
                                                                  (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _ref_pt (tptr tuchar)) ::
                                                                    nil))
                                                                  Sbreak)))
                                                            Sskip)
                                                          (Ssequence
                                                            (Scall None
                                                              (Evar _nondet_bytes 
                                                              (Tfunction
                                                                ((tptr tuchar) ::
                                                                 tulong ::
                                                                 nil) tvoid
                                                                cc_default))
                                                              ((Etempvar _pt (tptr tuchar)) ::
                                                               (Etempvar _L tulong) ::
                                                               nil))
                                                            (Ssequence
                                                              (Scall None
                                                                (Evar _chacha20poly1305_encrypt 
                                                                (Tfunction
                                                                  ((tptr tuchar) ::
                                                                   (tptr tuchar) ::
                                                                   tulong ::
                                                                   (tptr tuchar) ::
                                                                   tulong ::
                                                                   tulong ::
                                                                   (tptr tuchar) ::
                                                                   nil) tvoid
                                                                  cc_default))
                                                                ((Ebinop Oadd
                                                                   (Etempvar _pkt (tptr tuchar))
                                                                   (Econst_int (Int.repr 16) tint)
                                                                   (tptr tuchar)) ::
                                                                 (Etempvar _pt (tptr tuchar)) ::
                                                                 (Etempvar _L tulong) ::
                                                                 (Ecast
                                                                   (Econst_int (Int.repr 0) tint)
                                                                   (tptr tvoid)) ::
                                                                 (Econst_int (Int.repr 0) tint) ::
                                                                 (Etempvar _nonce tulong) ::
                                                                 (Evar _key (tarray tuchar 32)) ::
                                                                 nil))
                                                              (Ssequence
                                                                (Scall None
                                                                  (Evar _quickproof_free 
                                                                  (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Etempvar _pt (tptr tuchar)) ::
                                                                   nil))
                                                                (Sifthenelse 
                                                                  (Ebinop Oeq
                                                                    (Etempvar _kind tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'17)
                                                                    (Evar _nondet_size 
                                                                    (Tfunction
                                                                    nil
                                                                    tulong
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _j
                                                                    (Etempvar _t'17 tulong)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _j tulong)
                                                                    (Etempvar _enc_len tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'18)
                                                                    (Evar _nondet_u8 
                                                                    (Tfunction
                                                                    nil
                                                                    tuchar
                                                                    cc_default))
                                                                    nil)
                                                                    (Ssequence
                                                                    (Sset _t'30
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pkt (tptr tuchar))
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    (Etempvar _j tulong)
                                                                    tulong)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pkt (tptr tuchar))
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    (Etempvar _j tulong)
                                                                    tulong)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Ebinop Oxor
                                                                    (Etempvar _t'30 tuchar)
                                                                    (Ecast
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Ebinop Omod
                                                                    (Etempvar _t'18 tuchar)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tint)
                                                                    tint)
                                                                    tuchar)
                                                                    tint))))
                                                                    Sskip))
                                                                  Sskip))))))
                                                      (Scall None
                                                        (Evar _nondet_bytes 
                                                        (Tfunction
                                                          ((tptr tuchar) ::
                                                           tulong :: nil)
                                                          tvoid cc_default))
                                                        ((Ebinop Oadd
                                                           (Etempvar _pkt (tptr tuchar))
                                                           (Econst_int (Int.repr 16) tint)
                                                           (tptr tuchar)) ::
                                                         (Etempvar _enc_len tulong) ::
                                                         nil))))
                                                  (Ssequence
                                                    (Scall None
                                                      (Evar _rc_take 
                                                      (Tfunction
                                                        ((tptr (Tstruct _rc_snap noattr)) ::
                                                         (tptr (Tstruct _noise_replay_counter noattr)) ::
                                                         nil) tvoid
                                                        cc_default))
                                                      ((Eaddrof
                                                         (Evar _snap (Tstruct _rc_snap noattr))
                                                         (tptr (Tstruct _rc_snap noattr))) ::
                                                       (Eaddrof
                                                         (Evar _rc (Tstruct _noise_replay_counter noattr))
                                                         (tptr (Tstruct _noise_replay_counter noattr))) ::
                                                       nil))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Scall (Some _t'21)
                                                          (Evar _chacha20poly1305_decrypt 
                                                          (Tfunction
                                                            ((tptr tuchar) ::
                                                             (tptr tuchar) ::
                                                             tulong ::
                                                             (tptr tuchar) ::
                                                             tulong ::
                                                             tulong ::
                                                             (tptr tuchar) ::
                                                             nil) tbool
                                                            cc_default))
                                                          ((Etempvar _pt_out (tptr tuchar)) ::
                                                           (Ebinop Oadd
                                                             (Etempvar _pkt (tptr tuchar))
                                                             (Econst_int (Int.repr 16) tint)
                                                             (tptr tuchar)) ::
                                                           (Etempvar _enc_len tulong) ::
                                                           (Ecast
                                                             (Econst_int (Int.repr 0) tint)
                                                             (tptr tvoid)) ::
                                                           (Econst_int (Int.repr 0) tint) ::
                                                           (Etempvar _nonce tulong) ::
                                                           (Evar _key (tarray tuchar 32)) ::
                                                           nil))
                                                        (Sset _ok
                                                          (Etempvar _t'21 tbool)))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Scall (Some _t'22)
                                                            (Evar _ref_aead_decrypt 
                                                            (Tfunction
                                                              ((tptr tuchar) ::
                                                               (tptr tuchar) ::
                                                               tulong ::
                                                               (tptr tuchar) ::
                                                               tulong ::
                                                               tulong ::
                                                               (tptr tuchar) ::
                                                               nil) tint
                                                              cc_default))
                                                            ((Etempvar _ref_pt (tptr tuchar)) ::
                                                             (Ebinop Oadd
                                                               (Etempvar _pkt (tptr tuchar))
                                                               (Econst_int (Int.repr 16) tint)
                                                               (tptr tuchar)) ::
                                                             (Etempvar _enc_len tulong) ::
                                                             (Ecast
                                                               (Econst_int (Int.repr 0) tint)
                                                               (tptr tvoid)) ::
                                                             (Econst_int (Int.repr 0) tint) ::
                                                             (Etempvar _nonce tulong) ::
                                                             (Evar _key (tarray tuchar 32)) ::
                                                             nil))
                                                          (Sset _ref_ok
                                                            (Etempvar _t'22 tint)))
                                                        (Ssequence
                                                          (Sloop
                                                            (Sifthenelse 
                                                              (Eunop Onotbool
                                                                (Ebinop Oeq
                                                                  (Etempvar _ok tint)
                                                                  (Etempvar _ref_ok tint)
                                                                  tint) tint)
                                                              (Scall None
                                                                (Evar _check_failed 
                                                                (Tfunction
                                                                  nil tvoid
                                                                  cc_default))
                                                                nil)
                                                              Sskip)
                                                            Sbreak)
                                                          (Ssequence
                                                            (Sifthenelse 
                                                              (Eunop Onotbool
                                                                (Etempvar _ok tint)
                                                                tint)
                                                              (Sloop
                                                                (Ssequence
                                                                  (Scall (Some _t'23)
                                                                    (Evar _rc_same 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _rc_snap noattr)) ::
                                                                    (tptr (Tstruct _noise_replay_counter noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _snap (Tstruct _rc_snap noattr))
                                                                    (tptr (Tstruct _rc_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _rc (Tstruct _noise_replay_counter noattr))
                                                                    (tptr (Tstruct _noise_replay_counter noattr))) ::
                                                                    nil))
                                                                  (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'23 tint)
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
                                                                (Ssequence
                                                                  (Scall (Some _t'24)
                                                                    (Evar _wm_accepts 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _wmodel noattr)) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _wm (Tstruct _wmodel noattr))
                                                                    (tptr (Tstruct _wmodel noattr))) ::
                                                                    (Etempvar _nonce tulong) ::
                                                                    nil))
                                                                  (Sset _pred
                                                                    (Etempvar _t'24 tint)))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Scall (Some _t'25)
                                                                    (Evar _wg_counter_validate 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _noise_replay_counter noattr)) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tbool
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _rc (Tstruct _noise_replay_counter noattr))
                                                                    (tptr (Tstruct _noise_replay_counter noattr))) ::
                                                                    (Etempvar _nonce tulong) ::
                                                                    nil))
                                                                    (Sset _r
                                                                    (Etempvar _t'25 tbool)))
                                                                  (Ssequence
                                                                    (Sloop
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Etempvar _pred tint)
                                                                    tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip)
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _r tint)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Scall (Some _t'26)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _pt_out (tptr tuchar)) ::
                                                                    (Etempvar _ref_pt (tptr tuchar)) ::
                                                                    (Ebinop Osub
                                                                    (Etempvar _enc_len tulong)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'26 tint)
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
                                                                    (Scall (Some _t'27)
                                                                    (Evar _wm_commit 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _wmodel noattr)) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _wm (Tstruct _wmodel noattr))
                                                                    (tptr (Tstruct _wmodel noattr))) ::
                                                                    (Etempvar _nonce tulong) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'27 tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _pkt (tptr tuchar)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _pt_out (tptr tuchar)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _ref_pt (tptr tuchar)) ::
                                                                    nil))
                                                                    Sbreak)))
                                                                    Sskip)))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sset _t'28
                                                                    (Efield
                                                                    (Evar _rc (Tstruct _noise_replay_counter noattr))
                                                                    _counter
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _t'29
                                                                    (Efield
                                                                    (Evar _wm (Tstruct _wmodel noattr))
                                                                    _top
                                                                    tulong))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'28 tulong)
                                                                    (Etempvar _t'29 tulong)
                                                                    tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip)))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sset _have_auth
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _last_nonce
                                                                    (Etempvar _nonce tulong)))))))))
                                                            (Ssequence
                                                              (Scall None
                                                                (Evar _quickproof_free 
                                                                (Tfunction
                                                                  ((tptr tvoid) ::
                                                                   nil) tvoid
                                                                  cc_default))
                                                                ((Etempvar _pkt (tptr tuchar)) ::
                                                                 nil))
                                                              (Ssequence
                                                                (Scall None
                                                                  (Evar _quickproof_free 
                                                                  (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Etempvar _pt_out (tptr tuchar)) ::
                                                                   nil))
                                                                (Scall None
                                                                  (Evar _quickproof_free 
                                                                  (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Etempvar _ref_pt (tptr tuchar)) ::
                                                                   nil))))))))))))))))))))))))
                    (Sset _i
                      (Ebinop Oadd (Etempvar _i tulong)
                        (Econst_int (Int.repr 1) tint) tulong))))
                (Ssequence
                  (Scall None
                    (Evar _wm_free (Tfunction
                                     ((tptr (Tstruct _wmodel noattr)) :: nil)
                                     tvoid cc_default))
                    ((Eaddrof (Evar _wm (Tstruct _wmodel noattr))
                       (tptr (Tstruct _wmodel noattr))) :: nil))
                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite ___gp_spinlock_t Struct (Member_plain _unused tint :: nil) noattr ::
 Composite _noise_replay_counter Struct
   (Member_plain _counter tulong ::
    Member_plain _lock (Tstruct ___gp_spinlock_t noattr) ::
    Member_plain _backtrack (tarray tulong 128) :: nil)
   noattr ::
 Composite _rpoly Struct
   (Member_plain _r (tarray tuint 17) :: Member_plain _h (tarray tuint 17) ::
    Member_plain _s (tarray tuchar 16) :: nil)
   noattr ::
 Composite _wacc Struct
   (Member_plain _n tulong ::
    Member_plain _next (tptr (Tstruct _wacc noattr)) :: nil)
   noattr ::
 Composite _wmodel Struct
   (Member_plain _set (tptr (Tstruct _wacc noattr)) ::
    Member_plain _top tulong :: nil)
   noattr ::
 Composite _rc_snap Struct
   (Member_plain _counter tulong ::
    Member_plain _backtrack (tarray tulong 128) :: nil)
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
 (_quickproof_malloc,
   Gfun(External (EF_external "quickproof_malloc"
                   (mksignature (AST.Xlong :: nil) AST.Xptr cc_default))
     (tulong :: nil) (tptr tvoid) cc_default)) ::
 (_quickproof_free,
   Gfun(External (EF_external "quickproof_free"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (_chacha20poly1305_encrypt,
   Gfun(External (EF_external "chacha20poly1305_encrypt"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xptr ::
                      AST.Xlong :: AST.Xlong :: AST.Xptr :: nil) AST.Xvoid
                     cc_default))
     ((tptr tuchar) :: (tptr tuchar) :: tulong :: (tptr tuchar) :: tulong ::
      tulong :: (tptr tuchar) :: nil) tvoid cc_default)) ::
 (_chacha20poly1305_decrypt,
   Gfun(External (EF_external "chacha20poly1305_decrypt"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xptr ::
                      AST.Xlong :: AST.Xlong :: AST.Xptr :: nil) AST.Xbool
                     cc_default))
     ((tptr tuchar) :: (tptr tuchar) :: tulong :: (tptr tuchar) :: tulong ::
      tulong :: (tptr tuchar) :: nil) tbool cc_default)) ::
 (_check_failed, Gfun(Internal f_check_failed)) ::
 (_bytes_eq, Gfun(Internal f_bytes_eq)) ::
 (_bytes_copy, Gfun(Internal f_bytes_copy)) ::
 (_bytes_set, Gfun(Internal f_bytes_set)) ::
 (_draw_size, Gfun(Internal f_draw_size)) ::
 (_draw_steps, Gfun(Internal f_draw_steps)) ::
 (_draw_u64, Gfun(Internal f_draw_u64)) ::
 (_le32_store, Gfun(Internal f_le32_store)) ::
 (_le32_load, Gfun(Internal f_le32_load)) ::
 (_le64_store, Gfun(Internal f_le64_store)) ::
 (_rc_rotl, Gfun(Internal f_rc_rotl)) :: (_rc_qr, Gfun(Internal f_rc_qr)) ::
 (_rc_rounds, Gfun(Internal f_rc_rounds)) ::
 (_rc_setup, Gfun(Internal f_rc_setup)) ::
 (_ref_chacha20_block, Gfun(Internal f_ref_chacha20_block)) ::
 (_rp_add, Gfun(Internal f_rp_add)) ::
 (_rp_init, Gfun(Internal f_rp_init)) ::
 (_rp_mul, Gfun(Internal f_rp_mul)) ::
 (_rp_block, Gfun(Internal f_rp_block)) ::
 (_rp_padded, Gfun(Internal f_rp_padded)) :: (_x_transport_order__minusp, Gvar v_x_transport_order__minusp) ::
 (_rp_final, Gfun(Internal f_rp_final)) ::
 (_ref_aead_tag, Gfun(Internal f_ref_aead_tag)) ::
 (_ref_chacha20_xor, Gfun(Internal f_ref_chacha20_xor)) ::
 (_ref_aead_decrypt, Gfun(Internal f_ref_aead_decrypt)) ::
 (_wg_counter_validate,
   Gfun(External (EF_external "wg_counter_validate"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xbool
                     cc_default))
     ((tptr (Tstruct _noise_replay_counter noattr)) :: tulong :: nil) tbool
     cc_default)) :: (_wm_init, Gfun(Internal f_wm_init)) ::
 (_wm_accepts, Gfun(Internal f_wm_accepts)) ::
 (_wm_commit, Gfun(Internal f_wm_commit)) ::
 (_wm_free, Gfun(Internal f_wm_free)) ::
 (_rc_init, Gfun(Internal f_rc_init)) ::
 (_rc_take, Gfun(Internal f_rc_take)) ::
 (_rc_same, Gfun(Internal f_rc_same)) ::
 (_draw_nonce, Gfun(Internal f_draw_nonce)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _wg_counter_validate :: _chacha20poly1305_decrypt ::
 _chacha20poly1305_encrypt :: _quickproof_free :: _quickproof_malloc ::
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


