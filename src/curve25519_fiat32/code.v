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
  Definition source_file := "lib/crypto/curve25519-fiat32.c".
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
Definition _a0 : ident := $"a0".
Definition _a1 : ident := $"a1".
Definition _a2 : ident := $"a2".
Definition _a3 : ident := $"a3".
Definition _a4 : ident := $"a4".
Definition _a5 : ident := $"a5".
Definition _a6 : ident := $"a6".
Definition _a7 : ident := $"a7".
Definition _addcarryx_u25 : ident := $"addcarryx_u25".
Definition _addcarryx_u26 : ident := $"addcarryx_u26".
Definition _b : ident := $"b".
Definition _c : ident := $"c".
Definition _cmovznz32 : ident := $"cmovznz32".
Definition _count : ident := $"count".
Definition _curve25519_clamp_secret : ident := $"curve25519_clamp_secret".
Definition _curve25519_generic : ident := $"curve25519_generic".
Definition _e : ident := $"e".
Definition _f : ident := $"f".
Definition _fe : ident := $"fe".
Definition _fe_0 : ident := $"fe_0".
Definition _fe_1 : ident := $"fe_1".
Definition _fe_add : ident := $"fe_add".
Definition _fe_add_impl : ident := $"fe_add_impl".
Definition _fe_copy : ident := $"fe_copy".
Definition _fe_copy_lt : ident := $"fe_copy_lt".
Definition _fe_cswap : ident := $"fe_cswap".
Definition _fe_freeze : ident := $"fe_freeze".
Definition _fe_frombytes : ident := $"fe_frombytes".
Definition _fe_frombytes_impl : ident := $"fe_frombytes_impl".
Definition _fe_invert : ident := $"fe_invert".
Definition _fe_loose : ident := $"fe_loose".
Definition _fe_loose_invert : ident := $"fe_loose_invert".
Definition _fe_mul121666 : ident := $"fe_mul121666".
Definition _fe_mul_121666_impl : ident := $"fe_mul_121666_impl".
Definition _fe_mul_impl : ident := $"fe_mul_impl".
Definition _fe_mul_tll : ident := $"fe_mul_tll".
Definition _fe_mul_tlt : ident := $"fe_mul_tlt".
Definition _fe_mul_ttt : ident := $"fe_mul_ttt".
Definition _fe_sq_tl : ident := $"fe_sq_tl".
Definition _fe_sq_tt : ident := $"fe_sq_tt".
Definition _fe_sqr_impl : ident := $"fe_sqr_impl".
Definition _fe_sub : ident := $"fe_sub".
Definition _fe_sub_impl : ident := $"fe_sub_impl".
Definition _fe_tobytes : ident := $"fe_tobytes".
Definition _g : ident := $"g".
Definition _get_unaligned_le32 : ident := $"get_unaligned_le32".
Definition _h : ident := $"h".
Definition _i : ident := $"i".
Definition _in1 : ident := $"in1".
Definition _in2 : ident := $"in2".
Definition _l : ident := $"l".
Definition _low : ident := $"low".
Definition _main : ident := $"main".
Definition _memcpy : ident := $"memcpy".
Definition _memset : ident := $"memset".
Definition _memzero_explicit : ident := $"memzero_explicit".
Definition _nz : ident := $"nz".
Definition _out : ident := $"out".
Definition _p : ident := $"p".
Definition _point : ident := $"point".
Definition _pos : ident := $"pos".
Definition _s : ident := $"s".
Definition _scalar : ident := $"scalar".
Definition _secret : ident := $"secret".
Definition _subborrow_u25 : ident := $"subborrow_u25".
Definition _subborrow_u26 : ident := $"subborrow_u26".
Definition _swap : ident := $"swap".
Definition _t : ident := $"t".
Definition _t0 : ident := $"t0".
Definition _t1 : ident := $"t1".
Definition _t2 : ident := $"t2".
Definition _t3 : ident := $"t3".
Definition _tmp0 : ident := $"tmp0".
Definition _tmp0l : ident := $"tmp0l".
Definition _tmp1 : ident := $"tmp1".
Definition _tmp1l : ident := $"tmp1l".
Definition _v : ident := $"v".
Definition _x : ident := $"x".
Definition _x1 : ident := $"x1".
Definition _x10 : ident := $"x10".
Definition _x100 : ident := $"x100".
Definition _x101 : ident := $"x101".
Definition _x102 : ident := $"x102".
Definition _x103 : ident := $"x103".
Definition _x104 : ident := $"x104".
Definition _x105 : ident := $"x105".
Definition _x106 : ident := $"x106".
Definition _x107 : ident := $"x107".
Definition _x108 : ident := $"x108".
Definition _x109 : ident := $"x109".
Definition _x11 : ident := $"x11".
Definition _x110 : ident := $"x110".
Definition _x111 : ident := $"x111".
Definition _x112 : ident := $"x112".
Definition _x113 : ident := $"x113".
Definition _x114 : ident := $"x114".
Definition _x115 : ident := $"x115".
Definition _x116 : ident := $"x116".
Definition _x117 : ident := $"x117".
Definition _x118 : ident := $"x118".
Definition _x119 : ident := $"x119".
Definition _x12 : ident := $"x12".
Definition _x120 : ident := $"x120".
Definition _x13 : ident := $"x13".
Definition _x14 : ident := $"x14".
Definition _x15 : ident := $"x15".
Definition _x16 : ident := $"x16".
Definition _x17 : ident := $"x17".
Definition _x18 : ident := $"x18".
Definition _x19 : ident := $"x19".
Definition _x2 : ident := $"x2".
Definition _x20 : ident := $"x20".
Definition _x21 : ident := $"x21".
Definition _x22 : ident := $"x22".
Definition _x23 : ident := $"x23".
Definition _x24 : ident := $"x24".
Definition _x25 : ident := $"x25".
Definition _x26 : ident := $"x26".
Definition _x27 : ident := $"x27".
Definition _x28 : ident := $"x28".
Definition _x29 : ident := $"x29".
Definition _x2l : ident := $"x2l".
Definition _x3 : ident := $"x3".
Definition _x30 : ident := $"x30".
Definition _x31 : ident := $"x31".
Definition _x32 : ident := $"x32".
Definition _x33 : ident := $"x33".
Definition _x34 : ident := $"x34".
Definition _x35 : ident := $"x35".
Definition _x36 : ident := $"x36".
Definition _x37 : ident := $"x37".
Definition _x38 : ident := $"x38".
Definition _x39 : ident := $"x39".
Definition _x3l : ident := $"x3l".
Definition _x4 : ident := $"x4".
Definition _x40 : ident := $"x40".
Definition _x41 : ident := $"x41".
Definition _x42 : ident := $"x42".
Definition _x43 : ident := $"x43".
Definition _x44 : ident := $"x44".
Definition _x45 : ident := $"x45".
Definition _x46 : ident := $"x46".
Definition _x47 : ident := $"x47".
Definition _x48 : ident := $"x48".
Definition _x49 : ident := $"x49".
Definition _x5 : ident := $"x5".
Definition _x50 : ident := $"x50".
Definition _x51 : ident := $"x51".
Definition _x52 : ident := $"x52".
Definition _x53 : ident := $"x53".
Definition _x54 : ident := $"x54".
Definition _x55 : ident := $"x55".
Definition _x56 : ident := $"x56".
Definition _x57 : ident := $"x57".
Definition _x58 : ident := $"x58".
Definition _x59 : ident := $"x59".
Definition _x6 : ident := $"x6".
Definition _x60 : ident := $"x60".
Definition _x61 : ident := $"x61".
Definition _x62 : ident := $"x62".
Definition _x63 : ident := $"x63".
Definition _x64 : ident := $"x64".
Definition _x65 : ident := $"x65".
Definition _x66 : ident := $"x66".
Definition _x67 : ident := $"x67".
Definition _x68 : ident := $"x68".
Definition _x69 : ident := $"x69".
Definition _x7 : ident := $"x7".
Definition _x70 : ident := $"x70".
Definition _x71 : ident := $"x71".
Definition _x72 : ident := $"x72".
Definition _x73 : ident := $"x73".
Definition _x74 : ident := $"x74".
Definition _x75 : ident := $"x75".
Definition _x76 : ident := $"x76".
Definition _x77 : ident := $"x77".
Definition _x78 : ident := $"x78".
Definition _x79 : ident := $"x79".
Definition _x8 : ident := $"x8".
Definition _x80 : ident := $"x80".
Definition _x81 : ident := $"x81".
Definition _x82 : ident := $"x82".
Definition _x83 : ident := $"x83".
Definition _x84 : ident := $"x84".
Definition _x85 : ident := $"x85".
Definition _x86 : ident := $"x86".
Definition _x87 : ident := $"x87".
Definition _x88 : ident := $"x88".
Definition _x89 : ident := $"x89".
Definition _x9 : ident := $"x9".
Definition _x90 : ident := $"x90".
Definition _x91 : ident := $"x91".
Definition _x92 : ident := $"x92".
Definition _x93 : ident := $"x93".
Definition _x94 : ident := $"x94".
Definition _x95 : ident := $"x95".
Definition _x96 : ident := $"x96".
Definition _x97 : ident := $"x97".
Definition _x98 : ident := $"x98".
Definition _x99 : ident := $"x99".
Definition _z : ident := $"z".
Definition _z2 : ident := $"z2".
Definition _z2l : ident := $"z2l".
Definition _z3 : ident := $"z3".
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
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition f_memzero_explicit := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr tvoid)) :: (_count, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _memset (Tfunction ((tptr tvoid) :: tint :: tulong :: nil)
                  (tptr tvoid) cc_default))
  ((Etempvar _s (tptr tvoid)) :: (Econst_int (Int.repr 0) tint) ::
   (Etempvar _count tulong) :: nil))
|}.

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

Definition f_curve25519_clamp_secret := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_secret, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Ederef
        (Ebinop Oadd (Etempvar _secret (tptr tuchar))
          (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar))
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar _secret (tptr tuchar))
          (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
      (Ebinop Oand (Etempvar _t'2 tuchar) (Econst_int (Int.repr 248) tint)
        tint)))
  (Ssequence
    (Sset _t'1
      (Ederef
        (Ebinop Oadd (Etempvar _secret (tptr tuchar))
          (Econst_int (Int.repr 31) tint) (tptr tuchar)) tuchar))
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar _secret (tptr tuchar))
          (Econst_int (Int.repr 31) tint) (tptr tuchar)) tuchar)
      (Ebinop Oor
        (Ebinop Oand (Etempvar _t'1 tuchar) (Econst_int (Int.repr 127) tint)
          tint) (Econst_int (Int.repr 64) tint) tint))))
|}.

Definition f_fe_frombytes_impl := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr tuint)) :: (_s, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_a0, tuint) :: (_a1, tuint) :: (_a2, tuint) ::
               (_a3, tuint) :: (_a4, tuint) :: (_a5, tuint) ::
               (_a6, tuint) :: (_a7, tuint) :: (_t'8, tuint) ::
               (_t'7, tuint) :: (_t'6, tuint) :: (_t'5, tuint) ::
               (_t'4, tuint) :: (_t'3, tuint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_unaligned_le32 (Tfunction ((tptr tvoid) :: nil) tuint
                                  cc_default))
      ((Etempvar _s (tptr tuchar)) :: nil))
    (Sset _a0 (Etempvar _t'1 tuint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _get_unaligned_le32 (Tfunction ((tptr tvoid) :: nil) tuint
                                    cc_default))
        ((Ebinop Oadd (Etempvar _s (tptr tuchar))
           (Econst_int (Int.repr 4) tint) (tptr tuchar)) :: nil))
      (Sset _a1 (Etempvar _t'2 tuint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _get_unaligned_le32 (Tfunction ((tptr tvoid) :: nil) tuint
                                      cc_default))
          ((Ebinop Oadd (Etempvar _s (tptr tuchar))
             (Econst_int (Int.repr 8) tint) (tptr tuchar)) :: nil))
        (Sset _a2 (Etempvar _t'3 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _get_unaligned_le32 (Tfunction ((tptr tvoid) :: nil) tuint
                                        cc_default))
            ((Ebinop Oadd (Etempvar _s (tptr tuchar))
               (Econst_int (Int.repr 12) tint) (tptr tuchar)) :: nil))
          (Sset _a3 (Etempvar _t'4 tuint)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'5)
              (Evar _get_unaligned_le32 (Tfunction ((tptr tvoid) :: nil)
                                          tuint cc_default))
              ((Ebinop Oadd (Etempvar _s (tptr tuchar))
                 (Econst_int (Int.repr 16) tint) (tptr tuchar)) :: nil))
            (Sset _a4 (Etempvar _t'5 tuint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'6)
                (Evar _get_unaligned_le32 (Tfunction ((tptr tvoid) :: nil)
                                            tuint cc_default))
                ((Ebinop Oadd (Etempvar _s (tptr tuchar))
                   (Econst_int (Int.repr 20) tint) (tptr tuchar)) :: nil))
              (Sset _a5 (Etempvar _t'6 tuint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'7)
                  (Evar _get_unaligned_le32 (Tfunction ((tptr tvoid) :: nil)
                                              tuint cc_default))
                  ((Ebinop Oadd (Etempvar _s (tptr tuchar))
                     (Econst_int (Int.repr 24) tint) (tptr tuchar)) :: nil))
                (Sset _a6 (Etempvar _t'7 tuint)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'8)
                    (Evar _get_unaligned_le32 (Tfunction
                                                ((tptr tvoid) :: nil) tuint
                                                cc_default))
                    ((Ebinop Oadd (Etempvar _s (tptr tuchar))
                       (Econst_int (Int.repr 28) tint) (tptr tuchar)) :: nil))
                  (Sset _a7 (Etempvar _t'8 tuint)))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _h (tptr tuint))
                        (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
                    (Ebinop Oand (Etempvar _a0 tuint)
                      (Ebinop Osub
                        (Ebinop Oshl (Econst_int (Int.repr 1) tint)
                          (Econst_int (Int.repr 26) tint) tint)
                        (Econst_int (Int.repr 1) tint) tint) tuint))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Etempvar _h (tptr tuint))
                          (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint)
                      (Ebinop Oor
                        (Ebinop Oshr (Etempvar _a0 tuint)
                          (Econst_int (Int.repr 26) tint) tuint)
                        (Ebinop Oshl
                          (Ebinop Oand (Etempvar _a1 tuint)
                            (Ebinop Osub
                              (Ebinop Oshl (Econst_int (Int.repr 1) tint)
                                (Econst_int (Int.repr 19) tint) tint)
                              (Econst_int (Int.repr 1) tint) tint) tuint)
                          (Econst_int (Int.repr 6) tint) tuint) tuint))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _h (tptr tuint))
                            (Econst_int (Int.repr 2) tint) (tptr tuint))
                          tuint)
                        (Ebinop Oor
                          (Ebinop Oshr (Etempvar _a1 tuint)
                            (Econst_int (Int.repr 19) tint) tuint)
                          (Ebinop Oshl
                            (Ebinop Oand (Etempvar _a2 tuint)
                              (Ebinop Osub
                                (Ebinop Oshl (Econst_int (Int.repr 1) tint)
                                  (Econst_int (Int.repr 13) tint) tint)
                                (Econst_int (Int.repr 1) tint) tint) tuint)
                            (Econst_int (Int.repr 13) tint) tuint) tuint))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _h (tptr tuint))
                              (Econst_int (Int.repr 3) tint) (tptr tuint))
                            tuint)
                          (Ebinop Oor
                            (Ebinop Oshr (Etempvar _a2 tuint)
                              (Econst_int (Int.repr 13) tint) tuint)
                            (Ebinop Oshl
                              (Ebinop Oand (Etempvar _a3 tuint)
                                (Ebinop Osub
                                  (Ebinop Oshl (Econst_int (Int.repr 1) tint)
                                    (Econst_int (Int.repr 6) tint) tint)
                                  (Econst_int (Int.repr 1) tint) tint) tuint)
                              (Econst_int (Int.repr 19) tint) tuint) tuint))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Etempvar _h (tptr tuint))
                                (Econst_int (Int.repr 4) tint) (tptr tuint))
                              tuint)
                            (Ebinop Oshr (Etempvar _a3 tuint)
                              (Econst_int (Int.repr 6) tint) tuint))
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Etempvar _h (tptr tuint))
                                  (Econst_int (Int.repr 5) tint)
                                  (tptr tuint)) tuint)
                              (Ebinop Oand (Etempvar _a4 tuint)
                                (Ebinop Osub
                                  (Ebinop Oshl (Econst_int (Int.repr 1) tint)
                                    (Econst_int (Int.repr 25) tint) tint)
                                  (Econst_int (Int.repr 1) tint) tint) tuint))
                            (Ssequence
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd (Etempvar _h (tptr tuint))
                                    (Econst_int (Int.repr 6) tint)
                                    (tptr tuint)) tuint)
                                (Ebinop Oor
                                  (Ebinop Oshr (Etempvar _a4 tuint)
                                    (Econst_int (Int.repr 25) tint) tuint)
                                  (Ebinop Oshl
                                    (Ebinop Oand (Etempvar _a5 tuint)
                                      (Ebinop Osub
                                        (Ebinop Oshl
                                          (Econst_int (Int.repr 1) tint)
                                          (Econst_int (Int.repr 19) tint)
                                          tint)
                                        (Econst_int (Int.repr 1) tint) tint)
                                      tuint) (Econst_int (Int.repr 7) tint)
                                    tuint) tuint))
                              (Ssequence
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _h (tptr tuint))
                                      (Econst_int (Int.repr 7) tint)
                                      (tptr tuint)) tuint)
                                  (Ebinop Oor
                                    (Ebinop Oshr (Etempvar _a5 tuint)
                                      (Econst_int (Int.repr 19) tint) tuint)
                                    (Ebinop Oshl
                                      (Ebinop Oand (Etempvar _a6 tuint)
                                        (Ebinop Osub
                                          (Ebinop Oshl
                                            (Econst_int (Int.repr 1) tint)
                                            (Econst_int (Int.repr 12) tint)
                                            tint)
                                          (Econst_int (Int.repr 1) tint)
                                          tint) tuint)
                                      (Econst_int (Int.repr 13) tint) tuint)
                                    tuint))
                                (Ssequence
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd (Etempvar _h (tptr tuint))
                                        (Econst_int (Int.repr 8) tint)
                                        (tptr tuint)) tuint)
                                    (Ebinop Oor
                                      (Ebinop Oshr (Etempvar _a6 tuint)
                                        (Econst_int (Int.repr 12) tint)
                                        tuint)
                                      (Ebinop Oshl
                                        (Ebinop Oand (Etempvar _a7 tuint)
                                          (Ebinop Osub
                                            (Ebinop Oshl
                                              (Econst_int (Int.repr 1) tint)
                                              (Econst_int (Int.repr 6) tint)
                                              tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint) tuint)
                                        (Econst_int (Int.repr 20) tint)
                                        tuint) tuint))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd (Etempvar _h (tptr tuint))
                                        (Econst_int (Int.repr 9) tint)
                                        (tptr tuint)) tuint)
                                    (Ebinop Oand
                                      (Ebinop Oshr (Etempvar _a7 tuint)
                                        (Econst_int (Int.repr 6) tint) tuint)
                                      (Ebinop Osub
                                        (Ebinop Oshl
                                          (Econst_int (Int.repr 1) tint)
                                          (Econst_int (Int.repr 25) tint)
                                          tint)
                                        (Econst_int (Int.repr 1) tint) tint)
                                      tuint)))))))))))))))))))
|}.

Definition f_fe_frombytes := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _fe noattr))) :: (_s, (tptr tuchar)) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _fe_frombytes_impl (Tfunction ((tptr tuint) :: (tptr tuchar) :: nil)
                             tvoid cc_default))
  ((Efield
     (Ederef (Etempvar _h (tptr (Tstruct _fe noattr))) (Tstruct _fe noattr))
     _v (tarray tuint 10)) :: (Etempvar _s (tptr tuchar)) :: nil))
|}.

Definition f_addcarryx_u25 := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_c, tuchar) :: (_a, tuint) :: (_b, tuint) ::
                (_low, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_x, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _x
    (Ebinop Oadd (Ebinop Oadd (Etempvar _a tuint) (Etempvar _b tuint) tuint)
      (Etempvar _c tuchar) tuint))
  (Ssequence
    (Sassign (Ederef (Etempvar _low (tptr tuint)) tuint)
      (Ebinop Oand (Etempvar _x tuint)
        (Ebinop Osub
          (Ebinop Oshl (Econst_int (Int.repr 1) tint)
            (Econst_int (Int.repr 25) tint) tint)
          (Econst_int (Int.repr 1) tint) tint) tuint))
    (Sreturn (Some (Ebinop Oand
                     (Ebinop Oshr (Etempvar _x tuint)
                       (Econst_int (Int.repr 25) tint) tuint)
                     (Econst_int (Int.repr 1) tint) tuint)))))
|}.

Definition f_addcarryx_u26 := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_c, tuchar) :: (_a, tuint) :: (_b, tuint) ::
                (_low, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_x, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _x
    (Ebinop Oadd (Ebinop Oadd (Etempvar _a tuint) (Etempvar _b tuint) tuint)
      (Etempvar _c tuchar) tuint))
  (Ssequence
    (Sassign (Ederef (Etempvar _low (tptr tuint)) tuint)
      (Ebinop Oand (Etempvar _x tuint)
        (Ebinop Osub
          (Ebinop Oshl (Econst_int (Int.repr 1) tint)
            (Econst_int (Int.repr 26) tint) tint)
          (Econst_int (Int.repr 1) tint) tint) tuint))
    (Sreturn (Some (Ebinop Oand
                     (Ebinop Oshr (Etempvar _x tuint)
                       (Econst_int (Int.repr 26) tint) tuint)
                     (Econst_int (Int.repr 1) tint) tuint)))))
|}.

Definition f_subborrow_u25 := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_c, tuchar) :: (_a, tuint) :: (_b, tuint) ::
                (_low, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_x, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _x
    (Ebinop Osub (Ebinop Osub (Etempvar _a tuint) (Etempvar _b tuint) tuint)
      (Etempvar _c tuchar) tuint))
  (Ssequence
    (Sassign (Ederef (Etempvar _low (tptr tuint)) tuint)
      (Ebinop Oand (Etempvar _x tuint)
        (Ebinop Osub
          (Ebinop Oshl (Econst_int (Int.repr 1) tint)
            (Econst_int (Int.repr 25) tint) tint)
          (Econst_int (Int.repr 1) tint) tint) tuint))
    (Sreturn (Some (Ebinop Oshr (Etempvar _x tuint)
                     (Econst_int (Int.repr 31) tint) tuint)))))
|}.

Definition f_subborrow_u26 := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_c, tuchar) :: (_a, tuint) :: (_b, tuint) ::
                (_low, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_x, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _x
    (Ebinop Osub (Ebinop Osub (Etempvar _a tuint) (Etempvar _b tuint) tuint)
      (Etempvar _c tuchar) tuint))
  (Ssequence
    (Sassign (Ederef (Etempvar _low (tptr tuint)) tuint)
      (Ebinop Oand (Etempvar _x tuint)
        (Ebinop Osub
          (Ebinop Oshl (Econst_int (Int.repr 1) tint)
            (Econst_int (Int.repr 26) tint) tint)
          (Econst_int (Int.repr 1) tint) tint) tuint))
    (Sreturn (Some (Ebinop Oshr (Etempvar _x tuint)
                     (Econst_int (Int.repr 31) tint) tuint)))))
|}.

Definition f_cmovznz32 := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_t, tuint) :: (_z, tuint) :: (_nz, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sset _t
    (Eunop Oneg
      (Eunop Onotbool (Eunop Onotbool (Etempvar _t tuint) tint) tint) tint))
  (Sreturn (Some (Ebinop Oor
                   (Ebinop Oand (Etempvar _t tuint) (Etempvar _nz tuint)
                     tuint)
                   (Ebinop Oand (Eunop Onotint (Etempvar _t tuint) tuint)
                     (Etempvar _z tuint) tuint) tuint))))
|}.

Definition f_fe_freeze := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuint)) :: (_in1, (tptr tuint)) :: nil);
  fn_vars := ((_x20, tuint) :: (_x23, tuint) :: (_x26, tuint) ::
              (_x29, tuint) :: (_x32, tuint) :: (_x35, tuint) ::
              (_x38, tuint) :: (_x41, tuint) :: (_x44, tuint) ::
              (_x47, tuint) :: (_x52, tuint) :: (_x56, tuint) ::
              (_x60, tuint) :: (_x64, tuint) :: (_x68, tuint) ::
              (_x72, tuint) :: (_x76, tuint) :: (_x80, tuint) ::
              (_x84, tuint) :: (_x88, tuint) :: nil);
  fn_temps := ((_x17, tuint) :: (_x18, tuint) :: (_x16, tuint) ::
               (_x14, tuint) :: (_x12, tuint) :: (_x10, tuint) ::
               (_x8, tuint) :: (_x6, tuint) :: (_x4, tuint) ::
               (_x2, tuint) :: (_x21, tuchar) :: (_x24, tuchar) ::
               (_x27, tuchar) :: (_x30, tuchar) :: (_x33, tuchar) ::
               (_x36, tuchar) :: (_x39, tuchar) :: (_x42, tuchar) ::
               (_x45, tuchar) :: (_x48, tuchar) :: (_x49, tuint) ::
               (_x50, tuint) :: (_x53, tuchar) :: (_x54, tuint) ::
               (_x57, tuchar) :: (_x58, tuint) :: (_x61, tuchar) ::
               (_x62, tuint) :: (_x65, tuchar) :: (_x66, tuint) ::
               (_x69, tuchar) :: (_x70, tuint) :: (_x73, tuchar) ::
               (_x74, tuint) :: (_x77, tuchar) :: (_x78, tuint) ::
               (_x81, tuchar) :: (_x82, tuint) :: (_x85, tuchar) ::
               (_x86, tuint) :: (_t'20, tuchar) :: (_t'19, tuchar) ::
               (_t'18, tuchar) :: (_t'17, tuchar) :: (_t'16, tuchar) ::
               (_t'15, tuchar) :: (_t'14, tuchar) :: (_t'13, tuchar) ::
               (_t'12, tuchar) :: (_t'11, tuint) :: (_t'10, tuchar) ::
               (_t'9, tuchar) :: (_t'8, tuchar) :: (_t'7, tuchar) ::
               (_t'6, tuchar) :: (_t'5, tuchar) :: (_t'4, tuchar) ::
               (_t'3, tuchar) :: (_t'2, tuchar) :: (_t'1, tuchar) ::
               (_t'40, tuint) :: (_t'39, tuint) :: (_t'38, tuint) ::
               (_t'37, tuint) :: (_t'36, tuint) :: (_t'35, tuint) ::
               (_t'34, tuint) :: (_t'33, tuint) :: (_t'32, tuint) ::
               (_t'31, tuint) :: (_t'30, tuint) :: (_t'29, tuint) ::
               (_t'28, tuint) :: (_t'27, tuint) :: (_t'26, tuint) ::
               (_t'25, tuint) :: (_t'24, tuint) :: (_t'23, tuint) ::
               (_t'22, tuint) :: (_t'21, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _x17
    (Ederef
      (Ebinop Oadd (Etempvar _in1 (tptr tuint))
        (Econst_int (Int.repr 9) tint) (tptr tuint)) tuint))
  (Ssequence
    (Sset _x18
      (Ederef
        (Ebinop Oadd (Etempvar _in1 (tptr tuint))
          (Econst_int (Int.repr 8) tint) (tptr tuint)) tuint))
    (Ssequence
      (Sset _x16
        (Ederef
          (Ebinop Oadd (Etempvar _in1 (tptr tuint))
            (Econst_int (Int.repr 7) tint) (tptr tuint)) tuint))
      (Ssequence
        (Sset _x14
          (Ederef
            (Ebinop Oadd (Etempvar _in1 (tptr tuint))
              (Econst_int (Int.repr 6) tint) (tptr tuint)) tuint))
        (Ssequence
          (Sset _x12
            (Ederef
              (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                (Econst_int (Int.repr 5) tint) (tptr tuint)) tuint))
          (Ssequence
            (Sset _x10
              (Ederef
                (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                  (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint))
            (Ssequence
              (Sset _x8
                (Ederef
                  (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                    (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint))
              (Ssequence
                (Sset _x6
                  (Ederef
                    (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                      (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint))
                (Ssequence
                  (Sset _x4
                    (Ederef
                      (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                        (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint))
                  (Ssequence
                    (Sset _x2
                      (Ederef
                        (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'1)
                          (Evar _subborrow_u26 (Tfunction
                                                 (tuchar :: tuint :: tuint ::
                                                  (tptr tuint) :: nil) tuchar
                                                 cc_default))
                          ((Econst_int (Int.repr 0) tint) ::
                           (Etempvar _x2 tuint) ::
                           (Econst_int (Int.repr 67108845) tint) ::
                           (Eaddrof (Evar _x20 tuint) (tptr tuint)) :: nil))
                        (Sset _x21 (Ecast (Etempvar _t'1 tuchar) tuchar)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'2)
                            (Evar _subborrow_u25 (Tfunction
                                                   (tuchar :: tuint ::
                                                    tuint :: (tptr tuint) ::
                                                    nil) tuchar cc_default))
                            ((Etempvar _x21 tuchar) ::
                             (Etempvar _x4 tuint) ::
                             (Econst_int (Int.repr 33554431) tint) ::
                             (Eaddrof (Evar _x23 tuint) (tptr tuint)) :: nil))
                          (Sset _x24 (Ecast (Etempvar _t'2 tuchar) tuchar)))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'3)
                              (Evar _subborrow_u26 (Tfunction
                                                     (tuchar :: tuint ::
                                                      tuint ::
                                                      (tptr tuint) :: nil)
                                                     tuchar cc_default))
                              ((Etempvar _x24 tuchar) ::
                               (Etempvar _x6 tuint) ::
                               (Econst_int (Int.repr 67108863) tint) ::
                               (Eaddrof (Evar _x26 tuint) (tptr tuint)) ::
                               nil))
                            (Sset _x27 (Ecast (Etempvar _t'3 tuchar) tuchar)))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'4)
                                (Evar _subborrow_u25 (Tfunction
                                                       (tuchar :: tuint ::
                                                        tuint ::
                                                        (tptr tuint) :: nil)
                                                       tuchar cc_default))
                                ((Etempvar _x27 tuchar) ::
                                 (Etempvar _x8 tuint) ::
                                 (Econst_int (Int.repr 33554431) tint) ::
                                 (Eaddrof (Evar _x29 tuint) (tptr tuint)) ::
                                 nil))
                              (Sset _x30
                                (Ecast (Etempvar _t'4 tuchar) tuchar)))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'5)
                                  (Evar _subborrow_u26 (Tfunction
                                                         (tuchar :: tuint ::
                                                          tuint ::
                                                          (tptr tuint) ::
                                                          nil) tuchar
                                                         cc_default))
                                  ((Etempvar _x30 tuchar) ::
                                   (Etempvar _x10 tuint) ::
                                   (Econst_int (Int.repr 67108863) tint) ::
                                   (Eaddrof (Evar _x32 tuint) (tptr tuint)) ::
                                   nil))
                                (Sset _x33
                                  (Ecast (Etempvar _t'5 tuchar) tuchar)))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'6)
                                    (Evar _subborrow_u25 (Tfunction
                                                           (tuchar ::
                                                            tuint :: tuint ::
                                                            (tptr tuint) ::
                                                            nil) tuchar
                                                           cc_default))
                                    ((Etempvar _x33 tuchar) ::
                                     (Etempvar _x12 tuint) ::
                                     (Econst_int (Int.repr 33554431) tint) ::
                                     (Eaddrof (Evar _x35 tuint) (tptr tuint)) ::
                                     nil))
                                  (Sset _x36
                                    (Ecast (Etempvar _t'6 tuchar) tuchar)))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'7)
                                      (Evar _subborrow_u26 (Tfunction
                                                             (tuchar ::
                                                              tuint ::
                                                              tuint ::
                                                              (tptr tuint) ::
                                                              nil) tuchar
                                                             cc_default))
                                      ((Etempvar _x36 tuchar) ::
                                       (Etempvar _x14 tuint) ::
                                       (Econst_int (Int.repr 67108863) tint) ::
                                       (Eaddrof (Evar _x38 tuint)
                                         (tptr tuint)) :: nil))
                                    (Sset _x39
                                      (Ecast (Etempvar _t'7 tuchar) tuchar)))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'8)
                                        (Evar _subborrow_u25 (Tfunction
                                                               (tuchar ::
                                                                tuint ::
                                                                tuint ::
                                                                (tptr tuint) ::
                                                                nil) tuchar
                                                               cc_default))
                                        ((Etempvar _x39 tuchar) ::
                                         (Etempvar _x16 tuint) ::
                                         (Econst_int (Int.repr 33554431) tint) ::
                                         (Eaddrof (Evar _x41 tuint)
                                           (tptr tuint)) :: nil))
                                      (Sset _x42
                                        (Ecast (Etempvar _t'8 tuchar) tuchar)))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'9)
                                          (Evar _subborrow_u26 (Tfunction
                                                                 (tuchar ::
                                                                  tuint ::
                                                                  tuint ::
                                                                  (tptr tuint) ::
                                                                  nil) tuchar
                                                                 cc_default))
                                          ((Etempvar _x42 tuchar) ::
                                           (Etempvar _x18 tuint) ::
                                           (Econst_int (Int.repr 67108863) tint) ::
                                           (Eaddrof (Evar _x44 tuint)
                                             (tptr tuint)) :: nil))
                                        (Sset _x45
                                          (Ecast (Etempvar _t'9 tuchar)
                                            tuchar)))
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'10)
                                            (Evar _subborrow_u25 (Tfunction
                                                                   (tuchar ::
                                                                    tuint ::
                                                                    tuint ::
                                                                    (tptr tuint) ::
                                                                    nil)
                                                                   tuchar
                                                                   cc_default))
                                            ((Etempvar _x45 tuchar) ::
                                             (Etempvar _x17 tuint) ::
                                             (Econst_int (Int.repr 33554431) tint) ::
                                             (Eaddrof (Evar _x47 tuint)
                                               (tptr tuint)) :: nil))
                                          (Sset _x48
                                            (Ecast (Etempvar _t'10 tuchar)
                                              tuchar)))
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'11)
                                              (Evar _cmovznz32 (Tfunction
                                                                 (tuint ::
                                                                  tuint ::
                                                                  tuint ::
                                                                  nil) tuint
                                                                 cc_default))
                                              ((Etempvar _x48 tuchar) ::
                                               (Econst_int (Int.repr 0) tint) ::
                                               (Econst_int (Int.repr (-1)) tuint) ::
                                               nil))
                                            (Sset _x49
                                              (Etempvar _t'11 tuint)))
                                          (Ssequence
                                            (Sset _x50
                                              (Ebinop Oand
                                                (Etempvar _x49 tuint)
                                                (Econst_int (Int.repr 67108845) tint)
                                                tuint))
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'40
                                                    (Evar _x20 tuint))
                                                  (Scall (Some _t'12)
                                                    (Evar _addcarryx_u26 
                                                    (Tfunction
                                                      (tuchar :: tuint ::
                                                       tuint ::
                                                       (tptr tuint) :: nil)
                                                      tuchar cc_default))
                                                    ((Econst_int (Int.repr 0) tint) ::
                                                     (Etempvar _t'40 tuint) ::
                                                     (Etempvar _x50 tuint) ::
                                                     (Eaddrof
                                                       (Evar _x52 tuint)
                                                       (tptr tuint)) :: nil)))
                                                (Sset _x53
                                                  (Ecast
                                                    (Etempvar _t'12 tuchar)
                                                    tuchar)))
                                              (Ssequence
                                                (Sset _x54
                                                  (Ebinop Oand
                                                    (Etempvar _x49 tuint)
                                                    (Econst_int (Int.repr 33554431) tint)
                                                    tuint))
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'39
                                                        (Evar _x23 tuint))
                                                      (Scall (Some _t'13)
                                                        (Evar _addcarryx_u25 
                                                        (Tfunction
                                                          (tuchar :: tuint ::
                                                           tuint ::
                                                           (tptr tuint) ::
                                                           nil) tuchar
                                                          cc_default))
                                                        ((Etempvar _x53 tuchar) ::
                                                         (Etempvar _t'39 tuint) ::
                                                         (Etempvar _x54 tuint) ::
                                                         (Eaddrof
                                                           (Evar _x56 tuint)
                                                           (tptr tuint)) ::
                                                         nil)))
                                                    (Sset _x57
                                                      (Ecast
                                                        (Etempvar _t'13 tuchar)
                                                        tuchar)))
                                                  (Ssequence
                                                    (Sset _x58
                                                      (Ebinop Oand
                                                        (Etempvar _x49 tuint)
                                                        (Econst_int (Int.repr 67108863) tint)
                                                        tuint))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'38
                                                            (Evar _x26 tuint))
                                                          (Scall (Some _t'14)
                                                            (Evar _addcarryx_u26 
                                                            (Tfunction
                                                              (tuchar ::
                                                               tuint ::
                                                               tuint ::
                                                               (tptr tuint) ::
                                                               nil) tuchar
                                                              cc_default))
                                                            ((Etempvar _x57 tuchar) ::
                                                             (Etempvar _t'38 tuint) ::
                                                             (Etempvar _x58 tuint) ::
                                                             (Eaddrof
                                                               (Evar _x60 tuint)
                                                               (tptr tuint)) ::
                                                             nil)))
                                                        (Sset _x61
                                                          (Ecast
                                                            (Etempvar _t'14 tuchar)
                                                            tuchar)))
                                                      (Ssequence
                                                        (Sset _x62
                                                          (Ebinop Oand
                                                            (Etempvar _x49 tuint)
                                                            (Econst_int (Int.repr 33554431) tint)
                                                            tuint))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'37
                                                                (Evar _x29 tuint))
                                                              (Scall (Some _t'15)
                                                                (Evar _addcarryx_u25 
                                                                (Tfunction
                                                                  (tuchar ::
                                                                   tuint ::
                                                                   tuint ::
                                                                   (tptr tuint) ::
                                                                   nil)
                                                                  tuchar
                                                                  cc_default))
                                                                ((Etempvar _x61 tuchar) ::
                                                                 (Etempvar _t'37 tuint) ::
                                                                 (Etempvar _x62 tuint) ::
                                                                 (Eaddrof
                                                                   (Evar _x64 tuint)
                                                                   (tptr tuint)) ::
                                                                 nil)))
                                                            (Sset _x65
                                                              (Ecast
                                                                (Etempvar _t'15 tuchar)
                                                                tuchar)))
                                                          (Ssequence
                                                            (Sset _x66
                                                              (Ebinop Oand
                                                                (Etempvar _x49 tuint)
                                                                (Econst_int (Int.repr 67108863) tint)
                                                                tuint))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'36
                                                                    (Evar _x32 tuint))
                                                                  (Scall (Some _t'16)
                                                                    (Evar _addcarryx_u26 
                                                                    (Tfunction
                                                                    (tuchar ::
                                                                    tuint ::
                                                                    tuint ::
                                                                    (tptr tuint) ::
                                                                    nil)
                                                                    tuchar
                                                                    cc_default))
                                                                    ((Etempvar _x65 tuchar) ::
                                                                    (Etempvar _t'36 tuint) ::
                                                                    (Etempvar _x66 tuint) ::
                                                                    (Eaddrof
                                                                    (Evar _x68 tuint)
                                                                    (tptr tuint)) ::
                                                                    nil)))
                                                                (Sset _x69
                                                                  (Ecast
                                                                    (Etempvar _t'16 tuchar)
                                                                    tuchar)))
                                                              (Ssequence
                                                                (Sset _x70
                                                                  (Ebinop Oand
                                                                    (Etempvar _x49 tuint)
                                                                    (Econst_int (Int.repr 33554431) tint)
                                                                    tuint))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'35
                                                                    (Evar _x35 tuint))
                                                                    (Scall (Some _t'17)
                                                                    (Evar _addcarryx_u25 
                                                                    (Tfunction
                                                                    (tuchar ::
                                                                    tuint ::
                                                                    tuint ::
                                                                    (tptr tuint) ::
                                                                    nil)
                                                                    tuchar
                                                                    cc_default))
                                                                    ((Etempvar _x69 tuchar) ::
                                                                    (Etempvar _t'35 tuint) ::
                                                                    (Etempvar _x70 tuint) ::
                                                                    (Eaddrof
                                                                    (Evar _x72 tuint)
                                                                    (tptr tuint)) ::
                                                                    nil)))
                                                                    (Sset _x73
                                                                    (Ecast
                                                                    (Etempvar _t'17 tuchar)
                                                                    tuchar)))
                                                                  (Ssequence
                                                                    (Sset _x74
                                                                    (Ebinop Oand
                                                                    (Etempvar _x49 tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'34
                                                                    (Evar _x38 tuint))
                                                                    (Scall (Some _t'18)
                                                                    (Evar _addcarryx_u26 
                                                                    (Tfunction
                                                                    (tuchar ::
                                                                    tuint ::
                                                                    tuint ::
                                                                    (tptr tuint) ::
                                                                    nil)
                                                                    tuchar
                                                                    cc_default))
                                                                    ((Etempvar _x73 tuchar) ::
                                                                    (Etempvar _t'34 tuint) ::
                                                                    (Etempvar _x74 tuint) ::
                                                                    (Eaddrof
                                                                    (Evar _x76 tuint)
                                                                    (tptr tuint)) ::
                                                                    nil)))
                                                                    (Sset _x77
                                                                    (Ecast
                                                                    (Etempvar _t'18 tuchar)
                                                                    tuchar)))
                                                                    (Ssequence
                                                                    (Sset _x78
                                                                    (Ebinop Oand
                                                                    (Etempvar _x49 tuint)
                                                                    (Econst_int (Int.repr 33554431) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'33
                                                                    (Evar _x41 tuint))
                                                                    (Scall (Some _t'19)
                                                                    (Evar _addcarryx_u25 
                                                                    (Tfunction
                                                                    (tuchar ::
                                                                    tuint ::
                                                                    tuint ::
                                                                    (tptr tuint) ::
                                                                    nil)
                                                                    tuchar
                                                                    cc_default))
                                                                    ((Etempvar _x77 tuchar) ::
                                                                    (Etempvar _t'33 tuint) ::
                                                                    (Etempvar _x78 tuint) ::
                                                                    (Eaddrof
                                                                    (Evar _x80 tuint)
                                                                    (tptr tuint)) ::
                                                                    nil)))
                                                                    (Sset _x81
                                                                    (Ecast
                                                                    (Etempvar _t'19 tuchar)
                                                                    tuchar)))
                                                                    (Ssequence
                                                                    (Sset _x82
                                                                    (Ebinop Oand
                                                                    (Etempvar _x49 tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'32
                                                                    (Evar _x44 tuint))
                                                                    (Scall (Some _t'20)
                                                                    (Evar _addcarryx_u26 
                                                                    (Tfunction
                                                                    (tuchar ::
                                                                    tuint ::
                                                                    tuint ::
                                                                    (tptr tuint) ::
                                                                    nil)
                                                                    tuchar
                                                                    cc_default))
                                                                    ((Etempvar _x81 tuchar) ::
                                                                    (Etempvar _t'32 tuint) ::
                                                                    (Etempvar _x82 tuint) ::
                                                                    (Eaddrof
                                                                    (Evar _x84 tuint)
                                                                    (tptr tuint)) ::
                                                                    nil)))
                                                                    (Sset _x85
                                                                    (Ecast
                                                                    (Etempvar _t'20 tuchar)
                                                                    tuchar)))
                                                                    (Ssequence
                                                                    (Sset _x86
                                                                    (Ebinop Oand
                                                                    (Etempvar _x49 tuint)
                                                                    (Econst_int (Int.repr 33554431) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'31
                                                                    (Evar _x47 tuint))
                                                                    (Scall None
                                                                    (Evar _addcarryx_u25 
                                                                    (Tfunction
                                                                    (tuchar ::
                                                                    tuint ::
                                                                    tuint ::
                                                                    (tptr tuint) ::
                                                                    nil)
                                                                    tuchar
                                                                    cc_default))
                                                                    ((Etempvar _x85 tuchar) ::
                                                                    (Etempvar _t'31 tuint) ::
                                                                    (Etempvar _x86 tuint) ::
                                                                    (Eaddrof
                                                                    (Evar _x88 tuint)
                                                                    (tptr tuint)) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'30
                                                                    (Evar _x52 tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'30 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'29
                                                                    (Evar _x56 tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'29 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'28
                                                                    (Evar _x60 tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'28 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'27
                                                                    (Evar _x64 tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'27 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'26
                                                                    (Evar _x68 tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'26 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'25
                                                                    (Evar _x72 tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'25 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'24
                                                                    (Evar _x76 tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'24 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'23
                                                                    (Evar _x80 tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'23 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'22
                                                                    (Evar _x84 tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'22 tuint)))
                                                                    (Ssequence
                                                                    (Sset _t'21
                                                                    (Evar _x88 tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'21 tuint)))))))))))))))))))))))))))))))))))))))))))))))))))))
|}.

Definition f_fe_tobytes := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr tuchar)) :: (_f, (tptr (Tstruct _fe noattr))) ::
                nil);
  fn_vars := ((_h, (tarray tuint 10)) :: nil);
  fn_temps := ((_t'40, tuint) :: (_t'39, tuint) :: (_t'38, tuint) ::
               (_t'37, tuint) :: (_t'36, tuint) :: (_t'35, tuint) ::
               (_t'34, tuint) :: (_t'33, tuint) :: (_t'32, tuint) ::
               (_t'31, tuint) :: (_t'30, tuint) :: (_t'29, tuint) ::
               (_t'28, tuint) :: (_t'27, tuint) :: (_t'26, tuint) ::
               (_t'25, tuint) :: (_t'24, tuint) :: (_t'23, tuint) ::
               (_t'22, tuint) :: (_t'21, tuint) :: (_t'20, tuint) ::
               (_t'19, tuint) :: (_t'18, tuint) :: (_t'17, tuint) ::
               (_t'16, tuint) :: (_t'15, tuint) :: (_t'14, tuint) ::
               (_t'13, tuint) :: (_t'12, tuint) :: (_t'11, tuint) ::
               (_t'10, tuint) :: (_t'9, tuint) :: (_t'8, tuint) ::
               (_t'7, tuint) :: (_t'6, tuint) :: (_t'5, tuint) ::
               (_t'4, tuint) :: (_t'3, tuint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _fe_freeze (Tfunction ((tptr tuint) :: (tptr tuint) :: nil) tvoid
                       cc_default))
    ((Evar _h (tarray tuint 10)) ::
     (Efield
       (Ederef (Etempvar _f (tptr (Tstruct _fe noattr)))
         (Tstruct _fe noattr)) _v (tarray tuint 10)) :: nil))
  (Ssequence
    (Ssequence
      (Sset _t'40
        (Ederef
          (Ebinop Oadd (Evar _h (tarray tuint 10))
            (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _s (tptr tuchar))
            (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
        (Ebinop Oshr (Etempvar _t'40 tuint) (Econst_int (Int.repr 0) tint)
          tuint)))
    (Ssequence
      (Ssequence
        (Sset _t'39
          (Ederef
            (Ebinop Oadd (Evar _h (tarray tuint 10))
              (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _s (tptr tuchar))
              (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar)
          (Ebinop Oshr (Etempvar _t'39 tuint) (Econst_int (Int.repr 8) tint)
            tuint)))
      (Ssequence
        (Ssequence
          (Sset _t'38
            (Ederef
              (Ebinop Oadd (Evar _h (tarray tuint 10))
                (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _s (tptr tuchar))
                (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar)
            (Ebinop Oshr (Etempvar _t'38 tuint)
              (Econst_int (Int.repr 16) tint) tuint)))
        (Ssequence
          (Ssequence
            (Sset _t'36
              (Ederef
                (Ebinop Oadd (Evar _h (tarray tuint 10))
                  (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
            (Ssequence
              (Sset _t'37
                (Ederef
                  (Ebinop Oadd (Evar _h (tarray tuint 10))
                    (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _s (tptr tuchar))
                    (Econst_int (Int.repr 3) tint) (tptr tuchar)) tuchar)
                (Ebinop Oor
                  (Ebinop Oshr (Etempvar _t'36 tuint)
                    (Econst_int (Int.repr 24) tint) tuint)
                  (Ebinop Oshl (Etempvar _t'37 tuint)
                    (Econst_int (Int.repr 2) tint) tuint) tuint))))
          (Ssequence
            (Ssequence
              (Sset _t'35
                (Ederef
                  (Ebinop Oadd (Evar _h (tarray tuint 10))
                    (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _s (tptr tuchar))
                    (Econst_int (Int.repr 4) tint) (tptr tuchar)) tuchar)
                (Ebinop Oshr (Etempvar _t'35 tuint)
                  (Econst_int (Int.repr 6) tint) tuint)))
            (Ssequence
              (Ssequence
                (Sset _t'34
                  (Ederef
                    (Ebinop Oadd (Evar _h (tarray tuint 10))
                      (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _s (tptr tuchar))
                      (Econst_int (Int.repr 5) tint) (tptr tuchar)) tuchar)
                  (Ebinop Oshr (Etempvar _t'34 tuint)
                    (Econst_int (Int.repr 14) tint) tuint)))
              (Ssequence
                (Ssequence
                  (Sset _t'32
                    (Ederef
                      (Ebinop Oadd (Evar _h (tarray tuint 10))
                        (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint))
                  (Ssequence
                    (Sset _t'33
                      (Ederef
                        (Ebinop Oadd (Evar _h (tarray tuint 10))
                          (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Etempvar _s (tptr tuchar))
                          (Econst_int (Int.repr 6) tint) (tptr tuchar))
                        tuchar)
                      (Ebinop Oor
                        (Ebinop Oshr (Etempvar _t'32 tuint)
                          (Econst_int (Int.repr 22) tint) tuint)
                        (Ebinop Oshl (Etempvar _t'33 tuint)
                          (Econst_int (Int.repr 3) tint) tuint) tuint))))
                (Ssequence
                  (Ssequence
                    (Sset _t'31
                      (Ederef
                        (Ebinop Oadd (Evar _h (tarray tuint 10))
                          (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Etempvar _s (tptr tuchar))
                          (Econst_int (Int.repr 7) tint) (tptr tuchar))
                        tuchar)
                      (Ebinop Oshr (Etempvar _t'31 tuint)
                        (Econst_int (Int.repr 5) tint) tuint)))
                  (Ssequence
                    (Ssequence
                      (Sset _t'30
                        (Ederef
                          (Ebinop Oadd (Evar _h (tarray tuint 10))
                            (Econst_int (Int.repr 2) tint) (tptr tuint))
                          tuint))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _s (tptr tuchar))
                            (Econst_int (Int.repr 8) tint) (tptr tuchar))
                          tuchar)
                        (Ebinop Oshr (Etempvar _t'30 tuint)
                          (Econst_int (Int.repr 13) tint) tuint)))
                    (Ssequence
                      (Ssequence
                        (Sset _t'28
                          (Ederef
                            (Ebinop Oadd (Evar _h (tarray tuint 10))
                              (Econst_int (Int.repr 2) tint) (tptr tuint))
                            tuint))
                        (Ssequence
                          (Sset _t'29
                            (Ederef
                              (Ebinop Oadd (Evar _h (tarray tuint 10))
                                (Econst_int (Int.repr 3) tint) (tptr tuint))
                              tuint))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                (Econst_int (Int.repr 9) tint) (tptr tuchar))
                              tuchar)
                            (Ebinop Oor
                              (Ebinop Oshr (Etempvar _t'28 tuint)
                                (Econst_int (Int.repr 21) tint) tuint)
                              (Ebinop Oshl (Etempvar _t'29 tuint)
                                (Econst_int (Int.repr 5) tint) tuint) tuint))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'27
                            (Ederef
                              (Ebinop Oadd (Evar _h (tarray tuint 10))
                                (Econst_int (Int.repr 3) tint) (tptr tuint))
                              tuint))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                (Econst_int (Int.repr 10) tint)
                                (tptr tuchar)) tuchar)
                            (Ebinop Oshr (Etempvar _t'27 tuint)
                              (Econst_int (Int.repr 3) tint) tuint)))
                        (Ssequence
                          (Ssequence
                            (Sset _t'26
                              (Ederef
                                (Ebinop Oadd (Evar _h (tarray tuint 10))
                                  (Econst_int (Int.repr 3) tint)
                                  (tptr tuint)) tuint))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                  (Econst_int (Int.repr 11) tint)
                                  (tptr tuchar)) tuchar)
                              (Ebinop Oshr (Etempvar _t'26 tuint)
                                (Econst_int (Int.repr 11) tint) tuint)))
                          (Ssequence
                            (Ssequence
                              (Sset _t'24
                                (Ederef
                                  (Ebinop Oadd (Evar _h (tarray tuint 10))
                                    (Econst_int (Int.repr 3) tint)
                                    (tptr tuint)) tuint))
                              (Ssequence
                                (Sset _t'25
                                  (Ederef
                                    (Ebinop Oadd (Evar _h (tarray tuint 10))
                                      (Econst_int (Int.repr 4) tint)
                                      (tptr tuint)) tuint))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                      (Econst_int (Int.repr 12) tint)
                                      (tptr tuchar)) tuchar)
                                  (Ebinop Oor
                                    (Ebinop Oshr (Etempvar _t'24 tuint)
                                      (Econst_int (Int.repr 19) tint) tuint)
                                    (Ebinop Oshl (Etempvar _t'25 tuint)
                                      (Econst_int (Int.repr 6) tint) tuint)
                                    tuint))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'23
                                  (Ederef
                                    (Ebinop Oadd (Evar _h (tarray tuint 10))
                                      (Econst_int (Int.repr 4) tint)
                                      (tptr tuint)) tuint))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                      (Econst_int (Int.repr 13) tint)
                                      (tptr tuchar)) tuchar)
                                  (Ebinop Oshr (Etempvar _t'23 tuint)
                                    (Econst_int (Int.repr 2) tint) tuint)))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'22
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _h (tarray tuint 10))
                                        (Econst_int (Int.repr 4) tint)
                                        (tptr tuint)) tuint))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _s (tptr tuchar))
                                        (Econst_int (Int.repr 14) tint)
                                        (tptr tuchar)) tuchar)
                                    (Ebinop Oshr (Etempvar _t'22 tuint)
                                      (Econst_int (Int.repr 10) tint) tuint)))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'21
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _h (tarray tuint 10))
                                          (Econst_int (Int.repr 4) tint)
                                          (tptr tuint)) tuint))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _s (tptr tuchar))
                                          (Econst_int (Int.repr 15) tint)
                                          (tptr tuchar)) tuchar)
                                      (Ebinop Oshr (Etempvar _t'21 tuint)
                                        (Econst_int (Int.repr 18) tint)
                                        tuint)))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'20
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _h (tarray tuint 10))
                                            (Econst_int (Int.repr 5) tint)
                                            (tptr tuint)) tuint))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _s (tptr tuchar))
                                            (Econst_int (Int.repr 16) tint)
                                            (tptr tuchar)) tuchar)
                                        (Ebinop Oshr (Etempvar _t'20 tuint)
                                          (Econst_int (Int.repr 0) tint)
                                          tuint)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'19
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _h (tarray tuint 10))
                                              (Econst_int (Int.repr 5) tint)
                                              (tptr tuint)) tuint))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _s (tptr tuchar))
                                              (Econst_int (Int.repr 17) tint)
                                              (tptr tuchar)) tuchar)
                                          (Ebinop Oshr (Etempvar _t'19 tuint)
                                            (Econst_int (Int.repr 8) tint)
                                            tuint)))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'18
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _h (tarray tuint 10))
                                                (Econst_int (Int.repr 5) tint)
                                                (tptr tuint)) tuint))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _s (tptr tuchar))
                                                (Econst_int (Int.repr 18) tint)
                                                (tptr tuchar)) tuchar)
                                            (Ebinop Oshr
                                              (Etempvar _t'18 tuint)
                                              (Econst_int (Int.repr 16) tint)
                                              tuint)))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'16
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _h (tarray tuint 10))
                                                  (Econst_int (Int.repr 5) tint)
                                                  (tptr tuint)) tuint))
                                            (Ssequence
                                              (Sset _t'17
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _h (tarray tuint 10))
                                                    (Econst_int (Int.repr 6) tint)
                                                    (tptr tuint)) tuint))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _s (tptr tuchar))
                                                    (Econst_int (Int.repr 19) tint)
                                                    (tptr tuchar)) tuchar)
                                                (Ebinop Oor
                                                  (Ebinop Oshr
                                                    (Etempvar _t'16 tuint)
                                                    (Econst_int (Int.repr 24) tint)
                                                    tuint)
                                                  (Ebinop Oshl
                                                    (Etempvar _t'17 tuint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tuint) tuint))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'15
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _h (tarray tuint 10))
                                                    (Econst_int (Int.repr 6) tint)
                                                    (tptr tuint)) tuint))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _s (tptr tuchar))
                                                    (Econst_int (Int.repr 20) tint)
                                                    (tptr tuchar)) tuchar)
                                                (Ebinop Oshr
                                                  (Etempvar _t'15 tuint)
                                                  (Econst_int (Int.repr 7) tint)
                                                  tuint)))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'14
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _h (tarray tuint 10))
                                                      (Econst_int (Int.repr 6) tint)
                                                      (tptr tuint)) tuint))
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _s (tptr tuchar))
                                                      (Econst_int (Int.repr 21) tint)
                                                      (tptr tuchar)) tuchar)
                                                  (Ebinop Oshr
                                                    (Etempvar _t'14 tuint)
                                                    (Econst_int (Int.repr 15) tint)
                                                    tuint)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'12
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _h (tarray tuint 10))
                                                        (Econst_int (Int.repr 6) tint)
                                                        (tptr tuint)) tuint))
                                                  (Ssequence
                                                    (Sset _t'13
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _h (tarray tuint 10))
                                                          (Econst_int (Int.repr 7) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _s (tptr tuchar))
                                                          (Econst_int (Int.repr 22) tint)
                                                          (tptr tuchar))
                                                        tuchar)
                                                      (Ebinop Oor
                                                        (Ebinop Oshr
                                                          (Etempvar _t'12 tuint)
                                                          (Econst_int (Int.repr 23) tint)
                                                          tuint)
                                                        (Ebinop Oshl
                                                          (Etempvar _t'13 tuint)
                                                          (Econst_int (Int.repr 3) tint)
                                                          tuint) tuint))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'11
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _h (tarray tuint 10))
                                                          (Econst_int (Int.repr 7) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _s (tptr tuchar))
                                                          (Econst_int (Int.repr 23) tint)
                                                          (tptr tuchar))
                                                        tuchar)
                                                      (Ebinop Oshr
                                                        (Etempvar _t'11 tuint)
                                                        (Econst_int (Int.repr 5) tint)
                                                        tuint)))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'10
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _h (tarray tuint 10))
                                                            (Econst_int (Int.repr 7) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Etempvar _s (tptr tuchar))
                                                            (Econst_int (Int.repr 24) tint)
                                                            (tptr tuchar))
                                                          tuchar)
                                                        (Ebinop Oshr
                                                          (Etempvar _t'10 tuint)
                                                          (Econst_int (Int.repr 13) tint)
                                                          tuint)))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'8
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _h (tarray tuint 10))
                                                              (Econst_int (Int.repr 7) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _t'9
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _h (tarray tuint 10))
                                                                (Econst_int (Int.repr 8) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Etempvar _s (tptr tuchar))
                                                                (Econst_int (Int.repr 25) tint)
                                                                (tptr tuchar))
                                                              tuchar)
                                                            (Ebinop Oor
                                                              (Ebinop Oshr
                                                                (Etempvar _t'8 tuint)
                                                                (Econst_int (Int.repr 21) tint)
                                                                tuint)
                                                              (Ebinop Oshl
                                                                (Etempvar _t'9 tuint)
                                                                (Econst_int (Int.repr 4) tint)
                                                                tuint) tuint))))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'7
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _h (tarray tuint 10))
                                                                (Econst_int (Int.repr 8) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Etempvar _s (tptr tuchar))
                                                                (Econst_int (Int.repr 26) tint)
                                                                (tptr tuchar))
                                                              tuchar)
                                                            (Ebinop Oshr
                                                              (Etempvar _t'7 tuint)
                                                              (Econst_int (Int.repr 4) tint)
                                                              tuint)))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'6
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _h (tarray tuint 10))
                                                                  (Econst_int (Int.repr 8) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Etempvar _s (tptr tuchar))
                                                                  (Econst_int (Int.repr 27) tint)
                                                                  (tptr tuchar))
                                                                tuchar)
                                                              (Ebinop Oshr
                                                                (Etempvar _t'6 tuint)
                                                                (Econst_int (Int.repr 12) tint)
                                                                tuint)))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'4
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _h (tarray tuint 10))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _t'5
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _h (tarray tuint 10))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Sassign
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _s (tptr tuchar))
                                                                    (Econst_int (Int.repr 28) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                  (Ebinop Oor
                                                                    (Ebinop Oshr
                                                                    (Etempvar _t'4 tuint)
                                                                    (Econst_int (Int.repr 20) tint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _t'5 tuint)
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    tuint)
                                                                    tuint))))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'3
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _h (tarray tuint 10))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Sassign
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _s (tptr tuchar))
                                                                    (Econst_int (Int.repr 29) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                  (Ebinop Oshr
                                                                    (Etempvar _t'3 tuint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tuint)))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'2
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _h (tarray tuint 10))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _s (tptr tuchar))
                                                                    (Econst_int (Int.repr 30) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Ebinop Oshr
                                                                    (Etempvar _t'2 tuint)
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    tuint)))
                                                                (Ssequence
                                                                  (Sset _t'1
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _h (tarray tuint 10))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _s (tptr tuchar))
                                                                    (Econst_int (Int.repr 31) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Ebinop Oshr
                                                                    (Etempvar _t'1 tuint)
                                                                    (Econst_int (Int.repr 18) tint)
                                                                    tuint)))))))))))))))))))))))))))))))))))
|}.

Definition f_fe_copy := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _fe noattr))) ::
                (_f, (tptr (Tstruct _fe noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'1, tuint) :: nil);
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
        (Sset _t'1
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _f (tptr (Tstruct _fe noattr)))
                  (Tstruct _fe noattr)) _v (tarray tuint 10))
              (Etempvar _i tint) (tptr tuint)) tuint))
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _h (tptr (Tstruct _fe noattr)))
                  (Tstruct _fe noattr)) _v (tarray tuint 10))
              (Etempvar _i tint) (tptr tuint)) tuint) (Etempvar _t'1 tuint))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_fe_copy_lt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _fe_loose noattr))) ::
                (_f, (tptr (Tstruct _fe noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'1, tuint) :: nil);
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
        (Sset _t'1
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _f (tptr (Tstruct _fe noattr)))
                  (Tstruct _fe noattr)) _v (tarray tuint 10))
              (Etempvar _i tint) (tptr tuint)) tuint))
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _h (tptr (Tstruct _fe_loose noattr)))
                  (Tstruct _fe_loose noattr)) _v (tarray tuint 10))
              (Etempvar _i tint) (tptr tuint)) tuint) (Etempvar _t'1 tuint))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_fe_0 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _fe noattr))) :: nil);
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
      (Sassign
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _h (tptr (Tstruct _fe noattr)))
                (Tstruct _fe noattr)) _v (tarray tuint 10))
            (Etempvar _i tint) (tptr tuint)) tuint)
        (Econst_int (Int.repr 0) tint)))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_fe_1 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _fe noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 10) tint) tint)
          Sskip
          Sbreak)
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _h (tptr (Tstruct _fe noattr)))
                  (Tstruct _fe noattr)) _v (tarray tuint 10))
              (Etempvar _i tint) (tptr tuint)) tuint)
          (Econst_int (Int.repr 0) tint)))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Sassign
    (Ederef
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _h (tptr (Tstruct _fe noattr)))
            (Tstruct _fe noattr)) _v (tarray tuint 10))
        (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
    (Econst_int (Int.repr 1) tint)))
|}.

Definition f_fe_add_impl := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuint)) :: (_in1, (tptr tuint)) ::
                (_in2, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_x20, tuint) :: (_x21, tuint) :: (_x19, tuint) ::
               (_x17, tuint) :: (_x15, tuint) :: (_x13, tuint) ::
               (_x11, tuint) :: (_x9, tuint) :: (_x7, tuint) ::
               (_x5, tuint) :: (_x38, tuint) :: (_x39, tuint) ::
               (_x37, tuint) :: (_x35, tuint) :: (_x33, tuint) ::
               (_x31, tuint) :: (_x29, tuint) :: (_x27, tuint) ::
               (_x25, tuint) :: (_x23, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _x20
    (Ederef
      (Ebinop Oadd (Etempvar _in1 (tptr tuint))
        (Econst_int (Int.repr 9) tint) (tptr tuint)) tuint))
  (Ssequence
    (Sset _x21
      (Ederef
        (Ebinop Oadd (Etempvar _in1 (tptr tuint))
          (Econst_int (Int.repr 8) tint) (tptr tuint)) tuint))
    (Ssequence
      (Sset _x19
        (Ederef
          (Ebinop Oadd (Etempvar _in1 (tptr tuint))
            (Econst_int (Int.repr 7) tint) (tptr tuint)) tuint))
      (Ssequence
        (Sset _x17
          (Ederef
            (Ebinop Oadd (Etempvar _in1 (tptr tuint))
              (Econst_int (Int.repr 6) tint) (tptr tuint)) tuint))
        (Ssequence
          (Sset _x15
            (Ederef
              (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                (Econst_int (Int.repr 5) tint) (tptr tuint)) tuint))
          (Ssequence
            (Sset _x13
              (Ederef
                (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                  (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint))
            (Ssequence
              (Sset _x11
                (Ederef
                  (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                    (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint))
              (Ssequence
                (Sset _x9
                  (Ederef
                    (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                      (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint))
                (Ssequence
                  (Sset _x7
                    (Ederef
                      (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                        (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint))
                  (Ssequence
                    (Sset _x5
                      (Ederef
                        (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
                    (Ssequence
                      (Sset _x38
                        (Ederef
                          (Ebinop Oadd (Etempvar _in2 (tptr tuint))
                            (Econst_int (Int.repr 9) tint) (tptr tuint))
                          tuint))
                      (Ssequence
                        (Sset _x39
                          (Ederef
                            (Ebinop Oadd (Etempvar _in2 (tptr tuint))
                              (Econst_int (Int.repr 8) tint) (tptr tuint))
                            tuint))
                        (Ssequence
                          (Sset _x37
                            (Ederef
                              (Ebinop Oadd (Etempvar _in2 (tptr tuint))
                                (Econst_int (Int.repr 7) tint) (tptr tuint))
                              tuint))
                          (Ssequence
                            (Sset _x35
                              (Ederef
                                (Ebinop Oadd (Etempvar _in2 (tptr tuint))
                                  (Econst_int (Int.repr 6) tint)
                                  (tptr tuint)) tuint))
                            (Ssequence
                              (Sset _x33
                                (Ederef
                                  (Ebinop Oadd (Etempvar _in2 (tptr tuint))
                                    (Econst_int (Int.repr 5) tint)
                                    (tptr tuint)) tuint))
                              (Ssequence
                                (Sset _x31
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _in2 (tptr tuint))
                                      (Econst_int (Int.repr 4) tint)
                                      (tptr tuint)) tuint))
                                (Ssequence
                                  (Sset _x29
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _in2 (tptr tuint))
                                        (Econst_int (Int.repr 3) tint)
                                        (tptr tuint)) tuint))
                                  (Ssequence
                                    (Sset _x27
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _in2 (tptr tuint))
                                          (Econst_int (Int.repr 2) tint)
                                          (tptr tuint)) tuint))
                                    (Ssequence
                                      (Sset _x25
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _in2 (tptr tuint))
                                            (Econst_int (Int.repr 1) tint)
                                            (tptr tuint)) tuint))
                                      (Ssequence
                                        (Sset _x23
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _in2 (tptr tuint))
                                              (Econst_int (Int.repr 0) tint)
                                              (tptr tuint)) tuint))
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _out (tptr tuint))
                                                (Econst_int (Int.repr 0) tint)
                                                (tptr tuint)) tuint)
                                            (Ebinop Oadd (Etempvar _x5 tuint)
                                              (Etempvar _x23 tuint) tuint))
                                          (Ssequence
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _out (tptr tuint))
                                                  (Econst_int (Int.repr 1) tint)
                                                  (tptr tuint)) tuint)
                                              (Ebinop Oadd
                                                (Etempvar _x7 tuint)
                                                (Etempvar _x25 tuint) tuint))
                                            (Ssequence
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _out (tptr tuint))
                                                    (Econst_int (Int.repr 2) tint)
                                                    (tptr tuint)) tuint)
                                                (Ebinop Oadd
                                                  (Etempvar _x9 tuint)
                                                  (Etempvar _x27 tuint)
                                                  tuint))
                                              (Ssequence
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _out (tptr tuint))
                                                      (Econst_int (Int.repr 3) tint)
                                                      (tptr tuint)) tuint)
                                                  (Ebinop Oadd
                                                    (Etempvar _x11 tuint)
                                                    (Etempvar _x29 tuint)
                                                    tuint))
                                                (Ssequence
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _out (tptr tuint))
                                                        (Econst_int (Int.repr 4) tint)
                                                        (tptr tuint)) tuint)
                                                    (Ebinop Oadd
                                                      (Etempvar _x13 tuint)
                                                      (Etempvar _x31 tuint)
                                                      tuint))
                                                  (Ssequence
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _out (tptr tuint))
                                                          (Econst_int (Int.repr 5) tint)
                                                          (tptr tuint))
                                                        tuint)
                                                      (Ebinop Oadd
                                                        (Etempvar _x15 tuint)
                                                        (Etempvar _x33 tuint)
                                                        tuint))
                                                    (Ssequence
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Etempvar _out (tptr tuint))
                                                            (Econst_int (Int.repr 6) tint)
                                                            (tptr tuint))
                                                          tuint)
                                                        (Ebinop Oadd
                                                          (Etempvar _x17 tuint)
                                                          (Etempvar _x35 tuint)
                                                          tuint))
                                                      (Ssequence
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _out (tptr tuint))
                                                              (Econst_int (Int.repr 7) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Ebinop Oadd
                                                            (Etempvar _x19 tuint)
                                                            (Etempvar _x37 tuint)
                                                            tuint))
                                                        (Ssequence
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Etempvar _out (tptr tuint))
                                                                (Econst_int (Int.repr 8) tint)
                                                                (tptr tuint))
                                                              tuint)
                                                            (Ebinop Oadd
                                                              (Etempvar _x21 tuint)
                                                              (Etempvar _x39 tuint)
                                                              tuint))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Etempvar _out (tptr tuint))
                                                                (Econst_int (Int.repr 9) tint)
                                                                (tptr tuint))
                                                              tuint)
                                                            (Ebinop Oadd
                                                              (Etempvar _x20 tuint)
                                                              (Etempvar _x38 tuint)
                                                              tuint)))))))))))))))))))))))))))))))
|}.

Definition f_fe_add := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _fe_loose noattr))) ::
                (_f, (tptr (Tstruct _fe noattr))) ::
                (_g, (tptr (Tstruct _fe noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _fe_add_impl (Tfunction
                       ((tptr tuint) :: (tptr tuint) :: (tptr tuint) :: nil)
                       tvoid cc_default))
  ((Efield
     (Ederef (Etempvar _h (tptr (Tstruct _fe_loose noattr)))
       (Tstruct _fe_loose noattr)) _v (tarray tuint 10)) ::
   (Efield
     (Ederef (Etempvar _f (tptr (Tstruct _fe noattr))) (Tstruct _fe noattr))
     _v (tarray tuint 10)) ::
   (Efield
     (Ederef (Etempvar _g (tptr (Tstruct _fe noattr))) (Tstruct _fe noattr))
     _v (tarray tuint 10)) :: nil))
|}.

Definition f_fe_sub_impl := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuint)) :: (_in1, (tptr tuint)) ::
                (_in2, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_x20, tuint) :: (_x21, tuint) :: (_x19, tuint) ::
               (_x17, tuint) :: (_x15, tuint) :: (_x13, tuint) ::
               (_x11, tuint) :: (_x9, tuint) :: (_x7, tuint) ::
               (_x5, tuint) :: (_x38, tuint) :: (_x39, tuint) ::
               (_x37, tuint) :: (_x35, tuint) :: (_x33, tuint) ::
               (_x31, tuint) :: (_x29, tuint) :: (_x27, tuint) ::
               (_x25, tuint) :: (_x23, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _x20
    (Ederef
      (Ebinop Oadd (Etempvar _in1 (tptr tuint))
        (Econst_int (Int.repr 9) tint) (tptr tuint)) tuint))
  (Ssequence
    (Sset _x21
      (Ederef
        (Ebinop Oadd (Etempvar _in1 (tptr tuint))
          (Econst_int (Int.repr 8) tint) (tptr tuint)) tuint))
    (Ssequence
      (Sset _x19
        (Ederef
          (Ebinop Oadd (Etempvar _in1 (tptr tuint))
            (Econst_int (Int.repr 7) tint) (tptr tuint)) tuint))
      (Ssequence
        (Sset _x17
          (Ederef
            (Ebinop Oadd (Etempvar _in1 (tptr tuint))
              (Econst_int (Int.repr 6) tint) (tptr tuint)) tuint))
        (Ssequence
          (Sset _x15
            (Ederef
              (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                (Econst_int (Int.repr 5) tint) (tptr tuint)) tuint))
          (Ssequence
            (Sset _x13
              (Ederef
                (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                  (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint))
            (Ssequence
              (Sset _x11
                (Ederef
                  (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                    (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint))
              (Ssequence
                (Sset _x9
                  (Ederef
                    (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                      (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint))
                (Ssequence
                  (Sset _x7
                    (Ederef
                      (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                        (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint))
                  (Ssequence
                    (Sset _x5
                      (Ederef
                        (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
                    (Ssequence
                      (Sset _x38
                        (Ederef
                          (Ebinop Oadd (Etempvar _in2 (tptr tuint))
                            (Econst_int (Int.repr 9) tint) (tptr tuint))
                          tuint))
                      (Ssequence
                        (Sset _x39
                          (Ederef
                            (Ebinop Oadd (Etempvar _in2 (tptr tuint))
                              (Econst_int (Int.repr 8) tint) (tptr tuint))
                            tuint))
                        (Ssequence
                          (Sset _x37
                            (Ederef
                              (Ebinop Oadd (Etempvar _in2 (tptr tuint))
                                (Econst_int (Int.repr 7) tint) (tptr tuint))
                              tuint))
                          (Ssequence
                            (Sset _x35
                              (Ederef
                                (Ebinop Oadd (Etempvar _in2 (tptr tuint))
                                  (Econst_int (Int.repr 6) tint)
                                  (tptr tuint)) tuint))
                            (Ssequence
                              (Sset _x33
                                (Ederef
                                  (Ebinop Oadd (Etempvar _in2 (tptr tuint))
                                    (Econst_int (Int.repr 5) tint)
                                    (tptr tuint)) tuint))
                              (Ssequence
                                (Sset _x31
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _in2 (tptr tuint))
                                      (Econst_int (Int.repr 4) tint)
                                      (tptr tuint)) tuint))
                                (Ssequence
                                  (Sset _x29
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _in2 (tptr tuint))
                                        (Econst_int (Int.repr 3) tint)
                                        (tptr tuint)) tuint))
                                  (Ssequence
                                    (Sset _x27
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _in2 (tptr tuint))
                                          (Econst_int (Int.repr 2) tint)
                                          (tptr tuint)) tuint))
                                    (Ssequence
                                      (Sset _x25
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _in2 (tptr tuint))
                                            (Econst_int (Int.repr 1) tint)
                                            (tptr tuint)) tuint))
                                      (Ssequence
                                        (Sset _x23
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _in2 (tptr tuint))
                                              (Econst_int (Int.repr 0) tint)
                                              (tptr tuint)) tuint))
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _out (tptr tuint))
                                                (Econst_int (Int.repr 0) tint)
                                                (tptr tuint)) tuint)
                                            (Ebinop Osub
                                              (Ebinop Oadd
                                                (Econst_int (Int.repr 134217690) tint)
                                                (Etempvar _x5 tuint) tuint)
                                              (Etempvar _x23 tuint) tuint))
                                          (Ssequence
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _out (tptr tuint))
                                                  (Econst_int (Int.repr 1) tint)
                                                  (tptr tuint)) tuint)
                                              (Ebinop Osub
                                                (Ebinop Oadd
                                                  (Econst_int (Int.repr 67108862) tint)
                                                  (Etempvar _x7 tuint) tuint)
                                                (Etempvar _x25 tuint) tuint))
                                            (Ssequence
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _out (tptr tuint))
                                                    (Econst_int (Int.repr 2) tint)
                                                    (tptr tuint)) tuint)
                                                (Ebinop Osub
                                                  (Ebinop Oadd
                                                    (Econst_int (Int.repr 134217726) tint)
                                                    (Etempvar _x9 tuint)
                                                    tuint)
                                                  (Etempvar _x27 tuint)
                                                  tuint))
                                              (Ssequence
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _out (tptr tuint))
                                                      (Econst_int (Int.repr 3) tint)
                                                      (tptr tuint)) tuint)
                                                  (Ebinop Osub
                                                    (Ebinop Oadd
                                                      (Econst_int (Int.repr 67108862) tint)
                                                      (Etempvar _x11 tuint)
                                                      tuint)
                                                    (Etempvar _x29 tuint)
                                                    tuint))
                                                (Ssequence
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _out (tptr tuint))
                                                        (Econst_int (Int.repr 4) tint)
                                                        (tptr tuint)) tuint)
                                                    (Ebinop Osub
                                                      (Ebinop Oadd
                                                        (Econst_int (Int.repr 134217726) tint)
                                                        (Etempvar _x13 tuint)
                                                        tuint)
                                                      (Etempvar _x31 tuint)
                                                      tuint))
                                                  (Ssequence
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _out (tptr tuint))
                                                          (Econst_int (Int.repr 5) tint)
                                                          (tptr tuint))
                                                        tuint)
                                                      (Ebinop Osub
                                                        (Ebinop Oadd
                                                          (Econst_int (Int.repr 67108862) tint)
                                                          (Etempvar _x15 tuint)
                                                          tuint)
                                                        (Etempvar _x33 tuint)
                                                        tuint))
                                                    (Ssequence
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Etempvar _out (tptr tuint))
                                                            (Econst_int (Int.repr 6) tint)
                                                            (tptr tuint))
                                                          tuint)
                                                        (Ebinop Osub
                                                          (Ebinop Oadd
                                                            (Econst_int (Int.repr 134217726) tint)
                                                            (Etempvar _x17 tuint)
                                                            tuint)
                                                          (Etempvar _x35 tuint)
                                                          tuint))
                                                      (Ssequence
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _out (tptr tuint))
                                                              (Econst_int (Int.repr 7) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Ebinop Osub
                                                            (Ebinop Oadd
                                                              (Econst_int (Int.repr 67108862) tint)
                                                              (Etempvar _x19 tuint)
                                                              tuint)
                                                            (Etempvar _x37 tuint)
                                                            tuint))
                                                        (Ssequence
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Etempvar _out (tptr tuint))
                                                                (Econst_int (Int.repr 8) tint)
                                                                (tptr tuint))
                                                              tuint)
                                                            (Ebinop Osub
                                                              (Ebinop Oadd
                                                                (Econst_int (Int.repr 134217726) tint)
                                                                (Etempvar _x21 tuint)
                                                                tuint)
                                                              (Etempvar _x39 tuint)
                                                              tuint))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Etempvar _out (tptr tuint))
                                                                (Econst_int (Int.repr 9) tint)
                                                                (tptr tuint))
                                                              tuint)
                                                            (Ebinop Osub
                                                              (Ebinop Oadd
                                                                (Econst_int (Int.repr 67108862) tint)
                                                                (Etempvar _x20 tuint)
                                                                tuint)
                                                              (Etempvar _x38 tuint)
                                                              tuint)))))))))))))))))))))))))))))))
|}.

Definition f_fe_sub := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _fe_loose noattr))) ::
                (_f, (tptr (Tstruct _fe noattr))) ::
                (_g, (tptr (Tstruct _fe noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _fe_sub_impl (Tfunction
                       ((tptr tuint) :: (tptr tuint) :: (tptr tuint) :: nil)
                       tvoid cc_default))
  ((Efield
     (Ederef (Etempvar _h (tptr (Tstruct _fe_loose noattr)))
       (Tstruct _fe_loose noattr)) _v (tarray tuint 10)) ::
   (Efield
     (Ederef (Etempvar _f (tptr (Tstruct _fe noattr))) (Tstruct _fe noattr))
     _v (tarray tuint 10)) ::
   (Efield
     (Ederef (Etempvar _g (tptr (Tstruct _fe noattr))) (Tstruct _fe noattr))
     _v (tarray tuint 10)) :: nil))
|}.

Definition f_fe_mul_impl := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuint)) :: (_in1, (tptr tuint)) ::
                (_in2, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_x20, tuint) :: (_x21, tuint) :: (_x19, tuint) ::
               (_x17, tuint) :: (_x15, tuint) :: (_x13, tuint) ::
               (_x11, tuint) :: (_x9, tuint) :: (_x7, tuint) ::
               (_x5, tuint) :: (_x38, tuint) :: (_x39, tuint) ::
               (_x37, tuint) :: (_x35, tuint) :: (_x33, tuint) ::
               (_x31, tuint) :: (_x29, tuint) :: (_x27, tuint) ::
               (_x25, tuint) :: (_x23, tuint) :: (_x40, tulong) ::
               (_x41, tulong) :: (_x42, tulong) :: (_x43, tulong) ::
               (_x44, tulong) :: (_x45, tulong) :: (_x46, tulong) ::
               (_x47, tulong) :: (_x48, tulong) :: (_x49, tulong) ::
               (_x50, tulong) :: (_x51, tulong) :: (_x52, tulong) ::
               (_x53, tulong) :: (_x54, tulong) :: (_x55, tulong) ::
               (_x56, tulong) :: (_x57, tulong) :: (_x58, tulong) ::
               (_x59, tulong) :: (_x60, tulong) :: (_x61, tulong) ::
               (_x62, tulong) :: (_x63, tulong) :: (_x64, tulong) ::
               (_x65, tulong) :: (_x66, tulong) :: (_x67, tulong) ::
               (_x68, tulong) :: (_x69, tulong) :: (_x70, tulong) ::
               (_x71, tulong) :: (_x72, tulong) :: (_x73, tulong) ::
               (_x74, tulong) :: (_x75, tulong) :: (_x76, tulong) ::
               (_x77, tulong) :: (_x78, tulong) :: (_x79, tulong) ::
               (_x80, tulong) :: (_x81, tulong) :: (_x82, tulong) ::
               (_x83, tulong) :: (_x84, tulong) :: (_x85, tulong) ::
               (_x86, tulong) :: (_x87, tuint) :: (_x88, tulong) ::
               (_x89, tulong) :: (_x90, tuint) :: (_x91, tulong) ::
               (_x92, tulong) :: (_x93, tuint) :: (_x94, tulong) ::
               (_x95, tulong) :: (_x96, tuint) :: (_x97, tulong) ::
               (_x98, tulong) :: (_x99, tuint) :: (_x100, tulong) ::
               (_x101, tulong) :: (_x102, tuint) :: (_x103, tulong) ::
               (_x104, tulong) :: (_x105, tuint) :: (_x106, tulong) ::
               (_x107, tulong) :: (_x108, tuint) :: (_x109, tulong) ::
               (_x110, tulong) :: (_x111, tuint) :: (_x112, tulong) ::
               (_x113, tulong) :: (_x114, tuint) :: (_x115, tulong) ::
               (_x116, tuint) :: (_x117, tuint) :: (_x118, tuint) ::
               (_x119, tuint) :: (_x120, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _x20
    (Ederef
      (Ebinop Oadd (Etempvar _in1 (tptr tuint))
        (Econst_int (Int.repr 9) tint) (tptr tuint)) tuint))
  (Ssequence
    (Sset _x21
      (Ederef
        (Ebinop Oadd (Etempvar _in1 (tptr tuint))
          (Econst_int (Int.repr 8) tint) (tptr tuint)) tuint))
    (Ssequence
      (Sset _x19
        (Ederef
          (Ebinop Oadd (Etempvar _in1 (tptr tuint))
            (Econst_int (Int.repr 7) tint) (tptr tuint)) tuint))
      (Ssequence
        (Sset _x17
          (Ederef
            (Ebinop Oadd (Etempvar _in1 (tptr tuint))
              (Econst_int (Int.repr 6) tint) (tptr tuint)) tuint))
        (Ssequence
          (Sset _x15
            (Ederef
              (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                (Econst_int (Int.repr 5) tint) (tptr tuint)) tuint))
          (Ssequence
            (Sset _x13
              (Ederef
                (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                  (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint))
            (Ssequence
              (Sset _x11
                (Ederef
                  (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                    (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint))
              (Ssequence
                (Sset _x9
                  (Ederef
                    (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                      (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint))
                (Ssequence
                  (Sset _x7
                    (Ederef
                      (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                        (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint))
                  (Ssequence
                    (Sset _x5
                      (Ederef
                        (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
                    (Ssequence
                      (Sset _x38
                        (Ederef
                          (Ebinop Oadd (Etempvar _in2 (tptr tuint))
                            (Econst_int (Int.repr 9) tint) (tptr tuint))
                          tuint))
                      (Ssequence
                        (Sset _x39
                          (Ederef
                            (Ebinop Oadd (Etempvar _in2 (tptr tuint))
                              (Econst_int (Int.repr 8) tint) (tptr tuint))
                            tuint))
                        (Ssequence
                          (Sset _x37
                            (Ederef
                              (Ebinop Oadd (Etempvar _in2 (tptr tuint))
                                (Econst_int (Int.repr 7) tint) (tptr tuint))
                              tuint))
                          (Ssequence
                            (Sset _x35
                              (Ederef
                                (Ebinop Oadd (Etempvar _in2 (tptr tuint))
                                  (Econst_int (Int.repr 6) tint)
                                  (tptr tuint)) tuint))
                            (Ssequence
                              (Sset _x33
                                (Ederef
                                  (Ebinop Oadd (Etempvar _in2 (tptr tuint))
                                    (Econst_int (Int.repr 5) tint)
                                    (tptr tuint)) tuint))
                              (Ssequence
                                (Sset _x31
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _in2 (tptr tuint))
                                      (Econst_int (Int.repr 4) tint)
                                      (tptr tuint)) tuint))
                                (Ssequence
                                  (Sset _x29
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _in2 (tptr tuint))
                                        (Econst_int (Int.repr 3) tint)
                                        (tptr tuint)) tuint))
                                  (Ssequence
                                    (Sset _x27
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _in2 (tptr tuint))
                                          (Econst_int (Int.repr 2) tint)
                                          (tptr tuint)) tuint))
                                    (Ssequence
                                      (Sset _x25
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _in2 (tptr tuint))
                                            (Econst_int (Int.repr 1) tint)
                                            (tptr tuint)) tuint))
                                      (Ssequence
                                        (Sset _x23
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _in2 (tptr tuint))
                                              (Econst_int (Int.repr 0) tint)
                                              (tptr tuint)) tuint))
                                        (Ssequence
                                          (Sset _x40
                                            (Ebinop Omul
                                              (Ecast (Etempvar _x23 tuint)
                                                tulong) (Etempvar _x5 tuint)
                                              tulong))
                                          (Ssequence
                                            (Sset _x41
                                              (Ebinop Oadd
                                                (Ebinop Omul
                                                  (Ecast
                                                    (Etempvar _x23 tuint)
                                                    tulong)
                                                  (Etempvar _x7 tuint)
                                                  tulong)
                                                (Ebinop Omul
                                                  (Ecast
                                                    (Etempvar _x25 tuint)
                                                    tulong)
                                                  (Etempvar _x5 tuint)
                                                  tulong) tulong))
                                            (Ssequence
                                              (Sset _x42
                                                (Ebinop Oadd
                                                  (Ebinop Oadd
                                                    (Ebinop Omul
                                                      (Ecast
                                                        (Ebinop Omul
                                                          (Econst_int (Int.repr 2) tint)
                                                          (Etempvar _x25 tuint)
                                                          tuint) tulong)
                                                      (Etempvar _x7 tuint)
                                                      tulong)
                                                    (Ebinop Omul
                                                      (Ecast
                                                        (Etempvar _x23 tuint)
                                                        tulong)
                                                      (Etempvar _x9 tuint)
                                                      tulong) tulong)
                                                  (Ebinop Omul
                                                    (Ecast
                                                      (Etempvar _x27 tuint)
                                                      tulong)
                                                    (Etempvar _x5 tuint)
                                                    tulong) tulong))
                                              (Ssequence
                                                (Sset _x43
                                                  (Ebinop Oadd
                                                    (Ebinop Oadd
                                                      (Ebinop Oadd
                                                        (Ebinop Omul
                                                          (Ecast
                                                            (Etempvar _x25 tuint)
                                                            tulong)
                                                          (Etempvar _x9 tuint)
                                                          tulong)
                                                        (Ebinop Omul
                                                          (Ecast
                                                            (Etempvar _x27 tuint)
                                                            tulong)
                                                          (Etempvar _x7 tuint)
                                                          tulong) tulong)
                                                      (Ebinop Omul
                                                        (Ecast
                                                          (Etempvar _x23 tuint)
                                                          tulong)
                                                        (Etempvar _x11 tuint)
                                                        tulong) tulong)
                                                    (Ebinop Omul
                                                      (Ecast
                                                        (Etempvar _x29 tuint)
                                                        tulong)
                                                      (Etempvar _x5 tuint)
                                                      tulong) tulong))
                                                (Ssequence
                                                  (Sset _x44
                                                    (Ebinop Oadd
                                                      (Ebinop Oadd
                                                        (Ebinop Oadd
                                                          (Ebinop Omul
                                                            (Ecast
                                                              (Etempvar _x27 tuint)
                                                              tulong)
                                                            (Etempvar _x9 tuint)
                                                            tulong)
                                                          (Ebinop Omul
                                                            (Econst_int (Int.repr 2) tint)
                                                            (Ebinop Oadd
                                                              (Ebinop Omul
                                                                (Ecast
                                                                  (Etempvar _x25 tuint)
                                                                  tulong)
                                                                (Etempvar _x11 tuint)
                                                                tulong)
                                                              (Ebinop Omul
                                                                (Ecast
                                                                  (Etempvar _x29 tuint)
                                                                  tulong)
                                                                (Etempvar _x7 tuint)
                                                                tulong)
                                                              tulong) tulong)
                                                          tulong)
                                                        (Ebinop Omul
                                                          (Ecast
                                                            (Etempvar _x23 tuint)
                                                            tulong)
                                                          (Etempvar _x13 tuint)
                                                          tulong) tulong)
                                                      (Ebinop Omul
                                                        (Ecast
                                                          (Etempvar _x31 tuint)
                                                          tulong)
                                                        (Etempvar _x5 tuint)
                                                        tulong) tulong))
                                                  (Ssequence
                                                    (Sset _x45
                                                      (Ebinop Oadd
                                                        (Ebinop Oadd
                                                          (Ebinop Oadd
                                                            (Ebinop Oadd
                                                              (Ebinop Oadd
                                                                (Ebinop Omul
                                                                  (Ecast
                                                                    (Etempvar _x27 tuint)
                                                                    tulong)
                                                                  (Etempvar _x11 tuint)
                                                                  tulong)
                                                                (Ebinop Omul
                                                                  (Ecast
                                                                    (Etempvar _x29 tuint)
                                                                    tulong)
                                                                  (Etempvar _x9 tuint)
                                                                  tulong)
                                                                tulong)
                                                              (Ebinop Omul
                                                                (Ecast
                                                                  (Etempvar _x25 tuint)
                                                                  tulong)
                                                                (Etempvar _x13 tuint)
                                                                tulong)
                                                              tulong)
                                                            (Ebinop Omul
                                                              (Ecast
                                                                (Etempvar _x31 tuint)
                                                                tulong)
                                                              (Etempvar _x7 tuint)
                                                              tulong) tulong)
                                                          (Ebinop Omul
                                                            (Ecast
                                                              (Etempvar _x23 tuint)
                                                              tulong)
                                                            (Etempvar _x15 tuint)
                                                            tulong) tulong)
                                                        (Ebinop Omul
                                                          (Ecast
                                                            (Etempvar _x33 tuint)
                                                            tulong)
                                                          (Etempvar _x5 tuint)
                                                          tulong) tulong))
                                                    (Ssequence
                                                      (Sset _x46
                                                        (Ebinop Oadd
                                                          (Ebinop Oadd
                                                            (Ebinop Oadd
                                                              (Ebinop Oadd
                                                                (Ebinop Omul
                                                                  (Econst_int (Int.repr 2) tint)
                                                                  (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x29 tuint)
                                                                    tulong)
                                                                    (Etempvar _x11 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x25 tuint)
                                                                    tulong)
                                                                    (Etempvar _x15 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x33 tuint)
                                                                    tulong)
                                                                    (Etempvar _x7 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                  tulong)
                                                                (Ebinop Omul
                                                                  (Ecast
                                                                    (Etempvar _x27 tuint)
                                                                    tulong)
                                                                  (Etempvar _x13 tuint)
                                                                  tulong)
                                                                tulong)
                                                              (Ebinop Omul
                                                                (Ecast
                                                                  (Etempvar _x31 tuint)
                                                                  tulong)
                                                                (Etempvar _x9 tuint)
                                                                tulong)
                                                              tulong)
                                                            (Ebinop Omul
                                                              (Ecast
                                                                (Etempvar _x23 tuint)
                                                                tulong)
                                                              (Etempvar _x17 tuint)
                                                              tulong) tulong)
                                                          (Ebinop Omul
                                                            (Ecast
                                                              (Etempvar _x35 tuint)
                                                              tulong)
                                                            (Etempvar _x5 tuint)
                                                            tulong) tulong))
                                                      (Ssequence
                                                        (Sset _x47
                                                          (Ebinop Oadd
                                                            (Ebinop Oadd
                                                              (Ebinop Oadd
                                                                (Ebinop Oadd
                                                                  (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x29 tuint)
                                                                    tulong)
                                                                    (Etempvar _x13 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x31 tuint)
                                                                    tulong)
                                                                    (Etempvar _x11 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x27 tuint)
                                                                    tulong)
                                                                    (Etempvar _x15 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x33 tuint)
                                                                    tulong)
                                                                    (Etempvar _x9 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                  (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x25 tuint)
                                                                    tulong)
                                                                    (Etempvar _x17 tuint)
                                                                    tulong)
                                                                  tulong)
                                                                (Ebinop Omul
                                                                  (Ecast
                                                                    (Etempvar _x35 tuint)
                                                                    tulong)
                                                                  (Etempvar _x7 tuint)
                                                                  tulong)
                                                                tulong)
                                                              (Ebinop Omul
                                                                (Ecast
                                                                  (Etempvar _x23 tuint)
                                                                  tulong)
                                                                (Etempvar _x19 tuint)
                                                                tulong)
                                                              tulong)
                                                            (Ebinop Omul
                                                              (Ecast
                                                                (Etempvar _x37 tuint)
                                                                tulong)
                                                              (Etempvar _x5 tuint)
                                                              tulong) tulong))
                                                        (Ssequence
                                                          (Sset _x48
                                                            (Ebinop Oadd
                                                              (Ebinop Oadd
                                                                (Ebinop Oadd
                                                                  (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x31 tuint)
                                                                    tulong)
                                                                    (Etempvar _x13 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x29 tuint)
                                                                    tulong)
                                                                    (Etempvar _x15 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x33 tuint)
                                                                    tulong)
                                                                    (Etempvar _x11 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x25 tuint)
                                                                    tulong)
                                                                    (Etempvar _x19 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x37 tuint)
                                                                    tulong)
                                                                    (Etempvar _x7 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x27 tuint)
                                                                    tulong)
                                                                    (Etempvar _x17 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                  (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x35 tuint)
                                                                    tulong)
                                                                    (Etempvar _x9 tuint)
                                                                    tulong)
                                                                  tulong)
                                                                (Ebinop Omul
                                                                  (Ecast
                                                                    (Etempvar _x23 tuint)
                                                                    tulong)
                                                                  (Etempvar _x21 tuint)
                                                                  tulong)
                                                                tulong)
                                                              (Ebinop Omul
                                                                (Ecast
                                                                  (Etempvar _x39 tuint)
                                                                  tulong)
                                                                (Etempvar _x5 tuint)
                                                                tulong)
                                                              tulong))
                                                          (Ssequence
                                                            (Sset _x49
                                                              (Ebinop Oadd
                                                                (Ebinop Oadd
                                                                  (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x31 tuint)
                                                                    tulong)
                                                                    (Etempvar _x15 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x33 tuint)
                                                                    tulong)
                                                                    (Etempvar _x13 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x29 tuint)
                                                                    tulong)
                                                                    (Etempvar _x17 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x35 tuint)
                                                                    tulong)
                                                                    (Etempvar _x11 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x27 tuint)
                                                                    tulong)
                                                                    (Etempvar _x19 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x37 tuint)
                                                                    tulong)
                                                                    (Etempvar _x9 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x25 tuint)
                                                                    tulong)
                                                                    (Etempvar _x21 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x39 tuint)
                                                                    tulong)
                                                                    (Etempvar _x7 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                  (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x23 tuint)
                                                                    tulong)
                                                                    (Etempvar _x20 tuint)
                                                                    tulong)
                                                                  tulong)
                                                                (Ebinop Omul
                                                                  (Ecast
                                                                    (Etempvar _x38 tuint)
                                                                    tulong)
                                                                  (Etempvar _x5 tuint)
                                                                  tulong)
                                                                tulong))
                                                            (Ssequence
                                                              (Sset _x50
                                                                (Ebinop Oadd
                                                                  (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x33 tuint)
                                                                    tulong)
                                                                    (Etempvar _x15 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x29 tuint)
                                                                    tulong)
                                                                    (Etempvar _x19 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x37 tuint)
                                                                    tulong)
                                                                    (Etempvar _x11 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x25 tuint)
                                                                    tulong)
                                                                    (Etempvar _x20 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x38 tuint)
                                                                    tulong)
                                                                    (Etempvar _x7 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x31 tuint)
                                                                    tulong)
                                                                    (Etempvar _x17 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x35 tuint)
                                                                    tulong)
                                                                    (Etempvar _x13 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x27 tuint)
                                                                    tulong)
                                                                    (Etempvar _x21 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                  (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x39 tuint)
                                                                    tulong)
                                                                    (Etempvar _x9 tuint)
                                                                    tulong)
                                                                  tulong))
                                                              (Ssequence
                                                                (Sset _x51
                                                                  (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x33 tuint)
                                                                    tulong)
                                                                    (Etempvar _x17 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x35 tuint)
                                                                    tulong)
                                                                    (Etempvar _x15 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x31 tuint)
                                                                    tulong)
                                                                    (Etempvar _x19 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x37 tuint)
                                                                    tulong)
                                                                    (Etempvar _x13 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x29 tuint)
                                                                    tulong)
                                                                    (Etempvar _x21 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x39 tuint)
                                                                    tulong)
                                                                    (Etempvar _x11 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x27 tuint)
                                                                    tulong)
                                                                    (Etempvar _x20 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x38 tuint)
                                                                    tulong)
                                                                    (Etempvar _x9 tuint)
                                                                    tulong)
                                                                    tulong))
                                                                (Ssequence
                                                                  (Sset _x52
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x35 tuint)
                                                                    tulong)
                                                                    (Etempvar _x17 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x33 tuint)
                                                                    tulong)
                                                                    (Etempvar _x19 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x37 tuint)
                                                                    tulong)
                                                                    (Etempvar _x15 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x29 tuint)
                                                                    tulong)
                                                                    (Etempvar _x20 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x38 tuint)
                                                                    tulong)
                                                                    (Etempvar _x11 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x31 tuint)
                                                                    tulong)
                                                                    (Etempvar _x21 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x39 tuint)
                                                                    tulong)
                                                                    (Etempvar _x13 tuint)
                                                                    tulong)
                                                                    tulong))
                                                                  (Ssequence
                                                                    (Sset _x53
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x35 tuint)
                                                                    tulong)
                                                                    (Etempvar _x19 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x37 tuint)
                                                                    tulong)
                                                                    (Etempvar _x17 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x33 tuint)
                                                                    tulong)
                                                                    (Etempvar _x21 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x39 tuint)
                                                                    tulong)
                                                                    (Etempvar _x15 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x31 tuint)
                                                                    tulong)
                                                                    (Etempvar _x20 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x38 tuint)
                                                                    tulong)
                                                                    (Etempvar _x13 tuint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x54
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x37 tuint)
                                                                    tulong)
                                                                    (Etempvar _x19 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x33 tuint)
                                                                    tulong)
                                                                    (Etempvar _x20 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x38 tuint)
                                                                    tulong)
                                                                    (Etempvar _x15 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x35 tuint)
                                                                    tulong)
                                                                    (Etempvar _x21 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x39 tuint)
                                                                    tulong)
                                                                    (Etempvar _x17 tuint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x55
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x37 tuint)
                                                                    tulong)
                                                                    (Etempvar _x21 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x39 tuint)
                                                                    tulong)
                                                                    (Etempvar _x19 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x35 tuint)
                                                                    tulong)
                                                                    (Etempvar _x20 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x38 tuint)
                                                                    tulong)
                                                                    (Etempvar _x17 tuint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x56
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x39 tuint)
                                                                    tulong)
                                                                    (Etempvar _x21 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x37 tuint)
                                                                    tulong)
                                                                    (Etempvar _x20 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x38 tuint)
                                                                    tulong)
                                                                    (Etempvar _x19 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x57
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x39 tuint)
                                                                    tulong)
                                                                    (Etempvar _x20 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x38 tuint)
                                                                    tulong)
                                                                    (Etempvar _x21 tuint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x58
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Etempvar _x38 tuint)
                                                                    tuint)
                                                                    tulong)
                                                                    (Etempvar _x20 tuint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x59
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x48 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x58 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x60
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x59 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x58 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x61
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x60 tulong)
                                                                    (Etempvar _x58 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x62
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x47 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x57 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x63
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x62 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x57 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x64
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x63 tulong)
                                                                    (Etempvar _x57 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x65
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x46 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x56 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x66
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x65 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x56 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x67
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x66 tulong)
                                                                    (Etempvar _x56 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x68
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x45 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x55 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x69
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x68 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x55 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x70
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x69 tulong)
                                                                    (Etempvar _x55 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x71
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x44 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x54 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x72
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x71 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x54 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x73
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x72 tulong)
                                                                    (Etempvar _x54 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x74
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x43 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x53 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x75
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x74 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x53 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x76
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x75 tulong)
                                                                    (Etempvar _x53 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x77
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x42 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x52 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x78
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x77 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x52 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x79
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x78 tulong)
                                                                    (Etempvar _x52 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x80
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x41 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x51 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x81
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x80 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x51 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x82
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x81 tulong)
                                                                    (Etempvar _x51 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x83
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x40 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x50 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x84
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x83 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x50 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x85
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x84 tulong)
                                                                    (Etempvar _x50 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x86
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x85 tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x87
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x85 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x88
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x86 tulong)
                                                                    (Etempvar _x82 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x89
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x88 tulong)
                                                                    (Econst_int (Int.repr 25) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x90
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x88 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 33554431) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x91
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x89 tulong)
                                                                    (Etempvar _x79 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x92
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x91 tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x93
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x91 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x94
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x92 tulong)
                                                                    (Etempvar _x76 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x95
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x94 tulong)
                                                                    (Econst_int (Int.repr 25) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x96
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x94 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 33554431) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x97
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x95 tulong)
                                                                    (Etempvar _x73 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x98
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x97 tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x99
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x97 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x100
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x98 tulong)
                                                                    (Etempvar _x70 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x101
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x100 tulong)
                                                                    (Econst_int (Int.repr 25) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x102
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x100 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 33554431) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x103
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x101 tulong)
                                                                    (Etempvar _x67 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x104
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x103 tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x105
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x103 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x106
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x104 tulong)
                                                                    (Etempvar _x64 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x107
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x106 tulong)
                                                                    (Econst_int (Int.repr 25) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x108
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x106 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 33554431) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x109
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x107 tulong)
                                                                    (Etempvar _x61 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x110
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x109 tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x111
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x109 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x112
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x110 tulong)
                                                                    (Etempvar _x49 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x113
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x112 tulong)
                                                                    (Econst_int (Int.repr 25) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x114
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x112 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 33554431) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x115
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x87 tuint)
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 19) tint)
                                                                    (Etempvar _x113 tulong)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x116
                                                                    (Ecast
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x115 tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x117
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x115 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x118
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x116 tuint)
                                                                    (Etempvar _x90 tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x119
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x118 tuint)
                                                                    (Econst_int (Int.repr 25) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x120
                                                                    (Ebinop Oand
                                                                    (Etempvar _x118 tuint)
                                                                    (Econst_int (Int.repr 33554431) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x117 tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x120 tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x119 tuint)
                                                                    (Etempvar _x93 tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x96 tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x99 tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x102 tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x105 tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x108 tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x111 tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x114 tuint))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
|}.

Definition f_fe_mul_ttt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _fe noattr))) ::
                (_f, (tptr (Tstruct _fe noattr))) ::
                (_g, (tptr (Tstruct _fe noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _fe_mul_impl (Tfunction
                       ((tptr tuint) :: (tptr tuint) :: (tptr tuint) :: nil)
                       tvoid cc_default))
  ((Efield
     (Ederef (Etempvar _h (tptr (Tstruct _fe noattr))) (Tstruct _fe noattr))
     _v (tarray tuint 10)) ::
   (Efield
     (Ederef (Etempvar _f (tptr (Tstruct _fe noattr))) (Tstruct _fe noattr))
     _v (tarray tuint 10)) ::
   (Efield
     (Ederef (Etempvar _g (tptr (Tstruct _fe noattr))) (Tstruct _fe noattr))
     _v (tarray tuint 10)) :: nil))
|}.

Definition f_fe_mul_tlt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _fe noattr))) ::
                (_f, (tptr (Tstruct _fe_loose noattr))) ::
                (_g, (tptr (Tstruct _fe noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _fe_mul_impl (Tfunction
                       ((tptr tuint) :: (tptr tuint) :: (tptr tuint) :: nil)
                       tvoid cc_default))
  ((Efield
     (Ederef (Etempvar _h (tptr (Tstruct _fe noattr))) (Tstruct _fe noattr))
     _v (tarray tuint 10)) ::
   (Efield
     (Ederef (Etempvar _f (tptr (Tstruct _fe_loose noattr)))
       (Tstruct _fe_loose noattr)) _v (tarray tuint 10)) ::
   (Efield
     (Ederef (Etempvar _g (tptr (Tstruct _fe noattr))) (Tstruct _fe noattr))
     _v (tarray tuint 10)) :: nil))
|}.

Definition f_fe_mul_tll := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _fe noattr))) ::
                (_f, (tptr (Tstruct _fe_loose noattr))) ::
                (_g, (tptr (Tstruct _fe_loose noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _fe_mul_impl (Tfunction
                       ((tptr tuint) :: (tptr tuint) :: (tptr tuint) :: nil)
                       tvoid cc_default))
  ((Efield
     (Ederef (Etempvar _h (tptr (Tstruct _fe noattr))) (Tstruct _fe noattr))
     _v (tarray tuint 10)) ::
   (Efield
     (Ederef (Etempvar _f (tptr (Tstruct _fe_loose noattr)))
       (Tstruct _fe_loose noattr)) _v (tarray tuint 10)) ::
   (Efield
     (Ederef (Etempvar _g (tptr (Tstruct _fe_loose noattr)))
       (Tstruct _fe_loose noattr)) _v (tarray tuint 10)) :: nil))
|}.

Definition f_fe_sqr_impl := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuint)) :: (_in1, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_x17, tuint) :: (_x18, tuint) :: (_x16, tuint) ::
               (_x14, tuint) :: (_x12, tuint) :: (_x10, tuint) ::
               (_x8, tuint) :: (_x6, tuint) :: (_x4, tuint) ::
               (_x2, tuint) :: (_x19, tulong) :: (_x20, tulong) ::
               (_x21, tulong) :: (_x22, tulong) :: (_x23, tulong) ::
               (_x24, tulong) :: (_x25, tulong) :: (_x26, tulong) ::
               (_x27, tulong) :: (_x28, tulong) :: (_x29, tulong) ::
               (_x30, tulong) :: (_x31, tulong) :: (_x32, tulong) ::
               (_x33, tulong) :: (_x34, tulong) :: (_x35, tulong) ::
               (_x36, tulong) :: (_x37, tulong) :: (_x38, tulong) ::
               (_x39, tulong) :: (_x40, tulong) :: (_x41, tulong) ::
               (_x42, tulong) :: (_x43, tulong) :: (_x44, tulong) ::
               (_x45, tulong) :: (_x46, tulong) :: (_x47, tulong) ::
               (_x48, tulong) :: (_x49, tulong) :: (_x50, tulong) ::
               (_x51, tulong) :: (_x52, tulong) :: (_x53, tulong) ::
               (_x54, tulong) :: (_x55, tulong) :: (_x56, tulong) ::
               (_x57, tulong) :: (_x58, tulong) :: (_x59, tulong) ::
               (_x60, tulong) :: (_x61, tulong) :: (_x62, tulong) ::
               (_x63, tulong) :: (_x64, tulong) :: (_x65, tulong) ::
               (_x66, tuint) :: (_x67, tulong) :: (_x68, tulong) ::
               (_x69, tuint) :: (_x70, tulong) :: (_x71, tulong) ::
               (_x72, tuint) :: (_x73, tulong) :: (_x74, tulong) ::
               (_x75, tuint) :: (_x76, tulong) :: (_x77, tulong) ::
               (_x78, tuint) :: (_x79, tulong) :: (_x80, tulong) ::
               (_x81, tuint) :: (_x82, tulong) :: (_x83, tulong) ::
               (_x84, tuint) :: (_x85, tulong) :: (_x86, tulong) ::
               (_x87, tuint) :: (_x88, tulong) :: (_x89, tulong) ::
               (_x90, tuint) :: (_x91, tulong) :: (_x92, tulong) ::
               (_x93, tuint) :: (_x94, tulong) :: (_x95, tuint) ::
               (_x96, tuint) :: (_x97, tuint) :: (_x98, tuint) ::
               (_x99, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _x17
    (Ederef
      (Ebinop Oadd (Etempvar _in1 (tptr tuint))
        (Econst_int (Int.repr 9) tint) (tptr tuint)) tuint))
  (Ssequence
    (Sset _x18
      (Ederef
        (Ebinop Oadd (Etempvar _in1 (tptr tuint))
          (Econst_int (Int.repr 8) tint) (tptr tuint)) tuint))
    (Ssequence
      (Sset _x16
        (Ederef
          (Ebinop Oadd (Etempvar _in1 (tptr tuint))
            (Econst_int (Int.repr 7) tint) (tptr tuint)) tuint))
      (Ssequence
        (Sset _x14
          (Ederef
            (Ebinop Oadd (Etempvar _in1 (tptr tuint))
              (Econst_int (Int.repr 6) tint) (tptr tuint)) tuint))
        (Ssequence
          (Sset _x12
            (Ederef
              (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                (Econst_int (Int.repr 5) tint) (tptr tuint)) tuint))
          (Ssequence
            (Sset _x10
              (Ederef
                (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                  (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint))
            (Ssequence
              (Sset _x8
                (Ederef
                  (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                    (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint))
              (Ssequence
                (Sset _x6
                  (Ederef
                    (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                      (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint))
                (Ssequence
                  (Sset _x4
                    (Ederef
                      (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                        (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint))
                  (Ssequence
                    (Sset _x2
                      (Ederef
                        (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
                    (Ssequence
                      (Sset _x19
                        (Ebinop Omul (Ecast (Etempvar _x2 tuint) tulong)
                          (Etempvar _x2 tuint) tulong))
                      (Ssequence
                        (Sset _x20
                          (Ebinop Omul
                            (Ecast
                              (Ebinop Omul (Econst_int (Int.repr 2) tint)
                                (Etempvar _x2 tuint) tuint) tulong)
                            (Etempvar _x4 tuint) tulong))
                        (Ssequence
                          (Sset _x21
                            (Ebinop Omul (Econst_int (Int.repr 2) tint)
                              (Ebinop Oadd
                                (Ebinop Omul
                                  (Ecast (Etempvar _x4 tuint) tulong)
                                  (Etempvar _x4 tuint) tulong)
                                (Ebinop Omul
                                  (Ecast (Etempvar _x2 tuint) tulong)
                                  (Etempvar _x6 tuint) tulong) tulong)
                              tulong))
                          (Ssequence
                            (Sset _x22
                              (Ebinop Omul (Econst_int (Int.repr 2) tint)
                                (Ebinop Oadd
                                  (Ebinop Omul
                                    (Ecast (Etempvar _x4 tuint) tulong)
                                    (Etempvar _x6 tuint) tulong)
                                  (Ebinop Omul
                                    (Ecast (Etempvar _x2 tuint) tulong)
                                    (Etempvar _x8 tuint) tulong) tulong)
                                tulong))
                            (Ssequence
                              (Sset _x23
                                (Ebinop Oadd
                                  (Ebinop Oadd
                                    (Ebinop Omul
                                      (Ecast (Etempvar _x6 tuint) tulong)
                                      (Etempvar _x6 tuint) tulong)
                                    (Ebinop Omul
                                      (Ecast
                                        (Ebinop Omul
                                          (Econst_int (Int.repr 4) tint)
                                          (Etempvar _x4 tuint) tuint) tulong)
                                      (Etempvar _x8 tuint) tulong) tulong)
                                  (Ebinop Omul
                                    (Ecast
                                      (Ebinop Omul
                                        (Econst_int (Int.repr 2) tint)
                                        (Etempvar _x2 tuint) tuint) tulong)
                                    (Etempvar _x10 tuint) tulong) tulong))
                              (Ssequence
                                (Sset _x24
                                  (Ebinop Omul (Econst_int (Int.repr 2) tint)
                                    (Ebinop Oadd
                                      (Ebinop Oadd
                                        (Ebinop Omul
                                          (Ecast (Etempvar _x6 tuint) tulong)
                                          (Etempvar _x8 tuint) tulong)
                                        (Ebinop Omul
                                          (Ecast (Etempvar _x4 tuint) tulong)
                                          (Etempvar _x10 tuint) tulong)
                                        tulong)
                                      (Ebinop Omul
                                        (Ecast (Etempvar _x2 tuint) tulong)
                                        (Etempvar _x12 tuint) tulong) tulong)
                                    tulong))
                                (Ssequence
                                  (Sset _x25
                                    (Ebinop Omul
                                      (Econst_int (Int.repr 2) tint)
                                      (Ebinop Oadd
                                        (Ebinop Oadd
                                          (Ebinop Oadd
                                            (Ebinop Omul
                                              (Ecast (Etempvar _x8 tuint)
                                                tulong) (Etempvar _x8 tuint)
                                              tulong)
                                            (Ebinop Omul
                                              (Ecast (Etempvar _x6 tuint)
                                                tulong) (Etempvar _x10 tuint)
                                              tulong) tulong)
                                          (Ebinop Omul
                                            (Ecast (Etempvar _x2 tuint)
                                              tulong) (Etempvar _x14 tuint)
                                            tulong) tulong)
                                        (Ebinop Omul
                                          (Ecast
                                            (Ebinop Omul
                                              (Econst_int (Int.repr 2) tint)
                                              (Etempvar _x4 tuint) tuint)
                                            tulong) (Etempvar _x12 tuint)
                                          tulong) tulong) tulong))
                                  (Ssequence
                                    (Sset _x26
                                      (Ebinop Omul
                                        (Econst_int (Int.repr 2) tint)
                                        (Ebinop Oadd
                                          (Ebinop Oadd
                                            (Ebinop Oadd
                                              (Ebinop Omul
                                                (Ecast (Etempvar _x8 tuint)
                                                  tulong)
                                                (Etempvar _x10 tuint) tulong)
                                              (Ebinop Omul
                                                (Ecast (Etempvar _x6 tuint)
                                                  tulong)
                                                (Etempvar _x12 tuint) tulong)
                                              tulong)
                                            (Ebinop Omul
                                              (Ecast (Etempvar _x4 tuint)
                                                tulong) (Etempvar _x14 tuint)
                                              tulong) tulong)
                                          (Ebinop Omul
                                            (Ecast (Etempvar _x2 tuint)
                                              tulong) (Etempvar _x16 tuint)
                                            tulong) tulong) tulong))
                                    (Ssequence
                                      (Sset _x27
                                        (Ebinop Oadd
                                          (Ebinop Omul
                                            (Ecast (Etempvar _x10 tuint)
                                              tulong) (Etempvar _x10 tuint)
                                            tulong)
                                          (Ebinop Omul
                                            (Econst_int (Int.repr 2) tint)
                                            (Ebinop Oadd
                                              (Ebinop Oadd
                                                (Ebinop Omul
                                                  (Ecast (Etempvar _x6 tuint)
                                                    tulong)
                                                  (Etempvar _x14 tuint)
                                                  tulong)
                                                (Ebinop Omul
                                                  (Ecast (Etempvar _x2 tuint)
                                                    tulong)
                                                  (Etempvar _x18 tuint)
                                                  tulong) tulong)
                                              (Ebinop Omul
                                                (Econst_int (Int.repr 2) tint)
                                                (Ebinop Oadd
                                                  (Ebinop Omul
                                                    (Ecast
                                                      (Etempvar _x4 tuint)
                                                      tulong)
                                                    (Etempvar _x16 tuint)
                                                    tulong)
                                                  (Ebinop Omul
                                                    (Ecast
                                                      (Etempvar _x8 tuint)
                                                      tulong)
                                                    (Etempvar _x12 tuint)
                                                    tulong) tulong) tulong)
                                              tulong) tulong) tulong))
                                      (Ssequence
                                        (Sset _x28
                                          (Ebinop Omul
                                            (Econst_int (Int.repr 2) tint)
                                            (Ebinop Oadd
                                              (Ebinop Oadd
                                                (Ebinop Oadd
                                                  (Ebinop Oadd
                                                    (Ebinop Omul
                                                      (Ecast
                                                        (Etempvar _x10 tuint)
                                                        tulong)
                                                      (Etempvar _x12 tuint)
                                                      tulong)
                                                    (Ebinop Omul
                                                      (Ecast
                                                        (Etempvar _x8 tuint)
                                                        tulong)
                                                      (Etempvar _x14 tuint)
                                                      tulong) tulong)
                                                  (Ebinop Omul
                                                    (Ecast
                                                      (Etempvar _x6 tuint)
                                                      tulong)
                                                    (Etempvar _x16 tuint)
                                                    tulong) tulong)
                                                (Ebinop Omul
                                                  (Ecast (Etempvar _x4 tuint)
                                                    tulong)
                                                  (Etempvar _x18 tuint)
                                                  tulong) tulong)
                                              (Ebinop Omul
                                                (Ecast (Etempvar _x2 tuint)
                                                  tulong)
                                                (Etempvar _x17 tuint) tulong)
                                              tulong) tulong))
                                        (Ssequence
                                          (Sset _x29
                                            (Ebinop Omul
                                              (Econst_int (Int.repr 2) tint)
                                              (Ebinop Oadd
                                                (Ebinop Oadd
                                                  (Ebinop Oadd
                                                    (Ebinop Omul
                                                      (Ecast
                                                        (Etempvar _x12 tuint)
                                                        tulong)
                                                      (Etempvar _x12 tuint)
                                                      tulong)
                                                    (Ebinop Omul
                                                      (Ecast
                                                        (Etempvar _x10 tuint)
                                                        tulong)
                                                      (Etempvar _x14 tuint)
                                                      tulong) tulong)
                                                  (Ebinop Omul
                                                    (Ecast
                                                      (Etempvar _x6 tuint)
                                                      tulong)
                                                    (Etempvar _x18 tuint)
                                                    tulong) tulong)
                                                (Ebinop Omul
                                                  (Econst_int (Int.repr 2) tint)
                                                  (Ebinop Oadd
                                                    (Ebinop Omul
                                                      (Ecast
                                                        (Etempvar _x8 tuint)
                                                        tulong)
                                                      (Etempvar _x16 tuint)
                                                      tulong)
                                                    (Ebinop Omul
                                                      (Ecast
                                                        (Etempvar _x4 tuint)
                                                        tulong)
                                                      (Etempvar _x17 tuint)
                                                      tulong) tulong) tulong)
                                                tulong) tulong))
                                          (Ssequence
                                            (Sset _x30
                                              (Ebinop Omul
                                                (Econst_int (Int.repr 2) tint)
                                                (Ebinop Oadd
                                                  (Ebinop Oadd
                                                    (Ebinop Oadd
                                                      (Ebinop Omul
                                                        (Ecast
                                                          (Etempvar _x12 tuint)
                                                          tulong)
                                                        (Etempvar _x14 tuint)
                                                        tulong)
                                                      (Ebinop Omul
                                                        (Ecast
                                                          (Etempvar _x10 tuint)
                                                          tulong)
                                                        (Etempvar _x16 tuint)
                                                        tulong) tulong)
                                                    (Ebinop Omul
                                                      (Ecast
                                                        (Etempvar _x8 tuint)
                                                        tulong)
                                                      (Etempvar _x18 tuint)
                                                      tulong) tulong)
                                                  (Ebinop Omul
                                                    (Ecast
                                                      (Etempvar _x6 tuint)
                                                      tulong)
                                                    (Etempvar _x17 tuint)
                                                    tulong) tulong) tulong))
                                            (Ssequence
                                              (Sset _x31
                                                (Ebinop Oadd
                                                  (Ebinop Omul
                                                    (Ecast
                                                      (Etempvar _x14 tuint)
                                                      tulong)
                                                    (Etempvar _x14 tuint)
                                                    tulong)
                                                  (Ebinop Omul
                                                    (Econst_int (Int.repr 2) tint)
                                                    (Ebinop Oadd
                                                      (Ebinop Omul
                                                        (Ecast
                                                          (Etempvar _x10 tuint)
                                                          tulong)
                                                        (Etempvar _x18 tuint)
                                                        tulong)
                                                      (Ebinop Omul
                                                        (Econst_int (Int.repr 2) tint)
                                                        (Ebinop Oadd
                                                          (Ebinop Omul
                                                            (Ecast
                                                              (Etempvar _x12 tuint)
                                                              tulong)
                                                            (Etempvar _x16 tuint)
                                                            tulong)
                                                          (Ebinop Omul
                                                            (Ecast
                                                              (Etempvar _x8 tuint)
                                                              tulong)
                                                            (Etempvar _x17 tuint)
                                                            tulong) tulong)
                                                        tulong) tulong)
                                                    tulong) tulong))
                                              (Ssequence
                                                (Sset _x32
                                                  (Ebinop Omul
                                                    (Econst_int (Int.repr 2) tint)
                                                    (Ebinop Oadd
                                                      (Ebinop Oadd
                                                        (Ebinop Omul
                                                          (Ecast
                                                            (Etempvar _x14 tuint)
                                                            tulong)
                                                          (Etempvar _x16 tuint)
                                                          tulong)
                                                        (Ebinop Omul
                                                          (Ecast
                                                            (Etempvar _x12 tuint)
                                                            tulong)
                                                          (Etempvar _x18 tuint)
                                                          tulong) tulong)
                                                      (Ebinop Omul
                                                        (Ecast
                                                          (Etempvar _x10 tuint)
                                                          tulong)
                                                        (Etempvar _x17 tuint)
                                                        tulong) tulong)
                                                    tulong))
                                                (Ssequence
                                                  (Sset _x33
                                                    (Ebinop Omul
                                                      (Econst_int (Int.repr 2) tint)
                                                      (Ebinop Oadd
                                                        (Ebinop Oadd
                                                          (Ebinop Omul
                                                            (Ecast
                                                              (Etempvar _x16 tuint)
                                                              tulong)
                                                            (Etempvar _x16 tuint)
                                                            tulong)
                                                          (Ebinop Omul
                                                            (Ecast
                                                              (Etempvar _x14 tuint)
                                                              tulong)
                                                            (Etempvar _x18 tuint)
                                                            tulong) tulong)
                                                        (Ebinop Omul
                                                          (Ecast
                                                            (Ebinop Omul
                                                              (Econst_int (Int.repr 2) tint)
                                                              (Etempvar _x12 tuint)
                                                              tuint) tulong)
                                                          (Etempvar _x17 tuint)
                                                          tulong) tulong)
                                                      tulong))
                                                  (Ssequence
                                                    (Sset _x34
                                                      (Ebinop Omul
                                                        (Econst_int (Int.repr 2) tint)
                                                        (Ebinop Oadd
                                                          (Ebinop Omul
                                                            (Ecast
                                                              (Etempvar _x16 tuint)
                                                              tulong)
                                                            (Etempvar _x18 tuint)
                                                            tulong)
                                                          (Ebinop Omul
                                                            (Ecast
                                                              (Etempvar _x14 tuint)
                                                              tulong)
                                                            (Etempvar _x17 tuint)
                                                            tulong) tulong)
                                                        tulong))
                                                    (Ssequence
                                                      (Sset _x35
                                                        (Ebinop Oadd
                                                          (Ebinop Omul
                                                            (Ecast
                                                              (Etempvar _x18 tuint)
                                                              tulong)
                                                            (Etempvar _x18 tuint)
                                                            tulong)
                                                          (Ebinop Omul
                                                            (Ecast
                                                              (Ebinop Omul
                                                                (Econst_int (Int.repr 4) tint)
                                                                (Etempvar _x16 tuint)
                                                                tuint)
                                                              tulong)
                                                            (Etempvar _x17 tuint)
                                                            tulong) tulong))
                                                      (Ssequence
                                                        (Sset _x36
                                                          (Ebinop Omul
                                                            (Ecast
                                                              (Ebinop Omul
                                                                (Econst_int (Int.repr 2) tint)
                                                                (Etempvar _x18 tuint)
                                                                tuint)
                                                              tulong)
                                                            (Etempvar _x17 tuint)
                                                            tulong))
                                                        (Ssequence
                                                          (Sset _x37
                                                            (Ebinop Omul
                                                              (Ecast
                                                                (Ebinop Omul
                                                                  (Econst_int (Int.repr 2) tint)
                                                                  (Etempvar _x17 tuint)
                                                                  tuint)
                                                                tulong)
                                                              (Etempvar _x17 tuint)
                                                              tulong))
                                                          (Ssequence
                                                            (Sset _x38
                                                              (Ebinop Oadd
                                                                (Etempvar _x27 tulong)
                                                                (Ebinop Oshl
                                                                  (Etempvar _x37 tulong)
                                                                  (Econst_int (Int.repr 4) tint)
                                                                  tulong)
                                                                tulong))
                                                            (Ssequence
                                                              (Sset _x39
                                                                (Ebinop Oadd
                                                                  (Etempvar _x38 tulong)
                                                                  (Ebinop Oshl
                                                                    (Etempvar _x37 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                  tulong))
                                                              (Ssequence
                                                                (Sset _x40
                                                                  (Ebinop Oadd
                                                                    (Etempvar _x39 tulong)
                                                                    (Etempvar _x37 tulong)
                                                                    tulong))
                                                                (Ssequence
                                                                  (Sset _x41
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x26 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x36 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                  (Ssequence
                                                                    (Sset _x42
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x41 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x36 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x43
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x42 tulong)
                                                                    (Etempvar _x36 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x44
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x25 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x35 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x45
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x44 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x35 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x46
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x45 tulong)
                                                                    (Etempvar _x35 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x47
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x24 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x34 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x48
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x47 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x34 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x49
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x48 tulong)
                                                                    (Etempvar _x34 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x50
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x23 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x33 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x51
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x50 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x33 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x52
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x51 tulong)
                                                                    (Etempvar _x33 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x53
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x22 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x32 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x54
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x53 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x32 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x55
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x54 tulong)
                                                                    (Etempvar _x32 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x56
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x21 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x31 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x57
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x56 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x31 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x58
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x57 tulong)
                                                                    (Etempvar _x31 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x59
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x20 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x30 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x60
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x59 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x30 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x61
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x60 tulong)
                                                                    (Etempvar _x30 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x62
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x19 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x29 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x63
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x62 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x29 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x64
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x63 tulong)
                                                                    (Etempvar _x29 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x65
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x64 tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x66
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x64 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x67
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x65 tulong)
                                                                    (Etempvar _x61 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x68
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x67 tulong)
                                                                    (Econst_int (Int.repr 25) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x69
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x67 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 33554431) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x70
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x68 tulong)
                                                                    (Etempvar _x58 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x71
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x70 tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x72
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x70 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x73
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x71 tulong)
                                                                    (Etempvar _x55 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x74
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x73 tulong)
                                                                    (Econst_int (Int.repr 25) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x75
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x73 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 33554431) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x76
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x74 tulong)
                                                                    (Etempvar _x52 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x77
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x76 tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x78
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x76 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x79
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x77 tulong)
                                                                    (Etempvar _x49 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x80
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x79 tulong)
                                                                    (Econst_int (Int.repr 25) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x81
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x79 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 33554431) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x82
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x80 tulong)
                                                                    (Etempvar _x46 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x83
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x82 tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x84
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x82 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x85
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x83 tulong)
                                                                    (Etempvar _x43 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x86
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x85 tulong)
                                                                    (Econst_int (Int.repr 25) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x87
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x85 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 33554431) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x88
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x86 tulong)
                                                                    (Etempvar _x40 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x89
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x88 tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x90
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x88 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x91
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x89 tulong)
                                                                    (Etempvar _x28 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x92
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x91 tulong)
                                                                    (Econst_int (Int.repr 25) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x93
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x91 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 33554431) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x94
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x66 tuint)
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 19) tint)
                                                                    (Etempvar _x92 tulong)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x95
                                                                    (Ecast
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x94 tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x96
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x94 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x97
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x95 tuint)
                                                                    (Etempvar _x69 tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x98
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x97 tuint)
                                                                    (Econst_int (Int.repr 25) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x99
                                                                    (Ebinop Oand
                                                                    (Etempvar _x97 tuint)
                                                                    (Econst_int (Int.repr 33554431) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x96 tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x99 tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x98 tuint)
                                                                    (Etempvar _x72 tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x75 tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x78 tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x81 tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x84 tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x87 tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x90 tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x93 tuint))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
|}.

Definition f_fe_sq_tl := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _fe noattr))) ::
                (_f, (tptr (Tstruct _fe_loose noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _fe_sqr_impl (Tfunction ((tptr tuint) :: (tptr tuint) :: nil) tvoid
                       cc_default))
  ((Efield
     (Ederef (Etempvar _h (tptr (Tstruct _fe noattr))) (Tstruct _fe noattr))
     _v (tarray tuint 10)) ::
   (Efield
     (Ederef (Etempvar _f (tptr (Tstruct _fe_loose noattr)))
       (Tstruct _fe_loose noattr)) _v (tarray tuint 10)) :: nil))
|}.

Definition f_fe_sq_tt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _fe noattr))) ::
                (_f, (tptr (Tstruct _fe noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _fe_sqr_impl (Tfunction ((tptr tuint) :: (tptr tuint) :: nil) tvoid
                       cc_default))
  ((Efield
     (Ederef (Etempvar _h (tptr (Tstruct _fe noattr))) (Tstruct _fe noattr))
     _v (tarray tuint 10)) ::
   (Efield
     (Ederef (Etempvar _f (tptr (Tstruct _fe noattr))) (Tstruct _fe noattr))
     _v (tarray tuint 10)) :: nil))
|}.

Definition f_fe_loose_invert := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr (Tstruct _fe noattr))) ::
                (_z, (tptr (Tstruct _fe_loose noattr))) :: nil);
  fn_vars := ((_t0, (Tstruct _fe noattr)) :: (_t1, (Tstruct _fe noattr)) ::
              (_t2, (Tstruct _fe noattr)) :: (_t3, (Tstruct _fe noattr)) ::
              nil);
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _fe_sq_tl (Tfunction
                      ((tptr (Tstruct _fe noattr)) ::
                       (tptr (Tstruct _fe_loose noattr)) :: nil) tvoid
                      cc_default))
    ((Eaddrof (Evar _t0 (Tstruct _fe noattr)) (tptr (Tstruct _fe noattr))) ::
     (Etempvar _z (tptr (Tstruct _fe_loose noattr))) :: nil))
  (Ssequence
    (Scall None
      (Evar _fe_sq_tt (Tfunction
                        ((tptr (Tstruct _fe noattr)) ::
                         (tptr (Tstruct _fe noattr)) :: nil) tvoid
                        cc_default))
      ((Eaddrof (Evar _t1 (Tstruct _fe noattr)) (tptr (Tstruct _fe noattr))) ::
       (Eaddrof (Evar _t0 (Tstruct _fe noattr)) (tptr (Tstruct _fe noattr))) ::
       nil))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 1) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Econst_int (Int.repr 2) tint) tint)
              Sskip
              Sbreak)
            (Scall None
              (Evar _fe_sq_tt (Tfunction
                                ((tptr (Tstruct _fe noattr)) ::
                                 (tptr (Tstruct _fe noattr)) :: nil) tvoid
                                cc_default))
              ((Eaddrof (Evar _t1 (Tstruct _fe noattr))
                 (tptr (Tstruct _fe noattr))) ::
               (Eaddrof (Evar _t1 (Tstruct _fe noattr))
                 (tptr (Tstruct _fe noattr))) :: nil)))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Ssequence
        (Scall None
          (Evar _fe_mul_tlt (Tfunction
                              ((tptr (Tstruct _fe noattr)) ::
                               (tptr (Tstruct _fe_loose noattr)) ::
                               (tptr (Tstruct _fe noattr)) :: nil) tvoid
                              cc_default))
          ((Eaddrof (Evar _t1 (Tstruct _fe noattr))
             (tptr (Tstruct _fe noattr))) ::
           (Etempvar _z (tptr (Tstruct _fe_loose noattr))) ::
           (Eaddrof (Evar _t1 (Tstruct _fe noattr))
             (tptr (Tstruct _fe noattr))) :: nil))
        (Ssequence
          (Scall None
            (Evar _fe_mul_ttt (Tfunction
                                ((tptr (Tstruct _fe noattr)) ::
                                 (tptr (Tstruct _fe noattr)) ::
                                 (tptr (Tstruct _fe noattr)) :: nil) tvoid
                                cc_default))
            ((Eaddrof (Evar _t0 (Tstruct _fe noattr))
               (tptr (Tstruct _fe noattr))) ::
             (Eaddrof (Evar _t0 (Tstruct _fe noattr))
               (tptr (Tstruct _fe noattr))) ::
             (Eaddrof (Evar _t1 (Tstruct _fe noattr))
               (tptr (Tstruct _fe noattr))) :: nil))
          (Ssequence
            (Scall None
              (Evar _fe_sq_tt (Tfunction
                                ((tptr (Tstruct _fe noattr)) ::
                                 (tptr (Tstruct _fe noattr)) :: nil) tvoid
                                cc_default))
              ((Eaddrof (Evar _t2 (Tstruct _fe noattr))
                 (tptr (Tstruct _fe noattr))) ::
               (Eaddrof (Evar _t0 (Tstruct _fe noattr))
                 (tptr (Tstruct _fe noattr))) :: nil))
            (Ssequence
              (Scall None
                (Evar _fe_mul_ttt (Tfunction
                                    ((tptr (Tstruct _fe noattr)) ::
                                     (tptr (Tstruct _fe noattr)) ::
                                     (tptr (Tstruct _fe noattr)) :: nil)
                                    tvoid cc_default))
                ((Eaddrof (Evar _t1 (Tstruct _fe noattr))
                   (tptr (Tstruct _fe noattr))) ::
                 (Eaddrof (Evar _t1 (Tstruct _fe noattr))
                   (tptr (Tstruct _fe noattr))) ::
                 (Eaddrof (Evar _t2 (Tstruct _fe noattr))
                   (tptr (Tstruct _fe noattr))) :: nil))
              (Ssequence
                (Scall None
                  (Evar _fe_sq_tt (Tfunction
                                    ((tptr (Tstruct _fe noattr)) ::
                                     (tptr (Tstruct _fe noattr)) :: nil)
                                    tvoid cc_default))
                  ((Eaddrof (Evar _t2 (Tstruct _fe noattr))
                     (tptr (Tstruct _fe noattr))) ::
                   (Eaddrof (Evar _t1 (Tstruct _fe noattr))
                     (tptr (Tstruct _fe noattr))) :: nil))
                (Ssequence
                  (Ssequence
                    (Sset _i (Econst_int (Int.repr 1) tint))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                       (Econst_int (Int.repr 5) tint) tint)
                          Sskip
                          Sbreak)
                        (Scall None
                          (Evar _fe_sq_tt (Tfunction
                                            ((tptr (Tstruct _fe noattr)) ::
                                             (tptr (Tstruct _fe noattr)) ::
                                             nil) tvoid cc_default))
                          ((Eaddrof (Evar _t2 (Tstruct _fe noattr))
                             (tptr (Tstruct _fe noattr))) ::
                           (Eaddrof (Evar _t2 (Tstruct _fe noattr))
                             (tptr (Tstruct _fe noattr))) :: nil)))
                      (Sset _i
                        (Ebinop Oadd (Etempvar _i tint)
                          (Econst_int (Int.repr 1) tint) tint))))
                  (Ssequence
                    (Scall None
                      (Evar _fe_mul_ttt (Tfunction
                                          ((tptr (Tstruct _fe noattr)) ::
                                           (tptr (Tstruct _fe noattr)) ::
                                           (tptr (Tstruct _fe noattr)) ::
                                           nil) tvoid cc_default))
                      ((Eaddrof (Evar _t1 (Tstruct _fe noattr))
                         (tptr (Tstruct _fe noattr))) ::
                       (Eaddrof (Evar _t2 (Tstruct _fe noattr))
                         (tptr (Tstruct _fe noattr))) ::
                       (Eaddrof (Evar _t1 (Tstruct _fe noattr))
                         (tptr (Tstruct _fe noattr))) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _fe_sq_tt (Tfunction
                                          ((tptr (Tstruct _fe noattr)) ::
                                           (tptr (Tstruct _fe noattr)) ::
                                           nil) tvoid cc_default))
                        ((Eaddrof (Evar _t2 (Tstruct _fe noattr))
                           (tptr (Tstruct _fe noattr))) ::
                         (Eaddrof (Evar _t1 (Tstruct _fe noattr))
                           (tptr (Tstruct _fe noattr))) :: nil))
                      (Ssequence
                        (Ssequence
                          (Sset _i (Econst_int (Int.repr 1) tint))
                          (Sloop
                            (Ssequence
                              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                             (Econst_int (Int.repr 10) tint)
                                             tint)
                                Sskip
                                Sbreak)
                              (Scall None
                                (Evar _fe_sq_tt (Tfunction
                                                  ((tptr (Tstruct _fe noattr)) ::
                                                   (tptr (Tstruct _fe noattr)) ::
                                                   nil) tvoid cc_default))
                                ((Eaddrof (Evar _t2 (Tstruct _fe noattr))
                                   (tptr (Tstruct _fe noattr))) ::
                                 (Eaddrof (Evar _t2 (Tstruct _fe noattr))
                                   (tptr (Tstruct _fe noattr))) :: nil)))
                            (Sset _i
                              (Ebinop Oadd (Etempvar _i tint)
                                (Econst_int (Int.repr 1) tint) tint))))
                        (Ssequence
                          (Scall None
                            (Evar _fe_mul_ttt (Tfunction
                                                ((tptr (Tstruct _fe noattr)) ::
                                                 (tptr (Tstruct _fe noattr)) ::
                                                 (tptr (Tstruct _fe noattr)) ::
                                                 nil) tvoid cc_default))
                            ((Eaddrof (Evar _t2 (Tstruct _fe noattr))
                               (tptr (Tstruct _fe noattr))) ::
                             (Eaddrof (Evar _t2 (Tstruct _fe noattr))
                               (tptr (Tstruct _fe noattr))) ::
                             (Eaddrof (Evar _t1 (Tstruct _fe noattr))
                               (tptr (Tstruct _fe noattr))) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar _fe_sq_tt (Tfunction
                                                ((tptr (Tstruct _fe noattr)) ::
                                                 (tptr (Tstruct _fe noattr)) ::
                                                 nil) tvoid cc_default))
                              ((Eaddrof (Evar _t3 (Tstruct _fe noattr))
                                 (tptr (Tstruct _fe noattr))) ::
                               (Eaddrof (Evar _t2 (Tstruct _fe noattr))
                                 (tptr (Tstruct _fe noattr))) :: nil))
                            (Ssequence
                              (Ssequence
                                (Sset _i (Econst_int (Int.repr 1) tint))
                                (Sloop
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _i tint)
                                                   (Econst_int (Int.repr 20) tint)
                                                   tint)
                                      Sskip
                                      Sbreak)
                                    (Scall None
                                      (Evar _fe_sq_tt (Tfunction
                                                        ((tptr (Tstruct _fe noattr)) ::
                                                         (tptr (Tstruct _fe noattr)) ::
                                                         nil) tvoid
                                                        cc_default))
                                      ((Eaddrof
                                         (Evar _t3 (Tstruct _fe noattr))
                                         (tptr (Tstruct _fe noattr))) ::
                                       (Eaddrof
                                         (Evar _t3 (Tstruct _fe noattr))
                                         (tptr (Tstruct _fe noattr))) :: nil)))
                                  (Sset _i
                                    (Ebinop Oadd (Etempvar _i tint)
                                      (Econst_int (Int.repr 1) tint) tint))))
                              (Ssequence
                                (Scall None
                                  (Evar _fe_mul_ttt (Tfunction
                                                      ((tptr (Tstruct _fe noattr)) ::
                                                       (tptr (Tstruct _fe noattr)) ::
                                                       (tptr (Tstruct _fe noattr)) ::
                                                       nil) tvoid cc_default))
                                  ((Eaddrof (Evar _t2 (Tstruct _fe noattr))
                                     (tptr (Tstruct _fe noattr))) ::
                                   (Eaddrof (Evar _t3 (Tstruct _fe noattr))
                                     (tptr (Tstruct _fe noattr))) ::
                                   (Eaddrof (Evar _t2 (Tstruct _fe noattr))
                                     (tptr (Tstruct _fe noattr))) :: nil))
                                (Ssequence
                                  (Scall None
                                    (Evar _fe_sq_tt (Tfunction
                                                      ((tptr (Tstruct _fe noattr)) ::
                                                       (tptr (Tstruct _fe noattr)) ::
                                                       nil) tvoid cc_default))
                                    ((Eaddrof (Evar _t2 (Tstruct _fe noattr))
                                       (tptr (Tstruct _fe noattr))) ::
                                     (Eaddrof (Evar _t2 (Tstruct _fe noattr))
                                       (tptr (Tstruct _fe noattr))) :: nil))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _i
                                        (Econst_int (Int.repr 1) tint))
                                      (Sloop
                                        (Ssequence
                                          (Sifthenelse (Ebinop Olt
                                                         (Etempvar _i tint)
                                                         (Econst_int (Int.repr 10) tint)
                                                         tint)
                                            Sskip
                                            Sbreak)
                                          (Scall None
                                            (Evar _fe_sq_tt (Tfunction
                                                              ((tptr (Tstruct _fe noattr)) ::
                                                               (tptr (Tstruct _fe noattr)) ::
                                                               nil) tvoid
                                                              cc_default))
                                            ((Eaddrof
                                               (Evar _t2 (Tstruct _fe noattr))
                                               (tptr (Tstruct _fe noattr))) ::
                                             (Eaddrof
                                               (Evar _t2 (Tstruct _fe noattr))
                                               (tptr (Tstruct _fe noattr))) ::
                                             nil)))
                                        (Sset _i
                                          (Ebinop Oadd (Etempvar _i tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint))))
                                    (Ssequence
                                      (Scall None
                                        (Evar _fe_mul_ttt (Tfunction
                                                            ((tptr (Tstruct _fe noattr)) ::
                                                             (tptr (Tstruct _fe noattr)) ::
                                                             (tptr (Tstruct _fe noattr)) ::
                                                             nil) tvoid
                                                            cc_default))
                                        ((Eaddrof
                                           (Evar _t1 (Tstruct _fe noattr))
                                           (tptr (Tstruct _fe noattr))) ::
                                         (Eaddrof
                                           (Evar _t2 (Tstruct _fe noattr))
                                           (tptr (Tstruct _fe noattr))) ::
                                         (Eaddrof
                                           (Evar _t1 (Tstruct _fe noattr))
                                           (tptr (Tstruct _fe noattr))) ::
                                         nil))
                                      (Ssequence
                                        (Scall None
                                          (Evar _fe_sq_tt (Tfunction
                                                            ((tptr (Tstruct _fe noattr)) ::
                                                             (tptr (Tstruct _fe noattr)) ::
                                                             nil) tvoid
                                                            cc_default))
                                          ((Eaddrof
                                             (Evar _t2 (Tstruct _fe noattr))
                                             (tptr (Tstruct _fe noattr))) ::
                                           (Eaddrof
                                             (Evar _t1 (Tstruct _fe noattr))
                                             (tptr (Tstruct _fe noattr))) ::
                                           nil))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _i
                                              (Econst_int (Int.repr 1) tint))
                                            (Sloop
                                              (Ssequence
                                                (Sifthenelse (Ebinop Olt
                                                               (Etempvar _i tint)
                                                               (Econst_int (Int.repr 50) tint)
                                                               tint)
                                                  Sskip
                                                  Sbreak)
                                                (Scall None
                                                  (Evar _fe_sq_tt (Tfunction
                                                                    ((tptr (Tstruct _fe noattr)) ::
                                                                    (tptr (Tstruct _fe noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                  ((Eaddrof
                                                     (Evar _t2 (Tstruct _fe noattr))
                                                     (tptr (Tstruct _fe noattr))) ::
                                                   (Eaddrof
                                                     (Evar _t2 (Tstruct _fe noattr))
                                                     (tptr (Tstruct _fe noattr))) ::
                                                   nil)))
                                              (Sset _i
                                                (Ebinop Oadd
                                                  (Etempvar _i tint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tint))))
                                          (Ssequence
                                            (Scall None
                                              (Evar _fe_mul_ttt (Tfunction
                                                                  ((tptr (Tstruct _fe noattr)) ::
                                                                   (tptr (Tstruct _fe noattr)) ::
                                                                   (tptr (Tstruct _fe noattr)) ::
                                                                   nil) tvoid
                                                                  cc_default))
                                              ((Eaddrof
                                                 (Evar _t2 (Tstruct _fe noattr))
                                                 (tptr (Tstruct _fe noattr))) ::
                                               (Eaddrof
                                                 (Evar _t2 (Tstruct _fe noattr))
                                                 (tptr (Tstruct _fe noattr))) ::
                                               (Eaddrof
                                                 (Evar _t1 (Tstruct _fe noattr))
                                                 (tptr (Tstruct _fe noattr))) ::
                                               nil))
                                            (Ssequence
                                              (Scall None
                                                (Evar _fe_sq_tt (Tfunction
                                                                  ((tptr (Tstruct _fe noattr)) ::
                                                                   (tptr (Tstruct _fe noattr)) ::
                                                                   nil) tvoid
                                                                  cc_default))
                                                ((Eaddrof
                                                   (Evar _t3 (Tstruct _fe noattr))
                                                   (tptr (Tstruct _fe noattr))) ::
                                                 (Eaddrof
                                                   (Evar _t2 (Tstruct _fe noattr))
                                                   (tptr (Tstruct _fe noattr))) ::
                                                 nil))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _i
                                                    (Econst_int (Int.repr 1) tint))
                                                  (Sloop
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop Olt
                                                                    (Etempvar _i tint)
                                                                    (Econst_int (Int.repr 100) tint)
                                                                    tint)
                                                        Sskip
                                                        Sbreak)
                                                      (Scall None
                                                        (Evar _fe_sq_tt 
                                                        (Tfunction
                                                          ((tptr (Tstruct _fe noattr)) ::
                                                           (tptr (Tstruct _fe noattr)) ::
                                                           nil) tvoid
                                                          cc_default))
                                                        ((Eaddrof
                                                           (Evar _t3 (Tstruct _fe noattr))
                                                           (tptr (Tstruct _fe noattr))) ::
                                                         (Eaddrof
                                                           (Evar _t3 (Tstruct _fe noattr))
                                                           (tptr (Tstruct _fe noattr))) ::
                                                         nil)))
                                                    (Sset _i
                                                      (Ebinop Oadd
                                                        (Etempvar _i tint)
                                                        (Econst_int (Int.repr 1) tint)
                                                        tint))))
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _fe_mul_ttt 
                                                    (Tfunction
                                                      ((tptr (Tstruct _fe noattr)) ::
                                                       (tptr (Tstruct _fe noattr)) ::
                                                       (tptr (Tstruct _fe noattr)) ::
                                                       nil) tvoid cc_default))
                                                    ((Eaddrof
                                                       (Evar _t2 (Tstruct _fe noattr))
                                                       (tptr (Tstruct _fe noattr))) ::
                                                     (Eaddrof
                                                       (Evar _t3 (Tstruct _fe noattr))
                                                       (tptr (Tstruct _fe noattr))) ::
                                                     (Eaddrof
                                                       (Evar _t2 (Tstruct _fe noattr))
                                                       (tptr (Tstruct _fe noattr))) ::
                                                     nil))
                                                  (Ssequence
                                                    (Scall None
                                                      (Evar _fe_sq_tt 
                                                      (Tfunction
                                                        ((tptr (Tstruct _fe noattr)) ::
                                                         (tptr (Tstruct _fe noattr)) ::
                                                         nil) tvoid
                                                        cc_default))
                                                      ((Eaddrof
                                                         (Evar _t2 (Tstruct _fe noattr))
                                                         (tptr (Tstruct _fe noattr))) ::
                                                       (Eaddrof
                                                         (Evar _t2 (Tstruct _fe noattr))
                                                         (tptr (Tstruct _fe noattr))) ::
                                                       nil))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _i
                                                          (Econst_int (Int.repr 1) tint))
                                                        (Sloop
                                                          (Ssequence
                                                            (Sifthenelse 
                                                              (Ebinop Olt
                                                                (Etempvar _i tint)
                                                                (Econst_int (Int.repr 50) tint)
                                                                tint)
                                                              Sskip
                                                              Sbreak)
                                                            (Scall None
                                                              (Evar _fe_sq_tt 
                                                              (Tfunction
                                                                ((tptr (Tstruct _fe noattr)) ::
                                                                 (tptr (Tstruct _fe noattr)) ::
                                                                 nil) tvoid
                                                                cc_default))
                                                              ((Eaddrof
                                                                 (Evar _t2 (Tstruct _fe noattr))
                                                                 (tptr (Tstruct _fe noattr))) ::
                                                               (Eaddrof
                                                                 (Evar _t2 (Tstruct _fe noattr))
                                                                 (tptr (Tstruct _fe noattr))) ::
                                                               nil)))
                                                          (Sset _i
                                                            (Ebinop Oadd
                                                              (Etempvar _i tint)
                                                              (Econst_int (Int.repr 1) tint)
                                                              tint))))
                                                      (Ssequence
                                                        (Scall None
                                                          (Evar _fe_mul_ttt 
                                                          (Tfunction
                                                            ((tptr (Tstruct _fe noattr)) ::
                                                             (tptr (Tstruct _fe noattr)) ::
                                                             (tptr (Tstruct _fe noattr)) ::
                                                             nil) tvoid
                                                            cc_default))
                                                          ((Eaddrof
                                                             (Evar _t1 (Tstruct _fe noattr))
                                                             (tptr (Tstruct _fe noattr))) ::
                                                           (Eaddrof
                                                             (Evar _t2 (Tstruct _fe noattr))
                                                             (tptr (Tstruct _fe noattr))) ::
                                                           (Eaddrof
                                                             (Evar _t1 (Tstruct _fe noattr))
                                                             (tptr (Tstruct _fe noattr))) ::
                                                           nil))
                                                        (Ssequence
                                                          (Scall None
                                                            (Evar _fe_sq_tt 
                                                            (Tfunction
                                                              ((tptr (Tstruct _fe noattr)) ::
                                                               (tptr (Tstruct _fe noattr)) ::
                                                               nil) tvoid
                                                              cc_default))
                                                            ((Eaddrof
                                                               (Evar _t1 (Tstruct _fe noattr))
                                                               (tptr (Tstruct _fe noattr))) ::
                                                             (Eaddrof
                                                               (Evar _t1 (Tstruct _fe noattr))
                                                               (tptr (Tstruct _fe noattr))) ::
                                                             nil))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _i
                                                                (Econst_int (Int.repr 1) tint))
                                                              (Sloop
                                                                (Ssequence
                                                                  (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _i tint)
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                  (Scall None
                                                                    (Evar _fe_sq_tt 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _fe noattr)) ::
                                                                    (tptr (Tstruct _fe noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _t1 (Tstruct _fe noattr))
                                                                    (tptr (Tstruct _fe noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _t1 (Tstruct _fe noattr))
                                                                    (tptr (Tstruct _fe noattr))) ::
                                                                    nil)))
                                                                (Sset _i
                                                                  (Ebinop Oadd
                                                                    (Etempvar _i tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint))))
                                                            (Scall None
                                                              (Evar _fe_mul_ttt 
                                                              (Tfunction
                                                                ((tptr (Tstruct _fe noattr)) ::
                                                                 (tptr (Tstruct _fe noattr)) ::
                                                                 (tptr (Tstruct _fe noattr)) ::
                                                                 nil) tvoid
                                                                cc_default))
                                                              ((Etempvar _out (tptr (Tstruct _fe noattr))) ::
                                                               (Eaddrof
                                                                 (Evar _t1 (Tstruct _fe noattr))
                                                                 (tptr (Tstruct _fe noattr))) ::
                                                               (Eaddrof
                                                                 (Evar _t0 (Tstruct _fe noattr))
                                                                 (tptr (Tstruct _fe noattr))) ::
                                                               nil))))))))))))))))))))))))))))))))
|}.

Definition f_fe_invert := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr (Tstruct _fe noattr))) ::
                (_z, (tptr (Tstruct _fe noattr))) :: nil);
  fn_vars := ((_l, (Tstruct _fe_loose noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _fe_copy_lt (Tfunction
                        ((tptr (Tstruct _fe_loose noattr)) ::
                         (tptr (Tstruct _fe noattr)) :: nil) tvoid
                        cc_default))
    ((Eaddrof (Evar _l (Tstruct _fe_loose noattr))
       (tptr (Tstruct _fe_loose noattr))) ::
     (Etempvar _z (tptr (Tstruct _fe noattr))) :: nil))
  (Scall None
    (Evar _fe_loose_invert (Tfunction
                             ((tptr (Tstruct _fe noattr)) ::
                              (tptr (Tstruct _fe_loose noattr)) :: nil) tvoid
                             cc_default))
    ((Etempvar _out (tptr (Tstruct _fe noattr))) ::
     (Eaddrof (Evar _l (Tstruct _fe_loose noattr))
       (tptr (Tstruct _fe_loose noattr))) :: nil)))
|}.

Definition f_fe_cswap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_f, (tptr (Tstruct _fe noattr))) ::
                (_g, (tptr (Tstruct _fe noattr))) :: (_b, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_x, tuint) :: (_t'4, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _b
    (Ebinop Osub (Econst_int (Int.repr 0) tint) (Etempvar _b tuint) tuint))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                       (Econst_int (Int.repr 10) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _f (tptr (Tstruct _fe noattr)))
                      (Tstruct _fe noattr)) _v (tarray tuint 10))
                  (Etempvar _i tuint) (tptr tuint)) tuint))
            (Ssequence
              (Sset _t'4
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _g (tptr (Tstruct _fe noattr)))
                        (Tstruct _fe noattr)) _v (tarray tuint 10))
                    (Etempvar _i tuint) (tptr tuint)) tuint))
              (Sset _x
                (Ebinop Oxor (Etempvar _t'3 tuint) (Etempvar _t'4 tuint)
                  tuint))))
          (Ssequence
            (Sset _x
              (Ebinop Oand (Etempvar _x tuint) (Etempvar _b tuint) tuint))
            (Ssequence
              (Ssequence
                (Sset _t'2
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _f (tptr (Tstruct _fe noattr)))
                          (Tstruct _fe noattr)) _v (tarray tuint 10))
                      (Etempvar _i tuint) (tptr tuint)) tuint))
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _f (tptr (Tstruct _fe noattr)))
                          (Tstruct _fe noattr)) _v (tarray tuint 10))
                      (Etempvar _i tuint) (tptr tuint)) tuint)
                  (Ebinop Oxor (Etempvar _t'2 tuint) (Etempvar _x tuint)
                    tuint)))
              (Ssequence
                (Sset _t'1
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _g (tptr (Tstruct _fe noattr)))
                          (Tstruct _fe noattr)) _v (tarray tuint 10))
                      (Etempvar _i tuint) (tptr tuint)) tuint))
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _g (tptr (Tstruct _fe noattr)))
                          (Tstruct _fe noattr)) _v (tarray tuint 10))
                      (Etempvar _i tuint) (tptr tuint)) tuint)
                  (Ebinop Oxor (Etempvar _t'1 tuint) (Etempvar _x tuint)
                    tuint)))))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
          tuint)))))
|}.

Definition f_fe_mul_121666_impl := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuint)) :: (_in1, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_x20, tuint) :: (_x21, tuint) :: (_x19, tuint) ::
               (_x17, tuint) :: (_x15, tuint) :: (_x13, tuint) ::
               (_x11, tuint) :: (_x9, tuint) :: (_x7, tuint) ::
               (_x5, tuint) :: (_x38, tuint) :: (_x39, tuint) ::
               (_x37, tuint) :: (_x35, tuint) :: (_x33, tuint) ::
               (_x31, tuint) :: (_x29, tuint) :: (_x27, tuint) ::
               (_x25, tuint) :: (_x23, tuint) :: (_x40, tulong) ::
               (_x41, tulong) :: (_x42, tulong) :: (_x43, tulong) ::
               (_x44, tulong) :: (_x45, tulong) :: (_x46, tulong) ::
               (_x47, tulong) :: (_x48, tulong) :: (_x49, tulong) ::
               (_x50, tulong) :: (_x51, tulong) :: (_x52, tulong) ::
               (_x53, tulong) :: (_x54, tulong) :: (_x55, tulong) ::
               (_x56, tulong) :: (_x57, tulong) :: (_x58, tulong) ::
               (_x59, tulong) :: (_x60, tulong) :: (_x61, tulong) ::
               (_x62, tulong) :: (_x63, tulong) :: (_x64, tulong) ::
               (_x65, tulong) :: (_x66, tulong) :: (_x67, tulong) ::
               (_x68, tulong) :: (_x69, tulong) :: (_x70, tulong) ::
               (_x71, tulong) :: (_x72, tulong) :: (_x73, tulong) ::
               (_x74, tulong) :: (_x75, tulong) :: (_x76, tulong) ::
               (_x77, tulong) :: (_x78, tulong) :: (_x79, tulong) ::
               (_x80, tulong) :: (_x81, tulong) :: (_x82, tulong) ::
               (_x83, tulong) :: (_x84, tulong) :: (_x85, tulong) ::
               (_x86, tulong) :: (_x87, tuint) :: (_x88, tulong) ::
               (_x89, tulong) :: (_x90, tuint) :: (_x91, tulong) ::
               (_x92, tulong) :: (_x93, tuint) :: (_x94, tulong) ::
               (_x95, tulong) :: (_x96, tuint) :: (_x97, tulong) ::
               (_x98, tulong) :: (_x99, tuint) :: (_x100, tulong) ::
               (_x101, tulong) :: (_x102, tuint) :: (_x103, tulong) ::
               (_x104, tulong) :: (_x105, tuint) :: (_x106, tulong) ::
               (_x107, tulong) :: (_x108, tuint) :: (_x109, tulong) ::
               (_x110, tulong) :: (_x111, tuint) :: (_x112, tulong) ::
               (_x113, tulong) :: (_x114, tuint) :: (_x115, tulong) ::
               (_x116, tuint) :: (_x117, tuint) :: (_x118, tuint) ::
               (_x119, tuint) :: (_x120, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _x20
    (Ederef
      (Ebinop Oadd (Etempvar _in1 (tptr tuint))
        (Econst_int (Int.repr 9) tint) (tptr tuint)) tuint))
  (Ssequence
    (Sset _x21
      (Ederef
        (Ebinop Oadd (Etempvar _in1 (tptr tuint))
          (Econst_int (Int.repr 8) tint) (tptr tuint)) tuint))
    (Ssequence
      (Sset _x19
        (Ederef
          (Ebinop Oadd (Etempvar _in1 (tptr tuint))
            (Econst_int (Int.repr 7) tint) (tptr tuint)) tuint))
      (Ssequence
        (Sset _x17
          (Ederef
            (Ebinop Oadd (Etempvar _in1 (tptr tuint))
              (Econst_int (Int.repr 6) tint) (tptr tuint)) tuint))
        (Ssequence
          (Sset _x15
            (Ederef
              (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                (Econst_int (Int.repr 5) tint) (tptr tuint)) tuint))
          (Ssequence
            (Sset _x13
              (Ederef
                (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                  (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint))
            (Ssequence
              (Sset _x11
                (Ederef
                  (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                    (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint))
              (Ssequence
                (Sset _x9
                  (Ederef
                    (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                      (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint))
                (Ssequence
                  (Sset _x7
                    (Ederef
                      (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                        (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint))
                  (Ssequence
                    (Sset _x5
                      (Ederef
                        (Ebinop Oadd (Etempvar _in1 (tptr tuint))
                          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
                    (Ssequence
                      (Sset _x38 (Econst_int (Int.repr 0) tint))
                      (Ssequence
                        (Sset _x39 (Econst_int (Int.repr 0) tint))
                        (Ssequence
                          (Sset _x37 (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Sset _x35 (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Sset _x33 (Econst_int (Int.repr 0) tint))
                              (Ssequence
                                (Sset _x31 (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Sset _x29 (Econst_int (Int.repr 0) tint))
                                  (Ssequence
                                    (Sset _x27
                                      (Econst_int (Int.repr 0) tint))
                                    (Ssequence
                                      (Sset _x25
                                        (Econst_int (Int.repr 0) tint))
                                      (Ssequence
                                        (Sset _x23
                                          (Econst_int (Int.repr 121666) tint))
                                        (Ssequence
                                          (Sset _x40
                                            (Ebinop Omul
                                              (Ecast (Etempvar _x23 tuint)
                                                tulong) (Etempvar _x5 tuint)
                                              tulong))
                                          (Ssequence
                                            (Sset _x41
                                              (Ebinop Oadd
                                                (Ebinop Omul
                                                  (Ecast
                                                    (Etempvar _x23 tuint)
                                                    tulong)
                                                  (Etempvar _x7 tuint)
                                                  tulong)
                                                (Ebinop Omul
                                                  (Ecast
                                                    (Etempvar _x25 tuint)
                                                    tulong)
                                                  (Etempvar _x5 tuint)
                                                  tulong) tulong))
                                            (Ssequence
                                              (Sset _x42
                                                (Ebinop Oadd
                                                  (Ebinop Oadd
                                                    (Ebinop Omul
                                                      (Ecast
                                                        (Ebinop Omul
                                                          (Econst_int (Int.repr 2) tint)
                                                          (Etempvar _x25 tuint)
                                                          tuint) tulong)
                                                      (Etempvar _x7 tuint)
                                                      tulong)
                                                    (Ebinop Omul
                                                      (Ecast
                                                        (Etempvar _x23 tuint)
                                                        tulong)
                                                      (Etempvar _x9 tuint)
                                                      tulong) tulong)
                                                  (Ebinop Omul
                                                    (Ecast
                                                      (Etempvar _x27 tuint)
                                                      tulong)
                                                    (Etempvar _x5 tuint)
                                                    tulong) tulong))
                                              (Ssequence
                                                (Sset _x43
                                                  (Ebinop Oadd
                                                    (Ebinop Oadd
                                                      (Ebinop Oadd
                                                        (Ebinop Omul
                                                          (Ecast
                                                            (Etempvar _x25 tuint)
                                                            tulong)
                                                          (Etempvar _x9 tuint)
                                                          tulong)
                                                        (Ebinop Omul
                                                          (Ecast
                                                            (Etempvar _x27 tuint)
                                                            tulong)
                                                          (Etempvar _x7 tuint)
                                                          tulong) tulong)
                                                      (Ebinop Omul
                                                        (Ecast
                                                          (Etempvar _x23 tuint)
                                                          tulong)
                                                        (Etempvar _x11 tuint)
                                                        tulong) tulong)
                                                    (Ebinop Omul
                                                      (Ecast
                                                        (Etempvar _x29 tuint)
                                                        tulong)
                                                      (Etempvar _x5 tuint)
                                                      tulong) tulong))
                                                (Ssequence
                                                  (Sset _x44
                                                    (Ebinop Oadd
                                                      (Ebinop Oadd
                                                        (Ebinop Oadd
                                                          (Ebinop Omul
                                                            (Ecast
                                                              (Etempvar _x27 tuint)
                                                              tulong)
                                                            (Etempvar _x9 tuint)
                                                            tulong)
                                                          (Ebinop Omul
                                                            (Econst_int (Int.repr 2) tint)
                                                            (Ebinop Oadd
                                                              (Ebinop Omul
                                                                (Ecast
                                                                  (Etempvar _x25 tuint)
                                                                  tulong)
                                                                (Etempvar _x11 tuint)
                                                                tulong)
                                                              (Ebinop Omul
                                                                (Ecast
                                                                  (Etempvar _x29 tuint)
                                                                  tulong)
                                                                (Etempvar _x7 tuint)
                                                                tulong)
                                                              tulong) tulong)
                                                          tulong)
                                                        (Ebinop Omul
                                                          (Ecast
                                                            (Etempvar _x23 tuint)
                                                            tulong)
                                                          (Etempvar _x13 tuint)
                                                          tulong) tulong)
                                                      (Ebinop Omul
                                                        (Ecast
                                                          (Etempvar _x31 tuint)
                                                          tulong)
                                                        (Etempvar _x5 tuint)
                                                        tulong) tulong))
                                                  (Ssequence
                                                    (Sset _x45
                                                      (Ebinop Oadd
                                                        (Ebinop Oadd
                                                          (Ebinop Oadd
                                                            (Ebinop Oadd
                                                              (Ebinop Oadd
                                                                (Ebinop Omul
                                                                  (Ecast
                                                                    (Etempvar _x27 tuint)
                                                                    tulong)
                                                                  (Etempvar _x11 tuint)
                                                                  tulong)
                                                                (Ebinop Omul
                                                                  (Ecast
                                                                    (Etempvar _x29 tuint)
                                                                    tulong)
                                                                  (Etempvar _x9 tuint)
                                                                  tulong)
                                                                tulong)
                                                              (Ebinop Omul
                                                                (Ecast
                                                                  (Etempvar _x25 tuint)
                                                                  tulong)
                                                                (Etempvar _x13 tuint)
                                                                tulong)
                                                              tulong)
                                                            (Ebinop Omul
                                                              (Ecast
                                                                (Etempvar _x31 tuint)
                                                                tulong)
                                                              (Etempvar _x7 tuint)
                                                              tulong) tulong)
                                                          (Ebinop Omul
                                                            (Ecast
                                                              (Etempvar _x23 tuint)
                                                              tulong)
                                                            (Etempvar _x15 tuint)
                                                            tulong) tulong)
                                                        (Ebinop Omul
                                                          (Ecast
                                                            (Etempvar _x33 tuint)
                                                            tulong)
                                                          (Etempvar _x5 tuint)
                                                          tulong) tulong))
                                                    (Ssequence
                                                      (Sset _x46
                                                        (Ebinop Oadd
                                                          (Ebinop Oadd
                                                            (Ebinop Oadd
                                                              (Ebinop Oadd
                                                                (Ebinop Omul
                                                                  (Econst_int (Int.repr 2) tint)
                                                                  (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x29 tuint)
                                                                    tulong)
                                                                    (Etempvar _x11 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x25 tuint)
                                                                    tulong)
                                                                    (Etempvar _x15 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x33 tuint)
                                                                    tulong)
                                                                    (Etempvar _x7 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                  tulong)
                                                                (Ebinop Omul
                                                                  (Ecast
                                                                    (Etempvar _x27 tuint)
                                                                    tulong)
                                                                  (Etempvar _x13 tuint)
                                                                  tulong)
                                                                tulong)
                                                              (Ebinop Omul
                                                                (Ecast
                                                                  (Etempvar _x31 tuint)
                                                                  tulong)
                                                                (Etempvar _x9 tuint)
                                                                tulong)
                                                              tulong)
                                                            (Ebinop Omul
                                                              (Ecast
                                                                (Etempvar _x23 tuint)
                                                                tulong)
                                                              (Etempvar _x17 tuint)
                                                              tulong) tulong)
                                                          (Ebinop Omul
                                                            (Ecast
                                                              (Etempvar _x35 tuint)
                                                              tulong)
                                                            (Etempvar _x5 tuint)
                                                            tulong) tulong))
                                                      (Ssequence
                                                        (Sset _x47
                                                          (Ebinop Oadd
                                                            (Ebinop Oadd
                                                              (Ebinop Oadd
                                                                (Ebinop Oadd
                                                                  (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x29 tuint)
                                                                    tulong)
                                                                    (Etempvar _x13 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x31 tuint)
                                                                    tulong)
                                                                    (Etempvar _x11 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x27 tuint)
                                                                    tulong)
                                                                    (Etempvar _x15 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x33 tuint)
                                                                    tulong)
                                                                    (Etempvar _x9 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                  (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x25 tuint)
                                                                    tulong)
                                                                    (Etempvar _x17 tuint)
                                                                    tulong)
                                                                  tulong)
                                                                (Ebinop Omul
                                                                  (Ecast
                                                                    (Etempvar _x35 tuint)
                                                                    tulong)
                                                                  (Etempvar _x7 tuint)
                                                                  tulong)
                                                                tulong)
                                                              (Ebinop Omul
                                                                (Ecast
                                                                  (Etempvar _x23 tuint)
                                                                  tulong)
                                                                (Etempvar _x19 tuint)
                                                                tulong)
                                                              tulong)
                                                            (Ebinop Omul
                                                              (Ecast
                                                                (Etempvar _x37 tuint)
                                                                tulong)
                                                              (Etempvar _x5 tuint)
                                                              tulong) tulong))
                                                        (Ssequence
                                                          (Sset _x48
                                                            (Ebinop Oadd
                                                              (Ebinop Oadd
                                                                (Ebinop Oadd
                                                                  (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x31 tuint)
                                                                    tulong)
                                                                    (Etempvar _x13 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x29 tuint)
                                                                    tulong)
                                                                    (Etempvar _x15 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x33 tuint)
                                                                    tulong)
                                                                    (Etempvar _x11 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x25 tuint)
                                                                    tulong)
                                                                    (Etempvar _x19 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x37 tuint)
                                                                    tulong)
                                                                    (Etempvar _x7 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x27 tuint)
                                                                    tulong)
                                                                    (Etempvar _x17 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                  (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x35 tuint)
                                                                    tulong)
                                                                    (Etempvar _x9 tuint)
                                                                    tulong)
                                                                  tulong)
                                                                (Ebinop Omul
                                                                  (Ecast
                                                                    (Etempvar _x23 tuint)
                                                                    tulong)
                                                                  (Etempvar _x21 tuint)
                                                                  tulong)
                                                                tulong)
                                                              (Ebinop Omul
                                                                (Ecast
                                                                  (Etempvar _x39 tuint)
                                                                  tulong)
                                                                (Etempvar _x5 tuint)
                                                                tulong)
                                                              tulong))
                                                          (Ssequence
                                                            (Sset _x49
                                                              (Ebinop Oadd
                                                                (Ebinop Oadd
                                                                  (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x31 tuint)
                                                                    tulong)
                                                                    (Etempvar _x15 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x33 tuint)
                                                                    tulong)
                                                                    (Etempvar _x13 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x29 tuint)
                                                                    tulong)
                                                                    (Etempvar _x17 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x35 tuint)
                                                                    tulong)
                                                                    (Etempvar _x11 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x27 tuint)
                                                                    tulong)
                                                                    (Etempvar _x19 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x37 tuint)
                                                                    tulong)
                                                                    (Etempvar _x9 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x25 tuint)
                                                                    tulong)
                                                                    (Etempvar _x21 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x39 tuint)
                                                                    tulong)
                                                                    (Etempvar _x7 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                  (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x23 tuint)
                                                                    tulong)
                                                                    (Etempvar _x20 tuint)
                                                                    tulong)
                                                                  tulong)
                                                                (Ebinop Omul
                                                                  (Ecast
                                                                    (Etempvar _x38 tuint)
                                                                    tulong)
                                                                  (Etempvar _x5 tuint)
                                                                  tulong)
                                                                tulong))
                                                            (Ssequence
                                                              (Sset _x50
                                                                (Ebinop Oadd
                                                                  (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x33 tuint)
                                                                    tulong)
                                                                    (Etempvar _x15 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x29 tuint)
                                                                    tulong)
                                                                    (Etempvar _x19 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x37 tuint)
                                                                    tulong)
                                                                    (Etempvar _x11 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x25 tuint)
                                                                    tulong)
                                                                    (Etempvar _x20 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x38 tuint)
                                                                    tulong)
                                                                    (Etempvar _x7 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x31 tuint)
                                                                    tulong)
                                                                    (Etempvar _x17 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x35 tuint)
                                                                    tulong)
                                                                    (Etempvar _x13 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x27 tuint)
                                                                    tulong)
                                                                    (Etempvar _x21 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                  (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x39 tuint)
                                                                    tulong)
                                                                    (Etempvar _x9 tuint)
                                                                    tulong)
                                                                  tulong))
                                                              (Ssequence
                                                                (Sset _x51
                                                                  (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x33 tuint)
                                                                    tulong)
                                                                    (Etempvar _x17 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x35 tuint)
                                                                    tulong)
                                                                    (Etempvar _x15 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x31 tuint)
                                                                    tulong)
                                                                    (Etempvar _x19 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x37 tuint)
                                                                    tulong)
                                                                    (Etempvar _x13 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x29 tuint)
                                                                    tulong)
                                                                    (Etempvar _x21 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x39 tuint)
                                                                    tulong)
                                                                    (Etempvar _x11 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x27 tuint)
                                                                    tulong)
                                                                    (Etempvar _x20 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x38 tuint)
                                                                    tulong)
                                                                    (Etempvar _x9 tuint)
                                                                    tulong)
                                                                    tulong))
                                                                (Ssequence
                                                                  (Sset _x52
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x35 tuint)
                                                                    tulong)
                                                                    (Etempvar _x17 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x33 tuint)
                                                                    tulong)
                                                                    (Etempvar _x19 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x37 tuint)
                                                                    tulong)
                                                                    (Etempvar _x15 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x29 tuint)
                                                                    tulong)
                                                                    (Etempvar _x20 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x38 tuint)
                                                                    tulong)
                                                                    (Etempvar _x11 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x31 tuint)
                                                                    tulong)
                                                                    (Etempvar _x21 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x39 tuint)
                                                                    tulong)
                                                                    (Etempvar _x13 tuint)
                                                                    tulong)
                                                                    tulong))
                                                                  (Ssequence
                                                                    (Sset _x53
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x35 tuint)
                                                                    tulong)
                                                                    (Etempvar _x19 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x37 tuint)
                                                                    tulong)
                                                                    (Etempvar _x17 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x33 tuint)
                                                                    tulong)
                                                                    (Etempvar _x21 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x39 tuint)
                                                                    tulong)
                                                                    (Etempvar _x15 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x31 tuint)
                                                                    tulong)
                                                                    (Etempvar _x20 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x38 tuint)
                                                                    tulong)
                                                                    (Etempvar _x13 tuint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x54
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x37 tuint)
                                                                    tulong)
                                                                    (Etempvar _x19 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x33 tuint)
                                                                    tulong)
                                                                    (Etempvar _x20 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x38 tuint)
                                                                    tulong)
                                                                    (Etempvar _x15 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x35 tuint)
                                                                    tulong)
                                                                    (Etempvar _x21 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x39 tuint)
                                                                    tulong)
                                                                    (Etempvar _x17 tuint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x55
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x37 tuint)
                                                                    tulong)
                                                                    (Etempvar _x21 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x39 tuint)
                                                                    tulong)
                                                                    (Etempvar _x19 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x35 tuint)
                                                                    tulong)
                                                                    (Etempvar _x20 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x38 tuint)
                                                                    tulong)
                                                                    (Etempvar _x17 tuint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x56
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x39 tuint)
                                                                    tulong)
                                                                    (Etempvar _x21 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x37 tuint)
                                                                    tulong)
                                                                    (Etempvar _x20 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x38 tuint)
                                                                    tulong)
                                                                    (Etempvar _x19 tuint)
                                                                    tulong)
                                                                    tulong)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x57
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x39 tuint)
                                                                    tulong)
                                                                    (Etempvar _x20 tuint)
                                                                    tulong)
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _x38 tuint)
                                                                    tulong)
                                                                    (Etempvar _x21 tuint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x58
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Etempvar _x38 tuint)
                                                                    tuint)
                                                                    tulong)
                                                                    (Etempvar _x20 tuint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x59
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x48 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x58 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x60
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x59 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x58 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x61
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x60 tulong)
                                                                    (Etempvar _x58 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x62
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x47 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x57 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x63
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x62 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x57 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x64
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x63 tulong)
                                                                    (Etempvar _x57 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x65
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x46 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x56 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x66
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x65 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x56 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x67
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x66 tulong)
                                                                    (Etempvar _x56 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x68
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x45 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x55 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x69
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x68 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x55 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x70
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x69 tulong)
                                                                    (Etempvar _x55 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x71
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x44 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x54 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x72
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x71 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x54 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x73
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x72 tulong)
                                                                    (Etempvar _x54 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x74
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x43 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x53 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x75
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x74 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x53 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x76
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x75 tulong)
                                                                    (Etempvar _x53 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x77
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x42 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x52 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x78
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x77 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x52 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x79
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x78 tulong)
                                                                    (Etempvar _x52 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x80
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x41 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x51 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x81
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x80 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x51 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x82
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x81 tulong)
                                                                    (Etempvar _x51 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x83
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x40 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x50 tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x84
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x83 tulong)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _x50 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x85
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x84 tulong)
                                                                    (Etempvar _x50 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x86
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x85 tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x87
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x85 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x88
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x86 tulong)
                                                                    (Etempvar _x82 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x89
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x88 tulong)
                                                                    (Econst_int (Int.repr 25) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x90
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x88 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 33554431) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x91
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x89 tulong)
                                                                    (Etempvar _x79 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x92
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x91 tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x93
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x91 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x94
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x92 tulong)
                                                                    (Etempvar _x76 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x95
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x94 tulong)
                                                                    (Econst_int (Int.repr 25) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x96
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x94 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 33554431) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x97
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x95 tulong)
                                                                    (Etempvar _x73 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x98
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x97 tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x99
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x97 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x100
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x98 tulong)
                                                                    (Etempvar _x70 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x101
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x100 tulong)
                                                                    (Econst_int (Int.repr 25) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x102
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x100 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 33554431) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x103
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x101 tulong)
                                                                    (Etempvar _x67 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x104
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x103 tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x105
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x103 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x106
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x104 tulong)
                                                                    (Etempvar _x64 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x107
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x106 tulong)
                                                                    (Econst_int (Int.repr 25) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x108
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x106 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 33554431) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x109
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x107 tulong)
                                                                    (Etempvar _x61 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x110
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x109 tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x111
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x109 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x112
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x110 tulong)
                                                                    (Etempvar _x49 tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x113
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x112 tulong)
                                                                    (Econst_int (Int.repr 25) tint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x114
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x112 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 33554431) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x115
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x87 tuint)
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 19) tint)
                                                                    (Etempvar _x113 tulong)
                                                                    tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _x116
                                                                    (Ecast
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x115 tulong)
                                                                    (Econst_int (Int.repr 26) tint)
                                                                    tulong)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x117
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _x115 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 67108863) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x118
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x116 tuint)
                                                                    (Etempvar _x90 tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x119
                                                                    (Ebinop Oshr
                                                                    (Etempvar _x118 tuint)
                                                                    (Econst_int (Int.repr 25) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _x120
                                                                    (Ebinop Oand
                                                                    (Etempvar _x118 tuint)
                                                                    (Econst_int (Int.repr 33554431) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x117 tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x120 tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x119 tuint)
                                                                    (Etempvar _x93 tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x96 tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x99 tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x102 tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x105 tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x108 tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x111 tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _out (tptr tuint))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _x114 tuint))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
|}.

Definition f_fe_mul121666 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _fe noattr))) ::
                (_f, (tptr (Tstruct _fe_loose noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _fe_mul_121666_impl (Tfunction ((tptr tuint) :: (tptr tuint) :: nil)
                              tvoid cc_default))
  ((Efield
     (Ederef (Etempvar _h (tptr (Tstruct _fe noattr))) (Tstruct _fe noattr))
     _v (tarray tuint 10)) ::
   (Efield
     (Ederef (Etempvar _f (tptr (Tstruct _fe_loose noattr)))
       (Tstruct _fe_loose noattr)) _v (tarray tuint 10)) :: nil))
|}.

Definition f_curve25519_generic := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) :: (_scalar, (tptr tuchar)) ::
                (_point, (tptr tuchar)) :: nil);
  fn_vars := ((_x1, (Tstruct _fe noattr)) :: (_x2, (Tstruct _fe noattr)) ::
              (_z2, (Tstruct _fe noattr)) :: (_x3, (Tstruct _fe noattr)) ::
              (_z3, (Tstruct _fe noattr)) ::
              (_x2l, (Tstruct _fe_loose noattr)) ::
              (_z2l, (Tstruct _fe_loose noattr)) ::
              (_x3l, (Tstruct _fe_loose noattr)) ::
              (_e, (tarray tuchar 32)) :: (_tmp0, (Tstruct _fe noattr)) ::
              (_tmp1, (Tstruct _fe noattr)) ::
              (_tmp0l, (Tstruct _fe_loose noattr)) ::
              (_tmp1l, (Tstruct _fe_loose noattr)) :: nil);
  fn_temps := ((_swap, tuint) :: (_pos, tint) :: (_b, tuint) ::
               (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _swap (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Scall None
      (Evar _memcpy (Tfunction
                      ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil)
                      (tptr tvoid) cc_default))
      ((Evar _e (tarray tuchar 32)) :: (Etempvar _scalar (tptr tuchar)) ::
       (Econst_int (Int.repr 32) tint) :: nil))
    (Ssequence
      (Scall None
        (Evar _curve25519_clamp_secret (Tfunction ((tptr tuchar) :: nil)
                                         tvoid cc_default))
        ((Evar _e (tarray tuchar 32)) :: nil))
      (Ssequence
        (Scall None
          (Evar _fe_frombytes (Tfunction
                                ((tptr (Tstruct _fe noattr)) ::
                                 (tptr tuchar) :: nil) tvoid cc_default))
          ((Eaddrof (Evar _x1 (Tstruct _fe noattr))
             (tptr (Tstruct _fe noattr))) ::
           (Etempvar _point (tptr tuchar)) :: nil))
        (Ssequence
          (Scall None
            (Evar _fe_1 (Tfunction ((tptr (Tstruct _fe noattr)) :: nil) tvoid
                          cc_default))
            ((Eaddrof (Evar _x2 (Tstruct _fe noattr))
               (tptr (Tstruct _fe noattr))) :: nil))
          (Ssequence
            (Scall None
              (Evar _fe_0 (Tfunction ((tptr (Tstruct _fe noattr)) :: nil)
                            tvoid cc_default))
              ((Eaddrof (Evar _z2 (Tstruct _fe noattr))
                 (tptr (Tstruct _fe noattr))) :: nil))
            (Ssequence
              (Scall None
                (Evar _fe_copy (Tfunction
                                 ((tptr (Tstruct _fe noattr)) ::
                                  (tptr (Tstruct _fe noattr)) :: nil) tvoid
                                 cc_default))
                ((Eaddrof (Evar _x3 (Tstruct _fe noattr))
                   (tptr (Tstruct _fe noattr))) ::
                 (Eaddrof (Evar _x1 (Tstruct _fe noattr))
                   (tptr (Tstruct _fe noattr))) :: nil))
              (Ssequence
                (Scall None
                  (Evar _fe_1 (Tfunction ((tptr (Tstruct _fe noattr)) :: nil)
                                tvoid cc_default))
                  ((Eaddrof (Evar _z3 (Tstruct _fe noattr))
                     (tptr (Tstruct _fe noattr))) :: nil))
                (Ssequence
                  (Ssequence
                    (Sset _pos (Econst_int (Int.repr 254) tint))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Oge (Etempvar _pos tint)
                                       (Econst_int (Int.repr 0) tint) tint)
                          Sskip
                          Sbreak)
                        (Ssequence
                          (Ssequence
                            (Sset _t'1
                              (Ederef
                                (Ebinop Oadd (Evar _e (tarray tuchar 32))
                                  (Ebinop Odiv (Etempvar _pos tint)
                                    (Econst_int (Int.repr 8) tint) tint)
                                  (tptr tuchar)) tuchar))
                            (Sset _b
                              (Ebinop Oand (Econst_int (Int.repr 1) tint)
                                (Ebinop Oshr (Etempvar _t'1 tuchar)
                                  (Ebinop Oand (Etempvar _pos tint)
                                    (Econst_int (Int.repr 7) tint) tint)
                                  tint) tint)))
                          (Ssequence
                            (Sset _swap
                              (Ebinop Oxor (Etempvar _swap tuint)
                                (Etempvar _b tuint) tuint))
                            (Ssequence
                              (Scall None
                                (Evar _fe_cswap (Tfunction
                                                  ((tptr (Tstruct _fe noattr)) ::
                                                   (tptr (Tstruct _fe noattr)) ::
                                                   tuint :: nil) tvoid
                                                  cc_default))
                                ((Eaddrof (Evar _x2 (Tstruct _fe noattr))
                                   (tptr (Tstruct _fe noattr))) ::
                                 (Eaddrof (Evar _x3 (Tstruct _fe noattr))
                                   (tptr (Tstruct _fe noattr))) ::
                                 (Etempvar _swap tuint) :: nil))
                              (Ssequence
                                (Scall None
                                  (Evar _fe_cswap (Tfunction
                                                    ((tptr (Tstruct _fe noattr)) ::
                                                     (tptr (Tstruct _fe noattr)) ::
                                                     tuint :: nil) tvoid
                                                    cc_default))
                                  ((Eaddrof (Evar _z2 (Tstruct _fe noattr))
                                     (tptr (Tstruct _fe noattr))) ::
                                   (Eaddrof (Evar _z3 (Tstruct _fe noattr))
                                     (tptr (Tstruct _fe noattr))) ::
                                   (Etempvar _swap tuint) :: nil))
                                (Ssequence
                                  (Sset _swap (Etempvar _b tuint))
                                  (Ssequence
                                    (Scall None
                                      (Evar _fe_sub (Tfunction
                                                      ((tptr (Tstruct _fe_loose noattr)) ::
                                                       (tptr (Tstruct _fe noattr)) ::
                                                       (tptr (Tstruct _fe noattr)) ::
                                                       nil) tvoid cc_default))
                                      ((Eaddrof
                                         (Evar _tmp0l (Tstruct _fe_loose noattr))
                                         (tptr (Tstruct _fe_loose noattr))) ::
                                       (Eaddrof
                                         (Evar _x3 (Tstruct _fe noattr))
                                         (tptr (Tstruct _fe noattr))) ::
                                       (Eaddrof
                                         (Evar _z3 (Tstruct _fe noattr))
                                         (tptr (Tstruct _fe noattr))) :: nil))
                                    (Ssequence
                                      (Scall None
                                        (Evar _fe_sub (Tfunction
                                                        ((tptr (Tstruct _fe_loose noattr)) ::
                                                         (tptr (Tstruct _fe noattr)) ::
                                                         (tptr (Tstruct _fe noattr)) ::
                                                         nil) tvoid
                                                        cc_default))
                                        ((Eaddrof
                                           (Evar _tmp1l (Tstruct _fe_loose noattr))
                                           (tptr (Tstruct _fe_loose noattr))) ::
                                         (Eaddrof
                                           (Evar _x2 (Tstruct _fe noattr))
                                           (tptr (Tstruct _fe noattr))) ::
                                         (Eaddrof
                                           (Evar _z2 (Tstruct _fe noattr))
                                           (tptr (Tstruct _fe noattr))) ::
                                         nil))
                                      (Ssequence
                                        (Scall None
                                          (Evar _fe_add (Tfunction
                                                          ((tptr (Tstruct _fe_loose noattr)) ::
                                                           (tptr (Tstruct _fe noattr)) ::
                                                           (tptr (Tstruct _fe noattr)) ::
                                                           nil) tvoid
                                                          cc_default))
                                          ((Eaddrof
                                             (Evar _x2l (Tstruct _fe_loose noattr))
                                             (tptr (Tstruct _fe_loose noattr))) ::
                                           (Eaddrof
                                             (Evar _x2 (Tstruct _fe noattr))
                                             (tptr (Tstruct _fe noattr))) ::
                                           (Eaddrof
                                             (Evar _z2 (Tstruct _fe noattr))
                                             (tptr (Tstruct _fe noattr))) ::
                                           nil))
                                        (Ssequence
                                          (Scall None
                                            (Evar _fe_add (Tfunction
                                                            ((tptr (Tstruct _fe_loose noattr)) ::
                                                             (tptr (Tstruct _fe noattr)) ::
                                                             (tptr (Tstruct _fe noattr)) ::
                                                             nil) tvoid
                                                            cc_default))
                                            ((Eaddrof
                                               (Evar _z2l (Tstruct _fe_loose noattr))
                                               (tptr (Tstruct _fe_loose noattr))) ::
                                             (Eaddrof
                                               (Evar _x3 (Tstruct _fe noattr))
                                               (tptr (Tstruct _fe noattr))) ::
                                             (Eaddrof
                                               (Evar _z3 (Tstruct _fe noattr))
                                               (tptr (Tstruct _fe noattr))) ::
                                             nil))
                                          (Ssequence
                                            (Scall None
                                              (Evar _fe_mul_tll (Tfunction
                                                                  ((tptr (Tstruct _fe noattr)) ::
                                                                   (tptr (Tstruct _fe_loose noattr)) ::
                                                                   (tptr (Tstruct _fe_loose noattr)) ::
                                                                   nil) tvoid
                                                                  cc_default))
                                              ((Eaddrof
                                                 (Evar _z3 (Tstruct _fe noattr))
                                                 (tptr (Tstruct _fe noattr))) ::
                                               (Eaddrof
                                                 (Evar _tmp0l (Tstruct _fe_loose noattr))
                                                 (tptr (Tstruct _fe_loose noattr))) ::
                                               (Eaddrof
                                                 (Evar _x2l (Tstruct _fe_loose noattr))
                                                 (tptr (Tstruct _fe_loose noattr))) ::
                                               nil))
                                            (Ssequence
                                              (Scall None
                                                (Evar _fe_mul_tll (Tfunction
                                                                    ((tptr (Tstruct _fe noattr)) ::
                                                                    (tptr (Tstruct _fe_loose noattr)) ::
                                                                    (tptr (Tstruct _fe_loose noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                ((Eaddrof
                                                   (Evar _z2 (Tstruct _fe noattr))
                                                   (tptr (Tstruct _fe noattr))) ::
                                                 (Eaddrof
                                                   (Evar _z2l (Tstruct _fe_loose noattr))
                                                   (tptr (Tstruct _fe_loose noattr))) ::
                                                 (Eaddrof
                                                   (Evar _tmp1l (Tstruct _fe_loose noattr))
                                                   (tptr (Tstruct _fe_loose noattr))) ::
                                                 nil))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _fe_sq_tl (Tfunction
                                                                    ((tptr (Tstruct _fe noattr)) ::
                                                                    (tptr (Tstruct _fe_loose noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                  ((Eaddrof
                                                     (Evar _tmp0 (Tstruct _fe noattr))
                                                     (tptr (Tstruct _fe noattr))) ::
                                                   (Eaddrof
                                                     (Evar _tmp1l (Tstruct _fe_loose noattr))
                                                     (tptr (Tstruct _fe_loose noattr))) ::
                                                   nil))
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _fe_sq_tl (Tfunction
                                                                    ((tptr (Tstruct _fe noattr)) ::
                                                                    (tptr (Tstruct _fe_loose noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                    ((Eaddrof
                                                       (Evar _tmp1 (Tstruct _fe noattr))
                                                       (tptr (Tstruct _fe noattr))) ::
                                                     (Eaddrof
                                                       (Evar _x2l (Tstruct _fe_loose noattr))
                                                       (tptr (Tstruct _fe_loose noattr))) ::
                                                     nil))
                                                  (Ssequence
                                                    (Scall None
                                                      (Evar _fe_add (Tfunction
                                                                    ((tptr (Tstruct _fe_loose noattr)) ::
                                                                    (tptr (Tstruct _fe noattr)) ::
                                                                    (tptr (Tstruct _fe noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                      ((Eaddrof
                                                         (Evar _x3l (Tstruct _fe_loose noattr))
                                                         (tptr (Tstruct _fe_loose noattr))) ::
                                                       (Eaddrof
                                                         (Evar _z3 (Tstruct _fe noattr))
                                                         (tptr (Tstruct _fe noattr))) ::
                                                       (Eaddrof
                                                         (Evar _z2 (Tstruct _fe noattr))
                                                         (tptr (Tstruct _fe noattr))) ::
                                                       nil))
                                                    (Ssequence
                                                      (Scall None
                                                        (Evar _fe_sub 
                                                        (Tfunction
                                                          ((tptr (Tstruct _fe_loose noattr)) ::
                                                           (tptr (Tstruct _fe noattr)) ::
                                                           (tptr (Tstruct _fe noattr)) ::
                                                           nil) tvoid
                                                          cc_default))
                                                        ((Eaddrof
                                                           (Evar _z2l (Tstruct _fe_loose noattr))
                                                           (tptr (Tstruct _fe_loose noattr))) ::
                                                         (Eaddrof
                                                           (Evar _z3 (Tstruct _fe noattr))
                                                           (tptr (Tstruct _fe noattr))) ::
                                                         (Eaddrof
                                                           (Evar _z2 (Tstruct _fe noattr))
                                                           (tptr (Tstruct _fe noattr))) ::
                                                         nil))
                                                      (Ssequence
                                                        (Scall None
                                                          (Evar _fe_mul_ttt 
                                                          (Tfunction
                                                            ((tptr (Tstruct _fe noattr)) ::
                                                             (tptr (Tstruct _fe noattr)) ::
                                                             (tptr (Tstruct _fe noattr)) ::
                                                             nil) tvoid
                                                            cc_default))
                                                          ((Eaddrof
                                                             (Evar _x2 (Tstruct _fe noattr))
                                                             (tptr (Tstruct _fe noattr))) ::
                                                           (Eaddrof
                                                             (Evar _tmp1 (Tstruct _fe noattr))
                                                             (tptr (Tstruct _fe noattr))) ::
                                                           (Eaddrof
                                                             (Evar _tmp0 (Tstruct _fe noattr))
                                                             (tptr (Tstruct _fe noattr))) ::
                                                           nil))
                                                        (Ssequence
                                                          (Scall None
                                                            (Evar _fe_sub 
                                                            (Tfunction
                                                              ((tptr (Tstruct _fe_loose noattr)) ::
                                                               (tptr (Tstruct _fe noattr)) ::
                                                               (tptr (Tstruct _fe noattr)) ::
                                                               nil) tvoid
                                                              cc_default))
                                                            ((Eaddrof
                                                               (Evar _tmp1l (Tstruct _fe_loose noattr))
                                                               (tptr (Tstruct _fe_loose noattr))) ::
                                                             (Eaddrof
                                                               (Evar _tmp1 (Tstruct _fe noattr))
                                                               (tptr (Tstruct _fe noattr))) ::
                                                             (Eaddrof
                                                               (Evar _tmp0 (Tstruct _fe noattr))
                                                               (tptr (Tstruct _fe noattr))) ::
                                                             nil))
                                                          (Ssequence
                                                            (Scall None
                                                              (Evar _fe_sq_tl 
                                                              (Tfunction
                                                                ((tptr (Tstruct _fe noattr)) ::
                                                                 (tptr (Tstruct _fe_loose noattr)) ::
                                                                 nil) tvoid
                                                                cc_default))
                                                              ((Eaddrof
                                                                 (Evar _z2 (Tstruct _fe noattr))
                                                                 (tptr (Tstruct _fe noattr))) ::
                                                               (Eaddrof
                                                                 (Evar _z2l (Tstruct _fe_loose noattr))
                                                                 (tptr (Tstruct _fe_loose noattr))) ::
                                                               nil))
                                                            (Ssequence
                                                              (Scall None
                                                                (Evar _fe_mul121666 
                                                                (Tfunction
                                                                  ((tptr (Tstruct _fe noattr)) ::
                                                                   (tptr (Tstruct _fe_loose noattr)) ::
                                                                   nil) tvoid
                                                                  cc_default))
                                                                ((Eaddrof
                                                                   (Evar _z3 (Tstruct _fe noattr))
                                                                   (tptr (Tstruct _fe noattr))) ::
                                                                 (Eaddrof
                                                                   (Evar _tmp1l (Tstruct _fe_loose noattr))
                                                                   (tptr (Tstruct _fe_loose noattr))) ::
                                                                 nil))
                                                              (Ssequence
                                                                (Scall None
                                                                  (Evar _fe_sq_tl 
                                                                  (Tfunction
                                                                    ((tptr (Tstruct _fe noattr)) ::
                                                                    (tptr (Tstruct _fe_loose noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Eaddrof
                                                                    (Evar _x3 (Tstruct _fe noattr))
                                                                    (tptr (Tstruct _fe noattr))) ::
                                                                   (Eaddrof
                                                                    (Evar _x3l (Tstruct _fe_loose noattr))
                                                                    (tptr (Tstruct _fe_loose noattr))) ::
                                                                   nil))
                                                                (Ssequence
                                                                  (Scall None
                                                                    (Evar _fe_add 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _fe_loose noattr)) ::
                                                                    (tptr (Tstruct _fe noattr)) ::
                                                                    (tptr (Tstruct _fe noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _tmp0l (Tstruct _fe_loose noattr))
                                                                    (tptr (Tstruct _fe_loose noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _tmp0 (Tstruct _fe noattr))
                                                                    (tptr (Tstruct _fe noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _z3 (Tstruct _fe noattr))
                                                                    (tptr (Tstruct _fe noattr))) ::
                                                                    nil))
                                                                  (Ssequence
                                                                    (Scall None
                                                                    (Evar _fe_mul_ttt 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _fe noattr)) ::
                                                                    (tptr (Tstruct _fe noattr)) ::
                                                                    (tptr (Tstruct _fe noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _z3 (Tstruct _fe noattr))
                                                                    (tptr (Tstruct _fe noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _x1 (Tstruct _fe noattr))
                                                                    (tptr (Tstruct _fe noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _z2 (Tstruct _fe noattr))
                                                                    (tptr (Tstruct _fe noattr))) ::
                                                                    nil))
                                                                    (Scall None
                                                                    (Evar _fe_mul_tll 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _fe noattr)) ::
                                                                    (tptr (Tstruct _fe_loose noattr)) ::
                                                                    (tptr (Tstruct _fe_loose noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _z2 (Tstruct _fe noattr))
                                                                    (tptr (Tstruct _fe noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _tmp1l (Tstruct _fe_loose noattr))
                                                                    (tptr (Tstruct _fe_loose noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _tmp0l (Tstruct _fe_loose noattr))
                                                                    (tptr (Tstruct _fe_loose noattr))) ::
                                                                    nil)))))))))))))))))))))))))
                      (Sset _pos
                        (Ebinop Osub (Etempvar _pos tint)
                          (Econst_int (Int.repr 1) tint) tint))))
                  (Ssequence
                    (Scall None
                      (Evar _fe_cswap (Tfunction
                                        ((tptr (Tstruct _fe noattr)) ::
                                         (tptr (Tstruct _fe noattr)) ::
                                         tuint :: nil) tvoid cc_default))
                      ((Eaddrof (Evar _x2 (Tstruct _fe noattr))
                         (tptr (Tstruct _fe noattr))) ::
                       (Eaddrof (Evar _x3 (Tstruct _fe noattr))
                         (tptr (Tstruct _fe noattr))) ::
                       (Etempvar _swap tuint) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _fe_cswap (Tfunction
                                          ((tptr (Tstruct _fe noattr)) ::
                                           (tptr (Tstruct _fe noattr)) ::
                                           tuint :: nil) tvoid cc_default))
                        ((Eaddrof (Evar _z2 (Tstruct _fe noattr))
                           (tptr (Tstruct _fe noattr))) ::
                         (Eaddrof (Evar _z3 (Tstruct _fe noattr))
                           (tptr (Tstruct _fe noattr))) ::
                         (Etempvar _swap tuint) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _fe_invert (Tfunction
                                             ((tptr (Tstruct _fe noattr)) ::
                                              (tptr (Tstruct _fe noattr)) ::
                                              nil) tvoid cc_default))
                          ((Eaddrof (Evar _z2 (Tstruct _fe noattr))
                             (tptr (Tstruct _fe noattr))) ::
                           (Eaddrof (Evar _z2 (Tstruct _fe noattr))
                             (tptr (Tstruct _fe noattr))) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _fe_mul_ttt (Tfunction
                                                ((tptr (Tstruct _fe noattr)) ::
                                                 (tptr (Tstruct _fe noattr)) ::
                                                 (tptr (Tstruct _fe noattr)) ::
                                                 nil) tvoid cc_default))
                            ((Eaddrof (Evar _x2 (Tstruct _fe noattr))
                               (tptr (Tstruct _fe noattr))) ::
                             (Eaddrof (Evar _x2 (Tstruct _fe noattr))
                               (tptr (Tstruct _fe noattr))) ::
                             (Eaddrof (Evar _z2 (Tstruct _fe noattr))
                               (tptr (Tstruct _fe noattr))) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar _fe_tobytes (Tfunction
                                                  ((tptr tuchar) ::
                                                   (tptr (Tstruct _fe noattr)) ::
                                                   nil) tvoid cc_default))
                              ((Etempvar _out (tptr tuchar)) ::
                               (Eaddrof (Evar _x2 (Tstruct _fe noattr))
                                 (tptr (Tstruct _fe noattr))) :: nil))
                            (Ssequence
                              (Scall None
                                (Evar _memzero_explicit (Tfunction
                                                          ((tptr tvoid) ::
                                                           tulong :: nil)
                                                          tvoid cc_default))
                                ((Eaddrof (Evar _x1 (Tstruct _fe noattr))
                                   (tptr (Tstruct _fe noattr))) ::
                                 (Esizeof (Tstruct _fe noattr) tulong) ::
                                 nil))
                              (Ssequence
                                (Scall None
                                  (Evar _memzero_explicit (Tfunction
                                                            ((tptr tvoid) ::
                                                             tulong :: nil)
                                                            tvoid cc_default))
                                  ((Eaddrof (Evar _x2 (Tstruct _fe noattr))
                                     (tptr (Tstruct _fe noattr))) ::
                                   (Esizeof (Tstruct _fe noattr) tulong) ::
                                   nil))
                                (Ssequence
                                  (Scall None
                                    (Evar _memzero_explicit (Tfunction
                                                              ((tptr tvoid) ::
                                                               tulong :: nil)
                                                              tvoid
                                                              cc_default))
                                    ((Eaddrof (Evar _z2 (Tstruct _fe noattr))
                                       (tptr (Tstruct _fe noattr))) ::
                                     (Esizeof (Tstruct _fe noattr) tulong) ::
                                     nil))
                                  (Ssequence
                                    (Scall None
                                      (Evar _memzero_explicit (Tfunction
                                                                ((tptr tvoid) ::
                                                                 tulong ::
                                                                 nil) tvoid
                                                                cc_default))
                                      ((Eaddrof
                                         (Evar _x3 (Tstruct _fe noattr))
                                         (tptr (Tstruct _fe noattr))) ::
                                       (Esizeof (Tstruct _fe noattr) tulong) ::
                                       nil))
                                    (Ssequence
                                      (Scall None
                                        (Evar _memzero_explicit (Tfunction
                                                                  ((tptr tvoid) ::
                                                                   tulong ::
                                                                   nil) tvoid
                                                                  cc_default))
                                        ((Eaddrof
                                           (Evar _z3 (Tstruct _fe noattr))
                                           (tptr (Tstruct _fe noattr))) ::
                                         (Esizeof (Tstruct _fe noattr) tulong) ::
                                         nil))
                                      (Ssequence
                                        (Scall None
                                          (Evar _memzero_explicit (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                          ((Eaddrof
                                             (Evar _x2l (Tstruct _fe_loose noattr))
                                             (tptr (Tstruct _fe_loose noattr))) ::
                                           (Esizeof (Tstruct _fe_loose noattr) tulong) ::
                                           nil))
                                        (Ssequence
                                          (Scall None
                                            (Evar _memzero_explicit (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                            ((Eaddrof
                                               (Evar _z2l (Tstruct _fe_loose noattr))
                                               (tptr (Tstruct _fe_loose noattr))) ::
                                             (Esizeof (Tstruct _fe_loose noattr) tulong) ::
                                             nil))
                                          (Ssequence
                                            (Scall None
                                              (Evar _memzero_explicit 
                                              (Tfunction
                                                ((tptr tvoid) :: tulong ::
                                                 nil) tvoid cc_default))
                                              ((Eaddrof
                                                 (Evar _x3l (Tstruct _fe_loose noattr))
                                                 (tptr (Tstruct _fe_loose noattr))) ::
                                               (Esizeof (Tstruct _fe_loose noattr) tulong) ::
                                               nil))
                                            (Scall None
                                              (Evar _memzero_explicit 
                                              (Tfunction
                                                ((tptr tvoid) :: tulong ::
                                                 nil) tvoid cc_default))
                                              ((Eaddrof
                                                 (Evar _e (tarray tuchar 32))
                                                 (tptr (tarray tuchar 32))) ::
                                               (Esizeof (tarray tuchar 32) tulong) ::
                                               nil))))))))))))))))))))))))
|}.

Definition composites : list composite_definition :=
(Composite _fe Struct (Member_plain _v (tarray tuint 10) :: nil) noattr ::
 Composite _fe_loose Struct (Member_plain _v (tarray tuint 10) :: nil) noattr ::
 nil).

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
 (_memzero_explicit, Gfun(Internal f_memzero_explicit)) ::
 (_get_unaligned_le32, Gfun(Internal f_get_unaligned_le32)) ::
 (_curve25519_clamp_secret, Gfun(Internal f_curve25519_clamp_secret)) ::
 (_fe_frombytes_impl, Gfun(Internal f_fe_frombytes_impl)) ::
 (_fe_frombytes, Gfun(Internal f_fe_frombytes)) ::
 (_addcarryx_u25, Gfun(Internal f_addcarryx_u25)) ::
 (_addcarryx_u26, Gfun(Internal f_addcarryx_u26)) ::
 (_subborrow_u25, Gfun(Internal f_subborrow_u25)) ::
 (_subborrow_u26, Gfun(Internal f_subborrow_u26)) ::
 (_cmovznz32, Gfun(Internal f_cmovznz32)) ::
 (_fe_freeze, Gfun(Internal f_fe_freeze)) ::
 (_fe_tobytes, Gfun(Internal f_fe_tobytes)) ::
 (_fe_copy, Gfun(Internal f_fe_copy)) ::
 (_fe_copy_lt, Gfun(Internal f_fe_copy_lt)) ::
 (_fe_0, Gfun(Internal f_fe_0)) :: (_fe_1, Gfun(Internal f_fe_1)) ::
 (_fe_add_impl, Gfun(Internal f_fe_add_impl)) ::
 (_fe_add, Gfun(Internal f_fe_add)) ::
 (_fe_sub_impl, Gfun(Internal f_fe_sub_impl)) ::
 (_fe_sub, Gfun(Internal f_fe_sub)) ::
 (_fe_mul_impl, Gfun(Internal f_fe_mul_impl)) ::
 (_fe_mul_ttt, Gfun(Internal f_fe_mul_ttt)) ::
 (_fe_mul_tlt, Gfun(Internal f_fe_mul_tlt)) ::
 (_fe_mul_tll, Gfun(Internal f_fe_mul_tll)) ::
 (_fe_sqr_impl, Gfun(Internal f_fe_sqr_impl)) ::
 (_fe_sq_tl, Gfun(Internal f_fe_sq_tl)) ::
 (_fe_sq_tt, Gfun(Internal f_fe_sq_tt)) ::
 (_fe_loose_invert, Gfun(Internal f_fe_loose_invert)) ::
 (_fe_invert, Gfun(Internal f_fe_invert)) ::
 (_fe_cswap, Gfun(Internal f_fe_cswap)) ::
 (_fe_mul_121666_impl, Gfun(Internal f_fe_mul_121666_impl)) ::
 (_fe_mul121666, Gfun(Internal f_fe_mul121666)) ::
 (_curve25519_generic, Gfun(Internal f_curve25519_generic)) :: nil).

Definition public_idents : list ident :=
(_curve25519_generic :: _memset :: _memcpy :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


