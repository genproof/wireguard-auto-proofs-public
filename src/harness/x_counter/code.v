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
  Definition source_file := "harness/x_counter.c".
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
Definition ___gp_spinlock_t : ident := $"__gp_spinlock_t".
Definition _a : ident := $"a".
Definition _acc : ident := $"acc".
Definition _backtrack : ident := $"backtrack".
Definition _c : ident := $"c".
Definition _check_failed : ident := $"check_failed".
Definition _counter : ident := $"counter".
Definition _draw_steps : ident := $"draw_steps".
Definition _draw_u64 : ident := $"draw_u64".
Definition _hi : ident := $"hi".
Definition _i : ident := $"i".
Definition _in : ident := $"in".
Definition _l : ident := $"l".
Definition _lock : ident := $"lock".
Definition _main : ident := $"main".
Definition _n : ident := $"n".
Definition _next : ident := $"next".
Definition _noise_replay_counter : ident := $"noise_replay_counter".
Definition _nondet_size : ident := $"nondet_size".
Definition _nondet_u32 : ident := $"nondet_u32".
Definition _nondet_u8 : ident := $"nondet_u8".
Definition _ok : ident := $"ok".
Definition _p : ident := $"p".
Definition _quickproof_free : ident := $"quickproof_free".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _r : ident := $"r".
Definition _set : ident := $"set".
Definition _steps : ident := $"steps".
Definition _top : ident := $"top".
Definition _unused : ident := $"unused".
Definition _wg_counter_validate : ident := $"wg_counter_validate".
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

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_c, (Tstruct _noise_replay_counter noattr)) ::
              (_set, (tptr (Tstruct _acc noattr))) :: nil);
  fn_temps := ((_a, (tptr (Tstruct _acc noattr))) ::
               (_l, (tptr (tptr (Tstruct _acc noattr)))) :: (_top, tulong) ::
               (_n, tulong) :: (_steps, tulong) :: (_i, tulong) ::
               (_in, tint) :: (_ok, tint) :: (_r, tbool) ::
               (_t'12, (tptr tvoid)) :: (_t'11, tint) :: (_t'10, tint) ::
               (_t'9, tint) :: (_t'8, tbool) :: (_t'7, tulong) ::
               (_t'6, tuint) :: (_t'5, tuint) :: (_t'4, tuint) ::
               (_t'3, tuint) :: (_t'2, tuchar) :: (_t'1, tulong) ::
               (_t'23, tulong) :: (_t'22, (tptr (Tstruct _acc noattr))) ::
               (_t'21, tulong) :: (_t'20, (tptr (Tstruct _acc noattr))) ::
               (_t'19, (tptr (Tstruct _acc noattr))) ::
               (_t'18, (tptr (Tstruct _acc noattr))) :: (_t'17, tulong) ::
               (_t'16, (tptr (Tstruct _acc noattr))) ::
               (_t'15, (tptr (Tstruct _acc noattr))) ::
               (_t'14, (tptr (Tstruct _acc noattr))) ::
               (_t'13, (tptr (Tstruct _acc noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sassign (Evar _set (tptr (Tstruct _acc noattr)))
      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Ssequence
      (Sset _top (Ecast (Econst_int (Int.repr 0) tint) tulong))
      (Ssequence
        (Sassign
          (Efield (Evar _c (Tstruct _noise_replay_counter noattr)) _counter
            tulong) (Econst_int (Int.repr 0) tint))
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
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Evar _c (Tstruct _noise_replay_counter noattr))
                        _backtrack (tarray tulong 128)) (Etempvar _i tulong)
                      (tptr tulong)) tulong) (Econst_int (Int.repr 0) tint)))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tulong)
                  (Econst_int (Int.repr 1) tint) tulong))))
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
                          (Evar _nondet_u8 (Tfunction nil tuchar cc_default))
                          nil)
                        (Sswitch (Ebinop Omod (Etempvar _t'2 tuchar)
                                   (Econst_int (Int.repr 5) tint) tint)
                          (LScons (Some 0)
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'3)
                                  (Evar _nondet_u32 (Tfunction nil tuint
                                                      cc_default)) nil)
                                (Sset _n
                                  (Ebinop Osub
                                    (Ebinop Oadd (Etempvar _top tulong)
                                      (Ecast
                                        (Ebinop Omod (Etempvar _t'3 tuint)
                                          (Econst_int (Int.repr 200) tint)
                                          tuint) tulong) tulong)
                                    (Econst_int (Int.repr 100) tint) tulong)))
                              Sbreak)
                            (LScons (Some 1)
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'4)
                                    (Evar _nondet_u32 (Tfunction nil tuint
                                                        cc_default)) nil)
                                  (Sset _n
                                    (Ebinop Osub (Etempvar _top tulong)
                                      (Ecast
                                        (Ebinop Omod (Etempvar _t'4 tuint)
                                          (Econst_int (Int.repr 9000) tint)
                                          tuint) tulong) tulong)))
                                Sbreak)
                              (LScons (Some 4)
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'5)
                                      (Evar _nondet_u32 (Tfunction nil tuint
                                                          cc_default)) nil)
                                    (Sset _n
                                      (Ebinop Osub
                                        (Ebinop Oadd
                                          (Ebinop Osub
                                            (Ebinop Osub
                                              (Etempvar _top tulong)
                                              (Econst_long (Int64.repr 8128) tulong)
                                              tulong)
                                            (Econst_int (Int.repr 1) tint)
                                            tulong)
                                          (Ecast
                                            (Ebinop Omod
                                              (Etempvar _t'5 tuint)
                                              (Econst_int (Int.repr 5) tint)
                                              tuint) tulong) tulong)
                                        (Econst_int (Int.repr 2) tint)
                                        tulong)))
                                  Sbreak)
                                (LScons (Some 2)
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'6)
                                        (Evar _nondet_u32 (Tfunction nil
                                                            tuint cc_default))
                                        nil)
                                      (Sset _n
                                        (Ebinop Osub
                                          (Ebinop Oadd
                                            (Ebinop Osub
                                              (Ebinop Osub
                                                (Econst_long (Int64.repr (-1)) tulong)
                                                (Econst_long (Int64.repr 8128) tulong)
                                                tulong)
                                              (Econst_int (Int.repr 1) tint)
                                              tulong)
                                            (Ecast
                                              (Ebinop Omod
                                                (Etempvar _t'6 tuint)
                                                (Econst_int (Int.repr 8) tint)
                                                tuint) tulong) tulong)
                                          (Econst_int (Int.repr 4) tint)
                                          tulong)))
                                    Sbreak)
                                  (LScons None
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'7)
                                          (Evar _draw_u64 (Tfunction nil
                                                            tulong
                                                            cc_default)) nil)
                                        (Sset _n (Etempvar _t'7 tulong)))
                                      Sbreak)
                                    LSnil)))))))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'8)
                            (Evar _wg_counter_validate (Tfunction
                                                         ((tptr (Tstruct _noise_replay_counter noattr)) ::
                                                          tulong :: nil)
                                                         tbool cc_default))
                            ((Eaddrof
                               (Evar _c (Tstruct _noise_replay_counter noattr))
                               (tptr (Tstruct _noise_replay_counter noattr))) ::
                             (Etempvar _n tulong) :: nil))
                          (Sset _r (Ecast (Etempvar _t'8 tbool) tbool)))
                        (Ssequence
                          (Sset _in (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Ssequence
                              (Sset _a
                                (Evar _set (tptr (Tstruct _acc noattr))))
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Etempvar _a (tptr (Tstruct _acc noattr)))
                                    Sskip
                                    Sbreak)
                                  (Ssequence
                                    (Sset _t'23
                                      (Efield
                                        (Ederef
                                          (Etempvar _a (tptr (Tstruct _acc noattr)))
                                          (Tstruct _acc noattr)) _n tulong))
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _t'23 tulong)
                                                   (Etempvar _n tulong) tint)
                                      (Sset _in
                                        (Econst_int (Int.repr 1) tint))
                                      Sskip)))
                                (Sset _a
                                  (Efield
                                    (Ederef
                                      (Etempvar _a (tptr (Tstruct _acc noattr)))
                                      (Tstruct _acc noattr)) _next
                                    (tptr (Tstruct _acc noattr))))))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _top tulong)
                                                   (Ebinop Oadd
                                                     (Ebinop Osub
                                                       (Ebinop Osub
                                                         (Econst_long (Int64.repr (-1)) tulong)
                                                         (Econst_long (Int64.repr 8128) tulong)
                                                         tulong)
                                                       (Econst_int (Int.repr 1) tint)
                                                       tulong)
                                                     (Econst_int (Int.repr 1) tint)
                                                     tulong) tint)
                                      (Sset _t'9
                                        (Ecast
                                          (Ebinop Olt (Etempvar _n tulong)
                                            (Ebinop Osub
                                              (Ebinop Osub
                                                (Econst_long (Int64.repr (-1)) tulong)
                                                (Econst_long (Int64.repr 8128) tulong)
                                                tulong)
                                              (Econst_int (Int.repr 1) tint)
                                              tulong) tint) tbool))
                                      (Sset _t'9
                                        (Econst_int (Int.repr 0) tint)))
                                    (Sifthenelse (Etempvar _t'9 tint)
                                      (Sset _t'10
                                        (Ecast
                                          (Ebinop Oge
                                            (Ebinop Oadd
                                              (Ebinop Oadd
                                                (Etempvar _n tulong)
                                                (Econst_int (Int.repr 1) tint)
                                                tulong)
                                              (Econst_long (Int64.repr 8128) tulong)
                                              tulong) (Etempvar _top tulong)
                                            tint) tbool))
                                      (Sset _t'10
                                        (Econst_int (Int.repr 0) tint))))
                                  (Sifthenelse (Etempvar _t'10 tint)
                                    (Sset _t'11
                                      (Ecast
                                        (Eunop Onotbool (Etempvar _in tint)
                                          tint) tbool))
                                    (Sset _t'11
                                      (Econst_int (Int.repr 0) tint))))
                                (Sset _ok (Etempvar _t'11 tint)))
                              (Ssequence
                                (Sloop
                                  (Sifthenelse (Eunop Onotbool
                                                 (Ebinop Oeq
                                                   (Etempvar _r tbool)
                                                   (Etempvar _ok tint) tint)
                                                 tint)
                                    (Scall None
                                      (Evar _check_failed (Tfunction nil
                                                            tvoid cc_default))
                                      nil)
                                    Sskip)
                                  Sbreak)
                                (Ssequence
                                  (Sifthenelse (Etempvar _ok tint)
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'12)
                                          (Evar _quickproof_malloc (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                          ((Esizeof (Tstruct _acc noattr) tulong) ::
                                           nil))
                                        (Sset _a
                                          (Etempvar _t'12 (tptr tvoid))))
                                      (Ssequence
                                        (Sifthenelse (Ebinop Oeq
                                                       (Etempvar _a (tptr (Tstruct _acc noattr)))
                                                       (Ecast
                                                         (Econst_int (Int.repr 0) tint)
                                                         (tptr tvoid)) tint)
                                          Sbreak
                                          Sskip)
                                        (Ssequence
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _a (tptr (Tstruct _acc noattr)))
                                                (Tstruct _acc noattr)) _n
                                              tulong) (Etempvar _n tulong))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'22
                                                (Evar _set (tptr (Tstruct _acc noattr))))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _a (tptr (Tstruct _acc noattr)))
                                                    (Tstruct _acc noattr))
                                                  _next
                                                  (tptr (Tstruct _acc noattr)))
                                                (Etempvar _t'22 (tptr (Tstruct _acc noattr)))))
                                            (Ssequence
                                              (Sassign
                                                (Evar _set (tptr (Tstruct _acc noattr)))
                                                (Etempvar _a (tptr (Tstruct _acc noattr))))
                                              (Sifthenelse (Ebinop Ogt
                                                             (Ebinop Oadd
                                                               (Etempvar _n tulong)
                                                               (Econst_int (Int.repr 1) tint)
                                                               tulong)
                                                             (Etempvar _top tulong)
                                                             tint)
                                                (Sset _top
                                                  (Ebinop Oadd
                                                    (Etempvar _n tulong)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tulong))
                                                Sskip))))))
                                    Sskip)
                                  (Ssequence
                                    (Sloop
                                      (Ssequence
                                        (Sset _t'21
                                          (Efield
                                            (Evar _c (Tstruct _noise_replay_counter noattr))
                                            _counter tulong))
                                        (Sifthenelse (Eunop Onotbool
                                                       (Ebinop Oeq
                                                         (Etempvar _t'21 tulong)
                                                         (Etempvar _top tulong)
                                                         tint) tint)
                                          (Scall None
                                            (Evar _check_failed (Tfunction
                                                                  nil tvoid
                                                                  cc_default))
                                            nil)
                                          Sskip))
                                      Sbreak)
                                    (Ssequence
                                      (Sset _l
                                        (Eaddrof
                                          (Evar _set (tptr (Tstruct _acc noattr)))
                                          (tptr (tptr (Tstruct _acc noattr)))))
                                      (Sloop
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'20
                                              (Ederef
                                                (Etempvar _l (tptr (tptr (Tstruct _acc noattr))))
                                                (tptr (Tstruct _acc noattr))))
                                            (Sifthenelse (Etempvar _t'20 (tptr (Tstruct _acc noattr)))
                                              Sskip
                                              Sbreak))
                                          (Ssequence
                                            (Sset _t'16
                                              (Ederef
                                                (Etempvar _l (tptr (tptr (Tstruct _acc noattr))))
                                                (tptr (Tstruct _acc noattr))))
                                            (Ssequence
                                              (Sset _t'17
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _t'16 (tptr (Tstruct _acc noattr)))
                                                    (Tstruct _acc noattr)) _n
                                                  tulong))
                                              (Sifthenelse (Ebinop Olt
                                                             (Ebinop Oadd
                                                               (Ebinop Oadd
                                                                 (Etempvar _t'17 tulong)
                                                                 (Econst_int (Int.repr 1) tint)
                                                                 tulong)
                                                               (Econst_long (Int64.repr 8128) tulong)
                                                               tulong)
                                                             (Etempvar _top tulong)
                                                             tint)
                                                (Ssequence
                                                  (Sset _a
                                                    (Ederef
                                                      (Etempvar _l (tptr (tptr (Tstruct _acc noattr))))
                                                      (tptr (Tstruct _acc noattr))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'19
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _a (tptr (Tstruct _acc noattr)))
                                                            (Tstruct _acc noattr))
                                                          _next
                                                          (tptr (Tstruct _acc noattr))))
                                                      (Sassign
                                                        (Ederef
                                                          (Etempvar _l (tptr (tptr (Tstruct _acc noattr))))
                                                          (tptr (Tstruct _acc noattr)))
                                                        (Etempvar _t'19 (tptr (Tstruct _acc noattr)))))
                                                    (Scall None
                                                      (Evar _quickproof_free 
                                                      (Tfunction
                                                        ((tptr tvoid) :: nil)
                                                        tvoid cc_default))
                                                      ((Etempvar _a (tptr (Tstruct _acc noattr))) ::
                                                       nil))))
                                                (Ssequence
                                                  (Sset _t'18
                                                    (Ederef
                                                      (Etempvar _l (tptr (tptr (Tstruct _acc noattr))))
                                                      (tptr (Tstruct _acc noattr))))
                                                  (Sset _l
                                                    (Eaddrof
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _t'18 (tptr (Tstruct _acc noattr)))
                                                          (Tstruct _acc noattr))
                                                        _next
                                                        (tptr (Tstruct _acc noattr)))
                                                      (tptr (tptr (Tstruct _acc noattr))))))))))
                                        Sskip)))))))))))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tulong)
                      (Econst_int (Int.repr 1) tint) tulong))))
              (Ssequence
                (Sloop
                  (Ssequence
                    (Ssequence
                      (Sset _t'15 (Evar _set (tptr (Tstruct _acc noattr))))
                      (Sifthenelse (Etempvar _t'15 (tptr (Tstruct _acc noattr)))
                        Sskip
                        Sbreak))
                    (Ssequence
                      (Ssequence
                        (Sset _t'14 (Evar _set (tptr (Tstruct _acc noattr))))
                        (Sset _a
                          (Efield
                            (Ederef
                              (Etempvar _t'14 (tptr (Tstruct _acc noattr)))
                              (Tstruct _acc noattr)) _next
                            (tptr (Tstruct _acc noattr)))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'13
                            (Evar _set (tptr (Tstruct _acc noattr))))
                          (Scall None
                            (Evar _quickproof_free (Tfunction
                                                     ((tptr tvoid) :: nil)
                                                     tvoid cc_default))
                            ((Etempvar _t'13 (tptr (Tstruct _acc noattr))) ::
                             nil)))
                        (Sassign (Evar _set (tptr (Tstruct _acc noattr)))
                          (Etempvar _a (tptr (Tstruct _acc noattr)))))))
                  Sskip)
                (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite ___gp_spinlock_t Struct (Member_plain _unused tint :: nil) noattr ::
 Composite _noise_replay_counter Struct
   (Member_plain _counter tulong ::
    Member_plain _lock (Tstruct ___gp_spinlock_t noattr) ::
    Member_plain _backtrack (tarray tulong 128) :: nil)
   noattr ::
 Composite _acc Struct
   (Member_plain _n tulong ::
    Member_plain _next (tptr (Tstruct _acc noattr)) :: nil)
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
 (_quickproof_malloc,
   Gfun(External (EF_external "quickproof_malloc"
                   (mksignature (AST.Xlong :: nil) AST.Xptr cc_default))
     (tulong :: nil) (tptr tvoid) cc_default)) ::
 (_quickproof_free,
   Gfun(External (EF_external "quickproof_free"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (_check_failed, Gfun(Internal f_check_failed)) ::
 (_draw_steps, Gfun(Internal f_draw_steps)) ::
 (_draw_u64, Gfun(Internal f_draw_u64)) ::
 (_wg_counter_validate,
   Gfun(External (EF_external "wg_counter_validate"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xbool
                     cc_default))
     ((tptr (Tstruct _noise_replay_counter noattr)) :: tulong :: nil) tbool
     cc_default)) :: (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _wg_counter_validate :: _quickproof_free :: _quickproof_malloc ::
 _nondet_size :: _nondet_u32 :: _nondet_u8 :: ___builtin_debug ::
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


