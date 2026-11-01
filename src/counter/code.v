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
  Definition source_file := "patch/counter_validate.c".
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
Definition _addr : ident := $"addr".
Definition _backtrack : ident := $"backtrack".
Definition _counter : ident := $"counter".
Definition _counter_validate : ident := $"counter_validate".
Definition _i : ident := $"i".
Definition _index : ident := $"index".
Definition _index_current : ident := $"index_current".
Definition _lock : ident := $"lock".
Definition _main : ident := $"main".
Definition _mask : ident := $"mask".
Definition _n : ident := $"n".
Definition _noise_replay_counter : ident := $"noise_replay_counter".
Definition _nr : ident := $"nr".
Definition _old : ident := $"old".
Definition _p : ident := $"p".
Definition _quickproof_ilog2 : ident := $"quickproof_ilog2".
Definition _r : ident := $"r".
Definition _ret : ident := $"ret".
Definition _test_and_set_bit : ident := $"test_and_set_bit".
Definition _their_counter : ident := $"their_counter".
Definition _top : ident := $"top".
Definition _unused : ident := $"unused".
Definition _wg_counter_validate : ident := $"wg_counter_validate".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition f_quickproof_ilog2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_r, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _r (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Swhile
      (Ebinop Ogt (Etempvar _n tulong) (Econst_int (Int.repr 1) tint) tint)
      (Ssequence
        (Sset _n
          (Ebinop Odiv (Etempvar _n tulong) (Econst_int (Int.repr 2) tint)
            tulong))
        (Sset _r
          (Ebinop Oadd (Etempvar _r tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Sreturn (Some (Etempvar _r tint)))))
|}.

Definition f_test_and_set_bit := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_nr, tulong) :: (_addr, (tptr tulong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_mask, tulong) :: (_p, (tptr tulong)) :: (_old, tulong) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _mask
    (Ebinop Oshl (Econst_long (Int64.repr 1) tulong)
      (Ebinop Omod (Etempvar _nr tulong) (Econst_int (Int.repr 64) tint)
        tulong) tulong))
  (Ssequence
    (Sset _p
      (Ebinop Oadd (Etempvar _addr (tptr tulong))
        (Ebinop Odiv (Etempvar _nr tulong) (Econst_int (Int.repr 64) tint)
          tulong) (tptr tulong)))
    (Ssequence
      (Sset _old (Ederef (Etempvar _p (tptr tulong)) tulong))
      (Ssequence
        (Sassign (Ederef (Etempvar _p (tptr tulong)) tulong)
          (Ebinop Oor (Etempvar _old tulong) (Etempvar _mask tulong) tulong))
        (Sreturn (Some (Ebinop One
                         (Ebinop Oand (Etempvar _old tulong)
                           (Etempvar _mask tulong) tulong)
                         (Econst_int (Int.repr 0) tint) tint)))))))
|}.

Definition f_counter_validate := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_counter, (tptr (Tstruct _noise_replay_counter noattr))) ::
                (_their_counter, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_index, tulong) :: (_index_current, tulong) ::
               (_top, tulong) :: (_i, tulong) :: (_ret, tbool) ::
               (_t'5, tint) :: (_t'4, tulong) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: (_t'9, tulong) ::
               (_t'8, tulong) :: (_t'7, tulong) :: (_t'6, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _ret (Ecast (Econst_int (Int.repr 0) tint) tbool))
  (Ssequence
    (Sloop
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'9
              (Efield
                (Ederef
                  (Etempvar _counter (tptr (Tstruct _noise_replay_counter noattr)))
                  (Tstruct _noise_replay_counter noattr)) _counter tulong))
            (Sifthenelse (Ebinop Oge (Etempvar _t'9 tulong)
                           (Ebinop Oadd (Econst_int (Int.repr (-8130)) tint)
                             (Econst_int (Int.repr 1) tint) tint) tint)
              (Sset _t'1 (Econst_int (Int.repr 1) tint))
              (Sset _t'1
                (Ecast
                  (Ebinop Oge (Etempvar _their_counter tulong)
                    (Econst_int (Int.repr (-8130)) tint) tint) tbool))))
          (Sifthenelse (Etempvar _t'1 tint) Sbreak Sskip))
        (Ssequence
          (Sset _their_counter
            (Ebinop Oadd (Etempvar _their_counter tulong)
              (Econst_int (Int.repr 1) tint) tulong))
          (Ssequence
            (Ssequence
              (Sset _t'8
                (Efield
                  (Ederef
                    (Etempvar _counter (tptr (Tstruct _noise_replay_counter noattr)))
                    (Tstruct _noise_replay_counter noattr)) _counter tulong))
              (Sifthenelse (Ebinop Olt
                             (Ebinop Oadd (Econst_int (Int.repr 8128) tint)
                               (Etempvar _their_counter tulong) tulong)
                             (Etempvar _t'8 tulong) tint)
                Sbreak
                Sskip))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _quickproof_ilog2 (Tfunction (tulong :: nil) tint
                                            cc_default))
                  ((Econst_int (Int.repr 64) tint) :: nil))
                (Sset _index
                  (Ebinop Oshr (Etempvar _their_counter tulong)
                    (Etempvar _t'2 tint) tulong)))
              (Ssequence
                (Ssequence
                  (Sset _t'6
                    (Efield
                      (Ederef
                        (Etempvar _counter (tptr (Tstruct _noise_replay_counter noattr)))
                        (Tstruct _noise_replay_counter noattr)) _counter
                      tulong))
                  (Sifthenelse (Ebinop Ogt (Etempvar _their_counter tulong)
                                 (Etempvar _t'6 tulong) tint)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'3)
                          (Evar _quickproof_ilog2 (Tfunction (tulong :: nil)
                                                    tint cc_default))
                          ((Econst_int (Int.repr 64) tint) :: nil))
                        (Ssequence
                          (Sset _t'7
                            (Efield
                              (Ederef
                                (Etempvar _counter (tptr (Tstruct _noise_replay_counter noattr)))
                                (Tstruct _noise_replay_counter noattr))
                              _counter tulong))
                          (Sset _index_current
                            (Ebinop Oshr (Etempvar _t'7 tulong)
                              (Etempvar _t'3 tint) tulong))))
                      (Ssequence
                        (Ssequence
                          (Sifthenelse (Ebinop Olt
                                         (Ecast
                                           (Ebinop Osub
                                             (Etempvar _index tulong)
                                             (Etempvar _index_current tulong)
                                             tulong) tulong)
                                         (Ecast
                                           (Ebinop Odiv
                                             (Econst_int (Int.repr 8192) tint)
                                             (Econst_int (Int.repr 64) tint)
                                             tint) tulong) tint)
                            (Sset _t'4
                              (Ecast
                                (Ecast
                                  (Ebinop Osub (Etempvar _index tulong)
                                    (Etempvar _index_current tulong) tulong)
                                  tulong) tulong))
                            (Sset _t'4
                              (Ecast
                                (Ecast
                                  (Ebinop Odiv
                                    (Econst_int (Int.repr 8192) tint)
                                    (Econst_int (Int.repr 64) tint) tint)
                                  tulong) tulong)))
                          (Sset _top (Etempvar _t'4 tulong)))
                        (Ssequence
                          (Ssequence
                            (Sset _i
                              (Ecast (Econst_int (Int.repr 1) tint) tulong))
                            (Sloop
                              (Ssequence
                                (Sifthenelse (Ebinop Ole (Etempvar _i tulong)
                                               (Etempvar _top tulong) tint)
                                  Sskip
                                  Sbreak)
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _counter (tptr (Tstruct _noise_replay_counter noattr)))
                                          (Tstruct _noise_replay_counter noattr))
                                        _backtrack (tarray tulong 128))
                                      (Ebinop Oand
                                        (Ebinop Oadd (Etempvar _i tulong)
                                          (Etempvar _index_current tulong)
                                          tulong)
                                        (Ebinop Osub
                                          (Ebinop Odiv
                                            (Econst_int (Int.repr 8192) tint)
                                            (Econst_int (Int.repr 64) tint)
                                            tint)
                                          (Econst_int (Int.repr 1) tint)
                                          tint) tulong) (tptr tulong))
                                    tulong) (Econst_int (Int.repr 0) tint)))
                              (Sset _i
                                (Ebinop Oadd (Etempvar _i tulong)
                                  (Econst_int (Int.repr 1) tint) tulong))))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _counter (tptr (Tstruct _noise_replay_counter noattr)))
                                (Tstruct _noise_replay_counter noattr))
                              _counter tulong)
                            (Etempvar _their_counter tulong)))))
                    Sskip))
                (Ssequence
                  (Sset _index
                    (Ebinop Oand (Etempvar _index tulong)
                      (Ebinop Osub
                        (Ebinop Odiv (Econst_int (Int.repr 8192) tint)
                          (Econst_int (Int.repr 64) tint) tint)
                        (Econst_int (Int.repr 1) tint) tint) tulong))
                  (Ssequence
                    (Scall (Some _t'5)
                      (Evar _test_and_set_bit (Tfunction
                                                (tulong :: (tptr tulong) ::
                                                 nil) tint cc_default))
                      ((Ebinop Oand (Etempvar _their_counter tulong)
                         (Ebinop Osub (Econst_int (Int.repr 64) tint)
                           (Econst_int (Int.repr 1) tint) tint) tulong) ::
                       (Ebinop Oadd
                         (Efield
                           (Ederef
                             (Etempvar _counter (tptr (Tstruct _noise_replay_counter noattr)))
                             (Tstruct _noise_replay_counter noattr))
                           _backtrack (tarray tulong 128))
                         (Etempvar _index tulong) (tptr tulong)) :: nil))
                    (Sset _ret
                      (Ecast (Eunop Onotbool (Etempvar _t'5 tint) tint)
                        tbool)))))))))
      Sbreak)
    (Sreturn (Some (Etempvar _ret tbool)))))
|}.

Definition f_wg_counter_validate := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_counter, (tptr (Tstruct _noise_replay_counter noattr))) ::
                (_their_counter, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _counter_validate (Tfunction
                              ((tptr (Tstruct _noise_replay_counter noattr)) ::
                               tulong :: nil) tbool cc_default))
    ((Etempvar _counter (tptr (Tstruct _noise_replay_counter noattr))) ::
     (Etempvar _their_counter tulong) :: nil))
  (Sreturn (Some (Etempvar _t'1 tbool))))
|}.

Definition composites : list composite_definition :=
(Composite ___gp_spinlock_t Struct (Member_plain _unused tint :: nil) noattr ::
 Composite _noise_replay_counter Struct
   (Member_plain _counter tulong ::
    Member_plain _lock (Tstruct ___gp_spinlock_t noattr) ::
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
 (_quickproof_ilog2, Gfun(Internal f_quickproof_ilog2)) ::
 (_test_and_set_bit, Gfun(Internal f_test_and_set_bit)) ::
 (_counter_validate, Gfun(Internal f_counter_validate)) ::
 (_wg_counter_validate, Gfun(Internal f_wg_counter_validate)) :: nil).

Definition public_idents : list ident :=
(_wg_counter_validate :: ___builtin_debug :: ___builtin_write32_reversed ::
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


