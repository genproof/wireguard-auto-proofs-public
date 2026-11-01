(* the harness piece of law prim_poly1305 (harness/prim_poly1305.c + the common.h functions it reaches):
   the unit, the specifications of the harness's functions and the body-proof context.

   - Everything is in the world compspecs W_prim_poly1305 (wg3_worlds.v): the harness unit's compspecs is
     included in it (cspecs_sub), and the assembly needs it.
   - The varspecs of the unit are those of the WHOLE program (hp1305_V, a literal list): main's precondition
     (main_pre of whole_prog) describes every global of the program.
   - The Poly1305 functions main calls are imported with the specifications of the AEAD piece (aead_spec3.v,
     at Poly1305.CS: poly1305_init_spec, poly1305_update_spec3, poly1305_final_spec): main converts its
     local `struct poly1305_desc_ctx d` between W_prim_poly1305 and Poly1305.CS.
   - The TweetNaCl reference rp_* (common.h) is specified over the plain-Coq model of
     src/proof/harness/hrp1305_math3.v (shared with law prim_aead); ref_poly1305 computes aead_model.v's
     poly1305_tag. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Export WgNoise.proof.aead.aead_spec3.
Require Export WgNoise.proof.harness.hrp1305_math3.
Require WgNoise.contracts.x_prim_poly1305.
Require WgNoise.harness.x_prim_poly1305.code.

#[local] Existing Instance W_prim_poly1305.
Local Open Scope Z_scope.

Module HP.
  Definition _check_failed := WgNoise.harness.x_prim_poly1305.code._check_failed.
  Definition _bytes_eq := WgNoise.harness.x_prim_poly1305.code._bytes_eq.
  Definition _bytes_zero := WgNoise.harness.x_prim_poly1305.code._bytes_zero.
  Definition _bytes_copy := WgNoise.harness.x_prim_poly1305.code._bytes_copy.
  Definition _draw_size := WgNoise.harness.x_prim_poly1305.code._draw_size.
  Definition _rpoly := WgNoise.harness.x_prim_poly1305.code._rpoly.
  Definition _rp_add := WgNoise.harness.x_prim_poly1305.code._rp_add.
  Definition _rp_init := WgNoise.harness.x_prim_poly1305.code._rp_init.
  Definition _rp_mul := WgNoise.harness.x_prim_poly1305.code._rp_mul.
  Definition _rp_block := WgNoise.harness.x_prim_poly1305.code._rp_block.
  Definition _minusp := WgNoise.harness.x_prim_poly1305.code._x_prim_poly1305__minusp.
  Definition _rp_final := WgNoise.harness.x_prim_poly1305.code._rp_final.
  Definition _ref_poly1305 := WgNoise.harness.x_prim_poly1305.code._ref_poly1305.
  Definition _main := WgNoise.harness.x_prim_poly1305.code._main.
End HP.

(* the varspecs of the whole program (literal) *)
Definition hp1305_V : varspecs :=
  ltac:(let x := eval vm_compute in (QPvarspecs WgNoise.contracts.x_prim_poly1305.whole_prog) in exact x).

(* the harness unit, in the world compspecs, with the whole program's varspecs *)
Definition u_hp1305 : unit_ctx := mk_unit W_prim_poly1305 hp1305_V WgNoise.harness.x_prim_poly1305.code.prog.

(* main: the precondition is fixed (main_pre of the whole program), the postcondition anything *)
Definition hp1305_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition hp1305_main_spec : ident * funspec :=
  (HP._main, QPmain_spec_ext' WgNoise.contracts.x_prim_poly1305.whole_prog tt hp1305_post).

(* ---------------------------------------------------------------------- *)
(* common.h: checks and small helpers                                      *)
(* ---------------------------------------------------------------------- *)

(* check_failed() dereferences NULL: never callable *)
Definition check_failed_spec :=
  DECLARE HP._check_failed
  WITH u: unit
  PRE [ ] PROP (False) PARAMS () SEP ()
  POST [ tvoid ] PROP () RETURN () SEP ().

(* bytes_eq(a, b, n): 1 iff equal *)
Definition bytes_eq_spec :=
  DECLARE HP._bytes_eq
  WITH sha: share, a: val, la: list byte, shb: share, b: val, lb: list byte
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (readable_share sha; readable_share shb; Zlength la = Zlength lb; Zlength la <= Int64.max_unsigned)
    PARAMS (a; b; Vlong (Int64.repr (Zlength la)))
    SEP (data_at sha (tarray tuchar (Zlength la)) (map Vubyte la) a;
         data_at shb (tarray tuchar (Zlength lb)) (map Vubyte lb) b)
  POST [ tint ]
    PROP () RETURN (Vint (if list_eq_dec Byte.eq_dec la lb then Int.one else Int.zero))
    SEP (data_at sha (tarray tuchar (Zlength la)) (map Vubyte la) a;
         data_at shb (tarray tuchar (Zlength lb)) (map Vubyte lb) b).

(* bytes_zero(a, n): 1 iff all zero *)
Definition bytes_zero_spec :=
  DECLARE HP._bytes_zero
  WITH sh: share, a: val, l: list byte
  PRE [ tptr tuchar, tulong ]
    PROP (readable_share sh; Zlength l <= Int64.max_unsigned)
    PARAMS (a; Vlong (Int64.repr (Zlength l)))
    SEP (data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) a)
  POST [ tint ]
    PROP ()
    RETURN (Vint (if list_eq_dec Byte.eq_dec l (Zrepeat Byte.zero (Zlength l)) then Int.one else Int.zero))
    SEP (data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) a).

(* bytes_copy(d, s, n) *)
Definition bytes_copy_spec :=
  DECLARE HP._bytes_copy
  WITH dsh: share, d: val, ssh: share, s: val, bs: list byte
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (writable_share dsh; readable_share ssh; Zlength bs <= Int64.max_unsigned)
    PARAMS (d; s; Vlong (Int64.repr (Zlength bs)))
    SEP (data_at_ dsh (tarray tuchar (Zlength bs)) d;
         data_at ssh (tarray tuchar (Zlength bs)) (map Vubyte bs) s)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at dsh (tarray tuchar (Zlength bs)) (map Vubyte bs) d;
         data_at ssh (tarray tuchar (Zlength bs)) (map Vubyte bs) s).

(* draw_size(): any size (N_MAX = SIZE_MAX) *)
Definition draw_size_spec :=
  DECLARE HP._draw_size
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX n: Z,
    PROP (0 <= n <= Int64.max_unsigned) RETURN (Vlong (Int64.repr n)) SEP ().

(* ---------------------------------------------------------------------- *)
(* common.h: the reference Poly1305 (TweetNaCl, 17 limbs of 8 bits)        *)
(* ---------------------------------------------------------------------- *)

Definition t_rpoly : type := Tstruct HP._rpoly noattr.

(* struct rpoly { u32 r[17]; u32 h[17]; u8 s[16]; } *)
Definition rpoly_val (r h: list int) (s: list byte) : reptype t_rpoly := (map Vint r, (map Vint h, map Vubyte s)).

(* rp_final's static const u32 minusp[17] (readonly global) *)
Definition hp1305_globals (gv: globals) : mpred :=
  data_at Ers (tarray tuint 17) (map Vint hrp_minusp) (gv HP._minusp).

(* rp_add(h, c): hrp_add (h and c distinct arrays) *)
Definition rp_add_spec :=
  DECLARE HP._rp_add
  WITH hsh: share, hp: val, h: list int, csh: share, cp: val, c: list int
  PRE [ tptr tuint, tptr tuint ]
    PROP (writable_share hsh; readable_share csh; Zlength h = 17; Zlength c = 17)
    PARAMS (hp; cp)
    SEP (data_at hsh (tarray tuint 17) (map Vint h) hp; data_at csh (tarray tuint 17) (map Vint c) cp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at hsh (tarray tuint 17) (map Vint (hrp_add h c)) hp;
         data_at csh (tarray tuint 17) (map Vint c) cp).

(* rp_init(p, key): the key buffer kbuf has at least 32 bytes (prim_aead passes a 64-byte block) *)
Definition rp_init_spec :=
  DECLARE HP._rp_init
  WITH sh: share, p: val, ksh: share, k: val, kbuf: list byte
  PRE [ tptr t_rpoly, tptr tuchar ]
    PROP (writable_share sh; readable_share ksh; 32 <= Zlength kbuf)
    PARAMS (p; k)
    SEP (data_at_ sh t_rpoly p; data_at ksh (tarray tuchar (Zlength kbuf)) (map Vubyte kbuf) k)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_rpoly (rpoly_val (hrp_init_r kbuf) hrp_zero17 (hrp_init_s kbuf)) p;
         data_at ksh (tarray tuchar (Zlength kbuf)) (map Vubyte kbuf) k).

(* rp_mul(p, c): h := hrp_mul r h c *)
Definition rp_mul_spec :=
  DECLARE HP._rp_mul
  WITH sh: share, p: val, r: list int, h: list int, s: list byte, csh: share, cp: val, c: list int
  PRE [ tptr t_rpoly, tptr tuint ]
    PROP (writable_share sh; readable_share csh; Zlength r = 17; Zlength h = 17; Zlength c = 17)
    PARAMS (p; cp)
    SEP (data_at sh t_rpoly (rpoly_val r h s) p; data_at csh (tarray tuint 17) (map Vint c) cp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_rpoly (rpoly_val r (hrp_mul r h c) s) p;
         data_at csh (tarray tuint 17) (map Vint c) cp).

(* rp_block(p, m) with m = bs + i: the 16 bytes bs[i..i+16) *)
Definition rp_block_spec :=
  DECLARE HP._rp_block
  WITH sh: share, p: val, r: list int, h: list int, s: list byte, msh: share, mp: val, bs: list byte, i: Z
  PRE [ tptr t_rpoly, tptr tuchar ]
    PROP (writable_share sh; readable_share msh; Zlength r = 17; Zlength h = 17; 0 <= i; i + 16 <= Zlength bs)
    PARAMS (p; offset_val i mp)
    SEP (data_at sh t_rpoly (rpoly_val r h s) p; data_at msh (tarray tuchar (Zlength bs)) (map Vubyte bs) mp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_rpoly (rpoly_val r (hrp_block r h (sublist i (i + 16) bs)) s) p;
         data_at msh (tarray tuchar (Zlength bs)) (map Vubyte bs) mp).

(* rp_final(p, out) *)
Definition rp_final_spec :=
  DECLARE HP._rp_final
  WITH sh: share, p: val, r: list int, h: list int, s: list byte, osh: share, out: val, gv: globals
  PRE [ tptr t_rpoly, tptr tuchar ]
    PROP (writable_share sh; writable_share osh; Zlength r = 17; Zlength h = 17)
    PARAMS (p; out) GLOBALS (gv)
    SEP (data_at sh t_rpoly (rpoly_val r h s) p; data_at_ osh (tarray tuchar 16) out; hp1305_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_rpoly (rpoly_val r (hrp_final_h h s) s) p;
         data_at osh (tarray tuchar 16) (map Vubyte (hrp_final_out h s)) out;
         hp1305_globals gv).

(* ref_poly1305(out, key, m, len): out = the Poly1305 tag of m[0..len) under key *)
Definition ref_poly1305_spec :=
  DECLARE HP._ref_poly1305
  WITH osh: share, out: val, ksh: share, k: val, key: list byte, msh: share, m: val, msg: list byte,
       gv: globals
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tulong ]
    PROP (writable_share osh; readable_share ksh; readable_share msh; Zlength key = 32;
          Zlength msg <= Int64.max_unsigned)
    PARAMS (out; k; m; Vlong (Int64.repr (Zlength msg))) GLOBALS (gv)
    SEP (data_at_ osh (tarray tuchar 16) out;
         data_at ksh (tarray tuchar 32) (map Vubyte key) k;
         data_at msh (tarray tuchar (Zlength msg)) (map Vubyte msg) m;
         hp1305_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at osh (tarray tuchar 16) (map Vubyte (poly1305_tag key msg)) out;
         data_at ksh (tarray tuchar 32) (map Vubyte key) k;
         data_at msh (tarray tuchar (Zlength msg)) (map Vubyte msg) m;
         hp1305_globals gv).

(* ---------------------------------------------------------------------- *)
(* The piece                                                               *)
(* ---------------------------------------------------------------------- *)

(* imports: the external world (at W_prim_poly1305; nondet_u8 and nondet_u32 are not used) and the Poly1305 API
   main calls (aead_spec3.v) *)
Definition hp1305_imports (cs: compspecs) : funspecs :=
  [(_quickproof_malloc, @malloc_spec' W_prim_poly1305); (_quickproof_free, @free_spec' W_prim_poly1305);
   nondet_size_spec; asm_env.nondet_bytes_spec] ++
  [poly1305_init_spec; poly1305_update_spec3; poly1305_final_spec].

Definition hp1305_G : funspecs :=
  [check_failed_spec; bytes_eq_spec; bytes_zero_spec; bytes_copy_spec; draw_size_spec;
   rp_add_spec; rp_init_spec; rp_mul_spec; rp_block_spec; rp_final_spec; ref_poly1305_spec;
   hp1305_main_spec].

(* the context of every body proof of the harness piece *)
Definition hp1305_Gprog : funspecs := hp1305_imports W_prim_poly1305 ++ hp1305_G.
