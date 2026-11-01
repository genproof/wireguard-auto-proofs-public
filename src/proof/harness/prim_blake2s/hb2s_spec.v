(* the harness piece of law prim_blake2s (harness/prim_blake2s.c + the common.h functions it reaches):
   the unit, the specifications of the harness's functions and the body-proof context.

   - Everything is in the world compspecs W_prim_blake2s (wg3_worlds.v): the harness unit's compspecs is
     included in it (cspecs_sub), and the assembly needs it.
   - The varspecs of the unit are those of the WHOLE program (hb2s_V, a literal list): main's precondition
     (main_pre of whole_prog) describes every global of the program, among them blake2s_sigma of the
     blake2s unit, which blake2s_update/final need (blake2s_globals).
   - The BLAKE2s functions main calls are imported with the interface specs of b2s_spec3.v (Blake2s.CS):
     main converts its local `struct blake2s_ctx ctx` between W_prim_blake2s and Blake2s.CS.
   - The reference ref_blake2s (common.h) computes model.v's `blake2s` (sublist 0 keylen key). *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Export WgNoise.proof.blake2s.b2s_spec3.
Require WgNoise.contracts.x_prim_blake2s.
Require WgNoise.harness.x_prim_blake2s.code.

#[local] Existing Instance W_prim_blake2s.
Local Open Scope Z_scope.

Module HB.
  Definition _check_failed := WgNoise.harness.x_prim_blake2s.code._check_failed.
  Definition _bytes_eq := WgNoise.harness.x_prim_blake2s.code._bytes_eq.
  Definition _bytes_zero := WgNoise.harness.x_prim_blake2s.code._bytes_zero.
  Definition _bytes_copy := WgNoise.harness.x_prim_blake2s.code._bytes_copy.
  Definition _bytes_set := WgNoise.harness.x_prim_blake2s.code._bytes_set.
  Definition _draw_size := WgNoise.harness.x_prim_blake2s.code._draw_size.
  Definition _le32_load := WgNoise.harness.x_prim_blake2s.code._le32_load.
  Definition _RB2S_IV := WgNoise.harness.x_prim_blake2s.code._RB2S_IV.
  Definition _RB2S_SIGMA := WgNoise.harness.x_prim_blake2s.code._RB2S_SIGMA.
  Definition _rb2s_rotr := WgNoise.harness.x_prim_blake2s.code._rb2s_rotr.
  Definition _rb2s_g := WgNoise.harness.x_prim_blake2s.code._rb2s_g.
  Definition _rb2s_compress := WgNoise.harness.x_prim_blake2s.code._rb2s_compress.
  Definition _ref_blake2s := WgNoise.harness.x_prim_blake2s.code._ref_blake2s.
  Definition _main := WgNoise.harness.x_prim_blake2s.code._main.
End HB.

(* the varspecs of the whole program (literal) *)
Definition hb2s_V : varspecs :=
  ltac:(let x := eval vm_compute in (QPvarspecs WgNoise.contracts.x_prim_blake2s.whole_prog) in exact x).

(* the harness unit, in the world compspecs, with the whole program's varspecs *)
Definition u_hb2s : unit_ctx := mk_unit W_prim_blake2s hb2s_V WgNoise.harness.x_prim_blake2s.code.prog.

(* main: the precondition is fixed (main_pre of the whole program), the postcondition anything *)
Definition hb2s_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition hb2s_main_spec : ident * funspec :=
  (HB._main, QPmain_spec_ext' WgNoise.contracts.x_prim_blake2s.whole_prog tt hb2s_post).

(* ---------------------------------------------------------------------- *)
(* common.h: checks and small helpers                                      *)
(* ---------------------------------------------------------------------- *)

(* check_failed() dereferences NULL: never callable *)
Definition check_failed_spec :=
  DECLARE HB._check_failed
  WITH u: unit
  PRE [ ] PROP (False) PARAMS () SEP ()
  POST [ tvoid ] PROP () RETURN () SEP ().

(* bytes_eq(a, b, n): 1 iff equal *)
Definition bytes_eq_spec :=
  DECLARE HB._bytes_eq
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
  DECLARE HB._bytes_zero
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
  DECLARE HB._bytes_copy
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

(* bytes_set(d, v, n) *)
Definition bytes_set_spec :=
  DECLARE HB._bytes_set
  WITH sh: share, d: val, v: Z, n: Z
  PRE [ tptr tuchar, tuchar, tulong ]
    PROP (writable_share sh; 0 <= v <= Byte.max_unsigned; 0 <= n <= Int64.max_unsigned)
    PARAMS (d; Vint (Int.repr v); Vlong (Int64.repr n))
    SEP (data_at_ sh (tarray tuchar n) d)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh (tarray tuchar n) (Zrepeat (Vubyte (Byte.repr v)) n) d).

(* draw_size(): any size (N_MAX = SIZE_MAX) *)
Definition draw_size_spec :=
  DECLARE HB._draw_size
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX n: Z,
    PROP (0 <= n <= Int64.max_unsigned) RETURN (Vlong (Int64.repr n)) SEP ().

(* le32_load(p + i): the little-endian word at byte offset i of bs *)
Definition le32_load_spec :=
  DECLARE HB._le32_load
  WITH sh: share, p: val, i: Z, bs: list byte
  PRE [ tptr tuchar ]
    PROP (readable_share sh; 0 <= i; i + 4 <= Zlength bs)
    PARAMS (offset_val i p)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p)
  POST [ tuint ]
    PROP () RETURN (Vint (le32_at bs i))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p).

(* ---------------------------------------------------------------------- *)
(* common.h: the reference BLAKE2s                                         *)
(* ---------------------------------------------------------------------- *)

(* the two constant tables of the reference (static const, readonly share Ers) *)
Definition hb2s_globals (gv: globals) : mpred :=
  sepcon (data_at Ers (tarray tuint 8) (map Vint b2s_IV) (gv HB._RB2S_IV))
         (data_at Ers (tarray (tarray tuchar 16) 10) blake2s_sigma_val (gv HB._RB2S_SIGMA)).

(* rb2s_rotr(x, n), 0 < n < 32 *)
Definition rb2s_rotr_spec :=
  DECLARE HB._rb2s_rotr
  WITH x: int, n: Z
  PRE [ tuint, tuint ]
    PROP (0 < n < 32) PARAMS (Vint x; Vint (Int.repr n)) SEP ()
  POST [ tuint ]
    PROP () RETURN (Vint (Int.ror x (Int.repr n))) SEP ().

(* rb2s_g(v, a, b, c, d, x, y) = model.v's b2s_G *)
Definition rb2s_g_spec :=
  DECLARE HB._rb2s_g
  WITH sh: share, vp: val, vl: list int, a: Z, b: Z, c: Z, d: Z, x: int, y: int
  PRE [ tptr tuint, tint, tint, tint, tint, tuint, tuint ]
    PROP (writable_share sh; Zlength vl = 16; 0 <= a < 16; 0 <= b < 16; 0 <= c < 16; 0 <= d < 16)
    PARAMS (vp; Vint (Int.repr a); Vint (Int.repr b); Vint (Int.repr c); Vint (Int.repr d); Vint x; Vint y)
    SEP (data_at sh (tarray tuint 16) (map Vint vl) vp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh (tarray tuint 16) (map Vint (b2s_G vl a b c d x y)) vp).

(* rb2s_compress(h, block, t, last): h := model.v's compression of block with counter t, final flag iff
   last <> 0 *)
Definition rb2s_compress_spec :=
  DECLARE HB._rb2s_compress
  WITH shh: share, hp: val, hl: list int, shb: share, bp: val, blk: list byte, t: Z, last: Z, gv: globals
  PRE [ tptr tuint, tptr tuchar, tulong, tint ]
    PROP (writable_share shh; readable_share shb; Zlength hl = 8; Zlength blk = 64;
          0 <= t <= Int64.max_unsigned; Int.min_signed <= last <= Int.max_signed)
    PARAMS (hp; bp; Vlong (Int64.repr t); Vint (Int.repr last)) GLOBALS (gv)
    SEP (data_at shh (tarray tuint 8) (map Vint hl) hp;
         data_at shb (tarray tuchar 64) (map Vubyte blk) bp;
         hb2s_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at shh (tarray tuint 8)
           (map Vint (b2s_compress_block hl blk t (if Z.eq_dec last 0 then Int.zero else Int.mone))) hp;
         data_at shb (tarray tuchar 64) (map Vubyte blk) bp;
         hb2s_globals gv).

(* ref_blake2s(out, outlen, key, keylen, in, inlen): out = BLAKE2s-outlen(key[0..keylen), in[0..inlen));
   the key buffer kbuf may be longer than keylen (main passes its 32-byte array) *)
Definition ref_blake2s_spec :=
  DECLARE HB._ref_blake2s
  WITH osh: share, out: val, outlen: Z, ksh: share, k: val, kbuf: list byte, keylen: Z,
       dsh: share, d: val, data: list byte, gv: globals
  PRE [ tptr tuchar, tulong, tptr tuchar, tulong, tptr tuchar, tulong ]
    PROP (writable_share osh; readable_share ksh; readable_share dsh;
          1 <= outlen <= 32; 0 <= keylen <= 32; keylen <= Zlength kbuf <= Int64.max_unsigned;
          Zlength data <= Int64.max_signed)
    PARAMS (out; Vlong (Int64.repr outlen); k; Vlong (Int64.repr keylen); d; Vlong (Int64.repr (Zlength data)))
    GLOBALS (gv)
    SEP (data_at_ osh (tarray tuchar outlen) out;
         data_at ksh (tarray tuchar (Zlength kbuf)) (map Vubyte kbuf) k;
         data_at dsh (tarray tuchar (Zlength data)) (map Vubyte data) d;
         hb2s_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at osh (tarray tuchar outlen) (map Vubyte (blake2s (sublist 0 keylen kbuf) outlen data)) out;
         data_at ksh (tarray tuchar (Zlength kbuf)) (map Vubyte kbuf) k;
         data_at dsh (tarray tuchar (Zlength data)) (map Vubyte data) d;
         hb2s_globals gv).

(* ---------------------------------------------------------------------- *)
(* The piece                                                               *)
(* ---------------------------------------------------------------------- *)

(* imports: the external world (at W_prim_blake2s) and the BLAKE2s API main calls (b2s_spec3.v) *)
Definition hb2s_imports (cs: compspecs) : funspecs :=
  @asm_env.env_specs W_prim_blake2s ++
  [blake2s_init_spec; blake2s_init_key_spec; blake2s_update_spec3; blake2s_final_spec; blake2s_spec3].

Definition hb2s_G : funspecs :=
  [check_failed_spec; bytes_eq_spec; bytes_zero_spec; bytes_copy_spec; bytes_set_spec; draw_size_spec;
   le32_load_spec; rb2s_rotr_spec; rb2s_g_spec; rb2s_compress_spec; ref_blake2s_spec; hb2s_main_spec].

(* the context of every body proof of the harness piece *)
Definition hb2s_Gprog : funspecs := hb2s_imports W_prim_blake2s ++ hb2s_G.
