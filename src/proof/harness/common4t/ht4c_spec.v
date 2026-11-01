(* the common.h functions shared by the transport laws
   transport_len, transport_order, transport_keepalive.

   One body proof per function serves the three laws:
   - every common.h function of the three transport harnesses has the SAME Clight as law prim_aead's
     (src/harness/prim_aead/code.v), except rp_final (its static `minusp` is `<law>__minusp`);
   - the composite environment of law prim_aead is included in each transport law's
     (ht4_worlds.ht4_prim_aead_sub_<law>), so the bodies are proved at W_prim_aead;
   - they are proved with the EMPTY varspecs ht4c_V0 (no function here reads a global but rp_final), so that
     asm_lib.asm_body_lift lifts them into every transport law (its V-inclusion is trivial);
   - their Gprog contains only functions present in the three harnesses (ht4c_G1: no draw_ functions, no main,
     no ref_xaead_ ones); draw_size / draw_u64 (transport_len, transport_order only) have their own (ht4c_Gd).
   The specifications are haead_spec3.v's (law prim_aead), verbatim, but polymorphic in the compspecs (section
   HT4CS, prefix ht4_: the bodies use them at W_prim_aead, a main imports them at its world, the assembly relates
   the instances by funspec_sub: byte / u32 arrays only); rp_add .. rp_block mention struct rpoly and stay
   haead_spec3's (at W_prim_aead); rp_final's static minusp is a parameter `mp` (the law's identifier),
   `ht4_minusp mp gv` in place of haead_globals gv.  The NULL-tolerant
   reference AEAD (rp_padded, ref_aead_tag, ref_chacha20_xor, ref_aead_decrypt) is (files ht4r_). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Export WgNoise.proof.harness.prim_aead.haead_spec3.

Local Open Scope Z_scope.

Section HT4CS.
Context {cs: compspecs}.

(* rp_final's static const u32 minusp[17], at the law's identifier mp *)
Definition ht4_minusp (mp: ident) (gv: globals) : mpred :=
  data_at Ers (tarray tuint 17) (map Vint hrp_minusp) (gv mp).

Definition ht4_check_failed_spec :=
  DECLARE HA._check_failed
  WITH u: unit
  PRE [ ] PROP (False) PARAMS () SEP ()
  POST [ tvoid ] PROP () RETURN () SEP ().

(* bytes_eq(a, b, n): 1 iff equal *)
Definition ht4_bytes_eq_spec :=
  DECLARE HA._bytes_eq
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

(* bytes_copy(d, s, n) *)
Definition ht4_bytes_copy_spec :=
  DECLARE HA._bytes_copy
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
Definition ht4_bytes_set_spec :=
  DECLARE HA._bytes_set
  WITH sh: share, d: val, v: Z, n: Z
  PRE [ tptr tuchar, tuchar, tulong ]
    PROP (writable_share sh; 0 <= v <= Byte.max_unsigned; 0 <= n <= Int64.max_unsigned)
    PARAMS (d; Vint (Int.repr v); Vlong (Int64.repr n))
    SEP (data_at_ sh (tarray tuchar n) d)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh (tarray tuchar n) (Zrepeat (Vubyte (Byte.repr v)) n) d).

(* draw_size(): any size (N_MAX = SIZE_MAX) *)
Definition ht4_draw_size_spec :=
  DECLARE HA._draw_size
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX n: Z,
    PROP (0 <= n <= Int64.max_unsigned) RETURN (Vlong (Int64.repr n)) SEP ().

(* draw_u64(): any 64-bit value *)
Definition ht4_draw_u64_spec :=
  DECLARE HA._draw_u64
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX n: Z,
    PROP (0 <= n <= Int64.max_unsigned) RETURN (Vlong (Int64.repr n)) SEP ().

(* le32_store(p + i, v): the 4 little-endian bytes of v at offset i of the buffer (contents any values) *)
Definition ht4_le32_store_spec :=
  DECLARE HA._le32_store
  WITH sh: share, p: val, i: Z, contents: list val, v: int
  PRE [ tptr tuchar, tuint ]
    PROP (writable_share sh; 0 <= i; i + 4 <= Zlength contents)
    PARAMS (offset_val i p; Vint v)
    SEP (data_at sh (tarray tuchar (Zlength contents)) contents p)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh (tarray tuchar (Zlength contents)) (haead_splice i (le32_bytes v) contents) p).

(* le32_load(p + i): the little-endian word at byte offset i of bs *)
Definition ht4_le32_load_spec :=
  DECLARE HA._le32_load
  WITH sh: share, p: val, i: Z, bs: list byte
  PRE [ tptr tuchar ]
    PROP (readable_share sh; 0 <= i; i + 4 <= Zlength bs)
    PARAMS (offset_val i p)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p)
  POST [ tuint ]
    PROP () RETURN (Vint (le32_at bs i))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p).

(* le64_store(p + i, v): the 8 little-endian bytes of v at offset i *)
Definition ht4_le64_store_spec :=
  DECLARE HA._le64_store
  WITH sh: share, p: val, i: Z, contents: list val, v: Z
  PRE [ tptr tuchar, tulong ]
    PROP (writable_share sh; 0 <= i; i + 8 <= Zlength contents; 0 <= v <= Int64.max_unsigned)
    PARAMS (offset_val i p; Vlong (Int64.repr v))
    SEP (data_at sh (tarray tuchar (Zlength contents)) contents p)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh (tarray tuchar (Zlength contents)) (haead_splice i (le64_bytes v) contents) p).

(* le64_load(p + i): the little-endian 64-bit value at byte offset i of bs *)
Definition ht4_le64_load_spec :=
  DECLARE HA._le64_load
  WITH sh: share, p: val, i: Z, bs: list byte
  PRE [ tptr tuchar ]
    PROP (readable_share sh; 0 <= i; i + 8 <= Zlength bs)
    PARAMS (offset_val i p)
    SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (le_Z (sublist i (i + 8) bs))))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p).

(* ---------------------------------------------------------------------- *)
(* common.h: the reference ChaCha20                                        *)
(* ---------------------------------------------------------------------- *)

(* rc_rotl(x, n), 0 < n < 32 *)
Definition ht4_rc_rotl_spec :=
  DECLARE HA._rc_rotl
  WITH x: int, n: Z
  PRE [ tuint, tuint ]
    PROP (0 < n < 32) PARAMS (Vint x; Vint (Int.repr n)) SEP ()
  POST [ tuint ]
    PROP () RETURN (Vint (Int.rol x (Int.repr n))) SEP ().

(* rc_qr(x, a, b, c, d) = the model's quarter round *)
Definition ht4_rc_qr_spec :=
  DECLARE HA._rc_qr
  WITH sh: share, xp: val, x: list int, a: Z, b: Z, c: Z, d: Z
  PRE [ tptr tuint, tint, tint, tint, tint ]
    PROP (writable_share sh; Zlength x = 16; 0 <= a < 16; 0 <= b < 16; 0 <= c < 16; 0 <= d < 16)
    PARAMS (xp; Vint (Int.repr a); Vint (Int.repr b); Vint (Int.repr c); Vint (Int.repr d))
    SEP (data_at sh (tarray tuint 16) (map Vint x) xp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh (tarray tuint 16) (map Vint (chacha_qround x a b c d)) xp).

(* rc_rounds(x): the 10 double rounds *)
Definition ht4_rc_rounds_spec :=
  DECLARE HA._rc_rounds
  WITH sh: share, xp: val, x: list int
  PRE [ tptr tuint ]
    PROP (writable_share sh; Zlength x = 16)
    PARAMS (xp)
    SEP (data_at sh (tarray tuint 16) (map Vint x) xp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh (tarray tuint 16) (map Vint (chacha_rounds 10 x)) xp).

(* rc_setup(s, key, w12, w13, w14, w15) *)
Definition ht4_rc_setup_spec :=
  DECLARE HA._rc_setup
  WITH sh: share, sp: val, ksh: share, kp: val, key: list byte, w12: int, w13: int, w14: int, w15: int
  PRE [ tptr tuint, tptr tuchar, tuint, tuint, tuint, tuint ]
    PROP (writable_share sh; readable_share ksh; Zlength key = 32)
    PARAMS (sp; kp; Vint w12; Vint w13; Vint w14; Vint w15)
    SEP (data_at_ sh (tarray tuint 16) sp; data_at ksh (tarray tuchar 32) (map Vubyte key) kp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh (tarray tuint 16) (map Vint (chacha_consts ++ le32_words 8 key ++ [w12; w13; w14; w15])) sp;
         data_at ksh (tarray tuchar 32) (map Vubyte key) kp).

(* ref_chacha20_block(out, key, ctr, n): block ctr of the keystream of (key, n) *)
Definition ht4_ref_chacha20_block_spec :=
  DECLARE HA._ref_chacha20_block
  WITH osh: share, out: val, ksh: share, kp: val, key: list byte, ctr: int, n: Z
  PRE [ tptr tuchar, tptr tuchar, tuint, tulong ]
    PROP (writable_share osh; readable_share ksh; Zlength key = 32; 0 <= n <= Int64.max_unsigned)
    PARAMS (out; kp; Vint ctr; Vlong (Int64.repr n))
    SEP (data_at_ osh (tarray tuchar 64) out; data_at ksh (tarray tuchar 32) (map Vubyte key) kp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at osh (tarray tuchar 64)
           (map Vubyte (chacha_block_bytes 10 (chacha_advance (aead_st key n) (Int.unsigned ctr)))) out;
         data_at ksh (tarray tuchar 32) (map Vubyte key) kp).

End HT4CS.

#[local] Existing Instance W_prim_aead.

(* the varspecs of the shared body proofs: none *)
Definition ht4c_V0 : varspecs := [].

(* the varspecs of rp_final's body proof *)
Definition ht4c_Vmp (mp: ident) : varspecs := [(mp, tarray tuint 17)].

(* rp_final(p, out): haead_spec3.rp_final_spec with the minusp of identifier mp *)
Definition rp_final_spec_of (mp: ident) :=
  DECLARE HA._rp_final
  WITH sh: share, p: val, r: list int, h: list int, s: list byte, osh: share, out: val, gv: globals
  PRE [ tptr t_rpoly, tptr tuchar ]
    PROP (writable_share sh; writable_share osh; Zlength r = 17; Zlength h = 17)
    PARAMS (p; out) GLOBALS (gv)
    SEP (data_at sh t_rpoly (rpoly_val r h s) p; data_at_ osh (tarray tuchar 16) out; ht4_minusp mp gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_rpoly (rpoly_val r (hrp_final_h h s) s) p;
         data_at osh (tarray tuchar 16) (map Vubyte (hrp_final_out h s)) out;
         ht4_minusp mp gv).

(* the shared functions but rp_final (and the four ht4r_ ones, and the draw_ ones), at W_prim_aead *)
Definition ht4c_G1 : funspecs :=
  [ht4_check_failed_spec; ht4_bytes_eq_spec; ht4_bytes_copy_spec; ht4_bytes_set_spec;
   ht4_le32_store_spec; ht4_le32_load_spec; ht4_le64_store_spec;
   ht4_rc_rotl_spec; ht4_rc_qr_spec; ht4_rc_rounds_spec; ht4_rc_setup_spec; ht4_ref_chacha20_block_spec;
   rp_add_spec; rp_init_spec; rp_mul_spec; rp_block_spec].

(* the shared Gprog of the common.h bodies *)
Definition ht4c_G0 (mp: ident) : funspecs := ht4c_G1 ++ [rp_final_spec_of mp].

(* the Gprog of draw_size / draw_u64: the nondet functions they call *)
Definition ht4c_Gd : funspecs := [nondet_u32_spec; nondet_size_spec].
