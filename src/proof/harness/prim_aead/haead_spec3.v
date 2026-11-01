(* the harness piece of law prim_aead (harness/prim_aead.c, prim_aead.h + the common.h functions it
   reaches): the unit, the specifications of the harness's functions and the body-proof context.

   - Everything is in the world compspecs W_prim_aead (wg3_worlds.v).  The varspecs of the unit are those of
     the WHOLE program (haead_V): main_pre describes every global, among them quickproof_zero_page (read by
     the kernel AEAD: zero_page gv) and the harness's static `minusp` of rp_final (haead_globals gv).
   - The kernel AEAD entry points are imported as clones at W_prim_aead of aead_spec3.v's
     chacha20poly1305_encrypt_spec3 .. xchacha20poly1305_decrypt_spec3 (same text: only byte arrays; the
     assembly relates them by funspec_sub).
   - The references are specified against aead_model.v (the model of the kernel's specs): ref_aead_* =
     aead_enc / aead_dec, ref_xaead_* = xaead_enc / xaead_dec; the TweetNaCl Poly1305 rp_* by the
     transliterations of hrp1305_math3.v (shared with law prim_poly1305).
   - Byte buffers are exact arrays `data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p` (also when
     empty: main's buffers come from malloc).  Functions that take a pointer INTO a buffer (le32_load,
     le64_load, le32_store, le64_store, rp_block) take `offset_val i p` and the whole buffer. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Export WgNoise.proof.harness.prim_aead.haead_defs3.
Require WgNoise.contracts.x_prim_aead.
Require WgNoise.harness.x_prim_aead.code.

#[local] Existing Instance W_prim_aead.
Local Open Scope Z_scope.

Module HA.
  Definition _check_failed := WgNoise.harness.x_prim_aead.code._check_failed.
  Definition _bytes_eq := WgNoise.harness.x_prim_aead.code._bytes_eq.
  Definition _bytes_copy := WgNoise.harness.x_prim_aead.code._bytes_copy.
  Definition _bytes_set := WgNoise.harness.x_prim_aead.code._bytes_set.
  Definition _draw_size := WgNoise.harness.x_prim_aead.code._draw_size.
  Definition _draw_u64 := WgNoise.harness.x_prim_aead.code._draw_u64.
  Definition _le32_store := WgNoise.harness.x_prim_aead.code._le32_store.
  Definition _le32_load := WgNoise.harness.x_prim_aead.code._le32_load.
  Definition _le64_store := WgNoise.harness.x_prim_aead.code._le64_store.
  Definition _le64_load := WgNoise.harness.x_prim_aead.code._le64_load.
  Definition _rc_rotl := WgNoise.harness.x_prim_aead.code._rc_rotl.
  Definition _rc_qr := WgNoise.harness.x_prim_aead.code._rc_qr.
  Definition _rc_rounds := WgNoise.harness.x_prim_aead.code._rc_rounds.
  Definition _rc_setup := WgNoise.harness.x_prim_aead.code._rc_setup.
  Definition _ref_chacha20_block := WgNoise.harness.x_prim_aead.code._ref_chacha20_block.
  Definition _ref_hchacha20 := WgNoise.harness.x_prim_aead.code._ref_hchacha20.
  Definition _rpoly := WgNoise.harness.x_prim_aead.code._rpoly.
  Definition _minusp := WgNoise.harness.x_prim_aead.code._x_prim_aead__minusp.
  Definition _rp_add := WgNoise.harness.x_prim_aead.code._rp_add.
  Definition _rp_init := WgNoise.harness.x_prim_aead.code._rp_init.
  Definition _rp_mul := WgNoise.harness.x_prim_aead.code._rp_mul.
  Definition _rp_block := WgNoise.harness.x_prim_aead.code._rp_block.
  Definition _rp_padded := WgNoise.harness.x_prim_aead.code._rp_padded.
  Definition _rp_final := WgNoise.harness.x_prim_aead.code._rp_final.
  Definition _ref_aead_tag := WgNoise.harness.x_prim_aead.code._ref_aead_tag.
  Definition _ref_chacha20_xor := WgNoise.harness.x_prim_aead.code._ref_chacha20_xor.
  Definition _ref_aead_encrypt := WgNoise.harness.x_prim_aead.code._ref_aead_encrypt.
  Definition _ref_aead_decrypt := WgNoise.harness.x_prim_aead.code._ref_aead_decrypt.
  Definition _ref_xaead_encrypt := WgNoise.harness.x_prim_aead.code._ref_xaead_encrypt.
  Definition _ref_xaead_decrypt := WgNoise.harness.x_prim_aead.code._ref_xaead_decrypt.
  Definition _check_decrypt_any := WgNoise.harness.x_prim_aead.code._check_decrypt_any.
  Definition _main := WgNoise.harness.x_prim_aead.code._main.
End HA.

(* the varspecs of the whole program (literal) *)
Definition haead_V : varspecs :=
  ltac:(let x := eval vm_compute in (QPvarspecs WgNoise.contracts.x_prim_aead.whole_prog) in exact x).

(* the harness unit, in the world compspecs, with the whole program's varspecs *)
Definition u_haead : unit_ctx := mk_unit W_prim_aead haead_V WgNoise.harness.x_prim_aead.code.prog.

(* main: the precondition is fixed (main_pre of the whole program), the postcondition anything *)
Definition haead_post : (ident -> val) -> environ -> mpred := fun _ _ => TT.

Definition haead_main_spec : ident * funspec :=
  (HA._main, QPmain_spec_ext' WgNoise.contracts.x_prim_aead.whole_prog tt haead_post).

(* ---------------------------------------------------------------------- *)
(* common.h: checks and small helpers                                      *)
(* ---------------------------------------------------------------------- *)

(* check_failed() dereferences NULL: never callable *)
Definition check_failed_spec :=
  DECLARE HA._check_failed
  WITH u: unit
  PRE [ ] PROP (False) PARAMS () SEP ()
  POST [ tvoid ] PROP () RETURN () SEP ().

(* bytes_eq(a, b, n): 1 iff equal *)
Definition bytes_eq_spec :=
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
Definition bytes_copy_spec :=
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
Definition bytes_set_spec :=
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
Definition draw_size_spec :=
  DECLARE HA._draw_size
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX n: Z,
    PROP (0 <= n <= Int64.max_unsigned) RETURN (Vlong (Int64.repr n)) SEP ().

(* draw_u64(): any 64-bit value *)
Definition draw_u64_spec :=
  DECLARE HA._draw_u64
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tulong ] EX n: Z,
    PROP (0 <= n <= Int64.max_unsigned) RETURN (Vlong (Int64.repr n)) SEP ().

(* le32_store(p + i, v): the 4 little-endian bytes of v at offset i of the buffer (contents any values) *)
Definition le32_store_spec :=
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
Definition le32_load_spec :=
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
Definition le64_store_spec :=
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
Definition le64_load_spec :=
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
Definition rc_rotl_spec :=
  DECLARE HA._rc_rotl
  WITH x: int, n: Z
  PRE [ tuint, tuint ]
    PROP (0 < n < 32) PARAMS (Vint x; Vint (Int.repr n)) SEP ()
  POST [ tuint ]
    PROP () RETURN (Vint (Int.rol x (Int.repr n))) SEP ().

(* rc_qr(x, a, b, c, d) = the model's quarter round *)
Definition rc_qr_spec :=
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
Definition rc_rounds_spec :=
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
Definition rc_setup_spec :=
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
Definition ref_chacha20_block_spec :=
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

(* ref_hchacha20(out, key, nonce16): HChaCha20 of the key and the first 16 bytes of the nonce buffer *)
Definition ref_hchacha20_spec :=
  DECLARE HA._ref_hchacha20
  WITH osh: share, out: val, ksh: share, kp: val, key: list byte, nsh: share, np: val, nb: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share osh; readable_share ksh; readable_share nsh; Zlength key = 32;
          16 <= Zlength nb <= Int64.max_unsigned)
    PARAMS (out; kp; np)
    SEP (data_at_ osh (tarray tuchar 32) out; data_at ksh (tarray tuchar 32) (map Vubyte key) kp;
         data_at nsh (tarray tuchar (Zlength nb)) (map Vubyte nb) np)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at osh (tarray tuchar 32)
           (map Vubyte (words_bytes (hchacha_words 10 (chacha_init_st (le32_words 8 key) (sublist 0 16 nb))))) out;
         data_at ksh (tarray tuchar 32) (map Vubyte key) kp;
         data_at nsh (tarray tuchar (Zlength nb)) (map Vubyte nb) np).

(* ---------------------------------------------------------------------- *)
(* common.h: the reference Poly1305 (TweetNaCl, struct rpoly)              *)
(* ---------------------------------------------------------------------- *)

Definition t_rpoly : type := Tstruct HA._rpoly noattr.

(* struct rpoly { u32 r[17]; u32 h[17]; u8 s[16]; } *)
Definition rpoly_val (r h: list int) (s: list byte) : reptype t_rpoly :=
  (map Vint r, (map Vint h, map Vubyte s)).

(* rp_final's static const u32 minusp[17] *)
Definition haead_globals (gv: globals) : mpred :=
  data_at Ers (tarray tuint 17) (map Vint hrp_minusp) (gv HA._minusp).

(* rp_add(h, c): hrp_add (h and c distinct arrays) *)
Definition rp_add_spec :=
  DECLARE HA._rp_add
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
  DECLARE HA._rp_init
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
  DECLARE HA._rp_mul
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
  DECLARE HA._rp_block
  WITH sh: share, p: val, r: list int, h: list int, s: list byte, msh: share, mp: val, bs: list byte, i: Z
  PRE [ tptr t_rpoly, tptr tuchar ]
    PROP (writable_share sh; readable_share msh; Zlength r = 17; Zlength h = 17; 0 <= i; i + 16 <= Zlength bs)
    PARAMS (p; offset_val i mp)
    SEP (data_at sh t_rpoly (rpoly_val r h s) p; data_at msh (tarray tuchar (Zlength bs)) (map Vubyte bs) mp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_rpoly (rpoly_val r (hrp_block r h (sublist i (i + 16) bs)) s) p;
         data_at msh (tarray tuchar (Zlength bs)) (map Vubyte bs) mp).

(* rp_padded(p, in, len) *)
Definition rp_padded_spec :=
  DECLARE HA._rp_padded
  WITH sh: share, p: val, r: list int, h: list int, s: list byte, ish: share, ip: val, buf: list byte
  PRE [ tptr t_rpoly, tptr tuchar, tulong ]
    PROP (writable_share sh; readable_share ish; Zlength r = 17; Zlength h = 17;
          Zlength buf <= Int64.max_signed)
    PARAMS (p; ip; Vlong (Int64.repr (Zlength buf)))
    SEP (data_at sh t_rpoly (rpoly_val r h s) p; data_at ish (tarray tuchar (Zlength buf)) (map Vubyte buf) ip)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_rpoly (rpoly_val r (haead_padded r h buf) s) p;
         data_at ish (tarray tuchar (Zlength buf)) (map Vubyte buf) ip).

(* rp_final(p, out) *)
Definition rp_final_spec :=
  DECLARE HA._rp_final
  WITH sh: share, p: val, r: list int, h: list int, s: list byte, osh: share, out: val, gv: globals
  PRE [ tptr t_rpoly, tptr tuchar ]
    PROP (writable_share sh; writable_share osh; Zlength r = 17; Zlength h = 17)
    PARAMS (p; out) GLOBALS (gv)
    SEP (data_at sh t_rpoly (rpoly_val r h s) p; data_at_ osh (tarray tuchar 16) out; haead_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_rpoly (rpoly_val r (hrp_final_h h s) s) p;
         data_at osh (tarray tuchar 16) (map Vubyte (hrp_final_out h s)) out;
         haead_globals gv).

(* ---------------------------------------------------------------------- *)
(* common.h: the reference AEADs                                           *)
(* ---------------------------------------------------------------------- *)

(* ref_aead_tag(tag, key, nonce, ad, adlen, ct, ctlen) *)
Definition ref_aead_tag_spec :=
  DECLARE HA._ref_aead_tag
  WITH tsh: share, tag: val, ksh: share, kp: val, key: list byte, nonce: Z, ash: share, ad: val,
       a: list byte, csh: share, cp: val, ct: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tptr tuchar, tulong ]
    PROP (writable_share tsh; readable_share ksh; readable_share ash; readable_share csh; Zlength key = 32;
          0 <= nonce <= Int64.max_unsigned; Zlength a <= Int64.max_signed; Zlength ct <= Int64.max_signed)
    PARAMS (tag; kp; Vlong (Int64.repr nonce); ad; Vlong (Int64.repr (Zlength a)); cp;
            Vlong (Int64.repr (Zlength ct))) GLOBALS (gv)
    SEP (data_at_ tsh (tarray tuchar 16) tag; data_at ksh (tarray tuchar 32) (map Vubyte key) kp;
         data_at ash (tarray tuchar (Zlength a)) (map Vubyte a) ad;
         data_at csh (tarray tuchar (Zlength ct)) (map Vubyte ct) cp; haead_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at tsh (tarray tuchar 16) (map Vubyte (poly1305_tag (aead_otk (aead_st key nonce)) (aead_mac_data a ct))) tag;
         data_at ksh (tarray tuchar 32) (map Vubyte key) kp;
         data_at ash (tarray tuchar (Zlength a)) (map Vubyte a) ad;
         data_at csh (tarray tuchar (Zlength ct)) (map Vubyte ct) cp; haead_globals gv).

(* ref_chacha20_xor(dst, src, len, key, nonce): the keystream from block 1 *)
Definition ref_chacha20_xor_spec :=
  DECLARE HA._ref_chacha20_xor
  WITH dsh: share, dst: val, ssh: share, src: val, m: list byte, ksh: share, kp: val, key: list byte, nonce: Z
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong ]
    PROP (writable_share dsh; readable_share ssh; readable_share ksh; Zlength key = 32;
          0 <= nonce <= Int64.max_unsigned; Zlength m <= Int64.max_signed)
    PARAMS (dst; src; Vlong (Int64.repr (Zlength m)); kp; Vlong (Int64.repr nonce))
    SEP (data_at_ dsh (tarray tuchar (Zlength m)) dst; data_at ssh (tarray tuchar (Zlength m)) (map Vubyte m) src;
         data_at ksh (tarray tuchar 32) (map Vubyte key) kp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at dsh (tarray tuchar (Zlength m)) (map Vubyte (chacha_xor 10 (chacha_advance (aead_st key nonce) 1) m)) dst;
         data_at ssh (tarray tuchar (Zlength m)) (map Vubyte m) src;
         data_at ksh (tarray tuchar 32) (map Vubyte key) kp).

(* ref_aead_encrypt(dst, src, len, ad, adlen, nonce, key) = aead_enc *)
Definition ref_aead_encrypt_spec :=
  DECLARE HA._ref_aead_encrypt
  WITH dsh: share, dst: val, ssh: share, src: val, m: list byte, ash: share, ad: val, a: list byte,
       nonce: Z, ksh: share, kp: val, key: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tulong, tptr tuchar ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; readable_share ksh; Zlength key = 32;
          0 <= nonce <= Int64.max_unsigned; Zlength m + 16 <= Int64.max_signed; Zlength a <= Int64.max_signed)
    PARAMS (dst; src; Vlong (Int64.repr (Zlength m)); ad; Vlong (Int64.repr (Zlength a));
            Vlong (Int64.repr nonce); kp) GLOBALS (gv)
    SEP (data_at_ dsh (tarray tuchar (Zlength m + 16)) dst;
         data_at ssh (tarray tuchar (Zlength m)) (map Vubyte m) src;
         data_at ash (tarray tuchar (Zlength a)) (map Vubyte a) ad;
         data_at ksh (tarray tuchar 32) (map Vubyte key) kp; haead_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at dsh (tarray tuchar (Zlength m + 16)) (map Vubyte (aead_enc key nonce a m)) dst;
         data_at ssh (tarray tuchar (Zlength m)) (map Vubyte m) src;
         data_at ash (tarray tuchar (Zlength a)) (map Vubyte a) ad;
         data_at ksh (tarray tuchar 32) (map Vubyte key) kp; haead_globals gv).

(* ref_aead_decrypt(dst, src, len, ad, adlen, nonce, key): 1 and the plaintext iff aead_dec succeeds *)
Definition ref_aead_decrypt_spec :=
  DECLARE HA._ref_aead_decrypt
  WITH dsh: share, dst: val, old: list val, ssh: share, src: val, c: list byte, ash: share, ad: val,
       a: list byte, nonce: Z, ksh: share, kp: val, key: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tulong, tptr tuchar ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; readable_share ksh; Zlength key = 32;
          0 <= nonce <= Int64.max_unsigned; Zlength c <= Int64.max_signed; Zlength a <= Int64.max_signed;
          Zlength old = Z.max 0 (Zlength c - 16))
    PARAMS (dst; src; Vlong (Int64.repr (Zlength c)); ad; Vlong (Int64.repr (Zlength a));
            Vlong (Int64.repr nonce); kp) GLOBALS (gv)
    SEP (data_at dsh (tarray tuchar (Zlength old)) old dst;
         data_at ssh (tarray tuchar (Zlength c)) (map Vubyte c) src;
         data_at ash (tarray tuchar (Zlength a)) (map Vubyte a) ad;
         data_at ksh (tarray tuchar 32) (map Vubyte key) kp; haead_globals gv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (match aead_dec key nonce a c with Some _ => Int.one | None => Int.zero end))
    SEP (data_at dsh (tarray tuchar (Zlength old))
           (match aead_dec key nonce a c with Some pt => map Vubyte pt | None => old end) dst;
         data_at ssh (tarray tuchar (Zlength c)) (map Vubyte c) src;
         data_at ash (tarray tuchar (Zlength a)) (map Vubyte a) ad;
         data_at ksh (tarray tuchar 32) (map Vubyte key) kp; haead_globals gv).

(* ref_xaead_encrypt(dst, src, len, ad, adlen, nonce, key) = xaead_enc *)
Definition ref_xaead_encrypt_spec :=
  DECLARE HA._ref_xaead_encrypt
  WITH dsh: share, dst: val, ssh: share, src: val, m: list byte, ash: share, ad: val, a: list byte,
       nsh: share, np: val, nonce: list byte, ksh: share, kp: val, key: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tptr tuchar, tptr tuchar ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; readable_share nsh; readable_share ksh;
          Zlength key = 32; Zlength nonce = 24; Zlength m + 16 <= Int64.max_signed;
          Zlength a <= Int64.max_signed)
    PARAMS (dst; src; Vlong (Int64.repr (Zlength m)); ad; Vlong (Int64.repr (Zlength a)); np; kp)
    GLOBALS (gv)
    SEP (data_at_ dsh (tarray tuchar (Zlength m + 16)) dst;
         data_at ssh (tarray tuchar (Zlength m)) (map Vubyte m) src;
         data_at ash (tarray tuchar (Zlength a)) (map Vubyte a) ad;
         data_at nsh (tarray tuchar 24) (map Vubyte nonce) np;
         data_at ksh (tarray tuchar 32) (map Vubyte key) kp; haead_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at dsh (tarray tuchar (Zlength m + 16)) (map Vubyte (xaead_enc key nonce a m)) dst;
         data_at ssh (tarray tuchar (Zlength m)) (map Vubyte m) src;
         data_at ash (tarray tuchar (Zlength a)) (map Vubyte a) ad;
         data_at nsh (tarray tuchar 24) (map Vubyte nonce) np;
         data_at ksh (tarray tuchar 32) (map Vubyte key) kp; haead_globals gv).

(* ref_xaead_decrypt(dst, src, len, ad, adlen, nonce, key) *)
Definition ref_xaead_decrypt_spec :=
  DECLARE HA._ref_xaead_decrypt
  WITH dsh: share, dst: val, old: list val, ssh: share, src: val, c: list byte, ash: share, ad: val,
       a: list byte, nsh: share, np: val, nonce: list byte, ksh: share, kp: val, key: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tptr tuchar, tptr tuchar ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; readable_share nsh; readable_share ksh;
          Zlength key = 32; Zlength nonce = 24; Zlength c <= Int64.max_signed; Zlength a <= Int64.max_signed;
          Zlength old = Z.max 0 (Zlength c - 16))
    PARAMS (dst; src; Vlong (Int64.repr (Zlength c)); ad; Vlong (Int64.repr (Zlength a)); np; kp)
    GLOBALS (gv)
    SEP (data_at dsh (tarray tuchar (Zlength old)) old dst;
         data_at ssh (tarray tuchar (Zlength c)) (map Vubyte c) src;
         data_at ash (tarray tuchar (Zlength a)) (map Vubyte a) ad;
         data_at nsh (tarray tuchar 24) (map Vubyte nonce) np;
         data_at ksh (tarray tuchar 32) (map Vubyte key) kp; haead_globals gv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (match xaead_dec key nonce a c with Some _ => Int.one | None => Int.zero end))
    SEP (data_at dsh (tarray tuchar (Zlength old))
           (match xaead_dec key nonce a c with Some pt => map Vubyte pt | None => old end) dst;
         data_at ssh (tarray tuchar (Zlength c)) (map Vubyte c) src;
         data_at ash (tarray tuchar (Zlength a)) (map Vubyte a) ad;
         data_at nsh (tarray tuchar 24) (map Vubyte nonce) np;
         data_at ksh (tarray tuchar 32) (map Vubyte key) kp; haead_globals gv).

(* ---------------------------------------------------------------------- *)
(* prim_aead.h                                                             *)
(* ---------------------------------------------------------------------- *)

(* check_decrypt_any(x, key, nonce, xnonce, ad, adlen, ct, n): ct ANY n + 16 bytes; its checks hold, every
   allocation is freed, nothing changes *)
Definition check_decrypt_any_spec :=
  DECLARE HA._check_decrypt_any
  WITH x: Z, ksh: share, kp: val, key: list byte, nonce: Z, xsh: share, xp: val, xnonce: list byte,
       ash: share, ad: val, a: list byte, csh: share, cp: val, ct: list byte, gv: globals
  PRE [ tint, tptr tuchar, tulong, tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong ]
    PROP (readable_share ksh; readable_share xsh; readable_share ash; readable_share csh;
          Int.min_signed <= x <= Int.max_signed; Zlength key = 32; 0 <= nonce <= Int64.max_unsigned;
          Zlength xnonce = 24; Zlength a <= Int64.max_signed; 16 <= Zlength ct <= Int64.max_signed)
    PARAMS (Vint (Int.repr x); kp; Vlong (Int64.repr nonce); xp; ad; Vlong (Int64.repr (Zlength a)); cp;
            Vlong (Int64.repr (Zlength ct - 16))) GLOBALS (gv)
    SEP (data_at ksh (tarray tuchar 32) (map Vubyte key) kp;
         data_at xsh (tarray tuchar 24) (map Vubyte xnonce) xp;
         data_at ash (tarray tuchar (Zlength a)) (map Vubyte a) ad;
         data_at csh (tarray tuchar (Zlength ct)) (map Vubyte ct) cp;
         mem_mgr gv; zero_page gv; haead_globals gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at ksh (tarray tuchar 32) (map Vubyte key) kp;
         data_at xsh (tarray tuchar 24) (map Vubyte xnonce) xp;
         data_at ash (tarray tuchar (Zlength a)) (map Vubyte a) ad;
         data_at csh (tarray tuchar (Zlength ct)) (map Vubyte ct) cp;
         mem_mgr gv; zero_page gv; haead_globals gv).

(* ---------------------------------------------------------------------- *)
(* imports: the kernel AEAD, cloned at W_prim_aead (aead_spec3.v's text)   *)
(* ---------------------------------------------------------------------- *)

Definition haead_encrypt_spec :=
  DECLARE _chacha20poly1305_encrypt
  WITH dsh: share, dst: val, ssh: share, src: val, m: list byte, ash: share, ad: val, a: list byte,
       nonce: Z, ksh: share, key: val, k: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tulong, tptr tuchar ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; readable_share ksh;
          Zlength m + 16 <= Int64.max_unsigned; Zlength a <= Int64.max_unsigned;
          0 <= nonce <= Int64.max_unsigned; Zlength k = 32)
    PARAMS (dst; src; Vlong (Int64.repr (Zlength m)); ad; Vlong (Int64.repr (Zlength a));
            Vlong (Int64.repr nonce); key) GLOBALS (gv)
    SEP (data_at_ dsh (tarray tuchar (Zlength m + 16)) dst; prim_bytes ssh m src; prim_bytes ash a ad;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at dsh (tarray tuchar (Zlength m + 16)) (map Vubyte (aead_enc k nonce a m)) dst;
         prim_bytes ssh m src; prim_bytes ash a ad;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv).

Definition haead_decrypt_spec :=
  DECLARE _chacha20poly1305_decrypt
  WITH dsh: share, dst: val, old: list val, ssh: share, src: val, c: list byte, ash: share, ad: val,
       a: list byte, nonce: Z, ksh: share, key: val, k: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tulong, tptr tuchar ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; readable_share ksh;
          Zlength c <= Int64.max_unsigned; Zlength a <= Int64.max_unsigned;
          0 <= nonce <= Int64.max_unsigned;
          Zlength k = 32; Zlength old = Z.max 0 (Zlength c - 16))
    PARAMS (dst; src; Vlong (Int64.repr (Zlength c)); ad; Vlong (Int64.repr (Zlength a));
            Vlong (Int64.repr nonce); key) GLOBALS (gv)
    SEP (data_at dsh (tarray tuchar (Zlength old)) old dst; prim_bytes ssh c src; prim_bytes ash a ad;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv)
  POST [ tbool ]
    PROP ()
    RETURN (Val.of_bool (match aead_dec k nonce a c with Some _ => true | None => false end))
    SEP (data_at dsh (tarray tuchar (Zlength old))
           (match aead_dec k nonce a c with Some pt => map Vubyte pt | None => old end) dst;
         prim_bytes ssh c src; prim_bytes ash a ad;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv).

Definition haead_xencrypt_spec :=
  DECLARE _xchacha20poly1305_encrypt
  WITH dsh: share, dst: val, ssh: share, src: val, m: list byte, ash: share, ad: val, a: list byte,
       nsh: share, np: val, nonce: list byte, ksh: share, key: val, k: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tptr tuchar, tptr tuchar ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; readable_share nsh; readable_share ksh;
          Zlength m + 16 <= Int64.max_unsigned; Zlength a <= Int64.max_unsigned; Zlength nonce = 24;
          Zlength k = 32)
    PARAMS (dst; src; Vlong (Int64.repr (Zlength m)); ad; Vlong (Int64.repr (Zlength a)); np; key)
    GLOBALS (gv)
    SEP (data_at_ dsh (tarray tuchar (Zlength m + 16)) dst; prim_bytes ssh m src; prim_bytes ash a ad;
         data_at nsh (tarray tuchar 24) (map Vubyte nonce) np;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at dsh (tarray tuchar (Zlength m + 16)) (map Vubyte (xaead_enc k nonce a m)) dst;
         prim_bytes ssh m src; prim_bytes ash a ad;
         data_at nsh (tarray tuchar 24) (map Vubyte nonce) np;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv).

Definition haead_xdecrypt_spec :=
  DECLARE _xchacha20poly1305_decrypt
  WITH dsh: share, dst: val, old: list val, ssh: share, src: val, c: list byte, ash: share, ad: val,
       a: list byte, nsh: share, np: val, nonce: list byte, ksh: share, key: val, k: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tptr tuchar, tptr tuchar ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; readable_share nsh; readable_share ksh;
          Zlength c <= Int64.max_unsigned; Zlength a <= Int64.max_unsigned; Zlength nonce = 24;
          Zlength k = 32; Zlength old = Z.max 0 (Zlength c - 16))
    PARAMS (dst; src; Vlong (Int64.repr (Zlength c)); ad; Vlong (Int64.repr (Zlength a)); np; key)
    GLOBALS (gv)
    SEP (data_at dsh (tarray tuchar (Zlength old)) old dst; prim_bytes ssh c src; prim_bytes ash a ad;
         data_at nsh (tarray tuchar 24) (map Vubyte nonce) np;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv)
  POST [ tbool ]
    PROP ()
    RETURN (Val.of_bool (match xaead_dec k nonce a c with Some _ => true | None => false end))
    SEP (data_at dsh (tarray tuchar (Zlength old))
           (match xaead_dec k nonce a c with Some pt => map Vubyte pt | None => old end) dst;
         prim_bytes ssh c src; prim_bytes ash a ad;
         data_at nsh (tarray tuchar 24) (map Vubyte nonce) np;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv).

(* ---------------------------------------------------------------------- *)
(* The piece                                                               *)
(* ---------------------------------------------------------------------- *)

(* imports: the external world (at W_prim_aead) and the kernel AEAD main / check_decrypt_any call *)
Definition haead_imports (cs: compspecs) : funspecs :=
  @asm_env.env_specs W_prim_aead ++
  [haead_encrypt_spec; haead_decrypt_spec; haead_xencrypt_spec; haead_xdecrypt_spec].

Definition haead_G : funspecs :=
  [check_failed_spec; bytes_eq_spec; bytes_copy_spec; bytes_set_spec; draw_size_spec; draw_u64_spec;
   le32_store_spec; le32_load_spec; le64_store_spec; le64_load_spec;
   rc_rotl_spec; rc_qr_spec; rc_rounds_spec; rc_setup_spec; ref_chacha20_block_spec; ref_hchacha20_spec;
   rp_add_spec; rp_init_spec; rp_mul_spec; rp_block_spec; rp_padded_spec; rp_final_spec;
   ref_aead_tag_spec; ref_chacha20_xor_spec; ref_aead_encrypt_spec; ref_aead_decrypt_spec;
   ref_xaead_encrypt_spec; ref_xaead_decrypt_spec; check_decrypt_any_spec; haead_main_spec].

(* the context of every body proof of the harness piece *)
Definition haead_Gprog : funspecs := haead_imports W_prim_aead ++ haead_G.
