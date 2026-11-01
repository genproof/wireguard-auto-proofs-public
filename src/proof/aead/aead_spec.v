(* Specifications of the AEAD piece: every function of chacha.c, chacha-block-generic.c,
   poly1305.c, poly1305-donna32.c, chacha20poly1305.c (minus the shared inlines memzero_explicit,
   get_unaligned_le32, crypto_memneq) and the shim's __crypto_xor, against the model aead_model.v.

   Conventions:
   - each specification is stated in the compspecs of the unit that contains the function (the static
     inlines put_unaligned_le32 and chacha_zeroize_state, compiled into several units: in ChachaBlock.CS);
     a caller in another unit converts its structs with change_compspecs (instances in aead_cce.v) and
     its byte arrays with data_at_tarray_tuchar_cs (src/proof/libc/libc_bytes.v);
   - a ChaCha state is `data_at sh t_chacha_state (map Vint st) p`, st the 16 words (list int);
   - the Poly1305 streaming context is the predicate `p1305_state sh key msg desc` (key: 32 bytes, msg: all
     update chunks concatenated): clients never unfold it;
   - input buffers of a length that may be 0 are `prim_bytes` (emp when empty, pointer arbitrary);
   - output buffers are disjoint from the inputs. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.chacha.code WgNoise.chacha_block.code WgNoise.poly1305.code WgNoise.poly1305_donna32.code
        WgNoise.chacha20poly1305.code WgNoise.shim.code.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Export WgNoise.proof.aead.aead_model.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* identifiers (clightgen's $"name": the same in every unit)               *)
(* ---------------------------------------------------------------------- *)

Definition ___crypto_xor : ident := WgNoise.shim.code.___crypto_xor.
Definition _crypto_xor_cpy : ident := WgNoise.chacha.code._crypto_xor_cpy.
Definition _chacha_crypt_generic : ident := WgNoise.chacha.code._chacha_crypt_generic.
Definition _chacha_crypt : ident := WgNoise.chacha.code._chacha_crypt.
Definition _hchacha_block : ident := WgNoise.chacha.code._hchacha_block.
Definition _rol32 : ident := WgNoise.chacha_block.code._rol32.
Definition _put_unaligned_le32 : ident := WgNoise.chacha_block.code._put_unaligned_le32.
Definition _chacha_zeroize_state : ident := WgNoise.chacha_block.code._chacha_zeroize_state.
Definition _chacha_permute : ident := WgNoise.chacha_block.code._chacha_permute.
Definition _chacha_block_generic : ident := WgNoise.chacha_block.code._chacha_block_generic.
Definition _hchacha_block_generic : ident := WgNoise.chacha_block.code._hchacha_block_generic.
Definition _poly1305_core_init : ident := WgNoise.poly1305.code._poly1305_core_init.
Definition _poly1305_block_init_generic : ident := WgNoise.poly1305.code._poly1305_block_init_generic.
Definition _poly1305_blocks_generic : ident := WgNoise.poly1305.code._poly1305_blocks_generic.
Definition _poly1305_emit_generic : ident := WgNoise.poly1305.code._poly1305_emit_generic.
Definition _poly1305_init : ident := WgNoise.poly1305.code._poly1305_init.
Definition _poly1305_update : ident := WgNoise.poly1305.code._poly1305_update.
Definition _poly1305_final : ident := WgNoise.poly1305.code._poly1305_final.
Definition _poly1305_core_setkey : ident := WgNoise.poly1305_donna32.code._poly1305_core_setkey.
Definition _poly1305_core_blocks : ident := WgNoise.poly1305_donna32.code._poly1305_core_blocks.
Definition _poly1305_core_emit : ident := WgNoise.poly1305_donna32.code._poly1305_core_emit.
Definition _put_unaligned_le64 : ident := WgNoise.chacha20poly1305.code._put_unaligned_le64.
Definition _chacha_init_consts : ident := WgNoise.chacha20poly1305.code._chacha_init_consts.
Definition _chacha_init : ident := WgNoise.chacha20poly1305.code._chacha_init.
Definition _chacha20_crypt : ident := WgNoise.chacha20poly1305.code._chacha20_crypt.
Definition _chacha_load_key : ident := WgNoise.chacha20poly1305.code._chacha_load_key.
Definition _xchacha_init : ident := WgNoise.chacha20poly1305.code._xchacha_init.
Definition ___chacha20poly1305_encrypt : ident := WgNoise.chacha20poly1305.code.___chacha20poly1305_encrypt.
Definition ___chacha20poly1305_decrypt : ident := WgNoise.chacha20poly1305.code.___chacha20poly1305_decrypt.

Definition _chacha_state : ident := WgNoise.chacha_block.code._chacha_state.
Definition _poly1305_state : ident := WgNoise.poly1305.code._poly1305_state.
Definition _poly1305_core_key : ident := WgNoise.poly1305.code._poly1305_core_key.
Definition _poly1305_block_state : ident := WgNoise.poly1305.code._poly1305_block_state.
Definition _poly1305_desc_ctx : ident := WgNoise.poly1305.code._poly1305_desc_ctx.

Definition t_chacha_state : type := Tstruct _chacha_state noattr.
Definition t_p1305_state : type := Tstruct _poly1305_state noattr.          (* the accumulator h *)
Definition t_p1305_core_key : type := Tstruct _poly1305_core_key noattr.    (* r and 5 r *)
Definition t_p1305_block_state : type := Tstruct _poly1305_block_state noattr.
Definition t_p1305_ctx : type := Tstruct _poly1305_desc_ctx noattr.

(* ---------------------------------------------------------------------- *)
(* Poly1305: the donna32 representation                                    *)
(* ---------------------------------------------------------------------- *)

(* the accumulator: 5 limbs of 26 bits (h1 may carry a little more) *)
Definition p1305_limbs_val (h: list Z) : Z :=
  Znth 0 h + Znth 1 h * 2 ^ 26 + Znth 2 h * 2 ^ 52 + Znth 3 h * 2 ^ 78 + Znth 4 h * 2 ^ 104.

(* the limb bounds kept by poly1305_core_blocks (and needed by poly1305_core_emit) *)
Definition p1305_limbs_ok (h: list Z) : Prop :=
  Zlength h = 5 /\ 0 <= Znth 0 h < 2 ^ 26 /\ 0 <= Znth 1 h < 2 ^ 26 + 2 ^ 6 /\
  0 <= Znth 2 h < 2 ^ 26 /\ 0 <= Znth 3 h < 2 ^ 26 /\ 0 <= Znth 4 h < 2 ^ 26.

(* r (clamped, < 2^124) as 5 limbs of 26 bits *)
Definition p1305_r_limbs (r: Z) : list Z :=
  [r mod 2 ^ 26; (r / 2 ^ 26) mod 2 ^ 26; (r / 2 ^ 52) mod 2 ^ 26; (r / 2 ^ 78) mod 2 ^ 26; r / 2 ^ 104].

(* the 4 words of s = key[16..32) *)
Definition p1305_s_words (key: list byte) : list int :=
  [le32_at key 16; le32_at key 20; le32_at key 24; le32_at key 28].

(* the value of little-endian words *)
Fixpoint words_Z (ws: list int) : Z :=
  match ws with [] => 0 | w :: t => Int.unsigned w + 2 ^ 32 * words_Z t end.

Section P1305Rep.
#[local] Existing Instance Poly1305.CS.

(* struct poly1305_state: the union's first member h[5] *)
Definition p1305_h_val (h: list Z) : reptype t_p1305_state := inl (map Vint (map Int.repr h)).

(* struct poly1305_core_key after poly1305_core_setkey: key.r = the limbs of r, precomputed_s.r[0..3] =
   5 r1 .. 5 r4 (precomputed_s.r[4] is never written) *)
Definition p1305_key_val (r: Z) : reptype t_p1305_core_key :=
  (inl (map Vint (map Int.repr (p1305_r_limbs r))),
   inl (map (fun z => Vint (Int.repr (5 * z))) (sublist 1 5 (p1305_r_limbs r)) ++ [Vundef])).

(* struct poly1305_block_state: h, and the key in the union's member core_r *)
Definition p1305_bstate_val (h: list Z) (r: Z) : reptype t_p1305_block_state :=
  (p1305_h_val h, inr (p1305_key_val r)).

(* struct poly1305_desc_ctx *)
Definition p1305_ctx_val (buf: list val) (buflen: Z) (s: list int) (h: list Z) (r: Z) : reptype t_p1305_ctx :=
  (buf, (Vint (Int.repr buflen), (map Vint s, p1305_bstate_val h r))).

(* the context after poly1305_final: all zero (core_r the union's member) *)
Definition p1305_ctx_zero : reptype t_p1305_ctx :=
  (Zrepeat (Vubyte Byte.zero) 16,
   (Vint Int.zero,
    (Zrepeat (Vint Int.zero) 4,
     (inl (Zrepeat (Vint Int.zero) 5),
      inr (inl (Zrepeat (Vint Int.zero) 5), inl (Zrepeat (Vint Int.zero) 5)))))).

(* The streaming state: poly1305_init with key, then update with msg.  With full = the whole 16-byte blocks
   of msg and rest the remaining 0..15 bytes: h represents the accumulator of full (mod p), buf holds rest
   (then anything), buflen = |rest|, s = key[16..32), the key's r. *)
Definition p1305_state (sh: share) (key: list byte) (msg: list byte) (desc: val) : mpred :=
  let n := Zlength msg / 16 * 16 in
  let rest := sublist n (Zlength msg) msg in
  EX h: list Z, EX junk: list val,
    !! (Zlength key = 32 /\ p1305_limbs_ok h /\
        p1305_limbs_val h mod p1305_p = p1305_acc (p1305_r key) 0 (sublist 0 n msg) /\
        Zlength junk = 16 - Zlength rest) &&
    data_at sh t_p1305_ctx
      (p1305_ctx_val (map Vubyte rest ++ junk) (Zlength rest) (p1305_s_words key) h (p1305_r key)) desc.

End P1305Rep.

(* ---------------------------------------------------------------------- *)
(* shim: __crypto_xor                                                      *)
(* ---------------------------------------------------------------------- *)

Section ShimSpecs.
#[local] Existing Instance Shim.CS.

(* __crypto_xor(dst, src1, src2, len): dst[i] = src1[i] ^ src2[i]; dst disjoint from the sources *)
Definition __crypto_xor_spec :=
  DECLARE ___crypto_xor
  WITH dsh: share, dst: val, sh1: share, p1: val, a: list byte, sh2: share, p2: val, b: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tuint ]
    PROP (writable_share dsh; readable_share sh1; readable_share sh2; Zlength a = Zlength b;
          Zlength a <= Int.max_unsigned)
    PARAMS (dst; p1; p2; Vint (Int.repr (Zlength a)))
    SEP (data_at_ dsh (tarray tuchar (Zlength a)) dst;
         data_at sh1 (tarray tuchar (Zlength a)) (map Vubyte a) p1;
         data_at sh2 (tarray tuchar (Zlength a)) (map Vubyte b) p2)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at dsh (tarray tuchar (Zlength a)) (map Vubyte (xor_bytes a b)) dst;
         data_at sh1 (tarray tuchar (Zlength a)) (map Vubyte a) p1;
         data_at sh2 (tarray tuchar (Zlength a)) (map Vubyte b) p2).

End ShimSpecs.

(* ---------------------------------------------------------------------- *)
(* chacha.c                                                                *)
(* ---------------------------------------------------------------------- *)

Section ChachaSpecs.
#[local] Existing Instance Chacha.CS.

(* the inline crypto_xor_cpy: __crypto_xor *)
Definition crypto_xor_cpy_spec :=
  DECLARE _crypto_xor_cpy
  WITH dsh: share, dst: val, sh1: share, p1: val, a: list byte, sh2: share, p2: val, b: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tuint ]
    PROP (writable_share dsh; readable_share sh1; readable_share sh2; Zlength a = Zlength b;
          Zlength a <= Int.max_unsigned)
    PARAMS (dst; p1; p2; Vint (Int.repr (Zlength a)))
    SEP (data_at_ dsh (tarray tuchar (Zlength a)) dst;
         data_at sh1 (tarray tuchar (Zlength a)) (map Vubyte a) p1;
         data_at sh2 (tarray tuchar (Zlength a)) (map Vubyte b) p2)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at dsh (tarray tuchar (Zlength a)) (map Vubyte (xor_bytes a b)) dst;
         data_at sh1 (tarray tuchar (Zlength a)) (map Vubyte a) p1;
         data_at sh2 (tarray tuchar (Zlength a)) (map Vubyte b) p2).

(* chacha_crypt_generic / chacha_crypt(state, dst, src, |m|, nrounds): dst = m XOR the keystream from st;
   the block counter advances by the number of (partial) blocks.  nrounds 20 or 12. *)
Definition chacha_crypt_spec_for (i: ident) :=
  DECLARE i
  WITH ssh: share, state: val, st: list int, dsh: share, dst: val, msh: share, src: val, m: list byte,
       nr: Z
  PRE [ tptr t_chacha_state, tptr tuchar, tptr tuchar, tuint, tint ]
    PROP (writable_share ssh; writable_share dsh; readable_share msh; Zlength st = 16;
          Zlength m <= Int.max_unsigned; nr = 20 \/ nr = 12)
    PARAMS (state; dst; src; Vint (Int.repr (Zlength m)); Vint (Int.repr nr))
    SEP (data_at ssh t_chacha_state (map Vint st) state; data_at_ dsh (tarray tuchar (Zlength m)) dst;
         prim_bytes msh m src)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at ssh t_chacha_state (map Vint (chacha_advance st (chacha_nblocks (Zlength m)))) state;
         data_at dsh (tarray tuchar (Zlength m)) (map Vubyte (chacha_xor (Z.to_nat (nr / 2)) st m)) dst;
         prim_bytes msh m src).

Definition chacha_crypt_generic_spec := chacha_crypt_spec_for _chacha_crypt_generic.

(* (series patch P23 "lib/crypto: chacha: Take a size_t length in chacha_crypt()"): chacha_crypt takes
   a size_t length and feeds chacha_crypt_generic (unsigned int) chunks of round_down(UINT_MAX, 64) bytes; the
   same result as chacha_crypt_spec_for, for ANY size_t length (the block counter is a 32-bit word: it wraps as
   chacha_advance wraps it). *)
Definition chacha_crypt_spec :=
  DECLARE _chacha_crypt
  WITH ssh: share, state: val, st: list int, dsh: share, dst: val, msh: share, src: val, m: list byte,
       nr: Z
  PRE [ tptr t_chacha_state, tptr tuchar, tptr tuchar, tulong, tint ]
    PROP (writable_share ssh; writable_share dsh; readable_share msh; Zlength st = 16;
          Zlength m <= Int64.max_unsigned; nr = 20 \/ nr = 12)
    PARAMS (state; dst; src; Vlong (Int64.repr (Zlength m)); Vint (Int.repr nr))
    SEP (data_at ssh t_chacha_state (map Vint st) state; data_at_ dsh (tarray tuchar (Zlength m)) dst;
         prim_bytes msh m src)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at ssh t_chacha_state (map Vint (chacha_advance st (chacha_nblocks (Zlength m)))) state;
         data_at dsh (tarray tuchar (Zlength m)) (map Vubyte (chacha_xor (Z.to_nat (nr / 2)) st m)) dst;
         prim_bytes msh m src).

(* hchacha_block(state, out, nrounds): out = HChaCha words; the state is unchanged *)
Definition hchacha_block_spec_for (i: ident) :=
  DECLARE i
  WITH ssh: share, state: val, st: list int, osh: share, out: val, nr: Z
  PRE [ tptr t_chacha_state, tptr tuint, tint ]
    PROP (readable_share ssh; writable_share osh; Zlength st = 16; nr = 20 \/ nr = 12)
    PARAMS (state; out; Vint (Int.repr nr))
    SEP (data_at ssh t_chacha_state (map Vint st) state; data_at_ osh (tarray tuint 8) out)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at ssh t_chacha_state (map Vint st) state;
         data_at osh (tarray tuint 8) (map Vint (hchacha_words (Z.to_nat (nr / 2)) st)) out).

Definition hchacha_block_spec := hchacha_block_spec_for _hchacha_block.

End ChachaSpecs.

(* ---------------------------------------------------------------------- *)
(* chacha-block-generic.c (and the inlines put_unaligned_le32, chacha_zeroize_state) *)
(* ---------------------------------------------------------------------- *)

Section ChachaBlockSpecs.
#[local] Existing Instance ChachaBlock.CS.

(* rol32(w, s) = w rotated left by s *)
Definition rol32_spec :=
  DECLARE _rol32
  WITH w: int, s: Z
  PRE [ tuint, tuint ]
    PROP (0 <= s < 32) PARAMS (Vint w; Vint (Int.repr s)) SEP ()
  POST [ tuint ]
    PROP () RETURN (Vint (Int.rol w (Int.repr s))) SEP ().

(* put_unaligned_le32(v, p + i): bytes i..i+3 of the n-byte buffer at p := v little-endian *)
Definition put_unaligned_le32_spec :=
  DECLARE _put_unaligned_le32
  WITH v: int, sh: share, p: val, i: Z, old: list val
  PRE [ tuint, tptr tvoid ]
    PROP (writable_share sh; 0 <= i; i + 4 <= Zlength old)
    PARAMS (Vint v; offset_val i p)
    SEP (data_at sh (tarray tuchar (Zlength old)) old p)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh (tarray tuchar (Zlength old))
           (sublist 0 i old ++ map Vubyte (le32_bytes v) ++ sublist (i + 4) (Zlength old) old) p).

(* chacha_zeroize_state(state): memzero_explicit of the state (its contents are no one's business) *)
Definition chacha_zeroize_state_spec :=
  DECLARE _chacha_zeroize_state
  WITH sh: share, state: val
  PRE [ tptr t_chacha_state ]
    PROP (writable_share sh) PARAMS (state) SEP (data_at_ sh t_chacha_state state)
  POST [ tvoid ]
    PROP () RETURN () SEP (data_at_ sh t_chacha_state state).

(* chacha_permute(state, nrounds): nrounds / 2 double rounds *)
Definition chacha_permute_spec :=
  DECLARE _chacha_permute
  WITH sh: share, state: val, st: list int, nr: Z
  PRE [ tptr t_chacha_state, tint ]
    PROP (writable_share sh; Zlength st = 16; nr = 20 \/ nr = 12)
    PARAMS (state; Vint (Int.repr nr))
    SEP (data_at sh t_chacha_state (map Vint st) state)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_chacha_state (map Vint (chacha_rounds (Z.to_nat (nr / 2)) st)) state).

(* chacha_block_generic(state, out, nrounds): out = the block of st; the block counter + 1 *)
Definition chacha_block_generic_spec :=
  DECLARE _chacha_block_generic
  WITH ssh: share, state: val, st: list int, osh: share, out: val, nr: Z
  PRE [ tptr t_chacha_state, tptr tuchar, tint ]
    PROP (writable_share ssh; writable_share osh; Zlength st = 16; nr = 20 \/ nr = 12)
    PARAMS (state; out; Vint (Int.repr nr))
    SEP (data_at ssh t_chacha_state (map Vint st) state; data_at_ osh (tarray tuchar 64) out)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at ssh t_chacha_state (map Vint (chacha_advance st 1)) state;
         data_at osh (tarray tuchar 64) (map Vubyte (chacha_block_bytes (Z.to_nat (nr / 2)) st)) out).

Definition hchacha_block_generic_spec := hchacha_block_spec_for _hchacha_block_generic.

End ChachaBlockSpecs.

(* ---------------------------------------------------------------------- *)
(* poly1305-donna32.c                                                      *)
(* ---------------------------------------------------------------------- *)

(* r is a clamped Poly1305 key half *)
Definition p1305_r_ok (r: Z) : Prop :=
  Z.land r 21267647620597763993911028882763415551 = r /\ 0 <= r.

Section DonnaSpecs.
#[local] Existing Instance Poly1305Donna32.CS.

(* poly1305_core_setkey(key, raw): r = clamp(le(raw[0..16))) as limbs, and 5 r1 .. 5 r4 *)
Definition poly1305_core_setkey_spec :=
  DECLARE _poly1305_core_setkey
  WITH ksh: share, kp: val, rsh: share, raw: val, rk: list byte
  PRE [ tptr t_p1305_core_key, tptr tuchar ]
    PROP (writable_share ksh; readable_share rsh; 16 <= Zlength rk)
    PARAMS (kp; raw)
    SEP (data_at_ ksh t_p1305_core_key kp; data_at rsh (tarray tuchar (Zlength rk)) (map Vubyte rk) raw)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at ksh t_p1305_core_key (p1305_key_val (p1305_r rk)) kp;
         data_at rsh (tarray tuchar (Zlength rk)) (map Vubyte rk) raw).

(* poly1305_core_blocks(state, key, src, nb, hibit): h := the accumulator of the nb blocks (mod p), limbs
   kept in bounds *)
Definition poly1305_core_blocks_spec :=
  DECLARE _poly1305_core_blocks
  WITH hsh: share, hp: val, h: list Z, ksh: share, kp: val, r: Z, msh: share, src: val, bs: list byte,
       nb: Z, hibit: Z
  PRE [ tptr t_p1305_state, tptr t_p1305_core_key, tptr tvoid, tuint, tuint ]
    PROP (writable_share hsh; readable_share ksh; readable_share msh; p1305_limbs_ok h; p1305_r_ok r;
          0 <= nb <= Int.max_unsigned; Zlength bs = (16 * nb)%Z; hibit = 0 \/ hibit = 1)
    PARAMS (hp; kp; src; Vint (Int.repr nb); Vint (Int.repr hibit))
    SEP (data_at hsh t_p1305_state (p1305_h_val h) hp;
         data_at ksh t_p1305_core_key (p1305_key_val r) kp;
         prim_bytes msh bs src)
  POST [ tvoid ]
    EX h': list Z,
    PROP (p1305_limbs_ok h';
          p1305_limbs_val h' mod p1305_p = p1305_core_blocks r hibit (p1305_limbs_val h) bs mod p1305_p)
    RETURN ()
    SEP (data_at hsh t_p1305_state (p1305_h_val h') hp;
         data_at ksh t_p1305_core_key (p1305_key_val r) kp;
         prim_bytes msh bs src).

(* poly1305_core_emit(state, nonce, dst): dst = (h mod p + nonce) mod 2^128, little-endian; nonce non-NULL *)
Definition poly1305_core_emit_spec :=
  DECLARE _poly1305_core_emit
  WITH hsh: share, hp: val, h: list Z, nsh: share, np: val, s: list int, dsh: share, dst: val
  PRE [ tptr t_p1305_state, tptr tuint, tptr tvoid ]
    PROP (readable_share hsh; readable_share nsh; writable_share dsh; p1305_limbs_ok h; Zlength s = 4)
    PARAMS (hp; np; dst)
    SEP (data_at hsh t_p1305_state (p1305_h_val h) hp; data_at nsh (tarray tuint 4) (map Vint s) np;
         data_at_ dsh (tarray tuchar 16) dst)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at hsh t_p1305_state (p1305_h_val h) hp; data_at nsh (tarray tuint 4) (map Vint s) np;
         data_at dsh (tarray tuchar 16)
           (map Vubyte (le_bytes 16 ((p1305_limbs_val h mod p1305_p + words_Z s) mod 2 ^ 128))) dst).

End DonnaSpecs.

(* ---------------------------------------------------------------------- *)
(* poly1305.c                                                              *)
(* ---------------------------------------------------------------------- *)

Section Poly1305Specs.
#[local] Existing Instance Poly1305.CS.

(* poly1305_core_init(state): h = 0 *)
Definition poly1305_core_init_spec :=
  DECLARE _poly1305_core_init
  WITH sh: share, hp: val
  PRE [ tptr t_p1305_state ]
    PROP (writable_share sh) PARAMS (hp) SEP (data_at_ sh t_p1305_state hp)
  POST [ tvoid ]
    PROP () RETURN () SEP (data_at sh t_p1305_state (p1305_h_val [0; 0; 0; 0; 0]) hp).

(* poly1305_block_init_generic(desc, raw_key): h = 0, the key of raw[0..16) *)
Definition poly1305_block_init_generic_spec :=
  DECLARE _poly1305_block_init_generic
  WITH sh: share, bp: val, rsh: share, raw: val, rk: list byte
  PRE [ tptr t_p1305_block_state, tptr tuchar ]
    PROP (writable_share sh; readable_share rsh; 16 <= Zlength rk)
    PARAMS (bp; raw)
    SEP (data_at_ sh t_p1305_block_state bp; data_at rsh (tarray tuchar (Zlength rk)) (map Vubyte rk) raw)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_p1305_block_state (p1305_bstate_val [0; 0; 0; 0; 0] (p1305_r rk)) bp;
         data_at rsh (tarray tuchar (Zlength rk)) (map Vubyte rk) raw).

(* poly1305_blocks_generic(state, src, len, padbit): len a multiple of 16 *)
Definition poly1305_blocks_generic_spec :=
  DECLARE _poly1305_blocks_generic
  WITH sh: share, bp: val, h: list Z, r: Z, msh: share, src: val, bs: list byte, hibit: Z
  PRE [ tptr t_p1305_block_state, tptr tuchar, tuint, tuint ]
    PROP (writable_share sh; readable_share msh; p1305_limbs_ok h; p1305_r_ok r;
          Zlength bs <= Int.max_unsigned; Zlength bs mod 16 = 0; hibit = 0 \/ hibit = 1)
    PARAMS (bp; src; Vint (Int.repr (Zlength bs)); Vint (Int.repr hibit))
    SEP (data_at sh t_p1305_block_state (p1305_bstate_val h r) bp; prim_bytes msh bs src)
  POST [ tvoid ]
    EX h': list Z,
    PROP (p1305_limbs_ok h';
          p1305_limbs_val h' mod p1305_p = p1305_core_blocks r hibit (p1305_limbs_val h) bs mod p1305_p)
    RETURN ()
    SEP (data_at sh t_p1305_block_state (p1305_bstate_val h' r) bp; prim_bytes msh bs src).

(* poly1305_emit_generic(state, digest, nonce) = poly1305_core_emit(state, nonce, digest) *)
Definition poly1305_emit_generic_spec :=
  DECLARE _poly1305_emit_generic
  WITH hsh: share, hp: val, h: list Z, nsh: share, np: val, s: list int, dsh: share, dst: val
  PRE [ tptr t_p1305_state, tptr tuchar, tptr tuint ]
    PROP (readable_share hsh; readable_share nsh; writable_share dsh; p1305_limbs_ok h; Zlength s = 4)
    PARAMS (hp; dst; np)
    SEP (data_at hsh t_p1305_state (p1305_h_val h) hp; data_at nsh (tarray tuint 4) (map Vint s) np;
         data_at_ dsh (tarray tuchar 16) dst)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at hsh t_p1305_state (p1305_h_val h) hp; data_at nsh (tarray tuint 4) (map Vint s) np;
         data_at dsh (tarray tuchar 16)
           (map Vubyte (le_bytes 16 ((p1305_limbs_val h mod p1305_p + words_Z s) mod 2 ^ 128))) dst).

(* poly1305_init(desc, key) *)
Definition poly1305_init_spec :=
  DECLARE _poly1305_init
  WITH sh: share, desc: val, ksh: share, kp: val, key: list byte
  PRE [ tptr t_p1305_ctx, tptr tuchar ]
    PROP (writable_share sh; readable_share ksh; Zlength key = 32)
    PARAMS (desc; kp)
    SEP (data_at_ sh t_p1305_ctx desc; data_at ksh (tarray tuchar 32) (map Vubyte key) kp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (p1305_state sh key [] desc; data_at ksh (tarray tuchar 32) (map Vubyte key) kp).

(* poly1305_update(desc, src, |data|): ANY chunk (empty included) of ANY size_t length.  The series patch P22
   ("lib/crypto: poly1305: Take a size_t length in poly1305_update()") makes nbytes a size_t, tests
   `nbytes >= POLY1305_BLOCK_SIZE - desc->buflen` (no wrapping sum) and gives poly1305_blocks at most
   round_down(min(nbytes, UINT_MAX), 16) bytes per call. *)
Definition poly1305_update_spec :=
  DECLARE _poly1305_update
  WITH sh: share, desc: val, key: list byte, msg: list byte, dsh: share, src: val, data: list byte
  PRE [ tptr t_p1305_ctx, tptr tuchar, tulong ]
    PROP (writable_share sh; readable_share dsh; Zlength data <= Int64.max_unsigned)
    PARAMS (desc; src; Vlong (Int64.repr (Zlength data)))
    SEP (p1305_state sh key msg desc; prim_bytes dsh data src)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (p1305_state sh key (msg ++ data) desc; prim_bytes dsh data src).

(* poly1305_final(desc, dst): dst = the tag of msg; the context is all zero *)
Definition poly1305_final_spec :=
  DECLARE _poly1305_final
  WITH sh: share, desc: val, key: list byte, msg: list byte, osh: share, dst: val
  PRE [ tptr t_p1305_ctx, tptr tuchar ]
    PROP (writable_share sh; writable_share osh)
    PARAMS (desc; dst)
    SEP (p1305_state sh key msg desc; data_at_ osh (tarray tuchar 16) dst)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_p1305_ctx p1305_ctx_zero desc;
         data_at osh (tarray tuchar 16) (map Vubyte (poly1305_tag key msg)) dst).

End Poly1305Specs.

(* ---------------------------------------------------------------------- *)
(* chacha20poly1305.c                                                      *)
(* ---------------------------------------------------------------------- *)

Section AeadSpecs.
#[local] Existing Instance Chacha20poly1305.CS.

(* put_unaligned_le64(v, p + i) *)
Definition put_unaligned_le64_spec :=
  DECLARE _put_unaligned_le64
  WITH v: Z, sh: share, p: val, i: Z, old: list val
  PRE [ tulong, tptr tvoid ]
    PROP (writable_share sh; 0 <= v <= Int64.max_unsigned; 0 <= i; i + 8 <= Zlength old)
    PARAMS (Vlong (Int64.repr v); offset_val i p)
    SEP (data_at sh (tarray tuchar (Zlength old)) old p)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh (tarray tuchar (Zlength old))
           (sublist 0 i old ++ map Vubyte (le64_bytes v) ++ sublist (i + 8) (Zlength old) old) p).

(* chacha_init_consts(state): words 0..3 *)
Definition chacha_init_consts_spec :=
  DECLARE _chacha_init_consts
  WITH sh: share, state: val, old: list val
  PRE [ tptr t_chacha_state ]
    PROP (writable_share sh; Zlength old = 16) PARAMS (state)
    SEP (data_at sh t_chacha_state old state)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_chacha_state (map Vint chacha_consts ++ sublist 4 16 old) state).

(* chacha_init(state, key words, iv): iv's first 16 bytes are read *)
Definition chacha_init_spec :=
  DECLARE _chacha_init
  WITH sh: share, state: val, ksh: share, kp: val, k: list int, ish: share, ivp: val, iv: list byte
  PRE [ tptr t_chacha_state, tptr tuint, tptr tuchar ]
    PROP (writable_share sh; readable_share ksh; readable_share ish; Zlength k = 8; 16 <= Zlength iv)
    PARAMS (state; kp; ivp)
    SEP (data_at_ sh t_chacha_state state; data_at ksh (tarray tuint 8) (map Vint k) kp;
         data_at ish (tarray tuchar (Zlength iv)) (map Vubyte iv) ivp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_chacha_state (map Vint (chacha_init_st k iv)) state;
         data_at ksh (tarray tuint 8) (map Vint k) kp;
         data_at ish (tarray tuchar (Zlength iv)) (map Vubyte iv) ivp).

(* chacha20_crypt(state, dst, src, |m|) = chacha_crypt(..., 20); a size_t length *)
Definition chacha20_crypt_spec :=
  DECLARE _chacha20_crypt
  WITH ssh: share, state: val, st: list int, dsh: share, dst: val, msh: share, src: val, m: list byte
  PRE [ tptr t_chacha_state, tptr tuchar, tptr tuchar, tulong ]
    PROP (writable_share ssh; writable_share dsh; readable_share msh; Zlength st = 16;
          Zlength m <= Int64.max_unsigned)
    PARAMS (state; dst; src; Vlong (Int64.repr (Zlength m)))
    SEP (data_at ssh t_chacha_state (map Vint st) state; data_at_ dsh (tarray tuchar (Zlength m)) dst;
         prim_bytes msh m src)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at ssh t_chacha_state (map Vint (chacha_advance st (chacha_nblocks (Zlength m)))) state;
         data_at dsh (tarray tuchar (Zlength m)) (map Vubyte (chacha_xor 10 st m)) dst;
         prim_bytes msh m src).

(* chacha_load_key(k, in): the 8 little-endian words of the 32-byte key *)
Definition chacha_load_key_spec :=
  DECLARE _chacha_load_key
  WITH ksh: share, kp: val, ish: share, ip: val, key: list byte
  PRE [ tptr tuint, tptr tuchar ]
    PROP (writable_share ksh; readable_share ish; Zlength key = 32)
    PARAMS (kp; ip)
    SEP (data_at_ ksh (tarray tuint 8) kp; data_at ish (tarray tuchar 32) (map Vubyte key) ip)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at ksh (tarray tuint 8) (map Vint (le32_words 8 key)) kp;
         data_at ish (tarray tuchar 32) (map Vubyte key) ip).

(* xchacha_init(state, key, nonce): the XChaCha20 state *)
Definition xchacha_init_spec :=
  DECLARE _xchacha_init
  WITH sh: share, state: val, ksh: share, kp: val, key: list byte, nsh: share, np: val, nonce: list byte
  PRE [ tptr t_chacha_state, tptr tuchar, tptr tuchar ]
    PROP (writable_share sh; readable_share ksh; readable_share nsh; Zlength key = 32; Zlength nonce = 24)
    PARAMS (state; kp; np)
    SEP (data_at_ sh t_chacha_state state; data_at ksh (tarray tuchar 32) (map Vubyte key) kp;
         data_at nsh (tarray tuchar 24) (map Vubyte nonce) np)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_chacha_state (map Vint (xaead_st key nonce)) state;
         data_at ksh (tarray tuchar 32) (map Vubyte key) kp;
         data_at nsh (tarray tuchar 24) (map Vubyte nonce) np).

(* __chacha20poly1305_encrypt(dst, src, |m|, ad, |a|, state): dst = aead_enc_st st a m; state zeroized *)
Definition __chacha20poly1305_encrypt_spec :=
  DECLARE ___chacha20poly1305_encrypt
  WITH dsh: share, dst: val, ssh: share, src: val, m: list byte, ash: share, ad: val, a: list byte,
       csh: share, state: val, st: list int, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tptr t_chacha_state ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; writable_share csh;
          Zlength m <= Int.max_unsigned; Zlength a <= Int.max_unsigned; Zlength st = 16)
    PARAMS (dst; src; Vlong (Int64.repr (Zlength m)); ad; Vlong (Int64.repr (Zlength a)); state)
    GLOBALS (gv)
    SEP (data_at_ dsh (tarray tuchar (Zlength m + 16)) dst; prim_bytes ssh m src; prim_bytes ash a ad;
         data_at csh t_chacha_state (map Vint st) state; zero_page gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at dsh (tarray tuchar (Zlength m + 16)) (map Vubyte (aead_enc_st st a m)) dst;
         prim_bytes ssh m src; prim_bytes ash a ad;
         data_at_ csh t_chacha_state state; zero_page gv).

(* __chacha20poly1305_decrypt(dst, src, |c|, ad, |a|, state) *)
Definition __chacha20poly1305_decrypt_spec :=
  DECLARE ___chacha20poly1305_decrypt
  WITH dsh: share, dst: val, old: list val, ssh: share, src: val, c: list byte, ash: share, ad: val,
       a: list byte, csh: share, state: val, st: list int, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tptr t_chacha_state ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; writable_share csh;
          Zlength c <= Int.max_unsigned; Zlength a <= Int.max_unsigned; Zlength st = 16;
          Zlength old = Z.max 0 (Zlength c - 16))
    PARAMS (dst; src; Vlong (Int64.repr (Zlength c)); ad; Vlong (Int64.repr (Zlength a)); state)
    GLOBALS (gv)
    SEP (data_at dsh (tarray tuchar (Zlength old)) old dst; prim_bytes ssh c src; prim_bytes ash a ad;
         data_at csh t_chacha_state (map Vint st) state; zero_page gv)
  POST [ tbool ]
    PROP ()
    RETURN (Val.of_bool (match aead_dec_st st a c with Some _ => true | None => false end))
    SEP (data_at dsh (tarray tuchar (Zlength old))
           (match aead_dec_st st a c with Some pt => map Vubyte pt | None => old end) dst;
         prim_bytes ssh c src; prim_bytes ash a ad;
         data_at_ csh t_chacha_state state; zero_page gv).

End AeadSpecs.

Definition chacha20poly1305_encrypt_spec := @chacha20poly1305_encrypt_spec_of Chacha20poly1305.CS aead_enc.
Definition chacha20poly1305_decrypt_spec := @chacha20poly1305_decrypt_spec_of Chacha20poly1305.CS aead_dec.
Definition xchacha20poly1305_encrypt_spec := @xchacha20poly1305_encrypt_spec_of Chacha20poly1305.CS xaead_enc.
Definition xchacha20poly1305_decrypt_spec := @xchacha20poly1305_decrypt_spec_of Chacha20poly1305.CS xaead_dec.

(* ---------------------------------------------------------------------- *)
(* the piece                                                               *)
(* ---------------------------------------------------------------------- *)

(* the imports (= aead_imports of aead_piece.v) *)
Definition aead_imports_def (cs: compspecs) : funspecs :=
  [@WgNoise.proof.libc.spec.memcpy_spec cs; @WgNoise.proof.libc.spec.memset_spec cs;
   @memzero_explicit_spec cs; @get_unaligned_le32_spec cs; @crypto_memneq_spec cs].

Definition aead_G_def : funspecs :=
  [__crypto_xor_spec;
   crypto_xor_cpy_spec; chacha_crypt_generic_spec; chacha_crypt_spec; hchacha_block_spec;
   rol32_spec; put_unaligned_le32_spec; chacha_zeroize_state_spec; chacha_permute_spec;
   chacha_block_generic_spec; hchacha_block_generic_spec;
   poly1305_core_setkey_spec; poly1305_core_blocks_spec; poly1305_core_emit_spec;
   poly1305_core_init_spec; poly1305_block_init_generic_spec; poly1305_blocks_generic_spec;
   poly1305_emit_generic_spec; poly1305_init_spec; poly1305_update_spec; poly1305_final_spec;
   put_unaligned_le64_spec; chacha_init_consts_spec; chacha_init_spec; chacha20_crypt_spec;
   chacha_load_key_spec; xchacha_init_spec; __chacha20poly1305_encrypt_spec; __chacha20poly1305_decrypt_spec;
   chacha20poly1305_encrypt_spec; chacha20poly1305_decrypt_spec;
   xchacha20poly1305_encrypt_spec; xchacha20poly1305_decrypt_spec].
