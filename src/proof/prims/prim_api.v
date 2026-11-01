(* The primitive API: the specifications of the functions that cross the boundary between the primitives
   (Curve25519, ChaCha20-Poly1305, XChaCha20-Poly1305, crypto_memneq) and their clients (noise.c, cookie.c,
   curve25519.c, chacha20poly1305.c, the harnesses' model m_* and prim_* laws).

   The specifications are TEMPLATES, parameterised by the functional model of the primitive:
   - `x25519: list byte -> list byte -> list byte`      (scalar, point: 32 bytes each -> 32 bytes)
   - `aead_enc: key -> nonce(Z, u64) -> ad -> msg -> ct||tag`, `aead_dec: key -> nonce -> ad -> ct||tag ->
     option msg` (ChaCha20-Poly1305, the kernel's 64-bit nonce)
   - `xaead_enc` / `xaead_dec`: the same with a 24-byte nonce (list byte) (XChaCha20-Poly1305).
   The primitive proofs (units Curve25519Fiat32, Curve25519, Chacha20poly1305 ...) define the concrete
   functions (their functional models) and prove the bodies against the templates instantiated with them.
   The clients (noise.c, cookie.c, harness models) prove their bodies for ANY functions satisfying the
   properties they need (see `aead_props` below), in a Section; the assembly instantiates.

   Conventions: byte buffers are `map Vubyte bs`; the specifications are polymorphic in the compspecs (only
   byte arrays are involved); an input of length 0 is `prim_bytes` = emp (its pointer may be anything, NULL
   included: malloc(0) and `msg + len` pointers). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.curve25519.code.
Require WgNoise.chacha20poly1305.code.
Require WgNoise.curve25519_fiat32.code.

Local Open Scope Z_scope.

Definition _curve25519_generic : ident := WgNoise.curve25519.code._curve25519_generic.
Definition _curve25519 : ident := WgNoise.curve25519.code._curve25519.
Definition _curve25519_generate_public : ident := WgNoise.curve25519.code._curve25519_generate_public.
Definition _curve25519_null_point : ident := WgNoise.curve25519.code._curve25519_null_point.
Definition _curve25519_base_point : ident := WgNoise.curve25519.code._curve25519_base_point.
Definition _crypto_memneq : ident := WgNoise.curve25519.code._crypto_memneq.
Definition ___crypto_memneq : ident := WgNoise.curve25519.code.___crypto_memneq.
Definition _chacha20poly1305_encrypt : ident := WgNoise.chacha20poly1305.code._chacha20poly1305_encrypt.
Definition _chacha20poly1305_decrypt : ident := WgNoise.chacha20poly1305.code._chacha20poly1305_decrypt.
Definition _xchacha20poly1305_encrypt : ident := WgNoise.chacha20poly1305.code._xchacha20poly1305_encrypt.
Definition _xchacha20poly1305_decrypt : ident := WgNoise.chacha20poly1305.code._xchacha20poly1305_decrypt.
Definition _quickproof_zero_page : ident := WgNoise.chacha20poly1305.code._quickproof_zero_page.
Definition _curve25519_clamp_secret : ident := WgNoise.curve25519_fiat32.code._curve25519_clamp_secret.

(* curve25519_clamp_secret: secret[0] &= 248; secret[31] = (secret[31] & 127) | 64 *)
Definition clamp (s: list byte) : list byte :=
  upd_Znth 31 (upd_Znth 0 s (Byte.and (Znth 0 s) (Byte.repr 248)))
    (Byte.or (Byte.and (Znth 31 s) (Byte.repr 127)) (Byte.repr 64)).

Definition zeros32 : list byte := Zrepeat Byte.zero 32.
Definition basepoint9 : list byte := Byte.repr 9 :: Zrepeat Byte.zero 31.

(* __crypto_memneq's value: the OR of the byte differences (a ^ b), as an unsigned long *)
Fixpoint memneq_Z (a b: list byte) : Z :=
  match a, b with
  | x :: a', y :: b' => Z.lor (Z.lxor (Byte.unsigned x) (Byte.unsigned y)) (memneq_Z a' b')
  | _, _ => 0
  end.

(* crypto_memneq's value: 0 iff equal, else 1 *)
Definition memneq_bool (a b: list byte) : bool :=
  if list_eq_dec Byte.eq_dec a b then false else true.

(* The functional-model properties the clients may rely on.  The primitive proofs prove them for their
   concrete functions.  Clients: add what you need HERE (one place), with a note in the *)
Record aead_props
  (enc: list byte -> Z -> list byte -> list byte -> list byte)
  (dec: list byte -> Z -> list byte -> list byte -> option (list byte)) : Prop := {
  aead_enc_length: forall k n ad m, Zlength (enc k n ad m) = Zlength m + 16;
  aead_dec_enc: forall k n ad m, dec k n ad (enc k n ad m) = Some m;
  aead_dec_length: forall k n ad c m, dec k n ad c = Some m -> Zlength m = Zlength c - 16;
  aead_dec_short: forall k n ad c, Zlength c < 16 -> dec k n ad c = None
}.

Record xaead_props
  (enc: list byte -> list byte -> list byte -> list byte -> list byte)
  (dec: list byte -> list byte -> list byte -> list byte -> option (list byte)) : Prop := {
  xaead_enc_length: forall k n ad m, Zlength (enc k n ad m) = Zlength m + 16;
  xaead_dec_enc: forall k n ad m, dec k n ad (enc k n ad m) = Some m;
  xaead_dec_length: forall k n ad c m, dec k n ad c = Some m -> Zlength m = Zlength c - 16;
  xaead_dec_short: forall k n ad c, Zlength c < 16 -> dec k n ad c = None
}.

Definition x25519_props (x25519: list byte -> list byte -> list byte) : Prop :=
  forall s p, Zlength (x25519 s p) = 32.

Section Specs.
Context {cs: compspecs}.

(* an input buffer: nothing when empty (the pointer may then be anything) *)
Definition prim_bytes (sh: share) (bs: list byte) (p: val) : mpred :=
  if Z.eq_dec (Zlength bs) 0 then emp
  else data_at sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p.

(* the shim's zero page (const u8 quickproof_zero_page[64]), read by the AEAD *)
Definition zero_page (gv: globals) : mpred :=
  data_at Ers (tarray tuchar 64) (Zrepeat (Vubyte Byte.zero) 64) (gv _quickproof_zero_page).

(* curve25519.c's two static const points *)
Definition curve25519_globals (gv: globals) : mpred :=
  sepcon (data_at Ers (tarray tuchar 32) (map Vubyte zeros32) (gv _curve25519_null_point))
         (data_at Ers (tarray tuchar 32) (map Vubyte basepoint9) (gv _curve25519_base_point)).

(* ---------------------------------------------------------------------- *)
(* shim: __crypto_memneq, and the inline crypto_memneq of crypto/utils.h  *)
(* ---------------------------------------------------------------------- *)

Definition __crypto_memneq_spec :=
  DECLARE ___crypto_memneq
  WITH sh1: share, sh2: share, p1: val, p2: val, n: Z, a: list byte, b: list byte
  PRE [ tptr tvoid, tptr tvoid, tulong ]
    PROP (readable_share sh1; readable_share sh2; Zlength a = n; Zlength b = n; n <= Int64.max_unsigned)
    PARAMS (p1; p2; Vlong (Int64.repr n))
    SEP (data_at sh1 (tarray tuchar n) (map Vubyte a) p1; data_at sh2 (tarray tuchar n) (map Vubyte b) p2)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (memneq_Z a b)))
    SEP (data_at sh1 (tarray tuchar n) (map Vubyte a) p1; data_at sh2 (tarray tuchar n) (map Vubyte b) p2).

Definition crypto_memneq_spec :=
  DECLARE _crypto_memneq
  WITH sh1: share, sh2: share, p1: val, p2: val, n: Z, a: list byte, b: list byte
  PRE [ tptr tvoid, tptr tvoid, tulong ]
    PROP (readable_share sh1; readable_share sh2; Zlength a = n; Zlength b = n; n <= Int64.max_unsigned)
    PARAMS (p1; p2; Vlong (Int64.repr n))
    SEP (data_at sh1 (tarray tuchar n) (map Vubyte a) p1; data_at sh2 (tarray tuchar n) (map Vubyte b) p2)
  POST [ tint ]
    PROP () RETURN (Vint (if memneq_bool a b then Int.one else Int.zero))
    SEP (data_at sh1 (tarray tuchar n) (map Vubyte a) p1; data_at sh2 (tarray tuchar n) (map Vubyte b) p2).

(* ---------------------------------------------------------------------- *)
(* Curve25519                                                              *)
(* ---------------------------------------------------------------------- *)

(* the static inline curve25519_clamp_secret (include/crypto/curve25519.h; compiled into noise.c and
   curve25519-fiat32.c, identical Clight) *)
Definition curve25519_clamp_secret_spec :=
  DECLARE _curve25519_clamp_secret
  WITH sh: share, p: val, s: list byte
  PRE [ tptr tuchar ]
    PROP (writable_share sh; Zlength s = 32)
    PARAMS (p)
    SEP (data_at sh (tarray tuchar 32) (map Vubyte s) p)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh (tarray tuchar 32) (map Vubyte (clamp s)) p).

Section X25519.
Variable x25519: list byte -> list byte -> list byte.

(* curve25519_generic(out, scalar, point): out = x25519 scalar point; out disjoint from the inputs
   (scalar and point may be the same buffer only with two readable shares of it) *)
Definition curve25519_generic_spec_of :=
  DECLARE _curve25519_generic
  WITH osh: share, out: val, ssh: share, s: val, sc: list byte, psh: share, p: val, pt: list byte
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share osh; readable_share ssh; readable_share psh; Zlength sc = 32; Zlength pt = 32)
    PARAMS (out; s; p)
    SEP (data_at_ osh (tarray tuchar 32) out;
         data_at ssh (tarray tuchar 32) (map Vubyte sc) s; data_at psh (tarray tuchar 32) (map Vubyte pt) p)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at osh (tarray tuchar 32) (map Vubyte (x25519 sc pt)) out;
         data_at ssh (tarray tuchar 32) (map Vubyte sc) s; data_at psh (tarray tuchar 32) (map Vubyte pt) p).

(* curve25519(out, secret, basepoint): out = x25519 secret basepoint; returns true iff it is not all zero *)
Definition curve25519_spec_of :=
  DECLARE _curve25519
  WITH osh: share, out: val, ssh: share, s: val, sc: list byte, psh: share, p: val, pt: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share osh; readable_share ssh; readable_share psh; Zlength sc = 32; Zlength pt = 32)
    PARAMS (out; s; p) GLOBALS (gv)
    SEP (data_at_ osh (tarray tuchar 32) out;
         data_at ssh (tarray tuchar 32) (map Vubyte sc) s; data_at psh (tarray tuchar 32) (map Vubyte pt) p;
         curve25519_globals gv)
  POST [ tbool ]
    PROP ()
    RETURN (Val.of_bool (memneq_bool (x25519 sc pt) zeros32))
    SEP (data_at osh (tarray tuchar 32) (map Vubyte (x25519 sc pt)) out;
         data_at ssh (tarray tuchar 32) (map Vubyte sc) s; data_at psh (tarray tuchar 32) (map Vubyte pt) p;
         curve25519_globals gv).

(* curve25519_generate_public(pub, secret): false and pub untouched if secret is all zero; else
   pub = x25519 secret 9, true iff that is not all zero *)
Definition curve25519_generate_public_spec_of :=
  DECLARE _curve25519_generate_public
  WITH osh: share, out: val, old: list val, ssh: share, s: val, sc: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar ]
    PROP (writable_share osh; readable_share ssh; Zlength sc = 32; Zlength old = 32)
    PARAMS (out; s) GLOBALS (gv)
    SEP (data_at osh (tarray tuchar 32) old out; data_at ssh (tarray tuchar 32) (map Vubyte sc) s;
         curve25519_globals gv)
  POST [ tbool ]
    PROP ()
    RETURN (Val.of_bool (memneq_bool sc zeros32 && memneq_bool (x25519 sc basepoint9) zeros32))
    SEP (data_at osh (tarray tuchar 32)
           (if memneq_bool sc zeros32 then map Vubyte (x25519 sc basepoint9) else old) out;
         data_at ssh (tarray tuchar 32) (map Vubyte sc) s;
         curve25519_globals gv).

End X25519.

(* ---------------------------------------------------------------------- *)
(* ChaCha20-Poly1305 and XChaCha20-Poly1305                                *)
(* ---------------------------------------------------------------------- *)

(* Lengths: message and associated data below 2^32 in this interface.  dst is disjoint from every
   input. *)

Section AEAD.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* chacha20poly1305_encrypt(dst, src, |m|, ad, |ad|, nonce, key): dst[0..|m|+16) = aead_enc key nonce ad m *)
Definition chacha20poly1305_encrypt_spec_of :=
  DECLARE _chacha20poly1305_encrypt
  WITH dsh: share, dst: val, ssh: share, src: val, m: list byte, ash: share, ad: val, a: list byte,
       nonce: Z, ksh: share, key: val, k: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tulong, tptr tuchar ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; readable_share ksh;
          Zlength m <= Int.max_unsigned; Zlength a <= Int.max_unsigned; 0 <= nonce <= Int64.max_unsigned;
          Zlength k = 32)
    PARAMS (dst; src; Vlong (Int64.repr (Zlength m)); ad; Vlong (Int64.repr (Zlength a));
            Vlong (Int64.repr nonce); key) GLOBALS (gv)
    SEP (data_at_ dsh (tarray tuchar (Zlength m + 16)) dst; prim_bytes ssh m src; prim_bytes ash a ad;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at dsh (tarray tuchar (Zlength m + 16)) (map Vubyte (aead_enc k nonce a m)) dst;
         prim_bytes ssh m src; prim_bytes ash a ad;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv).

(* chacha20poly1305_decrypt(dst, src, |c|, ad, |ad|, nonce, key): dst has max(|c| - 16, 0) bytes (any prior
   contents `old`, Vundef allowed); true and dst = the plaintext when aead_dec gives Some; false and dst
   unchanged otherwise *)
Definition chacha20poly1305_decrypt_spec_of :=
  DECLARE _chacha20poly1305_decrypt
  WITH dsh: share, dst: val, old: list val, ssh: share, src: val, c: list byte, ash: share, ad: val,
       a: list byte, nonce: Z, ksh: share, key: val, k: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tulong, tptr tuchar ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; readable_share ksh;
          Zlength c <= Int.max_unsigned; Zlength a <= Int.max_unsigned; 0 <= nonce <= Int64.max_unsigned;
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

Definition xchacha20poly1305_encrypt_spec_of :=
  DECLARE _xchacha20poly1305_encrypt
  WITH dsh: share, dst: val, ssh: share, src: val, m: list byte, ash: share, ad: val, a: list byte,
       nsh: share, np: val, nonce: list byte, ksh: share, key: val, k: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tptr tuchar, tptr tuchar ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; readable_share nsh; readable_share ksh;
          Zlength m <= Int.max_unsigned; Zlength a <= Int.max_unsigned; Zlength nonce = 24; Zlength k = 32)
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

Definition xchacha20poly1305_decrypt_spec_of :=
  DECLARE _xchacha20poly1305_decrypt
  WITH dsh: share, dst: val, old: list val, ssh: share, src: val, c: list byte, ash: share, ad: val,
       a: list byte, nsh: share, np: val, nonce: list byte, ksh: share, key: val, k: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tptr tuchar, tptr tuchar ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; readable_share nsh; readable_share ksh;
          Zlength c <= Int.max_unsigned; Zlength a <= Int.max_unsigned; Zlength nonce = 24;
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

End AEAD.

End Specs.
