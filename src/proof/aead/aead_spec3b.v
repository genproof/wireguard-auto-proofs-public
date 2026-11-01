(* the AEAD piece with NULL-tolerant decryption.

   aead_G3b = aead_spec3.aead_G3 with three entries replaced: the destination of decryption is
   `prim_out dsh v dst` (prot_dec3.v): emp when empty, any pointer (NULL included); noise.c's consume_response
   calls chacha20poly1305_decrypt(NULL, src, 16, ...).  Everything else is aead_spec3's.  (aead_G3's chacha20_crypt /
   chacha_crypt / chacha_crypt_generic take a NULL-tolerant destination themselves.)
   - __chacha20poly1305_decrypt_spec3b, chacha20poly1305_decrypt_spec3b, xchacha20poly1305_decrypt_spec3b:
     `prim_out dsh old dst` -> `prim_out dsh (match .. with Some pt => map Vubyte pt | None => old end) dst`. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.chacha20poly1305.code.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.common.wg3_iface.
Require Export WgNoise.proof.aead.aead_spec3.

Local Open Scope Z_scope.

Section AeadSpecs3b.
#[local] Existing Instance Chacha20poly1305.CS.

Definition __chacha20poly1305_decrypt_spec3b :=
  DECLARE ___chacha20poly1305_decrypt
  WITH dsh: share, dst: val, old: list val, ssh: share, src: val, c: list byte, ash: share, ad: val,
       a: list byte, csh: share, state: val, st: list int, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tptr t_chacha_state ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; writable_share csh;
          Zlength c <= Int64.max_unsigned; Zlength a <= Int64.max_unsigned; Zlength st = 16;
          Zlength old = Z.max 0 (Zlength c - 16))
    PARAMS (dst; src; Vlong (Int64.repr (Zlength c)); ad; Vlong (Int64.repr (Zlength a)); state)
    GLOBALS (gv)
    SEP (prim_out dsh old dst; prim_bytes ssh c src; prim_bytes ash a ad;
         data_at csh t_chacha_state (map Vint st) state; zero_page gv)
  POST [ tbool ]
    PROP ()
    RETURN (Val.of_bool (match aead_dec_st st a c with Some _ => true | None => false end))
    SEP (prim_out dsh (match aead_dec_st st a c with Some pt => map Vubyte pt | None => old end) dst;
         prim_bytes ssh c src; prim_bytes ash a ad;
         data_at_ csh t_chacha_state state; zero_page gv).

Definition chacha20poly1305_decrypt_spec3b :=
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
    SEP (prim_out dsh old dst; prim_bytes ssh c src; prim_bytes ash a ad;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv)
  POST [ tbool ]
    PROP ()
    RETURN (Val.of_bool (match aead_dec k nonce a c with Some _ => true | None => false end))
    SEP (prim_out dsh (match aead_dec k nonce a c with Some pt => map Vubyte pt | None => old end) dst;
         prim_bytes ssh c src; prim_bytes ash a ad;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv).

Definition xchacha20poly1305_decrypt_spec3b :=
  DECLARE _xchacha20poly1305_decrypt
  WITH dsh: share, dst: val, old: list val, ssh: share, src: val, c: list byte, ash: share, ad: val,
       a: list byte, nsh: share, np: val, nonce: list byte, ksh: share, key: val, k: list byte, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tptr tuchar, tptr tuchar ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; readable_share nsh; readable_share ksh;
          Zlength c <= Int64.max_unsigned; Zlength a <= Int64.max_unsigned; Zlength nonce = 24;
          Zlength k = 32; Zlength old = Z.max 0 (Zlength c - 16))
    PARAMS (dst; src; Vlong (Int64.repr (Zlength c)); ad; Vlong (Int64.repr (Zlength a)); np; key)
    GLOBALS (gv)
    SEP (prim_out dsh old dst; prim_bytes ssh c src; prim_bytes ash a ad;
         data_at nsh (tarray tuchar 24) (map Vubyte nonce) np;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv)
  POST [ tbool ]
    PROP ()
    RETURN (Val.of_bool (match xaead_dec k nonce a c with Some _ => true | None => false end))
    SEP (prim_out dsh (match xaead_dec k nonce a c with Some pt => map Vubyte pt | None => old end) dst;
         prim_bytes ssh c src; prim_bytes ash a ad;
         data_at nsh (tarray tuchar 24) (map Vubyte nonce) np;
         data_at ksh (tarray tuchar 32) (map Vubyte k) key; zero_page gv).

End AeadSpecs3b.

(* THE specification list of aead3b_ok's G: aead_G3 with the three NULL-tolerant decryption entries *)
Definition aead_G3b : funspecs :=
  [__crypto_xor_spec;
   crypto_xor_cpy_spec; chacha_crypt_generic_spec3; chacha_crypt_spec3; hchacha_block_spec;
   rol32_spec; put_unaligned_le32_spec; chacha_zeroize_state_spec; chacha_permute_spec;
   chacha_block_generic_spec; hchacha_block_generic_spec;
   poly1305_core_setkey_spec; poly1305_core_blocks_spec; poly1305_core_emit_spec;
   poly1305_core_init_spec; poly1305_block_init_generic_spec; poly1305_blocks_generic_spec;
   poly1305_emit_generic_spec; poly1305_init_spec; poly1305_update_spec3; poly1305_final_spec;
   put_unaligned_le64_spec; chacha_init_consts_spec; chacha_init_spec; chacha20_crypt_spec3;
   chacha_load_key_spec; xchacha_init_spec;
   __chacha20poly1305_encrypt_spec3; __chacha20poly1305_decrypt_spec3b;
   chacha20poly1305_encrypt_spec3; chacha20poly1305_decrypt_spec3b;
   xchacha20poly1305_encrypt_spec3; xchacha20poly1305_decrypt_spec3b].

Lemma aead_G3b_ids : map fst aead_G3b = aead_idents3.
Proof. reflexivity. Qed.
