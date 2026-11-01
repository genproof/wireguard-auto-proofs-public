(* the interfaces between the subtrees of `suite`.

   `suite` is assembled (src/contracts/suite.v) from five parts, each proved in its own subtree:
     blake2s_part3  : blake2s3_ok /\ harness_safe prim_blake2s
     aead_part3     : aead3_ok /\ (blake2s3_ok -> harness_safe prim_aead /\ harness_safe prim_poly1305)
     x25519_part3   : x25519_ok3
     counter_part3  : blake2s3_ok -> aead3_ok -> x25519_ok3 -> harness_safe counter
     protocol_part3 : blake2s3_ok -> aead3_ok -> x25519_ok3 -> the 8 protocol laws
   The libc piece is proven (src/proof/libc/libc_piece.v, theorem libc_piece): Require it directly.

   The three lower pieces are stated with an existential specification list G: its identifiers are fixed
   (every function of the piece's units, minus the shared inlines owned elsewhere; a function nobody calls
   may get a vacuous specification), and G covers (asm_covers: funspec_sub entry by entry) the INTERFACE
   specifications other pieces import.  The owner may thus prove stronger specifications (e.g. the AEAD for
   any size_t length) without changing this file.

   the two static helpers of the old fix
   P23, chacha20_crypt_long and poly1305_update_long, are gone from chacha20poly1305.c (the AEAD passes its
   size_t lengths to chacha20_crypt / poly1305_update, which take a size_t now), so their identifiers left
   aead_idents3.  Nothing else changed here. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.prims.prim_api.
Require WgNoise.chacha.code WgNoise.chacha_block.code WgNoise.poly1305.code WgNoise.poly1305_donna32.code
        WgNoise.chacha20poly1305.code WgNoise.curve25519.code WgNoise.curve25519_fiat32.code
        WgNoise.shim.code.

(* ---------------------------------------------------------------------- *)
(* BLAKE2s: blake2s.c, the blake2s.h inlines, get_unaligned_le32, memzero_explicit (b2s_spec3.v)       *)
(* ---------------------------------------------------------------------- *)

Definition blake2s_units3 : list unit_ctx := [u_blake2s; u_cookie].

Definition blake2s3_ok : Prop :=
  exists G: funspecs,
    piece_ok blake2s_units3 blake2s_imports3 G /\
    map fst G = map fst blake2s_G3 /\
    asm_covers G blake2s_G3.

(* ---------------------------------------------------------------------- *)
(* ChaCha20, Poly1305, the AEADs: chacha.c, chacha-block-generic.c, poly1305.c, poly1305-donna32.c,     *)
(* chacha20poly1305.c (minus the shared inlines), the shim's __crypto_xor                                *)
(* ---------------------------------------------------------------------- *)

Definition aead_units3 : list unit_ctx :=
  [u_chacha; u_chacha_block; u_poly1305; u_poly1305_donna32; u_chacha20poly1305; u_shim].

Definition aead_imports3 (cs: compspecs) : funspecs :=
  [@memcpy_spec cs; @memset_spec cs; @memzero_explicit_spec cs; @get_unaligned_le32_spec cs;
   @crypto_memneq_spec cs].

Definition aead_idents3 : list ident :=
  [WgNoise.shim.code.___crypto_xor;
   WgNoise.chacha.code._crypto_xor_cpy; WgNoise.chacha.code._chacha_crypt_generic;
   WgNoise.chacha.code._chacha_crypt; WgNoise.chacha.code._hchacha_block;
   WgNoise.chacha_block.code._rol32; WgNoise.chacha_block.code._put_unaligned_le32;
   WgNoise.chacha_block.code._chacha_zeroize_state; WgNoise.chacha_block.code._chacha_permute;
   WgNoise.chacha_block.code._chacha_block_generic; WgNoise.chacha_block.code._hchacha_block_generic;
   WgNoise.poly1305_donna32.code._poly1305_core_setkey; WgNoise.poly1305_donna32.code._poly1305_core_blocks;
   WgNoise.poly1305_donna32.code._poly1305_core_emit;
   WgNoise.poly1305.code._poly1305_core_init; WgNoise.poly1305.code._poly1305_block_init_generic;
   WgNoise.poly1305.code._poly1305_blocks_generic; WgNoise.poly1305.code._poly1305_emit_generic;
   WgNoise.poly1305.code._poly1305_init; WgNoise.poly1305.code._poly1305_update;
   WgNoise.poly1305.code._poly1305_final;
   WgNoise.chacha20poly1305.code._put_unaligned_le64; WgNoise.chacha20poly1305.code._chacha_init_consts;
   WgNoise.chacha20poly1305.code._chacha_init; WgNoise.chacha20poly1305.code._chacha20_crypt;
   WgNoise.chacha20poly1305.code._chacha_load_key; WgNoise.chacha20poly1305.code._xchacha_init;
   WgNoise.chacha20poly1305.code.___chacha20poly1305_encrypt;
   WgNoise.chacha20poly1305.code.___chacha20poly1305_decrypt;
   WgNoise.chacha20poly1305.code._chacha20poly1305_encrypt;
   WgNoise.chacha20poly1305.code._chacha20poly1305_decrypt;
   WgNoise.chacha20poly1305.code._xchacha20poly1305_encrypt;
   WgNoise.chacha20poly1305.code._xchacha20poly1305_decrypt].

(* the AEAD entry points as the protocol imports them (prim_api.v templates, lengths below 2^32) *)
Definition aead_iface3
  (enc: list byte -> Z -> list byte -> list byte -> list byte)
  (dec: list byte -> Z -> list byte -> list byte -> option (list byte))
  (xenc: list byte -> list byte -> list byte -> list byte -> list byte)
  (xdec: list byte -> list byte -> list byte -> list byte -> option (list byte)) : funspecs :=
  [@chacha20poly1305_encrypt_spec_of Chacha20poly1305.CS enc;
   @chacha20poly1305_decrypt_spec_of Chacha20poly1305.CS dec;
   @xchacha20poly1305_encrypt_spec_of Chacha20poly1305.CS xenc;
   @xchacha20poly1305_decrypt_spec_of Chacha20poly1305.CS xdec].

Definition aead3_ok : Prop :=
  exists (G: funspecs)
         (enc: list byte -> Z -> list byte -> list byte -> list byte)
         (dec: list byte -> Z -> list byte -> list byte -> option (list byte))
         (xenc: list byte -> list byte -> list byte -> list byte -> list byte)
         (xdec: list byte -> list byte -> list byte -> list byte -> option (list byte)),
    aead_props enc dec /\ xaead_props xenc xdec /\
    piece_ok aead_units3 aead_imports3 G /\
    map fst G = aead_idents3 /\
    asm_covers G (aead_iface3 enc dec xenc xdec).

(* ---------------------------------------------------------------------- *)
(* Curve25519: curve25519.c, curve25519-fiat32.c (minus the shared inlines), curve25519_clamp_secret     *)
(* ---------------------------------------------------------------------- *)

Definition x25519_units3 : list unit_ctx := [u_curve25519; u_curve25519_fiat32].

Definition x25519_imports3 (cs: compspecs) : funspecs :=
  [@memcpy_spec cs; @memset_spec cs; @memzero_explicit_spec cs; @get_unaligned_le32_spec cs;
   @crypto_memneq_spec cs].

Definition x25519_idents3 : list ident :=
  [WgNoise.curve25519_fiat32.code._curve25519_clamp_secret;
   WgNoise.curve25519_fiat32.code._fe_frombytes_impl; WgNoise.curve25519_fiat32.code._fe_frombytes;
   WgNoise.curve25519_fiat32.code._addcarryx_u25; WgNoise.curve25519_fiat32.code._addcarryx_u26;
   WgNoise.curve25519_fiat32.code._subborrow_u25; WgNoise.curve25519_fiat32.code._subborrow_u26;
   WgNoise.curve25519_fiat32.code._cmovznz32; WgNoise.curve25519_fiat32.code._fe_freeze;
   WgNoise.curve25519_fiat32.code._fe_tobytes; WgNoise.curve25519_fiat32.code._fe_copy;
   WgNoise.curve25519_fiat32.code._fe_copy_lt; WgNoise.curve25519_fiat32.code._fe_0;
   WgNoise.curve25519_fiat32.code._fe_1; WgNoise.curve25519_fiat32.code._fe_add_impl;
   WgNoise.curve25519_fiat32.code._fe_add; WgNoise.curve25519_fiat32.code._fe_sub_impl;
   WgNoise.curve25519_fiat32.code._fe_sub; WgNoise.curve25519_fiat32.code._fe_mul_impl;
   WgNoise.curve25519_fiat32.code._fe_mul_ttt; WgNoise.curve25519_fiat32.code._fe_mul_tlt;
   WgNoise.curve25519_fiat32.code._fe_mul_tll; WgNoise.curve25519_fiat32.code._fe_sqr_impl;
   WgNoise.curve25519_fiat32.code._fe_sq_tl; WgNoise.curve25519_fiat32.code._fe_sq_tt;
   WgNoise.curve25519_fiat32.code._fe_loose_invert; WgNoise.curve25519_fiat32.code._fe_invert;
   WgNoise.curve25519_fiat32.code._fe_cswap; WgNoise.curve25519_fiat32.code._fe_mul_121666_impl;
   WgNoise.curve25519_fiat32.code._fe_mul121666; WgNoise.curve25519_fiat32.code._curve25519_generic;
   WgNoise.curve25519.code._curve25519_arch; WgNoise.curve25519.code._curve25519_base_arch;
   WgNoise.curve25519.code._curve25519; WgNoise.curve25519.code._curve25519_generate_public].

(* the Curve25519 entry points as the protocol and the harness models import them (prim_api.v templates) *)
Definition x25519_iface3 (x: list byte -> list byte -> list byte) : funspecs :=
  [@curve25519_generic_spec_of Curve25519Fiat32.CS x;
   @curve25519_spec_of Curve25519.CS x;
   @curve25519_generate_public_spec_of Curve25519.CS x;
   @curve25519_clamp_secret_spec Curve25519Fiat32.CS].

Definition x25519_ok3 : Prop :=
  exists (G: funspecs) (x: list byte -> list byte -> list byte),
    x25519_props x /\
    piece_ok x25519_units3 x25519_imports3 G /\
    map fst G = x25519_idents3 /\
    asm_covers G (x25519_iface3 x).
