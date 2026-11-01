(* the specifications of the AEAD piece for the new contract.

   aead_spec.v with these changes:
   - poly1305_update: ANY chunk.  poly1305_update_spec3 is aead_spec.v's poly1305_update_spec, which
     now has the series' signature (size_t nbytes, any length; series patch P22);
   - chacha_crypt_generic, chacha_crypt, chacha20_crypt (series patch P23): size_t lengths for the
     latter two, and for all three a NULL-tolerant destination `prim_out dsh v dst` (prot_dec3.v: emp when
     empty, any pointer): __chacha20poly1305_decrypt calls chacha20_crypt(state, NULL, src, 0) for an empty
     plaintext (noise.c's consume_response decrypts 16 bytes into NULL), and the series' chacha_crypt then calls
     chacha_crypt_generic(state, NULL, src, 0, 20), which touches nothing.  (an earlier P23 helper
     chacha20_crypt_long made no call for an empty message; it and poly1305_update_long are gone.)  These are
     funspec_sub of aead_spec.v's (data_at_ destination), so the earlier bodies still lift;
   - __chacha20poly1305_encrypt/decrypt and the four entry points: lengths of message and associated data
     up to 2^64 - 1 (encrypt: |m| + 16 <= 2^64 - 1), instead of 2^32 - 1.
     PROP; aead_G3 thus covers the templates by funspec_sub.
   Every other entry is aead_spec.v's.  aead_G3 is THE specification list of the piece (aead3_ok's G):
   its identifiers are wg3_iface.aead_idents3, in that order.

   A body proved in against aead_imports_def U.CS ++ aead_G_def lifts to aead_imports3 U.CS ++ aead_G3
   (every aead_G_def entry has an entry of aead_G3 that is funspec_sub of it). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.chacha.code WgNoise.chacha_block.code WgNoise.poly1305.code WgNoise.poly1305_donna32.code
        WgNoise.chacha20poly1305.code WgNoise.shim.code.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Export WgNoise.proof.aead.aead_model.
Require Export WgNoise.proof.aead.aead_spec.
Require Import WgNoise.proof.common.wg3_iface.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* poly1305.c: poly1305_update for any chunk (P22)                         *)
(* ---------------------------------------------------------------------- *)

Section Poly1305Specs3.
#[local] Existing Instance Poly1305.CS.

(* poly1305_update(desc, src, |data|): ANY chunk of ANY size_t length (empty included); the same
   specification as aead_spec.poly1305_update_spec (series patch P22) *)
Definition poly1305_update_spec3 := poly1305_update_spec.

End Poly1305Specs3.

(* ---------------------------------------------------------------------- *)
(* chacha.c (series patch P23): NULL-tolerant destination; size_t length  *)
(* ---------------------------------------------------------------------- *)

Section ChachaSpecs3.
#[local] Existing Instance Chacha.CS.

(* chacha_crypt_generic(state, dst, src, |m|, nrounds) (unchanged code, unsigned int length) *)
Definition chacha_crypt_generic_spec3 :=
  DECLARE _chacha_crypt_generic
  WITH ssh: share, state: val, st: list int, dsh: share, dst: val, msh: share, src: val, m: list byte,
       nr: Z
  PRE [ tptr t_chacha_state, tptr tuchar, tptr tuchar, tuint, tint ]
    PROP (writable_share ssh; writable_share dsh; readable_share msh; Zlength st = 16;
          Zlength m <= Int.max_unsigned; nr = 20 \/ nr = 12)
    PARAMS (state; dst; src; Vint (Int.repr (Zlength m)); Vint (Int.repr nr))
    SEP (data_at ssh t_chacha_state (map Vint st) state; prim_out dsh (Zrepeat Vundef (Zlength m)) dst;
         prim_bytes msh m src)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at ssh t_chacha_state (map Vint (chacha_advance st (chacha_nblocks (Zlength m)))) state;
         prim_out dsh (map Vubyte (chacha_xor (Z.to_nat (nr / 2)) st m)) dst;
         prim_bytes msh m src).

(* chacha_crypt(state, dst, src, |m|, nrounds): ANY size_t length (chunks of round_down(UINT_MAX, 64) bytes) *)
Definition chacha_crypt_spec3 :=
  DECLARE _chacha_crypt
  WITH ssh: share, state: val, st: list int, dsh: share, dst: val, msh: share, src: val, m: list byte,
       nr: Z
  PRE [ tptr t_chacha_state, tptr tuchar, tptr tuchar, tulong, tint ]
    PROP (writable_share ssh; writable_share dsh; readable_share msh; Zlength st = 16;
          Zlength m <= Int64.max_unsigned; nr = 20 \/ nr = 12)
    PARAMS (state; dst; src; Vlong (Int64.repr (Zlength m)); Vint (Int.repr nr))
    SEP (data_at ssh t_chacha_state (map Vint st) state; prim_out dsh (Zrepeat Vundef (Zlength m)) dst;
         prim_bytes msh m src)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at ssh t_chacha_state (map Vint (chacha_advance st (chacha_nblocks (Zlength m)))) state;
         prim_out dsh (map Vubyte (chacha_xor (Z.to_nat (nr / 2)) st m)) dst;
         prim_bytes msh m src).

End ChachaSpecs3.

(* ---------------------------------------------------------------------- *)
(* chacha20poly1305.c                                                      *)
(* ---------------------------------------------------------------------- *)

Section AeadSpecs3.
#[local] Existing Instance Chacha20poly1305.CS.

(* chacha20_crypt(state, dst, src, |m|) = chacha_crypt(..., 20): ANY size_t length, NULL-tolerant destination *)
Definition chacha20_crypt_spec3 :=
  DECLARE _chacha20_crypt
  WITH ssh: share, state: val, st: list int, dsh: share, dst: val, msh: share, src: val, m: list byte
  PRE [ tptr t_chacha_state, tptr tuchar, tptr tuchar, tulong ]
    PROP (writable_share ssh; writable_share dsh; readable_share msh; Zlength st = 16;
          Zlength m <= Int64.max_unsigned)
    PARAMS (state; dst; src; Vlong (Int64.repr (Zlength m)))
    SEP (data_at ssh t_chacha_state (map Vint st) state; prim_out dsh (Zrepeat Vundef (Zlength m)) dst;
         prim_bytes msh m src)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at ssh t_chacha_state (map Vint (chacha_advance st (chacha_nblocks (Zlength m)))) state;
         prim_out dsh (map Vubyte (chacha_xor 10 st m)) dst;
         prim_bytes msh m src).

(* __chacha20poly1305_encrypt(dst, src, |m|, ad, |a|, state): dst = aead_enc_st st a m; state zeroized *)
Definition __chacha20poly1305_encrypt_spec3 :=
  DECLARE ___chacha20poly1305_encrypt
  WITH dsh: share, dst: val, ssh: share, src: val, m: list byte, ash: share, ad: val, a: list byte,
       csh: share, state: val, st: list int, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tptr t_chacha_state ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; writable_share csh;
          Zlength m + 16 <= Int64.max_unsigned; Zlength a <= Int64.max_unsigned; Zlength st = 16)
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
Definition __chacha20poly1305_decrypt_spec3 :=
  DECLARE ___chacha20poly1305_decrypt
  WITH dsh: share, dst: val, old: list val, ssh: share, src: val, c: list byte, ash: share, ad: val,
       a: list byte, csh: share, state: val, st: list int, gv: globals
  PRE [ tptr tuchar, tptr tuchar, tulong, tptr tuchar, tulong, tptr t_chacha_state ]
    PROP (writable_share dsh; readable_share ssh; readable_share ash; writable_share csh;
          Zlength c <= Int64.max_unsigned; Zlength a <= Int64.max_unsigned; Zlength st = 16;
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

(* the four entry points: the templates of prim_api.v with lengths up to 2^64 - 1 *)
Definition chacha20poly1305_encrypt_spec3 :=
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

Definition chacha20poly1305_decrypt_spec3 :=
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

Definition xchacha20poly1305_encrypt_spec3 :=
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

Definition xchacha20poly1305_decrypt_spec3 :=
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

End AeadSpecs3.

(* ---------------------------------------------------------------------- *)
(* the piece                                                               *)
(* ---------------------------------------------------------------------- *)

(* THE specification list of the AEAD piece (the G of aead3_ok); identifiers: aead_idents3, in order *)
Definition aead_G3 : funspecs :=
  [__crypto_xor_spec;
   crypto_xor_cpy_spec; chacha_crypt_generic_spec3; chacha_crypt_spec3; hchacha_block_spec;
   rol32_spec; put_unaligned_le32_spec; chacha_zeroize_state_spec; chacha_permute_spec;
   chacha_block_generic_spec; hchacha_block_generic_spec;
   poly1305_core_setkey_spec; poly1305_core_blocks_spec; poly1305_core_emit_spec;
   poly1305_core_init_spec; poly1305_block_init_generic_spec; poly1305_blocks_generic_spec;
   poly1305_emit_generic_spec; poly1305_init_spec; poly1305_update_spec3; poly1305_final_spec;
   put_unaligned_le64_spec; chacha_init_consts_spec; chacha_init_spec; chacha20_crypt_spec3;
   chacha_load_key_spec; xchacha_init_spec;
   __chacha20poly1305_encrypt_spec3; __chacha20poly1305_decrypt_spec3;
   chacha20poly1305_encrypt_spec3; chacha20poly1305_decrypt_spec3;
   xchacha20poly1305_encrypt_spec3; xchacha20poly1305_decrypt_spec3].

Lemma aead_G3_ids : map fst aead_G3 = aead_idents3.
Proof. reflexivity. Qed.

(* the piece with these specifications *)
Definition aead_piece3_ok : Prop := piece_ok aead_units3 aead_imports3 aead_G3.
