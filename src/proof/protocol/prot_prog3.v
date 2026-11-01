(* the context of the protocol piece's body proofs: its imports
   prot_imports3 and its specifications prot_G3 (= prot_G_list of prot_specs3.v, in protocol_idents order).

   Imports:
   - QuickProof.Env (malloc, free, the nondet functions), at the world's compspecs CSw;
   - libc piece: memcpy, memset, memcmp (polymorphic: at the importing unit's cs), calloc (CSw),
     __crypto_memneq, crypto_memneq;
   - BLAKE2s piece: blake2s_G3 (incl. memzero_explicit, get_unaligned_le32);
   - x25519 piece: curve25519_clamp_secret, curve25519 and curve25519_generate_public (templates at x25519);
   - AEAD piece: the encrypt templates of prim_api.v, the NULL-tolerant decrypt templates of prot_dec3.v. *)
Require WgNoise.proof.assembly.asm_env.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import QuickProof.Env.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.prims.prim_api.
Require Export WgNoise.proof.protocol.prot_dec3.
Require Export WgNoise.proof.protocol.prot_model3.
Require Export WgNoise.proof.protocol.prot_repr3.
Require Export WgNoise.proof.protocol.prot_specs3.
Require Export WgNoise.proof.protocol.prot_cs.

(* QuickProof.Env's functions without nondet_size: no protocol (or common.h, except draw_size / draw_steps)
   function calls it, and law handshake's program does not contain it (asm_piece_lift needs every import
   present in the whole program) *)
Definition env_specs_ns (CSw: compspecs) : funspecs :=
  [(_quickproof_malloc, @malloc_spec' CSw); (_quickproof_free, @free_spec' CSw);
   nondet_u8_spec; nondet_u32_spec; asm_env.nondet_bytes_spec].

Section Prog.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

Definition prot_imports3 (cs: compspecs) : funspecs :=
  env_specs_ns CSw ++
  [@memcpy_spec cs; @memset_spec cs; @memcmp_spec cs; @calloc_spec CSw;
   @memzero_explicit_spec cs; @crypto_memneq_spec cs; @__crypto_memneq_spec cs;
   @curve25519_clamp_secret_spec cs;
   @curve25519_spec_of cs x25519; @curve25519_generate_public_spec_of cs x25519;
   @chacha20poly1305_encrypt_spec_of cs aead_enc; @chacha20poly1305_decrypt_spec_of3 cs aead_dec;
   @xchacha20poly1305_encrypt_spec_of cs xaead_enc; @xchacha20poly1305_decrypt_spec_of3 cs xaead_dec] ++
  blake2s_G3.

Definition prot_G3 : funspecs := prot_G_list x25519 aead_enc aead_dec xaead_enc xaead_dec CSw.

(* the function context of a body proof in unit u *)
Definition Gprot3 (cs: compspecs) : funspecs := prot_imports3 cs ++ prot_G3.

End Prog.
