(* The context of the protocol piece v5's body proofs (prot_specs5.v): its imports prot_imports5 and its
   specifications prot_G5.  The imports are v4's (prot_imports3) without what the per-law programs of the
   hs_ laws lack: nondet_u8 (not called by any harness of four of them, and by no function of noise.c or the
   shim), the XChaCha20-Poly1305 templates (called only by cookie.c), and blake2s_init_key (cookie.c): the
   BLAKE2s piece is blake2s_G5 (b2s_prog5.v).  Every function named here is defined in each hs_ program, so
   a body proved in this context can be lifted into each of them (asm_lib.asm_piece_lift). *)
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
Require Import WgNoise.proof.blake2s.b2s_prog5.
Require Import WgNoise.proof.prims.prim_api.
Require Export WgNoise.proof.protocol.prot_dec3.
Require Export WgNoise.proof.protocol.prot_model3.
Require Export WgNoise.proof.protocol.prot_repr3.
Require Export WgNoise.proof.protocol4.prot_repr4.
Require Export WgNoise.proof.protocol4.prot_model4.
Require Export WgNoise.proof.protocol5.prot_repr5.
Require Export WgNoise.proof.protocol5.prot_specs5.
Require Export WgNoise.proof.protocol.prot_cs.

(* QuickProof.Env's functions that noise.c, the shim and libc call *)
Definition env_specs5 (CSw: compspecs) : funspecs :=
  [(_quickproof_malloc, @malloc_spec' CSw); (_quickproof_free, @free_spec' CSw);
   nondet_u32_spec; asm_env.nondet_bytes_spec].

Section Prog.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

Definition prot_imports5 (cs: compspecs) : funspecs :=
  env_specs5 CSw ++
  [@memcpy_spec cs; @memset_spec cs; @memcmp_spec cs; @calloc_spec CSw;
   @memzero_explicit_spec cs; @crypto_memneq_spec cs; @__crypto_memneq_spec cs;
   @curve25519_clamp_secret_spec cs;
   @curve25519_spec_of cs x25519; @curve25519_generate_public_spec_of cs x25519;
   @chacha20poly1305_encrypt_spec_of cs aead_enc; @chacha20poly1305_decrypt_spec_of3 cs aead_dec] ++
  blake2s_G5.

(* the function context of a body proof in unit u (Noise.CS or Shim.CS) *)
Definition Gprot5 (cs: compspecs) : funspecs := prot_imports5 cs ++ prot_G5 x25519 aead_enc aead_dec CSw.

End Prog.
