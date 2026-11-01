(* The BLAKE2s piece for the per-law programs of the short handshake laws (hs_), which link noise.c but not
   cookie.c: blake2s_G3 without blake2s_init_key (defined only in cookie.c), the blake2s.h inlines being
   noise.c's copies (the same Clight functions as cookie.c's).  A body proved against b2s_Gprog3 cannot be
   used in such a program (its context names blake2s_init_key, which the program lacks), so the piece is
   proved again against these contexts (b2s_piece5.v), with the same specifications. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Export WgNoise.proof.libc.spec.
Require Export WgNoise.proof.blake2s.spec.
Require Export WgNoise.proof.blake2s.b2s_spec3.

Definition blake2s_G5 : funspecs :=
  [ror32_spec; blake2s_increment_counter_spec; blake2s_compress_generic_spec; blake2s_set_lastblock_spec;
   blake2s_update_spec3; blake2s_final_spec;
   __blake2s_init_spec; blake2s_init_spec; blake2s_spec3;
   @get_unaligned_le32_spec Blake2s.CS; @memzero_explicit_spec Blake2s.CS].

(* the context of a body proof in the unit blake2s (lib/crypto/blake2s.c) *)
Definition b2s_Gprog5 : funspecs := blake2s_imports3 Blake2s.CS ++ blake2s_G5.

(* the context of a body proof in the unit noise (the blake2s.h inlines, noise.c's copies) *)
Definition b2s_Gprog5_noise : funspecs := blake2s_imports3 Noise.CS ++ blake2s_G5.
