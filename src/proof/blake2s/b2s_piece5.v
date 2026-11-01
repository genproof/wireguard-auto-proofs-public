(* The BLAKE2s piece of the short handshake laws: every function of blake2s_G5 (b2s_prog5.v) against its
   specification, blake2s.c's functions in the unit blake2s with context b2s_Gprog5, the blake2s.h inlines on
   noise.c's copies with context b2s_Gprog5_noise.  The proofs are those of the b2s_*3.v body files, run
   against these contexts. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.blake2s.b2s_prog5.
Require WgNoise.proof.blake2s.b2s_small_body5 WgNoise.proof.blake2s.b2s_compress_body5
        WgNoise.proof.blake2s.b2s_update_body5 WgNoise.proof.blake2s.b2s_final_body5
        WgNoise.proof.blake2s.b2s_inline_body5.

Local Ltac b2s_body5 := first
  [ assumption
  | exact b2s_compress_body5.body_blake2s_compress_generic
  | exact b2s_update_body5.body_blake2s_update3
  | exact b2s_final_body5.body_blake2s_final ].

Theorem blake2s_piece5 : piece_ok [u_blake2s; u_noise] blake2s_imports3 blake2s_G5.
Proof.
  destruct b2s_small_body5.b2s_small_bodies as [Hror [Hinc [Hlast [Hle32 Hmz]]]].
  destruct b2s_inline_body5.b2s_inline_bodies5 as [Hinit0 [Hinit Hb2s]].
  split; [repeat constructor; simpl; intuition discriminate |].
  change (blake2s_imports3 Blake2s.CS ++ blake2s_G5) with b2s_Gprog5 in *.
  change (blake2s_imports3 Noise.CS ++ blake2s_G5) with b2s_Gprog5_noise in *.
  repeat constructor.
  all: first [ exists u_blake2s; split; [simpl; auto |]; eexists; split; [reflexivity |]; b2s_body5
             | exists u_noise; split; [simpl; auto |]; eexists; split; [reflexivity |]; b2s_body5 ].
Qed.
