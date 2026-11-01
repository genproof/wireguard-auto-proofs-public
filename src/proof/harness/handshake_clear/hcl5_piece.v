(* law handshake_clear: the law's own piece = main's body. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_world.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_spec.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_defs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_main.

Theorem hcl5_piece :
  forall x25519, hcl5_hyps x25519 -> piece_ok [u_hcl5] (hcl5_imports x25519) hcl5_G.
Proof.
  intros x25519 HH. split.
  - repeat constructor; simpl; intuition discriminate.
  - constructor; [| constructor].
    exists u_hcl5. split; [left; reflexivity |].
    exists WgNoise.harness.x_handshake_clear.code.f_main. split; [reflexivity |].
    apply (hcl5_main_body x25519); exact HH.
Qed.
