(* law handshake_receive: the law's main piece = main's
   body (hrx5_main.v), at the world compspecs. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_main.

Theorem hrx5_mpiece : hrx5_mpiece_stmt.
Proof.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec Hx Ha Hxa. split.
  - repeat constructor; simpl; intuition discriminate.
  - constructor; [| constructor].
    exists u_hrx5. split; [left; reflexivity |].
    exists WgNoise.harness.x_handshake_receive.code.f_main. split; [reflexivity |].
    apply (hrx5_main_body x25519 aead_enc aead_dec xaead_enc xaead_dec). split3; assumption.
Qed.
