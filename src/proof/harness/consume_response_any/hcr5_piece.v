(* law consume_response_any: the law's own piece = main's body. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_main.

Theorem hcr5_piece :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec,
  hcr5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  piece_ok [u_hcr5] (hcr5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec) hcr5_G.
Proof.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec HH. split.
  - repeat constructor. simpl. tauto.
  - constructor; [| constructor].
    exists u_hcr5. split; [left; reflexivity |].
    exists WgNoise.harness.x_consume_response_any.code.f_main. split; [reflexivity |].
    apply hcr5_main_body; exact HH.
Qed.
