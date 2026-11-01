(* law consume_initiation_any: the law's own piece = ts_step's and main's bodies. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_ts.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_main.

Theorem hci5_piece :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec,
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  piece_ok [u_hci5] (hci5_imports x25519 aead_enc aead_dec) hci5_G.
Proof.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec HH. split.
  - repeat constructor; simpl; intuition discriminate.
  - constructor; [| constructor; [| constructor]].
    + exists u_hci5. split; [left; reflexivity |].
      exists WgNoise.harness.x_consume_initiation_any.code.f_ts_step. split; [reflexivity |].
      apply hci5_ts_body.
    + exists u_hci5. split; [left; reflexivity |].
      exists WgNoise.harness.x_consume_initiation_any.code.f_main. split; [reflexivity |].
      apply (hci5_main_body x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH.
Qed.
