(* law cookie_mac: the law's own piece = the bodies of m_cookie, m_expired and main.  Port of v1's hck3_piece.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.cookie_mac.hck5_cut.
Require Import WgNoise.proof.harness.cookie_mac.hck5_spec.
Require Import WgNoise.proof.harness.cookie_mac.hck5_defs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_local.
Require Import WgNoise.proof.harness.cookie_mac.hck5_main.

Theorem hck5_piece :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec,
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  piece_ok [u_hck5] (hck5_imports x25519 aead_enc aead_dec xaead_enc xaead_dec) hck5_G.
Proof.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec HH. split.
  - repeat constructor; simpl; intuition discriminate.
  - repeat constructor.
    + exists u_hck5. split; [left; reflexivity |].
      exists HK.f_m_cookie. split; [reflexivity |].
      apply hck5_body_m_cookie.
    + exists u_hck5. split; [left; reflexivity |].
      exists HK.f_m_expired. split; [reflexivity |].
      apply hck5_body_m_expired.
    + exists u_hck5. split; [left; reflexivity |].
      exists HK.f_main. split; [reflexivity |].
      apply hck5_main_body; exact HH.
Qed.
