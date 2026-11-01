(* Body proofs of the protocol piece, group noise_rot.
   Target: prot_bodies3_noise_rot.  Prove each function's body against its specification (prot_specs3.v) in the
   compspecs of its unit, with the context Gprot3 (prot_prog3.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.
Require Import WgNoise.proof.protocol.prot3_noise_rot_clear.
Require Import WgNoise.proof.protocol.prot3_noise_rot_expire.
Require Import WgNoise.proof.protocol.prot3_noise_rot_add.
Require Import WgNoise.proof.protocol.prot3_noise_rot_recv.

Theorem prot_bodies3_noise_rot :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_wg_noise_keypairs_clear (wg_noise_keypairs_clear_spec CSw)) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_wg_noise_expire_current_peer_keypairs (wg_noise_expire_current_peer_keypairs_spec CSw)) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_add_new_keypair (add_new_keypair_spec CSw)) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_wg_noise_received_with_keypair (wg_noise_received_with_keypair_spec CSw)).
Proof.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec CSw _ _ _.
  split; [|split; [|split]].
  - apply prot3_noise_rot_body_clear.
  - apply prot3_noise_rot_body_expire.
  - apply prot3_noise_rot_body_add.
  - apply prot3_noise_rot_body_recv.
Qed.
