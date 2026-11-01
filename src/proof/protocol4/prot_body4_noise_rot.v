(* the body group `noise_rot` of the protocol piece v4 = v3's
   prot_body3_noise_rot.v re-proved against the v4 specifications (prot_specs4.v, context Gprot4 of prot_prog4.v: the
   shim's refcount_t warnings exact).  Owner of the statement: the config_any. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.
Require WgNoise.proof.protocol4.prot4_rot_bodies.

Theorem prot_bodies4_noise_rot :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_wg_noise_keypairs_clear (wg_noise_keypairs_clear_spec CSw)) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_wg_noise_expire_current_peer_keypairs (wg_noise_expire_current_peer_keypairs_spec CSw)) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_add_new_keypair (add_new_keypair_spec CSw)) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_wg_noise_received_with_keypair (wg_noise_received_with_keypair_spec CSw)).
Proof.
  exact WgNoise.proof.protocol4.prot4_rot_bodies.prot4_rot_bodies_noise_rot.
Qed.
