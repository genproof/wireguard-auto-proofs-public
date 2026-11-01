(* the body group `noise_small` of the protocol piece v4 = v3's
   prot_body3_noise_small.v re-proved against the v4 specifications (prot_specs4.v, context Gprot4 of prot_prog4.v: the
   shim's refcount_t warnings exact).  Owner of the statement: the config_any. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.
Require WgNoise.proof.protocol4.prot4_noise_grp_noise_small.

Theorem prot_bodies4_noise_small :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_quickproof_rounddown_pow_of_two quickproof_rounddown_pow_of_two_spec) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_put_unaligned_be32 put_unaligned_be32_spec) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_put_unaligned_be64 put_unaligned_be64_spec) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_curve25519_generate_secret curve25519_generate_secret_spec) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_wg_noise_reset_last_sent_handshake wg_noise_reset_last_sent_handshake_spec) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_handshake_zero handshake_zero_spec) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_tai64n_now tai64n_now_spec).
Proof.
  exact WgNoise.proof.protocol4.prot4_noise_grp_noise_small.prot4_noise_bodies_noise_small.
Qed.
