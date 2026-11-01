(* the body group `noise_mix` of the protocol piece v4 = v3's
   prot_body3_noise_mix.v re-proved against the v4 specifications (prot_specs4.v, context Gprot4 of prot_prog4.v: the
   shim's refcount_t warnings exact).  Owner of the statement: the config_any. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.
Require Import WgNoise.proof.protocol4.prot4_noise_mix_wg_noise_init.
Require Import WgNoise.proof.protocol4.prot4_noise_mix_derive_keys.
Require Import WgNoise.proof.protocol4.prot4_noise_mix_mix_dh.
Require Import WgNoise.proof.protocol4.prot4_noise_mix_mix_precomputed_dh.
Require Import WgNoise.proof.protocol4.prot4_noise_mix_mix_hash.
Require Import WgNoise.proof.protocol4.prot4_noise_mix_mix_psk.
Require Import WgNoise.proof.protocol4.prot4_noise_mix_handshake_init.
Require Import WgNoise.proof.protocol4.prot4_noise_mix_message_encrypt.
Require Import WgNoise.proof.protocol4.prot4_noise_mix_message_decrypt.
Require Import WgNoise.proof.protocol4.prot4_noise_mix_message_ephemeral.

Theorem prot4_noise_bodies_noise_mix :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_wg_noise_init wg_noise_init_spec) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_derive_keys derive_keys_spec) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_mix_dh (mix_dh_spec x25519)) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_mix_precomputed_dh mix_precomputed_dh_spec) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_mix_hash mix_hash_spec) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_mix_psk mix_psk_spec) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_handshake_init handshake_init_spec) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_message_encrypt (message_encrypt_spec aead_enc)) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_message_decrypt (message_decrypt_spec aead_dec)) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_message_ephemeral message_ephemeral_spec).
Proof.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Hx Ha Hxa.
  split; [apply prot4_noise_mix_body_wg_noise_init; auto |].
  split; [apply prot4_noise_mix_body_derive_keys; auto |].
  split; [apply prot4_noise_mix_body_mix_dh; auto |].
  split; [apply prot4_noise_mix_body_mix_precomputed_dh; auto |].
  split; [apply prot4_noise_mix_body_mix_hash; auto |].
  split; [apply prot4_noise_mix_body_mix_psk; auto |].
  split; [apply prot4_noise_mix_body_handshake_init; auto |].
  split; [apply prot4_noise_mix_body_message_encrypt; auto |].
  split; [apply prot4_noise_mix_body_message_decrypt; auto |].
  apply prot4_noise_mix_body_message_ephemeral; auto.
Qed.
