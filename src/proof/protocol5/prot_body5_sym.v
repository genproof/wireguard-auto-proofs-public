(* The bodies of the protocol piece v5, group `sym`: noise.c: the symmetric steps of the handshake; port of prot4_noise_kdf_*.v and prot4_noise_mix_*.v (wg_consts5).
   Each function against its v5 specification (prot_specs5.v) in its unit's compspecs, with the context
   Gprot5 (prot_prog5.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require WgNoise.noise.code WgNoise.shim.code.
Require WgNoise.proof.protocol5.prot5_sym_hmac WgNoise.proof.protocol5.prot5_sym_kdf.
Require WgNoise.proof.protocol5.prot5_sym_mix_a WgNoise.proof.protocol5.prot5_sym_mix_b.

Theorem prot_bodies5_sym :
  forall x25519 aead_enc aead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_hmac (hmac_spec) /\
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_kdf (kdf_spec) /\
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_wg_noise_init (wg_noise_init_spec) /\
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_derive_keys (derive_keys_spec) /\
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_mix_dh (mix_dh_spec x25519) /\
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_mix_precomputed_dh (mix_precomputed_dh_spec) /\
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_mix_hash (mix_hash_spec) /\
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_mix_psk (mix_psk_spec) /\
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_handshake_init (handshake_init_spec) /\
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_message_encrypt (message_encrypt_spec aead_enc) /\
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_message_decrypt (message_decrypt_spec aead_dec) /\
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_message_ephemeral (message_ephemeral_spec).
Proof.
  intros x25519 aead_enc aead_dec CSw Hx Ha.
  split; [exact (prot5_sym_hmac.prot5_body_hmac x25519 aead_enc aead_dec CSw) |].
  split; [exact (prot5_sym_kdf.prot5_body_kdf x25519 aead_enc aead_dec CSw) |].
  split; [apply prot5_sym_mix_a.prot5_sym_body_wg_noise_init; auto |].
  split; [apply prot5_sym_mix_a.prot5_sym_body_derive_keys; auto |].
  split; [apply prot5_sym_mix_a.prot5_sym_body_mix_dh; auto |].
  split; [apply prot5_sym_mix_a.prot5_sym_body_mix_precomputed_dh; auto |].
  split; [apply prot5_sym_mix_a.prot5_sym_body_mix_hash; auto |].
  split; [apply prot5_sym_mix_b.prot5_sym_body_mix_psk; auto |].
  split; [apply prot5_sym_mix_b.prot5_sym_body_handshake_init; auto |].
  split; [apply prot5_sym_mix_b.prot5_sym_body_message_encrypt; auto |].
  split; [apply prot5_sym_mix_b.prot5_sym_body_message_decrypt; auto |].
  apply prot5_sym_mix_b.prot5_sym_body_message_ephemeral; auto.
Qed.
