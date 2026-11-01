(* the protocol piece: every function of noise.c, cookie.c and the kernel shim
   wg_shim.c, except the
   shared inlines owned by other pieces (memzero_explicit, crypto_memneq, the blake2s.h inlines,
   curve25519_clamp_secret; the shim's __crypto_memneq (libc piece) and __crypto_xor (aead piece)).
   Proved for ANY functional models of the primitives satisfying the properties of prim_api.v and ANY world
   compspecs CSw, from the body groups prot_body3_<group>.v (specifications prot_specs3.v, context prot_prog3.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.protocol.prot_body3_begin_session.
Require Import WgNoise.proof.protocol.prot_body3_consume_init.
Require Import WgNoise.proof.protocol.prot_body3_consume_resp.
Require Import WgNoise.proof.protocol.prot_body3_cookie_make.
Require Import WgNoise.proof.protocol.prot_body3_cookie_msg.
Require Import WgNoise.proof.protocol.prot_body3_cookie_small.
Require Import WgNoise.proof.protocol.prot_body3_create_init.
Require Import WgNoise.proof.protocol.prot_body3_create_resp.
Require Import WgNoise.proof.protocol.prot_body3_noise_ident.
Require Import WgNoise.proof.protocol.prot_body3_noise_kdf.
Require Import WgNoise.proof.protocol.prot_body3_noise_kp.
Require Import WgNoise.proof.protocol.prot_body3_noise_mix.
Require Import WgNoise.proof.protocol.prot_body3_noise_rot.
Require Import WgNoise.proof.protocol.prot_body3_noise_small.
Require Import WgNoise.proof.protocol.prot_body3_shim_small.
Require Import WgNoise.proof.protocol.prot_body3_shim_rc.
Require Import WgNoise.proof.protocol.prot_body3_shim_table1.
Require Import WgNoise.proof.protocol.prot_body3_shim_table2.
Require Import WgNoise.proof.protocol.prot_body3_zero.

Definition protocol_idents3 : list ident :=
  [WgNoise.noise.code._quickproof_rounddown_pow_of_two;
   WgNoise.noise.code._put_unaligned_be32;
   WgNoise.noise.code._put_unaligned_be64;
   WgNoise.noise.code._curve25519_generate_secret;
   WgNoise.noise.code._wg_noise_reset_last_sent_handshake;
   WgNoise.noise.code._wg_noise_init;
   WgNoise.noise.code._wg_noise_precompute_static_static;
   WgNoise.noise.code._wg_noise_handshake_init;
   WgNoise.noise.code._handshake_zero;
   WgNoise.noise.code._wg_noise_handshake_clear;
   WgNoise.noise.code._keypair_create;
   WgNoise.noise.code._keypair_free_rcu;
   WgNoise.noise.code._keypair_free_kref;
   WgNoise.noise.code._wg_noise_keypair_put;
   WgNoise.noise.code._wg_noise_keypair_get;
   WgNoise.noise.code._wg_noise_keypairs_clear;
   WgNoise.noise.code._wg_noise_expire_current_peer_keypairs;
   WgNoise.noise.code._add_new_keypair;
   WgNoise.noise.code._wg_noise_received_with_keypair;
   WgNoise.noise.code._wg_noise_set_static_identity_private_key;
   WgNoise.noise.code._hmac;
   WgNoise.noise.code._kdf;
   WgNoise.noise.code._derive_keys;
   WgNoise.noise.code._mix_dh;
   WgNoise.noise.code._mix_precomputed_dh;
   WgNoise.noise.code._mix_hash;
   WgNoise.noise.code._mix_psk;
   WgNoise.noise.code._handshake_init;
   WgNoise.noise.code._message_encrypt;
   WgNoise.noise.code._message_decrypt;
   WgNoise.noise.code._message_ephemeral;
   WgNoise.noise.code._tai64n_now;
   WgNoise.noise.code._wg_noise_handshake_create_initiation;
   WgNoise.noise.code._wg_noise_handshake_consume_initiation;
   WgNoise.noise.code._wg_noise_handshake_create_response;
   WgNoise.noise.code._wg_noise_handshake_consume_response;
   WgNoise.noise.code._wg_noise_handshake_begin_session;
   WgNoise.cookie.code._quickproof_swab16;
   WgNoise.cookie.code._wg_cookie_checker_init;
   WgNoise.cookie.code._precompute_key;
   WgNoise.cookie.code._wg_cookie_checker_precompute_device_keys;
   WgNoise.cookie.code._wg_cookie_checker_precompute_peer_keys;
   WgNoise.cookie.code._wg_cookie_init;
   WgNoise.cookie.code._compute_mac1;
   WgNoise.cookie.code._compute_mac2;
   WgNoise.cookie.code._make_cookie;
   WgNoise.cookie.code._wg_cookie_validate_packet;
   WgNoise.cookie.code._wg_cookie_add_mac_to_packet;
   WgNoise.cookie.code._wg_cookie_message_create;
   WgNoise.cookie.code._wg_cookie_message_consume;
   WgNoise.shim.code._ktime_get_coarse_boottime_ns;
   WgNoise.shim.code._ktime_get_real_ts64;
   WgNoise.shim.code._get_random_bytes;
   WgNoise.shim.code._get_random_bytes_wait;
   WgNoise.shim.code._get_random_u32;
   WgNoise.shim.code._kzalloc;
   WgNoise.shim.code._kfree;
   WgNoise.shim.code._kfree_sensitive;
   WgNoise.shim.code._wg_shim_refcount_warn_saturate;
   WgNoise.shim.code._wg_shim_refcount_neg;
   WgNoise.shim.code._wg_shim_refcount_inc_not_zero;
   WgNoise.shim.code._wg_shim_refcount_inc;
   WgNoise.shim.code._wg_shim_refcount_dec_and_test;
   WgNoise.shim.code._wg_peer_get_maybe_zero;
   WgNoise.shim.code._wg_shim_peer_release;
   WgNoise.shim.code._wg_peer_put;
   WgNoise.shim.code._wg_pubkey_hashtable_lookup;
   WgNoise.shim.code._wg_index_hashtable_remove;
   WgNoise.shim.code._wg_shim_index_in_use;
   WgNoise.shim.code._wg_index_hashtable_insert;
   WgNoise.shim.code._wg_index_hashtable_replace;
   WgNoise.shim.code._wg_index_hashtable_lookup;
   WgNoise.shim.code._wg_ratelimiter_allow;
   WgNoise.shim.code._wg_birthdate_has_expired].

Theorem protocol_piece3 :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  map fst (prot_G3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw) = protocol_idents3 /\
  piece_ok [u_noise; u_cookie; u_shim]
    (prot_imports3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (prot_G3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw).
Proof.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Hx Ha Hxa.
  split; [reflexivity |].
  destruct (prot_bodies3_shim_small x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Hx Ha Hxa) as (B_ktime_get_coarse_boottime_ns & B_ktime_get_real_ts64 & B_get_random_bytes & B_get_random_bytes_wait & B_get_random_u32 & B_kzalloc & B_kfree & B_kfree_sensitive & B_wg_peer_get_maybe_zero & B_wg_shim_peer_release & B_wg_peer_put & B_wg_ratelimiter_allow & B_wg_birthdate_has_expired).
  destruct (prot_bodies3_shim_rc x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Hx Ha Hxa) as (B_wg_shim_refcount_warn_saturate & B_wg_shim_refcount_neg & B_wg_shim_refcount_inc_not_zero & B_wg_shim_refcount_inc & B_wg_shim_refcount_dec_and_test).
  destruct (prot_bodies3_shim_table1 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Hx Ha Hxa) as (B_wg_index_hashtable_remove & B_wg_shim_index_in_use & B_wg_index_hashtable_insert).
  destruct (prot_bodies3_shim_table2 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Hx Ha Hxa) as (B_wg_index_hashtable_replace & B_wg_index_hashtable_lookup & B_wg_pubkey_hashtable_lookup).
  destruct (prot_bodies3_noise_small x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Hx Ha Hxa) as (B_quickproof_rounddown_pow_of_two & B_put_unaligned_be32 & B_put_unaligned_be64 & B_curve25519_generate_secret & B_wg_noise_reset_last_sent_handshake & B_handshake_zero & B_tai64n_now).
  destruct (prot_bodies3_noise_kdf x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Hx Ha Hxa) as (B_hmac & B_kdf).
  destruct (prot_bodies3_noise_mix x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Hx Ha Hxa) as (B_wg_noise_init & B_derive_keys & B_mix_dh & B_mix_precomputed_dh & B_mix_hash & B_mix_psk & B_handshake_init & B_message_encrypt & B_message_decrypt & B_message_ephemeral).
  destruct (prot_bodies3_zero x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Hx Ha Hxa) as (B_wg_noise_handshake_init & B_keypair_create & B_wg_cookie_init).
  destruct (prot_bodies3_noise_ident x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Hx Ha Hxa) as (B_wg_noise_set_static_identity_private_key & B_wg_noise_precompute_static_static & B_wg_noise_handshake_clear).
  destruct (prot_bodies3_noise_kp x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Hx Ha Hxa) as (B_keypair_free_rcu & B_keypair_free_kref & B_wg_noise_keypair_put & B_wg_noise_keypair_get).
  destruct (prot_bodies3_noise_rot x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Hx Ha Hxa) as (B_wg_noise_keypairs_clear & B_wg_noise_expire_current_peer_keypairs & B_add_new_keypair & B_wg_noise_received_with_keypair).
  pose proof (prot_bodies3_create_init x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Hx Ha Hxa) as B_wg_noise_handshake_create_initiation.
  pose proof (prot_bodies3_create_resp x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Hx Ha Hxa) as B_wg_noise_handshake_create_response.
  pose proof (prot_bodies3_consume_init x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Hx Ha Hxa) as B_wg_noise_handshake_consume_initiation.
  pose proof (prot_bodies3_consume_resp x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Hx Ha Hxa) as B_wg_noise_handshake_consume_response.
  pose proof (prot_bodies3_begin_session x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Hx Ha Hxa) as B_wg_noise_handshake_begin_session.
  destruct (prot_bodies3_cookie_small x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Hx Ha Hxa) as (B_quickproof_swab16 & B_wg_cookie_checker_init & B_precompute_key & B_wg_cookie_checker_precompute_device_keys & B_wg_cookie_checker_precompute_peer_keys & B_compute_mac1 & B_compute_mac2).
  destruct (prot_bodies3_cookie_make x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Hx Ha Hxa) as (B_make_cookie & B_wg_cookie_validate_packet).
  destruct (prot_bodies3_cookie_msg x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Hx Ha Hxa) as (B_wg_cookie_add_mac_to_packet & B_wg_cookie_message_create & B_wg_cookie_message_consume).
  split.
  { unfold prot_G3, prot_G_list. apply compute_list_norepet_e. reflexivity. }
  unfold prot_G3, prot_G_list.
  repeat apply Forall_cons; try apply Forall_nil.
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_quickproof_rounddown_pow_of_two; split; [reflexivity | exact B_quickproof_rounddown_pow_of_two]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_put_unaligned_be32; split; [reflexivity | exact B_put_unaligned_be32]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_put_unaligned_be64; split; [reflexivity | exact B_put_unaligned_be64]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_curve25519_generate_secret; split; [reflexivity | exact B_curve25519_generate_secret]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_wg_noise_reset_last_sent_handshake; split; [reflexivity | exact B_wg_noise_reset_last_sent_handshake]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_wg_noise_init; split; [reflexivity | exact B_wg_noise_init]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_wg_noise_precompute_static_static; split; [reflexivity | exact B_wg_noise_precompute_static_static]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_wg_noise_handshake_init; split; [reflexivity | exact B_wg_noise_handshake_init]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_handshake_zero; split; [reflexivity | exact B_handshake_zero]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_wg_noise_handshake_clear; split; [reflexivity | exact B_wg_noise_handshake_clear]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_keypair_create; split; [reflexivity | exact B_keypair_create]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_keypair_free_rcu; split; [reflexivity | exact B_keypair_free_rcu]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_keypair_free_kref; split; [reflexivity | exact B_keypair_free_kref]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_wg_noise_keypair_put; split; [reflexivity | exact B_wg_noise_keypair_put]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_wg_noise_keypair_get; split; [reflexivity | exact B_wg_noise_keypair_get]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_wg_noise_keypairs_clear; split; [reflexivity | exact B_wg_noise_keypairs_clear]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_wg_noise_expire_current_peer_keypairs; split; [reflexivity | exact B_wg_noise_expire_current_peer_keypairs]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_add_new_keypair; split; [reflexivity | exact B_add_new_keypair]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_wg_noise_received_with_keypair; split; [reflexivity | exact B_wg_noise_received_with_keypair]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_wg_noise_set_static_identity_private_key; split; [reflexivity | exact B_wg_noise_set_static_identity_private_key]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_hmac; split; [reflexivity | exact B_hmac]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_kdf; split; [reflexivity | exact B_kdf]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_derive_keys; split; [reflexivity | exact B_derive_keys]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_mix_dh; split; [reflexivity | exact B_mix_dh]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_mix_precomputed_dh; split; [reflexivity | exact B_mix_precomputed_dh]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_mix_hash; split; [reflexivity | exact B_mix_hash]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_mix_psk; split; [reflexivity | exact B_mix_psk]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_handshake_init; split; [reflexivity | exact B_handshake_init]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_message_encrypt; split; [reflexivity | exact B_message_encrypt]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_message_decrypt; split; [reflexivity | exact B_message_decrypt]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_message_ephemeral; split; [reflexivity | exact B_message_ephemeral]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_tai64n_now; split; [reflexivity | exact B_tai64n_now]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_wg_noise_handshake_create_initiation; split; [reflexivity | exact B_wg_noise_handshake_create_initiation]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_wg_noise_handshake_consume_initiation; split; [reflexivity | exact B_wg_noise_handshake_consume_initiation]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_wg_noise_handshake_create_response; split; [reflexivity | exact B_wg_noise_handshake_create_response]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_wg_noise_handshake_consume_response; split; [reflexivity | exact B_wg_noise_handshake_consume_response]].
  - exists u_noise; split; [simpl; tauto | exists WgNoise.noise.code.f_wg_noise_handshake_begin_session; split; [reflexivity | exact B_wg_noise_handshake_begin_session]].
  - exists u_cookie; split; [simpl; tauto | exists WgNoise.cookie.code.f_quickproof_swab16; split; [reflexivity | exact B_quickproof_swab16]].
  - exists u_cookie; split; [simpl; tauto | exists WgNoise.cookie.code.f_wg_cookie_checker_init; split; [reflexivity | exact B_wg_cookie_checker_init]].
  - exists u_cookie; split; [simpl; tauto | exists WgNoise.cookie.code.f_precompute_key; split; [reflexivity | exact B_precompute_key]].
  - exists u_cookie; split; [simpl; tauto | exists WgNoise.cookie.code.f_wg_cookie_checker_precompute_device_keys; split; [reflexivity | exact B_wg_cookie_checker_precompute_device_keys]].
  - exists u_cookie; split; [simpl; tauto | exists WgNoise.cookie.code.f_wg_cookie_checker_precompute_peer_keys; split; [reflexivity | exact B_wg_cookie_checker_precompute_peer_keys]].
  - exists u_cookie; split; [simpl; tauto | exists WgNoise.cookie.code.f_wg_cookie_init; split; [reflexivity | exact B_wg_cookie_init]].
  - exists u_cookie; split; [simpl; tauto | exists WgNoise.cookie.code.f_compute_mac1; split; [reflexivity | exact B_compute_mac1]].
  - exists u_cookie; split; [simpl; tauto | exists WgNoise.cookie.code.f_compute_mac2; split; [reflexivity | exact B_compute_mac2]].
  - exists u_cookie; split; [simpl; tauto | exists WgNoise.cookie.code.f_make_cookie; split; [reflexivity | exact B_make_cookie]].
  - exists u_cookie; split; [simpl; tauto | exists WgNoise.cookie.code.f_wg_cookie_validate_packet; split; [reflexivity | exact B_wg_cookie_validate_packet]].
  - exists u_cookie; split; [simpl; tauto | exists WgNoise.cookie.code.f_wg_cookie_add_mac_to_packet; split; [reflexivity | exact B_wg_cookie_add_mac_to_packet]].
  - exists u_cookie; split; [simpl; tauto | exists WgNoise.cookie.code.f_wg_cookie_message_create; split; [reflexivity | exact B_wg_cookie_message_create]].
  - exists u_cookie; split; [simpl; tauto | exists WgNoise.cookie.code.f_wg_cookie_message_consume; split; [reflexivity | exact B_wg_cookie_message_consume]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_ktime_get_coarse_boottime_ns; split; [reflexivity | exact B_ktime_get_coarse_boottime_ns]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_ktime_get_real_ts64; split; [reflexivity | exact B_ktime_get_real_ts64]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_get_random_bytes; split; [reflexivity | exact B_get_random_bytes]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_get_random_bytes_wait; split; [reflexivity | exact B_get_random_bytes_wait]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_get_random_u32; split; [reflexivity | exact B_get_random_u32]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_kzalloc; split; [reflexivity | exact B_kzalloc]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_kfree; split; [reflexivity | exact B_kfree]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_kfree_sensitive; split; [reflexivity | exact B_kfree_sensitive]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_wg_shim_refcount_warn_saturate; split; [reflexivity | exact B_wg_shim_refcount_warn_saturate]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_wg_shim_refcount_neg; split; [reflexivity | exact B_wg_shim_refcount_neg]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_wg_shim_refcount_inc_not_zero; split; [reflexivity | exact B_wg_shim_refcount_inc_not_zero]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_wg_shim_refcount_inc; split; [reflexivity | exact B_wg_shim_refcount_inc]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_wg_shim_refcount_dec_and_test; split; [reflexivity | exact B_wg_shim_refcount_dec_and_test]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_wg_peer_get_maybe_zero; split; [reflexivity | exact B_wg_peer_get_maybe_zero]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_wg_shim_peer_release; split; [reflexivity | exact B_wg_shim_peer_release]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_wg_peer_put; split; [reflexivity | exact B_wg_peer_put]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_wg_pubkey_hashtable_lookup; split; [reflexivity | exact B_wg_pubkey_hashtable_lookup]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_wg_index_hashtable_remove; split; [reflexivity | exact B_wg_index_hashtable_remove]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_wg_shim_index_in_use; split; [reflexivity | exact B_wg_shim_index_in_use]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_wg_index_hashtable_insert; split; [reflexivity | exact B_wg_index_hashtable_insert]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_wg_index_hashtable_replace; split; [reflexivity | exact B_wg_index_hashtable_replace]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_wg_index_hashtable_lookup; split; [reflexivity | exact B_wg_index_hashtable_lookup]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_wg_ratelimiter_allow; split; [reflexivity | exact B_wg_ratelimiter_allow]].
  - exists u_shim; split; [simpl; tauto | exists WgNoise.shim.code.f_wg_birthdate_has_expired; split; [reflexivity | exact B_wg_birthdate_has_expired]].
Qed.
