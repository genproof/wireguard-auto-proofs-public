(* the body group `shim_small` of the protocol piece v4 = v3's
   prot_body3_shim_small.v re-proved against the v4 specifications (prot_specs4.v, context Gprot4 of prot_prog4.v: the
   shim's refcount_t warnings exact).  Owner of the statement: the config_any. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.
Require WgNoise.proof.protocol4.prot4_shim_small.

Theorem prot_bodies4_shim_small :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Shim.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_ktime_get_coarse_boottime_ns ktime_get_coarse_boottime_ns_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_ktime_get_real_ts64 ktime_get_real_ts64_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_get_random_bytes get_random_bytes_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_get_random_bytes_wait get_random_bytes_wait_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_get_random_u32 get_random_u32_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_kzalloc (kzalloc_spec CSw)) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_kfree (kfree_spec CSw)) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_kfree_sensitive (kfree_sensitive_spec CSw)) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_peer_get_maybe_zero wg_peer_get_maybe_zero_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_shim_peer_release wg_shim_peer_release_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_peer_put wg_peer_put_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_ratelimiter_allow wg_ratelimiter_allow_spec) /\
  (@semax_body (QPvarspecs Shim.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_birthdate_has_expired wg_birthdate_has_expired_spec).
Proof.
  exact WgNoise.proof.protocol4.prot4_shim_small.prot4_shim_bodies_small.
Qed.
