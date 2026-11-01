(* the body group `cookie_msg` of the protocol piece v4 = v3's
   prot_body3_cookie_msg.v re-proved against the v4 specifications (prot_specs4.v, context Gprot4 of prot_prog4.v: the
   shim's refcount_t warnings exact).  Owner of the statement: the config_any. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.
Require WgNoise.proof.protocol4.prot4_ck_msg.

Theorem prot_bodies4_cookie_msg :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Cookie.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Cookie.CS) Cookie.CS
      WgNoise.cookie.code.f_wg_cookie_add_mac_to_packet wg_cookie_add_mac_to_packet_spec) /\
  (@semax_body (QPvarspecs Cookie.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Cookie.CS) Cookie.CS
      WgNoise.cookie.code.f_wg_cookie_message_create (wg_cookie_message_create_spec xaead_enc)) /\
  (@semax_body (QPvarspecs Cookie.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Cookie.CS) Cookie.CS
      WgNoise.cookie.code.f_wg_cookie_message_consume (wg_cookie_message_consume_spec xaead_dec)).
Proof.
  exact WgNoise.proof.protocol4.prot4_ck_msg.prot4_ck_bodies_msg.
Qed.
