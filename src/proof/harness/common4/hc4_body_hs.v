(* the bodies of group `hs` of the common.h v2 layer: each proved ONCE at a small compspecs (hc4_cs.v / hc3_cs.v) with
   only its callees' specifications (hc4_ctx.v), lifted to every law's unit by hc4_bodies.v (hc3_lift.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_consume_initiation_any.code WgNoise.harness.x_keypairs.code
        WgNoise.harness.x_handshake.code WgNoise.harness.x_consume_response_any.code
        WgNoise.harness.x_handshake_receive.code.
Require WgNoise.proof.harness.common4.hc4b_hs_take WgNoise.proof.harness.common4.hc4b_hs_clock
        WgNoise.proof.harness.common4.hc4b_hs_same WgNoise.proof.harness.common4.hc4b_hs_sbn
        WgNoise.proof.harness.common4.hc4b_hs_zf WgNoise.proof.harness.common4.hc4b_hs_rand
        WgNoise.proof.harness.common4.hc4b_hs_setup.

Lemma hc4_body_hs_take :
   @semax_body [] hc4_G_hs_take CSkh WgNoise.harness.x_handshake.code.f_hs_take hs_take4_spec.
Proof. exact WgNoise.proof.harness.common4.hc4b_hs_take.hc4b_hs_take_body. Qed.

Lemma hc4_body_hs_same :
  forall CSw, @semax_body [] hc4_G_hs_same CSkh WgNoise.harness.x_handshake.code.f_hs_same (hs_same4_spec CSw).
Proof. exact WgNoise.proof.harness.common4.hc4b_hs_same.hc4b_hs_same_body. Qed.

Lemma hc4_body_hs_zeroed_from :
  forall CSw, @semax_body [] hc4_G_hs_zeroed_from CSkh WgNoise.harness.x_keypairs.code.f_hs_zeroed_from (hs_zeroed_from4_spec CSw).
Proof. exact WgNoise.proof.harness.common4.hc4b_hs_zf.hc4b_hs_zf_body. Qed.

Lemma hc4_body_hs_same_but_next :
  forall CSw, @semax_body [] hc4_G_hs_same CSkh WgNoise.harness.x_keypairs.code.f_hs_same_but_next (hs_same_but_next4_spec CSw).
Proof. exact WgNoise.proof.harness.common4.hc4b_hs_sbn.hc4b_hs_sbn_body. Qed.

Lemma hc4_body_hs_randomize :
   @semax_body [] hc4_G_hs_randomize CSk WgNoise.harness.x_consume_response_any.code.f_hs_randomize hs_randomize4_spec.
Proof. exact WgNoise.proof.harness.common4.hc4b_hs_rand.hc4b_hs_rand_body. Qed.

Lemma hc4_body_setup_device :
  forall x25519, @semax_body [] (hc4_G_setup_device x25519) CSk WgNoise.harness.x_handshake.code.f_setup_device (setup_device4_spec x25519).
Proof. exact WgNoise.proof.harness.common4.hc4b_hs_setup.hc4b_hs_setup_body. Qed.

Lemma hc4_body_draw_real_clock :
   @semax_body hc4_V_real_clock hc4_G_draw_real_clock CSk WgNoise.harness.x_handshake.code.f_draw_real_clock draw_real_clock4_spec.
Proof. exact WgNoise.proof.harness.common4.hc4b_hs_clock.hc4b_hs_clock_body. Qed.

(* the group *)
Theorem hc4_bodies_hs :
  (@semax_body [] hc4_G_hs_take CSkh WgNoise.harness.x_handshake.code.f_hs_take hs_take4_spec) /\
  (forall CSw, @semax_body [] hc4_G_hs_same CSkh WgNoise.harness.x_handshake.code.f_hs_same (hs_same4_spec CSw)) /\
  (forall CSw, @semax_body [] hc4_G_hs_zeroed_from CSkh WgNoise.harness.x_keypairs.code.f_hs_zeroed_from (hs_zeroed_from4_spec CSw)) /\
  (forall CSw, @semax_body [] hc4_G_hs_same CSkh WgNoise.harness.x_keypairs.code.f_hs_same_but_next (hs_same_but_next4_spec CSw)) /\
  (@semax_body [] hc4_G_hs_randomize CSk WgNoise.harness.x_consume_response_any.code.f_hs_randomize hs_randomize4_spec) /\
  (forall x25519, @semax_body [] (hc4_G_setup_device x25519) CSk WgNoise.harness.x_handshake.code.f_setup_device (setup_device4_spec x25519)) /\
  (@semax_body hc4_V_real_clock hc4_G_draw_real_clock CSk WgNoise.harness.x_handshake.code.f_draw_real_clock draw_real_clock4_spec).
Proof.
  exact (conj hc4_body_hs_take (conj hc4_body_hs_same (conj hc4_body_hs_zeroed_from (conj hc4_body_hs_same_but_next (conj hc4_body_hs_randomize (conj hc4_body_setup_device (hc4_body_draw_real_clock))))))).
Qed.
