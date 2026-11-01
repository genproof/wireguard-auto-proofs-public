(* hc_pieces3, group draws: common.h bodies, proved once at a small compspecs with the callee context
   of hc3_ctx.v.  One lemma per function (per law where the Clight
   reads a renamed constant). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common.hc3_ctx.
Require Import WgNoise.proof.harness.common.hc3b_draws_proofs.
Require WgNoise.harness.x_handshake.code WgNoise.harness.x_cookie_reply.code WgNoise.harness.x_consume_response_any.code
        WgNoise.harness.x_keypairs.code WgNoise.harness.x_create_any.code WgNoise.harness.x_replay.code
        WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_consume_initiation_any.code.
Require WgNoise.contracts.x_cookie_reply.

Module FH := WgNoise.harness.x_handshake.code.
Module FK := WgNoise.harness.x_cookie_reply.code.
Module FR := WgNoise.harness.x_consume_response_any.code.

(* every lemma takes all the section variables and hypotheses (a stable signature for the assembly) *)
#[local] Set Default Proof Using "All".

Section Bodies.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Hypothesis X25519: x25519_props x25519.
Hypothesis AEAD: aead_props aead_enc aead_dec.
Hypothesis XAEAD: xaead_props xaead_enc xaead_dec.

Lemma hc3_body_check_failed :
  @semax_body [] (hc3_G_none) CSk FH.f_check_failed (check_failed_spec).
Proof.
  exact (hc3b_draws_body_check_failed x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD).
Qed.

Lemma hc3_body_m_not_flood :
  @semax_body [] (hc3_G_none) CSk FH.f_m_not_flood (m_not_flood_spec).
Proof.
  exact (hc3b_draws_body_m_not_flood x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD).
Qed.

Lemma hc3_body_m_last_consumption :
  @semax_body [] (hc3_G_none) CSk FH.f_m_last_consumption (m_last_consumption_spec).
Proof.
  exact (hc3b_draws_body_m_last_consumption x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD).
Qed.

Lemma hc3_body_draw_size :
  @semax_body [] (hc3_G_draw_size) CSk FK.f_draw_size (draw_size_spec).
Proof.
  exact (hc3b_draws_body_draw_size x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD).
Qed.

Lemma hc3_body_draw_steps :
  @semax_body [] (hc3_G_draw_size) CSk FR.f_draw_steps (draw_steps_spec).
Proof.
  exact (hc3b_draws_body_draw_steps x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD).
Qed.

Lemma hc3_body_draw_u64 :
  @semax_body [] (hc3_G_draw_u64) CSk FH.f_draw_u64 (draw_u64_spec).
Proof.
  exact (hc3b_draws_body_draw_u64 x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD).
Qed.

Lemma hc3_body_draw_boottime :
  @semax_body [] (hc3_G_draw_boottime) CSk FH.f_draw_boottime (draw_boottime_spec).
Proof.
  exact (hc3b_draws_body_draw_boottime x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD).
Qed.

Lemma hc3_body_draw_hs_state :
  @semax_body [] (hc3_G_draw_hs_state) CSk FR.f_draw_hs_state (draw_hs_state_spec).
Proof.
  exact (hc3b_draws_body_draw_hs_state x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD).
Qed.

Lemma hc3_body_draw_real_clock :
  @semax_body hc3b_draws_V_real_clock (hc3_G_draw_real_clock) CSk FH.f_draw_real_clock (draw_real_clock_spec).
Proof.
  exact (hc3b_draws_body_draw_real_clock x25519 aead_enc aead_dec xaead_enc xaead_dec X25519 AEAD XAEAD).
Qed.

(* the group *)
Theorem hc3_bodies_draws :
  (@semax_body [] (hc3_G_none) CSk FH.f_check_failed (check_failed_spec)) /\
  (@semax_body [] (hc3_G_none) CSk FH.f_m_not_flood (m_not_flood_spec)) /\
  (@semax_body [] (hc3_G_none) CSk FH.f_m_last_consumption (m_last_consumption_spec)) /\
  (@semax_body [] (hc3_G_draw_size) CSk FK.f_draw_size (draw_size_spec)) /\
  (@semax_body [] (hc3_G_draw_size) CSk FR.f_draw_steps (draw_steps_spec)) /\
  (@semax_body [] (hc3_G_draw_u64) CSk FH.f_draw_u64 (draw_u64_spec)) /\
  (@semax_body [] (hc3_G_draw_boottime) CSk FH.f_draw_boottime (draw_boottime_spec)) /\
  (@semax_body [] (hc3_G_draw_hs_state) CSk FR.f_draw_hs_state (draw_hs_state_spec)) /\
  (@semax_body hc3b_draws_V_real_clock (hc3_G_draw_real_clock) CSk FH.f_draw_real_clock (draw_real_clock_spec)).
Proof.
  repeat split; first [ apply hc3_body_check_failed | apply hc3_body_m_not_flood | apply hc3_body_m_last_consumption
    | apply hc3_body_draw_size | apply hc3_body_draw_steps | apply hc3_body_draw_u64 | apply hc3_body_draw_boottime
    | apply hc3_body_draw_hs_state | apply hc3_body_draw_real_clock ].
Qed.

End Bodies.
