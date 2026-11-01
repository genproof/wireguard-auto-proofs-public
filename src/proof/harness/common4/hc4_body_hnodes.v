(* the bodies of group `hnodes` of the common.h v2 layer: each proved ONCE at a small compspecs (hc4_cs.v / hc3_cs.v) with
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
Require Import WgNoise.proof.harness.common4.hc4b_hn_fp.
Require Import WgNoise.proof.harness.common4.hc4b_hn_add.
Require Import WgNoise.proof.harness.common4.hc4b_hn_snap.
Require Import WgNoise.proof.harness.common4.hc4b_hn_same.

Lemma hc4_body_hnodes_add :
  forall x25519 CSw, cspecs_sub CS4 CSw -> @semax_body [] (hc4_G_hnodes_add x25519 CSw) CS4 WgNoise.harness.x_consume_initiation_any.code.f_hnodes_add (hnodes_add4_spec x25519 CSw).
Proof.
  exact hc4b_hna_body.
Qed.

Lemma hc4_body_hnodes_snap :
  forall CSw, @semax_body [] hc4_G_hnodes_snap CS4 WgNoise.harness.x_consume_initiation_any.code.f_hnodes_snap (hnodes_snap4_spec CSw).
Proof.
  intros CSw. exact (hc4b_hn_snap_body CSw).
Qed.

Lemma hc4_body_hnodes_same_except :
  forall CSw, @semax_body [] (hc4_G_hnodes_same_except CSw) CS4 WgNoise.harness.x_consume_initiation_any.code.f_hnodes_same_except (hnodes_same_except4_spec CSw).
Proof.
  intros CSw. exact (hc4b_hn_same_body CSw).
Qed.

Lemma hc4_body_hnodes_free :
  forall CSw, cspecs_sub CS4 CSw -> @semax_body [] (hc4_G_free CSw) CS4 WgNoise.harness.x_consume_initiation_any.code.f_hnodes_free (hnodes_free4_spec CSw).
Proof.
  intros CSw HSUB. exact (hc4b_hn_free_body CSw HSUB).
Qed.

Lemma hc4_body_hnodes_pick :
  forall CSw, @semax_body [] hc4_G_hnodes_pick CS4 WgNoise.harness.x_cookie_mac.code.f_hnodes_pick (hnodes_pick4_spec CSw).
Proof.
  intros CSw. exact (hc4b_hn_pick_body CSw).
Qed.

(* the group *)
Theorem hc4_bodies_hnodes :
  (forall x25519 CSw, cspecs_sub CS4 CSw -> @semax_body [] (hc4_G_hnodes_add x25519 CSw) CS4 WgNoise.harness.x_consume_initiation_any.code.f_hnodes_add (hnodes_add4_spec x25519 CSw)) /\
  (forall CSw, @semax_body [] hc4_G_hnodes_snap CS4 WgNoise.harness.x_consume_initiation_any.code.f_hnodes_snap (hnodes_snap4_spec CSw)) /\
  (forall CSw, @semax_body [] (hc4_G_hnodes_same_except CSw) CS4 WgNoise.harness.x_consume_initiation_any.code.f_hnodes_same_except (hnodes_same_except4_spec CSw)) /\
  (forall CSw, cspecs_sub CS4 CSw -> @semax_body [] (hc4_G_free CSw) CS4 WgNoise.harness.x_consume_initiation_any.code.f_hnodes_free (hnodes_free4_spec CSw)) /\
  (forall CSw, @semax_body [] hc4_G_hnodes_pick CS4 WgNoise.harness.x_cookie_mac.code.f_hnodes_pick (hnodes_pick4_spec CSw)).
Proof.
  exact (conj hc4_body_hnodes_add (conj hc4_body_hnodes_snap (conj hc4_body_hnodes_same_except (conj hc4_body_hnodes_free (hc4_body_hnodes_pick))))).
Qed.
