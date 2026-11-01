(* the bodies of group `snap` of the common.h v2 layer: each proved ONCE at a small compspecs (hc4_cs.v / hc3_cs.v) with
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
Require Import WgNoise.proof.harness.common4.hc4b_snap_vobjs.
Require Import WgNoise.proof.harness.common4.hc4b_snap_take.
Require Import WgNoise.proof.harness.common4.hc4b_snap_shim.
Require Import WgNoise.proof.harness.common4.hc4b_snap_misc.
Require Import WgNoise.proof.harness.common4.hc4b_snap_cmp.
Require Import WgNoise.proof.harness.common4.hc4b_snap_dev.
Require Import WgNoise.proof.harness.common4.hc4b_snap_skb.

Lemma hc4_body_pr_take :
   @semax_body [] hc4_G_pr_take CS4 WgNoise.harness.x_cookie_mac.code.f_pr_take pr_take4_spec.
Proof.
  exact (proj1 hc4b_snap_take_ok).
Qed.

Lemma hc4_body_pr_same_but_cookie :
  forall CSw, @semax_body [] hc4_G_none CS4 WgNoise.harness.x_cookie_mac.code.f_pr_same_but_cookie (pr_same_but_cookie4_spec CSw).
Proof.
  intros CSw. exact (hc4b_cmp_pr_same_but_cookie CSw hc4b_vaddrs_HV).
Qed.

Lemma hc4_body_pr_same :
  forall CSw, @semax_body [] (hc4_G_pr_same CSw) CS4 WgNoise.harness.x_cookie_mac.code.f_pr_same (pr_same4_spec CSw).
Proof.
  intros CSw. exact (hc4b_cmp_pr_same CSw).
Qed.

Lemma hc4_body_dev_take :
   @semax_body [] hc4_G_dev_take CS4 WgNoise.harness.x_cookie_mac.code.f_dev_take dev_take4_spec.
Proof.
  exact (proj1 (proj2 hc4b_snap_take_ok)).
Qed.

Lemma hc4_body_dev_same :
  forall CSw, @semax_body [] hc4_G_dev_same CS4 WgNoise.harness.x_cookie_mac.code.f_dev_same (dev_same4_spec CSw).
Proof.
  intros CSw. exact (hc4b_dev_same CSw hc4b_vaddrs_HV).
Qed.

Lemma hc4_body_shim_take :
   @semax_body hc4_V_shim hc4_G_none CS4s WgNoise.harness.x_cookie_mac.code.f_shim_take shim_take4_spec.
Proof.
  exact (proj1 hc4b_snap_shim_ok).
Qed.

Lemma hc4_body_shim_no_warning :
   @semax_body hc4_V_warn hc4_G_none CS4s WgNoise.harness.x_cookie_mac.code.f_shim_no_warning shim_no_warning4_spec.
Proof.
  exact (proj1 (proj2 hc4b_snap_shim_ok)).
Qed.

Lemma hc4_body_shim_same :
   @semax_body hc4_V_shim hc4_G_shim_same CS4s WgNoise.harness.x_cookie_mac.code.f_shim_same shim_same4_spec.
Proof.
  exact (proj2 (proj2 hc4b_snap_shim_ok)).
Qed.

Lemma hc4_body_skb_take :
   @semax_body [] hc4_G_dev_take CS4skb WgNoise.harness.x_cookie_mac.code.f_skb_take skb_take4_spec.
Proof.
  exact (proj2 (proj2 hc4b_snap_take_ok)).
Qed.

Lemma hc4_body_skb_same :
  forall CSw, @semax_body [] hc4_G_dev_same CS4skb WgNoise.harness.x_cookie_mac.code.f_skb_same (skb_same4_spec CSw).
Proof.
  intros CSw. exact (hc4b_skb_same CSw hc4b_vaddrs_HV).
Qed.

Lemma hc4_body_replay_counter_fresh :
   @semax_body [] hc4_G_none CSk WgNoise.harness.x_keypairs.code.f_replay_counter_fresh replay_counter_fresh4_spec.
Proof.
  exact (proj1 hc4b_snap_misc_ok).
Qed.

Lemma hc4_body_peer_randomize_rest :
   @semax_body [] hc4_G_peer_randomize_rest CSk WgNoise.harness.x_consume_initiation_any.code.f_peer_randomize_rest peer_randomize_rest4_spec.
Proof.
  exact (proj1 (proj2 hc4b_snap_misc_ok)).
Qed.

Lemma hc4_body_draw_peer_refs :
   @semax_body [] hc4_G_draw_peer_refs CSk WgNoise.harness.x_cookie_mac.code.f_draw_peer_refs draw_peer_refs4_spec.
Proof.
  exact (proj1 (proj2 (proj2 hc4b_snap_misc_ok))).
Qed.

Lemma hc4_body_le32_load :
   @semax_body [] hc4_G_none CSk WgNoise.harness.x_handshake_receive.code.f_le32_load le32_load4_spec.
Proof.
  exact (proj2 (proj2 (proj2 hc4b_snap_misc_ok))).
Qed.

(* the group *)
Theorem hc4_bodies_snap :
  (@semax_body [] hc4_G_pr_take CS4 WgNoise.harness.x_cookie_mac.code.f_pr_take pr_take4_spec) /\
  (forall CSw, @semax_body [] hc4_G_none CS4 WgNoise.harness.x_cookie_mac.code.f_pr_same_but_cookie (pr_same_but_cookie4_spec CSw)) /\
  (forall CSw, @semax_body [] (hc4_G_pr_same CSw) CS4 WgNoise.harness.x_cookie_mac.code.f_pr_same (pr_same4_spec CSw)) /\
  (@semax_body [] hc4_G_dev_take CS4 WgNoise.harness.x_cookie_mac.code.f_dev_take dev_take4_spec) /\
  (forall CSw, @semax_body [] hc4_G_dev_same CS4 WgNoise.harness.x_cookie_mac.code.f_dev_same (dev_same4_spec CSw)) /\
  (@semax_body hc4_V_shim hc4_G_none CS4s WgNoise.harness.x_cookie_mac.code.f_shim_take shim_take4_spec) /\
  (@semax_body hc4_V_warn hc4_G_none CS4s WgNoise.harness.x_cookie_mac.code.f_shim_no_warning shim_no_warning4_spec) /\
  (@semax_body hc4_V_shim hc4_G_shim_same CS4s WgNoise.harness.x_cookie_mac.code.f_shim_same shim_same4_spec) /\
  (@semax_body [] hc4_G_dev_take CS4skb WgNoise.harness.x_cookie_mac.code.f_skb_take skb_take4_spec) /\
  (forall CSw, @semax_body [] hc4_G_dev_same CS4skb WgNoise.harness.x_cookie_mac.code.f_skb_same (skb_same4_spec CSw)) /\
  (@semax_body [] hc4_G_none CSk WgNoise.harness.x_keypairs.code.f_replay_counter_fresh replay_counter_fresh4_spec) /\
  (@semax_body [] hc4_G_peer_randomize_rest CSk WgNoise.harness.x_consume_initiation_any.code.f_peer_randomize_rest peer_randomize_rest4_spec) /\
  (@semax_body [] hc4_G_draw_peer_refs CSk WgNoise.harness.x_cookie_mac.code.f_draw_peer_refs draw_peer_refs4_spec) /\
  (@semax_body [] hc4_G_none CSk WgNoise.harness.x_handshake_receive.code.f_le32_load le32_load4_spec).
Proof.
  exact (conj hc4_body_pr_take (conj hc4_body_pr_same_but_cookie (conj hc4_body_pr_same (conj hc4_body_dev_take (conj hc4_body_dev_same (conj hc4_body_shim_take (conj hc4_body_shim_no_warning (conj hc4_body_shim_same (conj hc4_body_skb_take (conj hc4_body_skb_same (conj hc4_body_replay_counter_fresh (conj hc4_body_peer_randomize_rest (conj hc4_body_draw_peer_refs (hc4_body_le32_load)))))))))))))).
Qed.
