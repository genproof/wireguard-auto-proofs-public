(* the statements of the four body groups of the common.h v2
   layer as Props (= the types of hc4_bodies_<group> in hc4_body_<group>.v), so that the assembly hc4_bodies.v is
   proved from them while the groups are being proved. *)
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

Definition hc4_bodies_snap_stmt : Prop :=
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

Definition hc4_bodies_hs_stmt : Prop :=
  (@semax_body [] hc4_G_hs_take CSkh WgNoise.harness.x_handshake.code.f_hs_take hs_take4_spec) /\
  (forall CSw, @semax_body [] hc4_G_hs_same CSkh WgNoise.harness.x_handshake.code.f_hs_same (hs_same4_spec CSw)) /\
  (forall CSw, @semax_body [] hc4_G_hs_zeroed_from CSkh WgNoise.harness.x_keypairs.code.f_hs_zeroed_from (hs_zeroed_from4_spec CSw)) /\
  (forall CSw, @semax_body [] hc4_G_hs_same CSkh WgNoise.harness.x_keypairs.code.f_hs_same_but_next (hs_same_but_next4_spec CSw)) /\
  (@semax_body [] hc4_G_hs_randomize CSk WgNoise.harness.x_consume_response_any.code.f_hs_randomize hs_randomize4_spec) /\
  (forall x25519, @semax_body [] (hc4_G_setup_device x25519) CSk WgNoise.harness.x_handshake.code.f_setup_device (setup_device4_spec x25519)) /\
  (@semax_body hc4_V_real_clock hc4_G_draw_real_clock CSk WgNoise.harness.x_handshake.code.f_draw_real_clock draw_real_clock4_spec).

Definition hc4_bodies_hnodes_stmt : Prop :=
  (forall x25519 CSw, cspecs_sub CS4 CSw -> @semax_body [] (hc4_G_hnodes_add x25519 CSw) CS4 WgNoise.harness.x_consume_initiation_any.code.f_hnodes_add (hnodes_add4_spec x25519 CSw)) /\
  (forall CSw, @semax_body [] hc4_G_hnodes_snap CS4 WgNoise.harness.x_consume_initiation_any.code.f_hnodes_snap (hnodes_snap4_spec CSw)) /\
  (forall CSw, @semax_body [] (hc4_G_hnodes_same_except CSw) CS4 WgNoise.harness.x_consume_initiation_any.code.f_hnodes_same_except (hnodes_same_except4_spec CSw)) /\
  (forall CSw, cspecs_sub CS4 CSw -> @semax_body [] (hc4_G_free CSw) CS4 WgNoise.harness.x_consume_initiation_any.code.f_hnodes_free (hnodes_free4_spec CSw)) /\
  (forall CSw, @semax_body [] hc4_G_hnodes_pick CS4 WgNoise.harness.x_cookie_mac.code.f_hnodes_pick (hnodes_pick4_spec CSw)).

Definition hc4_bodies_kents_stmt : Prop :=
  (forall CSw, cspecs_sub CS4 CSw -> @semax_body [] (hc4_G_kents_add CSw) CS4 WgNoise.harness.x_cookie_mac.code.f_kents_add (kents_add4_spec CSw)) /\
  (forall CSw, @semax_body [] hc4_G_dev_take CS4 WgNoise.harness.x_cookie_mac.code.f_kents_snap (kents_snap4_spec CSw)) /\
  (forall CSw, @semax_body [] hc4_G_dev_same CS4 WgNoise.harness.x_cookie_mac.code.f_kent_same_but_next (kent_same_but_next4_spec CSw)) /\
  (forall CSw, @semax_body [] (hc4_G_kents_same CSw) CS4 WgNoise.harness.x_cookie_mac.code.f_kents_same (kents_same4_spec CSw)) /\
  (forall CSw, @semax_body [] (hc4_G_kents_same_but_next CSw) CS4 WgNoise.harness.x_keypairs.code.f_kents_same_but_next (kents_same_but_next4_spec CSw)) /\
  (forall CSw, @semax_body [] hc4_G_none CS4 WgNoise.harness.x_keypairs.code.f_kents_hashed (kents_hashed4_spec CSw)) /\
  (forall CSw, cspecs_sub CS4 CSw -> @semax_body [] (hc4_G_free CSw) CS4 WgNoise.harness.x_cookie_mac.code.f_kents_free (kents_free4_spec CSw)).
