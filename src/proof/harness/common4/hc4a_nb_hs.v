(* the bodies of group HS that law handshake_clear's unit contains (hs_take, hs_zeroed_from, hs_same_but_next, hs_randomize, setup_device),
   at the compspecs WITHOUT struct blake2s_ctx (hc4a_nb_cs.v: CS4nb, CS4snb, CSknb, CSkhnb), because handshake_clear's
   unit has no blake2s_ctx and a semax_body only lifts to a larger compspecs.  The same statements as
   hc4_body_stmts.v's hc4_bodies_hs_stmt (contexts with nondet_bytes at the small compspecs: hc4a_nb_ctx.v). *)
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
Require Import WgNoise.proof.harness.common4.hc4a_nb_cs.
Require Import WgNoise.proof.harness.common4.hc4a_nb_ctx.
Require WgNoise.proof.harness.common4.hc4nb2_hs_take WgNoise.proof.harness.common4.hc4nb2_hs_zf
        WgNoise.proof.harness.common4.hc4nb2_hs_sbn WgNoise.proof.harness.common4.hc4nb2_hs_rand
        WgNoise.proof.harness.common4.hc4nb2_hs_setup.

Theorem hc4a_nb_bodies_hs :
  (@semax_body [] hc4_G_hs_take CSkhnb WgNoise.harness.x_handshake.code.f_hs_take hs_take4_spec) /\
  (forall CSw, @semax_body [] hc4_G_hs_zeroed_from CSkhnb WgNoise.harness.x_keypairs.code.f_hs_zeroed_from (hs_zeroed_from4_spec CSw)) /\
  (forall CSw, @semax_body [] hc4_G_hs_same CSkhnb WgNoise.harness.x_keypairs.code.f_hs_same_but_next (hs_same_but_next4_spec CSw)) /\
  (@semax_body [] hc4nb_G_hs_randomize CSknb WgNoise.harness.x_consume_response_any.code.f_hs_randomize hs_randomize4_spec) /\
  (forall x25519, @semax_body [] (hc4_G_setup_device x25519) CSknb WgNoise.harness.x_handshake.code.f_setup_device (setup_device4_spec x25519)).
Proof.
  split; [exact WgNoise.proof.harness.common4.hc4nb2_hs_take.hc4nb2_hs_take_body|].
  split; [exact WgNoise.proof.harness.common4.hc4nb2_hs_zf.hc4nb2_hs_zf_body|].
  split; [exact WgNoise.proof.harness.common4.hc4nb2_hs_sbn.hc4nb2_hs_sbn_body|].
  split; [exact WgNoise.proof.harness.common4.hc4nb2_hs_rand.hc4nb2_hs_rand_body|].
  exact WgNoise.proof.harness.common4.hc4nb2_hs_setup.hc4nb2_hs_setup_body.
Qed.
