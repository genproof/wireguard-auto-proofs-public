(* the bodies of group HNODES that law handshake_clear's unit contains (hnodes_add, hnodes_snap, hnodes_free, hnodes_pick),
   at the compspecs WITHOUT struct blake2s_ctx (hc4a_nb_cs.v: CS4nb, CS4snb, CSknb, CSkhnb), because handshake_clear's
   unit has no blake2s_ctx and a semax_body only lifts to a larger compspecs.  The same statements as
   hc4_body_stmts.v's hc4_bodies_hnodes_stmt (contexts with nondet_bytes at the small compspecs: hc4a_nb_ctx.v). *)
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
Require Import WgNoise.proof.harness.common4.hc4nb2_hn_fp WgNoise.proof.harness.common4.hc4nb2_hn_snap
  WgNoise.proof.harness.common4.hc4nb2_hn_add.

Theorem hc4a_nb_bodies_hnodes :
  (forall x25519 CSw, cspecs_sub CS4 CSw -> @semax_body [] (hc4nb_G_hnodes_add x25519 CSw) CS4nb WgNoise.harness.x_consume_initiation_any.code.f_hnodes_add (hnodes_add4_spec x25519 CSw)) /\
  (forall CSw, @semax_body [] hc4_G_hnodes_snap CS4nb WgNoise.harness.x_consume_initiation_any.code.f_hnodes_snap (hnodes_snap4_spec CSw)) /\
  (forall CSw, cspecs_sub CS4 CSw -> @semax_body [] (hc4_G_free CSw) CS4nb WgNoise.harness.x_consume_initiation_any.code.f_hnodes_free (hnodes_free4_spec CSw)) /\
  (forall CSw, @semax_body [] hc4_G_hnodes_pick CS4nb WgNoise.harness.x_cookie_mac.code.f_hnodes_pick (hnodes_pick4_spec CSw)).
Proof.
  split; [intros x25519 CSw HSUB; exact (hc4nb_hna_body x25519 CSw HSUB) |].
  split; [intros CSw; exact (hc4nb2_hn_snap_body CSw) |].
  split; [intros CSw HSUB; exact (hc4nb2_hn_free_body CSw HSUB) |].
  intros CSw; exact (hc4nb2_hn_pick_body CSw).
Qed.
