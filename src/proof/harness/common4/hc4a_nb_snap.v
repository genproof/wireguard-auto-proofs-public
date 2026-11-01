(* the bodies of group SNAP that law handshake_clear's unit contains (pr_take, pr_same_but_cookie, pr_same, dev_take, dev_same, shim_take, shim_no_warning, shim_same, peer_randomize_rest, draw_peer_refs),
   at the compspecs WITHOUT struct blake2s_ctx (hc4a_nb_cs.v: CS4nb, CS4snb, CSknb, CSkhnb), because handshake_clear's
   unit has no blake2s_ctx and a semax_body only lifts to a larger compspecs.  The same statements as
   hc4_body_stmts.v's hc4_bodies_snap_stmt (contexts with nondet_bytes at the small compspecs: hc4a_nb_ctx.v). *)
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
Require Import WgNoise.proof.harness.common4.hc4nb2_snap_vobjs.
Require WgNoise.proof.harness.common4.hc4nb2_snap_take WgNoise.proof.harness.common4.hc4nb2_snap_cmp
        WgNoise.proof.harness.common4.hc4nb2_snap_dev WgNoise.proof.harness.common4.hc4nb2_snap_shim
        WgNoise.proof.harness.common4.hc4nb2_snap_misc.

Theorem hc4a_nb_bodies_snap :
  (@semax_body [] hc4_G_pr_take CS4nb WgNoise.harness.x_cookie_mac.code.f_pr_take pr_take4_spec) /\
  (forall CSw, @semax_body [] hc4_G_none CS4nb WgNoise.harness.x_cookie_mac.code.f_pr_same_but_cookie (pr_same_but_cookie4_spec CSw)) /\
  (forall CSw, @semax_body [] (hc4_G_pr_same CSw) CS4nb WgNoise.harness.x_cookie_mac.code.f_pr_same (pr_same4_spec CSw)) /\
  (@semax_body [] hc4_G_dev_take CS4nb WgNoise.harness.x_cookie_mac.code.f_dev_take dev_take4_spec) /\
  (forall CSw, @semax_body [] hc4_G_dev_same CS4nb WgNoise.harness.x_cookie_mac.code.f_dev_same (dev_same4_spec CSw)) /\
  (@semax_body hc4_V_shim hc4_G_none CS4snb WgNoise.harness.x_cookie_mac.code.f_shim_take shim_take4_spec) /\
  (@semax_body hc4_V_warn hc4_G_none CS4snb WgNoise.harness.x_cookie_mac.code.f_shim_no_warning shim_no_warning4_spec) /\
  (@semax_body hc4_V_shim hc4_G_shim_same CS4snb WgNoise.harness.x_cookie_mac.code.f_shim_same shim_same4_spec) /\
  (@semax_body [] hc4nb_G_peer_randomize_rest CSknb WgNoise.harness.x_consume_initiation_any.code.f_peer_randomize_rest peer_randomize_rest4_spec) /\
  (@semax_body [] hc4_G_draw_peer_refs CSknb WgNoise.harness.x_cookie_mac.code.f_draw_peer_refs draw_peer_refs4_spec).
Proof.
  pose proof hc4nb2_vaddrs_HV as HV.
  exact (conj WgNoise.proof.harness.common4.hc4nb2_snap_take.hc4nb2t_pr_take
        (conj (fun CSw => WgNoise.proof.harness.common4.hc4nb2_snap_cmp.hc4nb2_cmp_pr_same_but_cookie CSw HV)
        (conj WgNoise.proof.harness.common4.hc4nb2_snap_cmp.hc4nb2_cmp_pr_same
        (conj WgNoise.proof.harness.common4.hc4nb2_snap_take.hc4nb2t_dev_take
        (conj (fun CSw => WgNoise.proof.harness.common4.hc4nb2_snap_dev.hc4nb2_dev_same CSw HV)
        (conj WgNoise.proof.harness.common4.hc4nb2_snap_shim.hc4nb2s_take
        (conj WgNoise.proof.harness.common4.hc4nb2_snap_shim.hc4nb2s_nowarn
        (conj WgNoise.proof.harness.common4.hc4nb2_snap_shim.hc4nb2s_same
        (conj WgNoise.proof.harness.common4.hc4nb2_snap_misc.hc4nb2m_prr
              WgNoise.proof.harness.common4.hc4nb2_snap_misc.hc4nb2m_refs))))))))).
Qed.
