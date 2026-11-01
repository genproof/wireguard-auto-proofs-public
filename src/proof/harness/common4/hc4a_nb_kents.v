(* the bodies of group KENTS that law handshake_clear's unit contains (kents_add, kents_snap, kent_same_but_next, kents_same_but_next, kents_hashed, kents_free),
   at the compspecs WITHOUT struct blake2s_ctx (hc4a_nb_cs.v: CS4nb, CS4snb, CSknb, CSkhnb), because handshake_clear's
   unit has no blake2s_ctx and a semax_body only lifts to a larger compspecs.  The same statements as
   hc4_body_stmts.v's hc4_bodies_kents_stmt (contexts with nondet_bytes at the small compspecs: hc4a_nb_ctx.v). *)
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
Require Import WgNoise.proof.harness.common4.hc4nb2_ke_cs WgNoise.proof.harness.common4.hc4nb2_ke_hf2
  WgNoise.proof.harness.common4.hc4nb2_ke_sbn WgNoise.proof.harness.common4.hc4nb2_ke_snap
  WgNoise.proof.harness.common4.hc4nb2_ke_add_split WgNoise.proof.harness.common4.hc4nb2_ke_add_segC
  WgNoise.proof.harness.common4.hc4nb2_ke_add_segD WgNoise.proof.harness.common4.hc4nb2_ke_add
  WgNoise.proof.harness.common4.hc4nb2_ke_k1_vp WgNoise.proof.harness.common4.hc4nb2_ke_k1.

Theorem hc4a_nb_bodies_kents :
  (forall CSw, cspecs_sub CS4 CSw -> @semax_body [] (hc4nb_G_kents_add CSw) CS4nb WgNoise.harness.x_cookie_mac.code.f_kents_add (kents_add4_spec CSw)) /\
  (forall CSw, @semax_body [] hc4_G_dev_take CS4nb WgNoise.harness.x_cookie_mac.code.f_kents_snap (kents_snap4_spec CSw)) /\
  (forall CSw, @semax_body [] hc4_G_dev_same CS4nb WgNoise.harness.x_cookie_mac.code.f_kent_same_but_next (kent_same_but_next4_spec CSw)) /\
  (forall CSw, @semax_body [] (hc4_G_kents_same_but_next CSw) CS4nb WgNoise.harness.x_keypairs.code.f_kents_same_but_next (kents_same_but_next4_spec CSw)) /\
  (forall CSw, @semax_body [] hc4_G_none CS4nb WgNoise.harness.x_keypairs.code.f_kents_hashed (kents_hashed4_spec CSw)) /\
  (forall CSw, cspecs_sub CS4 CSw -> @semax_body [] (hc4_G_free CSw) CS4nb WgNoise.harness.x_cookie_mac.code.f_kents_free (kents_free4_spec CSw)).
Proof.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - intros CSw H.
    exact (hc4nb2_ke_add_ok hc4nb2_ke_add_split (@hc4nb2_ke_add_segC_ok) (@hc4nb2_ke_add_segD_ok) CSw
             (hc4nb2_ke_cs_sub_w CSw H)).
  - intros CSw. apply hc4nb2_ke_snap_ok.
  - intros CSw. exact (hc4nb2_ke_k1_ok CSw hc4nb2_ke_k1_HV_ok).
  - intros CSw. apply hc4nb2_ke_sbn_ok.
  - intros CSw. apply hc4nb2_ke_hf_hashed_ok.
  - intros CSw H. apply hc4nb2_ke_hf_free_ok. exact (hc4nb2_ke_cs_sub_w CSw H).
Qed.
