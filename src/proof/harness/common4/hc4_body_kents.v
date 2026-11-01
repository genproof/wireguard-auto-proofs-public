(* the bodies of group `kents` of the common.h v2 layer: each proved ONCE at a small compspecs (hc4_cs.v / hc3_cs.v) with
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
Require Import WgNoise.proof.harness.common4.hc4b_ke_hf2.
Require Import WgNoise.proof.harness.common4.hc4b_ke_sbn.
Require Import WgNoise.proof.harness.common4.hc4b_ke_same_vp.
Require Import WgNoise.proof.harness.common4.hc4b_ke_same.
Require Import WgNoise.proof.harness.common4.hc4b_ke_snap.
Require Import WgNoise.proof.harness.common4.hc4b_ke_k1_vp.
Require Import WgNoise.proof.harness.common4.hc4b_ke_k1.
Require Import WgNoise.proof.harness.common4.hc4b_ke_add_split.
Require Import WgNoise.proof.harness.common4.hc4b_ke_add_segC.
Require Import WgNoise.proof.harness.common4.hc4b_ke_add_segD.
Require Import WgNoise.proof.harness.common4.hc4b_ke_add.

Lemma hc4_body_kents_add :
  forall CSw, cspecs_sub CS4 CSw -> @semax_body [] (hc4_G_kents_add CSw) CS4 WgNoise.harness.x_cookie_mac.code.f_kents_add (kents_add4_spec CSw).
Proof.
  exact (hc4b_ke_add_ok hc4b_ke_add_split (@hc4b_ke_add_segC_ok) (@hc4b_ke_add_segD_ok)).
Qed.

Lemma hc4_body_kents_snap :
  forall CSw, @semax_body [] hc4_G_dev_take CS4 WgNoise.harness.x_cookie_mac.code.f_kents_snap (kents_snap4_spec CSw).
Proof.
  intros CSw. exact (hc4b_ke_snap_ok CSw).
Qed.

Lemma hc4_body_kent_same_but_next :
  forall CSw, @semax_body [] hc4_G_dev_same CS4 WgNoise.harness.x_cookie_mac.code.f_kent_same_but_next (kent_same_but_next4_spec CSw).
Proof.
  intros CSw. exact (hc4b_ke_k1_ok CSw hc4b_ke_k1_HV_ok).
Qed.

Lemma hc4_body_kents_same :
  forall CSw, @semax_body [] (hc4_G_kents_same CSw) CS4 WgNoise.harness.x_cookie_mac.code.f_kents_same (kents_same4_spec CSw).
Proof.
  intros CSw. exact (hc4b_ke_same_ok_HV CSw hc4b_ke_same_HV_ok).
Qed.

Lemma hc4_body_kents_same_but_next :
  forall CSw, @semax_body [] (hc4_G_kents_same_but_next CSw) CS4 WgNoise.harness.x_keypairs.code.f_kents_same_but_next (kents_same_but_next4_spec CSw).
Proof.
  exact hc4b_ke_sbn_ok.
Qed.

Lemma hc4_body_kents_hashed :
  forall CSw, @semax_body [] hc4_G_none CS4 WgNoise.harness.x_keypairs.code.f_kents_hashed (kents_hashed4_spec CSw).
Proof.
  exact hc4b_ke_hf_hashed_ok.
Qed.

Lemma hc4_body_kents_free :
  forall CSw, cspecs_sub CS4 CSw -> @semax_body [] (hc4_G_free CSw) CS4 WgNoise.harness.x_cookie_mac.code.f_kents_free (kents_free4_spec CSw).
Proof.
  exact hc4b_ke_hf_free_ok.
Qed.

(* the group *)
Theorem hc4_bodies_kents :
  (forall CSw, cspecs_sub CS4 CSw -> @semax_body [] (hc4_G_kents_add CSw) CS4 WgNoise.harness.x_cookie_mac.code.f_kents_add (kents_add4_spec CSw)) /\
  (forall CSw, @semax_body [] hc4_G_dev_take CS4 WgNoise.harness.x_cookie_mac.code.f_kents_snap (kents_snap4_spec CSw)) /\
  (forall CSw, @semax_body [] hc4_G_dev_same CS4 WgNoise.harness.x_cookie_mac.code.f_kent_same_but_next (kent_same_but_next4_spec CSw)) /\
  (forall CSw, @semax_body [] (hc4_G_kents_same CSw) CS4 WgNoise.harness.x_cookie_mac.code.f_kents_same (kents_same4_spec CSw)) /\
  (forall CSw, @semax_body [] (hc4_G_kents_same_but_next CSw) CS4 WgNoise.harness.x_keypairs.code.f_kents_same_but_next (kents_same_but_next4_spec CSw)) /\
  (forall CSw, @semax_body [] hc4_G_none CS4 WgNoise.harness.x_keypairs.code.f_kents_hashed (kents_hashed4_spec CSw)) /\
  (forall CSw, cspecs_sub CS4 CSw -> @semax_body [] (hc4_G_free CSw) CS4 WgNoise.harness.x_cookie_mac.code.f_kents_free (kents_free4_spec CSw)).
Proof.
  exact (conj hc4_body_kents_add (conj hc4_body_kents_snap (conj hc4_body_kent_same_but_next (conj hc4_body_kents_same (conj hc4_body_kents_same_but_next (conj hc4_body_kents_hashed (hc4_body_kents_free))))))).
Qed.
