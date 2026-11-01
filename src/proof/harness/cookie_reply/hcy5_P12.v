(* law cookie_reply: phase P12 of main, statements
   70..75: the ck_same loop, the target / others CHECKs, CHECK(dev_same && head0 && kents_same && shim_same), cookie_img(img2), the image CHECK, the round trip.

   (+ its children's files). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_L.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_X.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_Y.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_I.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p12_R.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_P12_ok {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_S11 x25519 xaead_enc xaead_dec gv L FR) hcy5_P12
    (overridePost (hcy5_S11 x25519 xaead_enc xaead_dec gv L FR) (hcy5_R gv)).
Proof.
  intros HH. unfold hcy5_S11 at 1.
  Intros R S m c rp Q nonce rr CK CM. Intros NS PS T np CL KE CM' honest now2.
  assert (Hinv: hcy5_p12_inv x25519 xaead_enc R L Q m nonce rr CK CM NS PS T np CL KE CM' honest now2)
    by (unfold hcy5_p12_inv; tauto).
  set (St := hcy5_p12_St x25519 xaead_dec gv L FR R S m c rp Q rr CK NS PS T np CL KE CM' honest now2).
  apply semax_pre with (P' := St); [unfold St, hcy5_p12_St; apply andp_left2; apply derives_refl |].
  rewrite hcy5_p12_P12_eq.
  apply hcy5_p12_seq with St; [eapply hcy5_p12_L_ok; [exact HH | exact Hinv] |].
  apply hcy5_p12_seq with St; [eapply hcy5_p12_X_ok; [exact HH | exact Hinv] |].
  apply hcy5_p12_seq with St; [eapply hcy5_p12_Y_ok; [exact HH | exact Hinv] |].
  apply seq_assoc.
  apply hcy5_p12_seq with St; [eapply hcy5_p12_I_ok; [exact HH | exact Hinv] |].
  eapply semax_post; [| | | | eapply hcy5_p12_R_ok; [exact HH | exact Hinv]].
  - unfold St, hcy5_p12_St. simpl RA_normal.
    apply derives_trans with (hcy5_S11 x25519 xaead_enc xaead_dec gv L FR); [| intro rho; apply derives_refl].
    unfold hcy5_S11. Exists R S m c rp Q nonce rr CK CM. Exists NS PS T np CL KE CM' honest now2.
    unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB; cbn [app].
    apply andp_left2. unfold PROPx at 2. apply andp_right; [apply prop_right; simpl; tauto |].
    unfold PROPx. apply andp_left2. apply derives_refl.
  - apply andp_left2. apply FF_left.
  - apply andp_left2. apply FF_left.
  - intros vl. apply andp_left2. apply FF_left.
Qed.

End Phase.
