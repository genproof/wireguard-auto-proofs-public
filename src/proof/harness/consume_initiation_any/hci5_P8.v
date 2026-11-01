(* law consume_initiation_any: main's phase P8, statements 31..38: init_img(img_after, msg); CHECK(bytes_eq(img, img_after)); CHECK(dev_same && itb.head == head0 && kents_same && shim_same); if (target == NULL) CHECK(ret == NULL && hnodes_same_except(peers, NULL)) else { the CHECKs of the accepted peer, wg_peer_put }; free(msg); kents_free(kes); hnodes_free(peers); return 0.
   (states: hci5_defs.v).
   harness/consume_initiation_any/hci3_*.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_cut.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_model.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_globals.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_conv.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_a.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_b.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_if.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A1.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A2.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_c.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

Section P8.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_P8_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> hci5_closeH ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_S7 x25519 aead_dec gv L FR) hci5_P8
    (overridePost FF (hci5_R gv)).
Proof.
  intros HH HC.
  apply hci5_p8_cut with (hci5_p8_Q1 x25519 aead_dec gv L FR) (hci5_p8_Q2 x25519 gv L FR).
  - apply hci5_p8_a_ok with (xaead_enc := xaead_enc) (xaead_dec := xaead_dec); auto.
  - apply hci5_p8_b_ok with (xaead_enc := xaead_enc) (xaead_dec := xaead_dec); auto.
  - apply hci5_p8_if_ok with (xaead_enc := xaead_enc) (xaead_dec := xaead_dec); auto.
    apply hci5_p8_acc_cut with (hci5_p8_QA1 x25519 aead_dec gv L FR).
    + apply hci5_p8_A1_ok with (xaead_enc := xaead_enc) (xaead_dec := xaead_dec); auto.
    + apply hci5_p8_A2_ok with (xaead_enc := xaead_enc) (xaead_dec := xaead_dec); auto.
    + apply hci5_p8_A3_ok with (xaead_enc := xaead_enc) (xaead_dec := xaead_dec); auto.
  - rewrite <- (hci5_overridePost2 FF FF (hci5_R gv)).
    apply hci5_p8_c_ok with (xaead_enc := xaead_enc) (xaead_dec := xaead_dec); auto.
Qed.

End P8.
