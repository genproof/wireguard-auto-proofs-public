(* law consume_response_any, phase Q5: statements 17..18 of P6's then-branch: if (target == NULL) CHECK(ret == NULL && hnodes_same_except(peers, NULL)) else { the acceptance CHECKs, wg_peer_put(ret), hnodes_same_except, pr_same }; free(msg).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_cut.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_conv.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_pure.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_if.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_A1.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_A2.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_A3.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_A4.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_A5.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q5_free.
Require WgNoise.harness.x_consume_response_any.code.

#[local] Existing Instance W_consume_response_any.
Local Open Scope logic.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcr5_Q5_ok {Espec: OracleKind} gv L FR :
  hcr5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> 
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_SQ4 x25519 aead_dec gv L FR) hcr5_Q5
    (overridePost (hcr5_SE x25519 gv L FR) (hcr5_R gv)).
Proof.
  intros HH.
  pose proof (hcr5_q5_pure_ok x25519 aead_dec) as HP.
  apply hcr5_q5_cut with (hcr5_q5_QE x25519 gv L FR).
  - rewrite hcr5_overridePost2.
    apply hcr5_q5_if_ok; auto.
    apply hcr5_q5_acc_cut with (hcr5_q5_QA1 x25519 aead_dec gv L FR).
    + apply hcr5_q5_A1_ok; auto.
    + apply hcr5_q5_A2_ok; auto.
    + apply hcr5_q5_A3_ok; auto.
    + apply hcr5_q5_A4_ok; auto.
    + apply hcr5_q5_A5_ok; auto.
  - apply hcr5_q5_free_ok; auto.
Qed.

End Phase.
