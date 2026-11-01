(* the law consume_response_any, closed (Qed; nothing assumed in its closure).
*)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface3.
Require WgNoise.contracts.x_consume_response_any.
Require Import WgNoise.proof.harness.common4.hc4_pieces_final.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_from.

Theorem consume_response_any_safe5 :
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_consume_response_any.whole_prog.
Proof.
  exact (consume_response_any_from5 prot4_piece_ok hc4_piece_consume_response_any).
Qed.
