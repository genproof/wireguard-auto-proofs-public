(* the law consume_initiation_any, closed (Qed; nothing assumed in its closure).

   The proof: consume_initiation_any_from4 (the law from the statements of the
   shared v4 pieces) applied to the shared pieces. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface3.
Require WgNoise.contracts.x_consume_initiation_any.
Require Import WgNoise.proof.harness.common4.hc4_pieces_final.
Require Import WgNoise.proof.harness.consume_initiation_any.consume_initiation_any_from4.

Theorem consume_initiation_any_safe5 :
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_consume_initiation_any.whole_prog.
Proof.
  exact (consume_initiation_any_from4 prot4_piece_ok hc4_piece_consume_initiation_any).
Qed.
