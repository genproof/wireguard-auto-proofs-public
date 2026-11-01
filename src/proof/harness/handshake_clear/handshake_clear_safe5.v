(* the law handshake_clear, closed (Qed; nothing assumed in its closure).

   The proof: handshake_clear_from4
   applied to the shared pieces. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface3.
Require WgNoise.contracts.x_handshake_clear.
Require Import WgNoise.proof.harness.common4.hc4_pieces_final.
Require Import WgNoise.proof.harness.handshake_clear.handshake_clear_from4.

Theorem handshake_clear_safe5 :
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_handshake_clear.whole_prog.
Proof.
  exact (handshake_clear_from4 prot4_piece_ok hc4_piece_handshake_clear).
Qed.
