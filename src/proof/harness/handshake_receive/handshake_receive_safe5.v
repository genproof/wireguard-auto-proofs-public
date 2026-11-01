(* the law handshake_receive, closed (Qed; nothing assumed in its closure).
*)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface3.
Require WgNoise.contracts.x_handshake_receive.
Require Import WgNoise.proof.harness.common4.hc4_pieces_final.
Require Import WgNoise.proof.harness.handshake_receive.handshake_receive_from4.

Theorem handshake_receive_safe5 :
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_handshake_receive.whole_prog.
Proof.
  exact (handshake_receive_from4 prot4_piece_ok hc4_piece_handshake_receive).
Qed.
