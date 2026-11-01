(* the law keypairs, closed (Qed; nothing assumed in its closure).
*)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface3.
Require WgNoise.contracts.x_keypairs.
Require Import WgNoise.proof.harness.common4.hc4_pieces_final.
Require Import WgNoise.proof.harness.keypairs.hkp5_piece.
Require Import WgNoise.proof.harness.keypairs.hkp5_from.

Theorem keypairs_safe5 :
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_keypairs.whole_prog.
Proof.
  exact (keypairs_from5 prot4_piece_ok hc4_piece_keypairs hkp5_piece).
Qed.
