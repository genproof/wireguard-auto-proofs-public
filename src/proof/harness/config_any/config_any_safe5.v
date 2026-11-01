(* the law config_any, closed (Qed; nothing assumed in its closure).
*)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface3.
Require WgNoise.contracts.x_config_any.
Require Import WgNoise.proof.harness.common4.hc4_pieces_final.
Require Import WgNoise.proof.harness.config_any.config_any_from4.

Theorem config_any_safe5 :
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_config_any.whole_prog.
Proof.
  exact (config_any_from4 prot4_piece_ok hc4_piece_config_any).
Qed.
