(* the law config_any from the statements of the shared v4
   pieces (hc4_stmt.v: protocol_piece4's and the common.h piece's), so that the law's proof does not wait for their
   bodies.  config_any_safe5 (config_any_safe5.v) = this theorem applied to prot4_piece_ok and hc4_piece_config_any
   (hc4_bodies.v). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface3.
Require Import WgNoise.proof.harness.common4.hc4_stmt.
Require WgNoise.contracts.x_config_any.
Require Import WgNoise.proof.harness.config_any.hcf5_piece.
Require Import WgNoise.proof.harness.config_any.hcf5_asm.

Theorem config_any_from4 :
  prot4_piece_stmt -> hc4_piece_stmt_config_any ->
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_config_any.whole_prog.
Proof.
  exact (hcf5_asm hcf5_piece).
Qed.
