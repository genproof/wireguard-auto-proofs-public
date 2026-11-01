(* the law handshake_receive from the statements of the
   shared v4 pieces (hc4_stmt.v: protocol_piece4's and the common.h piece's), so that the law's proof does not wait
   for their bodies.  handshake_receive_safe5 = this theorem applied to prot4_piece_ok and
   hc4_piece_handshake_receive (hc4_pieces_final.v).  The proof: the assembly hrx5_asm_from (hrx5_asm.v) applied to
   the law's pieces hrx5_mpiece (main) and hrx5_lpiece (the harness unit's other functions). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface3.
Require Import WgNoise.proof.harness.common4.hc4_stmt.
Require WgNoise.contracts.x_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_piece.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_lpiece.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_asm.

Theorem handshake_receive_from4 :
  prot4_piece_stmt -> hc4_piece_stmt_handshake_receive ->
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_handshake_receive.whole_prog.
Proof.
  exact (hrx5_asm_from hrx5_mpiece hrx5_lpiece).
Qed.
