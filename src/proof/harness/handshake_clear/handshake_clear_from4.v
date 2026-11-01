(* the law handshake_clear from the statements of the
   shared v4 pieces (hc4_stmt.v: protocol_piece4's and the common.h piece's), so that the law's proof does not wait
   for their bodies (as config_any_from4.v).  handshake_clear_safe5 = this theorem applied to prot4_piece_ok and
   hc4_piece_handshake_clear (hc4_pieces_final.v).  The proof: the assembly hcl5_asm_from (hcl5_asm.v: asm_lib's
   asm_harness_safe in W_handshake_clear, every piece a hypothesis) applied to the law's piece hcl5_piece.
*)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface3.
Require Import WgNoise.proof.harness.common4.hc4_stmt.
Require WgNoise.contracts.x_handshake_clear.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_piece.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_asm.

Theorem handshake_clear_from4 :
  prot4_piece_stmt -> hc4_piece_stmt_handshake_clear ->
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_handshake_clear.whole_prog.
Proof.
  exact (hcl5_asm_from hcl5_piece).
Qed.
