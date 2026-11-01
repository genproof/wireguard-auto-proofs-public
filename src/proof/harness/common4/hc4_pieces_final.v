(* the shared v4 pieces, unconditional: protocol_piece4 and the
   common.h piece of each any-state law (hc4_pieces_of applied to the four body groups). *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.protocol4.prot_piece4.
Require Import WgNoise.proof.harness.common4.hc4_stmt.
Require Import WgNoise.proof.harness.common4.hc4_body_stmts.
Require Import WgNoise.proof.harness.common4.hc4_bodies.
Require Import WgNoise.proof.harness.common4.hc4_body_snap WgNoise.proof.harness.common4.hc4_body_hs
  WgNoise.proof.harness.common4.hc4_body_hnodes WgNoise.proof.harness.common4.hc4_body_kents.

Lemma prot4_piece_ok : prot4_piece_stmt.
Proof. exact protocol_piece4. Qed.

Lemma hc4_pieces_all : hc4_piece_stmt_config_any /\
  hc4_piece_stmt_consume_initiation_any /\
  hc4_piece_stmt_consume_response_any /\
  hc4_piece_stmt_cookie_mac /\
  hc4_piece_stmt_cookie_reply /\
  hc4_piece_stmt_create_any /\
  hc4_piece_stmt_handshake_clear /\
  hc4_piece_stmt_handshake_receive /\
  hc4_piece_stmt_keypairs.
Proof. exact (hc4_pieces_of hc4_bodies_snap hc4_bodies_hs hc4_bodies_hnodes hc4_bodies_kents). Qed.

Lemma hc4_piece_config_any : hc4_piece_stmt_config_any.
Proof. exact (proj1 (hc4_pieces_all)). Qed.

Lemma hc4_piece_consume_initiation_any : hc4_piece_stmt_consume_initiation_any.
Proof. exact (proj1 (proj2 (hc4_pieces_all))). Qed.

Lemma hc4_piece_consume_response_any : hc4_piece_stmt_consume_response_any.
Proof. exact (proj1 (proj2 (proj2 (hc4_pieces_all)))). Qed.

Lemma hc4_piece_cookie_mac : hc4_piece_stmt_cookie_mac.
Proof. exact (proj1 (proj2 (proj2 (proj2 (hc4_pieces_all))))). Qed.

Lemma hc4_piece_cookie_reply : hc4_piece_stmt_cookie_reply.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (hc4_pieces_all)))))). Qed.

Lemma hc4_piece_create_any : hc4_piece_stmt_create_any.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (hc4_pieces_all))))))). Qed.

Lemma hc4_piece_handshake_clear : hc4_piece_stmt_handshake_clear.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (hc4_pieces_all)))))))). Qed.

Lemma hc4_piece_handshake_receive : hc4_piece_stmt_handshake_receive.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (hc4_pieces_all))))))))). Qed.

Lemma hc4_piece_keypairs : hc4_piece_stmt_keypairs.
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (hc4_pieces_all))))))))). Qed.
