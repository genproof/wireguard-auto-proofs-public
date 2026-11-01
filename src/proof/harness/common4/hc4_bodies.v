(* the common.h piece of each any-state law,
   FROM the four body groups' statements (hc4_body_stmts.v; proved in hc4_body_<group>.v, instantiated in
   hc4_pieces_final.v): `hc4_pieces_of : hc4_bodies_snap_stmt -> hc4_bodies_hs_stmt -> hc4_bodies_hnodes_stmt ->
   hc4_bodies_kents_stmt -> hc4_piece_stmt_<law> /\ ...` (hc4_stmt.v).  Each piece: the law unit's copies of the
   common.h functions (hc4_G_<law>, hc4_prog.v) against their specifications, imports hc4_imports, for ANY primitive
   models with the prim_api properties and ANY world compspecs CSw containing CS4.  Method = hc_bodies3.v's: the
   unchanged functions by v1's hc3_body_*.v lemmas (proved, in the base), the v2 ones by the hypotheses, each lifted
   with hc3_lift (hc3_Gsub against hc4_imports ++ hc4_G_<law>, cspecs_sub of the small compspecs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import QuickProof.Env.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_stmt.
Require Import WgNoise.proof.harness.common4.hc4_body_stmts.
Require WgNoise.proof.harness.common4.hc4a_config_any WgNoise.proof.harness.common4.hc4a_consume_initiation_any
  WgNoise.proof.harness.common4.hc4a_consume_response_any WgNoise.proof.harness.common4.hc4a_cookie_mac
  WgNoise.proof.harness.common4.hc4a_cookie_reply WgNoise.proof.harness.common4.hc4a_create_any
  WgNoise.proof.harness.common4.hc4a_handshake_clear WgNoise.proof.harness.common4.hc4a_handshake_receive
  WgNoise.proof.harness.common4.hc4a_keypairs.

Theorem hc4_pieces_of :
  hc4_bodies_snap_stmt -> hc4_bodies_hs_stmt -> hc4_bodies_hnodes_stmt -> hc4_bodies_kents_stmt ->
  hc4_piece_stmt_config_any /\
  hc4_piece_stmt_consume_initiation_any /\
  hc4_piece_stmt_consume_response_any /\
  hc4_piece_stmt_cookie_mac /\
  hc4_piece_stmt_cookie_reply /\
  hc4_piece_stmt_create_any /\
  hc4_piece_stmt_handshake_clear /\
  hc4_piece_stmt_handshake_receive /\
  hc4_piece_stmt_keypairs.
Proof.
  intros S H N K.
  exact (conj (WgNoise.proof.harness.common4.hc4a_config_any.hc4a_piece_config_any S H N K)
    (conj (WgNoise.proof.harness.common4.hc4a_consume_initiation_any.hc4a_piece_consume_initiation_any S H N K)
    (conj (WgNoise.proof.harness.common4.hc4a_consume_response_any.hc4a_piece_consume_response_any S H N K)
    (conj (WgNoise.proof.harness.common4.hc4a_cookie_mac.hc4a_piece_cookie_mac S H N K)
    (conj (WgNoise.proof.harness.common4.hc4a_cookie_reply.hc4a_piece_cookie_reply S H N K)
    (conj (WgNoise.proof.harness.common4.hc4a_create_any.hc4a_piece_create_any S H N K)
    (conj WgNoise.proof.harness.common4.hc4a_handshake_clear.hc4a_piece_handshake_clear
    (conj (WgNoise.proof.harness.common4.hc4a_handshake_receive.hc4a_piece_handshake_receive S H N K)
    (WgNoise.proof.harness.common4.hc4a_keypairs.hc4a_piece_keypairs S H N K))))))))).
Qed.
