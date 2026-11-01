(* the law cookie_mac, closed (Qed; nothing assumed in its closure).
*)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface3.
Require WgNoise.contracts.x_cookie_mac.
Require Import WgNoise.proof.harness.common4.hc4_pieces_final.
Require Import WgNoise.proof.harness.cookie_mac.hck5_final.

Theorem cookie_mac_safe5 :
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_cookie_mac.whole_prog.
Proof.
  exact (hck5_from4 prot4_piece_ok hc4_piece_cookie_mac).
Qed.
