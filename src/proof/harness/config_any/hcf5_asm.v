(* law config_any: the assembly: for
   ANY lower pieces satisfying the interfaces (blake2s3_ok, aead3b_ok, x25519_ok3c, via prot3c_bridge's prot3c_aead /
   prot3c_x25519 as replay_safe3c.v / handshake_safe4.v do), the libc piece, the protocol piece (prot4_piece_stmt:
   protocol_piece4's statement), the common.h piece (hc4_piece_stmt_config_any, with CSw := W_config_any and
   cspecs_sub CS4 W_config_any: hcf5_world.v's hcf5_cs4_sub) and the law's piece (hcf5_piece_stmt: main), assembled
   with asm_lib's asm_harness_safe in the world W_config_any (hcf5_world.v). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface3.
Require Import WgNoise.proof.harness.common4.hc4_stmt.
Require Import WgNoise.proof.harness.config_any.hcf5_world.
Require Import WgNoise.proof.harness.config_any.hcf5_spec.
Require Import WgNoise.proof.harness.config_any.hcf5_piece.
Require WgNoise.contracts.x_config_any.
Require Import WgNoise.proof.protocol.prot3c_bridge.
Require Import WgNoise.proof.harness.config_any.hcf5_asm_a.

Theorem hcf5_asm :
  hcf5_piece_stmt -> prot4_piece_stmt -> hc4_piece_stmt_config_any ->
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_config_any.whole_prog.
Proof.
  intros HM Hprot Hhc (Gb & HpB & HidB & HcovB) HA HX.
  destruct (prot3c_aead HA) as (Ga & enc & dec & xenc & xdec & Hap & Hxap & HpA & HidA & HcovA & HcovD & HccA).
  destruct (prot3c_x25519 HX) as (Gx & x & Hxp & HpX & HidX & HcovX & HccX & _ & _).
  assert (HMx := HM x Hxp).
  eapply (hcf5_asm_safe Gb Ga Gx x enc dec xenc xdec); eassumption.
Qed.
