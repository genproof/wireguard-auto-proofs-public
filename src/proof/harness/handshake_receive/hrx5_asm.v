(* law handshake_receive: THE ASSEMBLY, with every piece
   as a hypothesis: the law's two pieces (main at the world compspecs W_handshake_receive: hrx5_mspec's
   hrx5_mpiece_stmt, proved in hrx5_piece.v; the harness unit's other functions at HRX: hrx5_spec's
   hrx5_lpiece_stmt, proved in hrx5_lpiece.v), the shared v4 pieces (hc4_stmt.v's statements: protocol_piece4 and
   the common.h piece of the law) and the interfaces of the lower pieces.  Proof: asm_lib's asm_harness_safe in the
   world W_handshake_receive. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_iface3.
Require Import WgNoise.proof.harness.common4.hc4_stmt.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require WgNoise.contracts.x_handshake_receive.
Require Import WgNoise.proof.protocol.prot3c_bridge.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_asm_a.

Lemma hrx5_asm_from :
  hrx5_mpiece_stmt -> hrx5_lpiece_stmt ->
  prot4_piece_stmt -> hc4_piece_stmt_handshake_receive ->
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_handshake_receive.whole_prog.
Proof.
  intros HM HL Hprot Hhc (Gb & HpB & HidB & HcovB) HA HX.
  destruct (prot3c_aead HA) as (Ga & enc & dec & xenc & xdec & Hap & Hxap & HpA & HidA & HcovA & HcovD & HccA).
  destruct (prot3c_x25519 HX) as (Gx & x & Hxp & HpX & HidX & HcovX & HccX & _ & _).
  assert (HMx := HM x enc dec xenc xdec Hxp Hap Hxap).
  assert (HLx := HL x enc dec xenc xdec W_handshake_receive Hxp Hap Hxap).
  eapply (hrx5a_safe Gb Ga Gx x enc dec xenc xdec); eassumption.
Qed.
