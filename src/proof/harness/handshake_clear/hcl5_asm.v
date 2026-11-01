(* law handshake_clear: THE ASSEMBLY, with every piece as a
   hypothesis: the law's own piece (hcl5_piece.v proves it from the phases), the shared v4 pieces (hc4_stmt.v's
   statements: protocol_piece4 and the common.h piece of the law) and the interfaces of the lower pieces.
   handshake_clear_from4 (handshake_clear_from4.v) = this lemma applied to hcl5_piece.  Proof: asm_lib's
   asm_harness_safe in the world W_handshake_clear. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_iface3.
Require Import WgNoise.proof.harness.common4.hc4_stmt.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_spec.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_defs.
Require WgNoise.contracts.x_handshake_clear.
Require Import WgNoise.proof.protocol.prot3c_bridge.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_asm_a.

Lemma hcl5_asm_from :
  (forall x25519, hcl5_hyps x25519 -> piece_ok [u_hcl5] (hcl5_imports x25519) hcl5_G) ->
  prot4_piece_stmt -> hc4_piece_stmt_handshake_clear ->
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_handshake_clear.whole_prog.
Proof.
  intros HM Hprot Hhc (Gb & HpB & HidB & HcovB) HA HX.
  destruct (prot3c_aead HA) as (Ga & enc & dec & xenc & xdec & Hap & Hxap & HpA & HidA & HcovA & HcovD & HccA).
  destruct (prot3c_x25519 HX) as (Gx & x & Hxp & HpX & HidX & HcovX & HccX & _ & _).
  assert (HMx := HM x (conj Hxp hcl5a_rep_ok)).
  eapply (hcl5a_safe Gb Ga Gx x enc dec xenc xdec); eassumption.
Qed.
