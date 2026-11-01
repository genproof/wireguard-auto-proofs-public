(* law consume_response_any: the law from the STATEMENTS of the shared v4 pieces
   (hc4_stmt.v: protocol_piece4's and the common.h piece's), the lower pieces' interfaces, the libc piece and the
   law's own piece, assembled by hcr5_asm.  consume_response_any_safe5 = this theorem applied to hc4_pieces_final's
   prot4_piece_ok and hc4_piece_consume_response_any. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface3.
Require Import WgNoise.proof.common.wg3_worlds.
Require WgNoise.contracts.x_consume_response_any.

Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol.prot3c_bridge.
Require Import WgNoise.proof.harness.common4.hc4_stmt.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_asm.
Require WgNoise.proof.libc.libc_bytes.

(* prot_rep_lemmas3 gives hcr5_rep (its last conjunct states the keypair's bytes at the world compspecs) *)
Lemma hcr5_rep_ok : hcr5_rep.
Proof.
  destruct prot_rep_lemmas3 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  repeat (split; [assumption |]).
  intros CSw k K E n h. rewrite (@WgNoise.proof.libc.libc_bytes.data_at__tarray_tuchar_cs Noise.CS CSw).
  apply A8.
Qed.

Theorem consume_response_any_from5 :
  prot4_piece_stmt -> hc4_piece_stmt_consume_response_any ->
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_consume_response_any.whole_prog.
Proof.
  intros HP HC (Gb & HpB & HidB & HcovB) A X.
  destruct (prot3c_aead A) as (Ga & enc & dec & xenc & xdec & Hap & Hxap & HpA & HidA & HcovA & HcovD & HccA).
  destruct (prot3c_x25519 X) as (Gx & x & Hxp & HpX & HidX & HcovX & HccX & _ & _).
  exact (hcr5a_safe Gb Ga Gx x enc dec xenc xdec HpB HidB HcovB Hap Hxap HpA HidA HcovA HcovD Hxp HpX HidX HcovX
           HccA HccX hcr5_rep_ok HP HC).
Qed.
