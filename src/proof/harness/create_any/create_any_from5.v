(* law create_any from the statements of the shared v4 pieces, the lower pieces' interfaces (via prot3c_bridge,
   as create_any_safe4 / handshake_safe4) and the law's own piece hca5_piece; the assembly ca5_asm. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface3.
Require Import WgNoise.proof.protocol.prot3c_bridge.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.common4.hc4_stmt.
Require Import WgNoise.proof.harness.create_any.hca3_model.
Require Import WgNoise.proof.harness.create_any.hca5_piece.
Require Import WgNoise.proof.harness.create_any.ca5_asm.
Require WgNoise.contracts.x_create_any.

Lemma create_any_from5 :
  prot4_piece_stmt -> hc4_piece_stmt_create_any ->
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_create_any.whole_prog.
Proof.
  intros Hprot Hhc B A X.
  destruct B as (Gb & HpB & HidB & HcovB).
  destruct (prot3c_aead A) as (Ga & enc & dec & xenc & xdec & Hap & Hxap & HpA & HidA & HcovA & HcovD & HccA).
  destruct (prot3c_x25519 X) as (Gx & x & Hxp & HpX & HidX & HcovX & HccX & _ & _).
  exact (ca5_safe Gb Ga Gx x enc dec xenc xdec HpB HidB HcovB Hap Hxap HpA HidA HcovA HcovD Hxp HpX HidX HcovX
           HccA HccX Hprot Hhc
           (hca5_piece x enc dec xenc xdec Hxp Hap Hxap
              (hca3_init_exp_ok x enc Hxp (aead_enc_length _ _ Hap))
              (hca3_resp_exp_ok x enc Hxp (aead_enc_length _ _ Hap)))).
Qed.
