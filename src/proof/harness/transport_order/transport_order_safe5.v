(* the law transport_order, closed (Qed; nothing assumed in its closure).
*)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface3.
Require WgNoise.contracts.x_transport_order.
Require WgNoise.proof.harness.transport_order.ht4o_asm.

(* The law compares the kernel's decryption with the reference ref_aead_decrypt (a concrete model) on packets of any
   length: the abstract, 2^32-bounded interface aead3b_ok cannot serve, the assembly uses the CONCRETE AEAD piece
   aead_piece3b (as law prim_aead does); blake2s3_ok gives the AEAD units' imports memzero_explicit /
   get_unaligned_le32. *)

Theorem transport_order_safe5 :
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_transport_order.whole_prog.
Proof.
  intros Hb _ _. exact (WgNoise.proof.harness.transport_order.ht4o_asm.ht4o_transport_order_safe Hb).
Qed.
