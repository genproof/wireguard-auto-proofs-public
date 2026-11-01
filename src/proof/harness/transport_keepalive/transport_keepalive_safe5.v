(* the law transport_keepalive, closed (Qed; nothing assumed in its closure).
*)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface3.
Require WgNoise.contracts.x_transport_keepalive.
Require WgNoise.proof.harness.transport_keepalive.hka5_asm.

Theorem transport_keepalive_safe5 :
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_transport_keepalive.whole_prog.
Proof.
  intros B _ _. exact (WgNoise.proof.harness.transport_keepalive.hka5_asm.hka5_harness_safe B).
Qed.
