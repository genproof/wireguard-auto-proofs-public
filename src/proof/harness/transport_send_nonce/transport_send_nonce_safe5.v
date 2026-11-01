(* the law transport_send_nonce, closed (Qed; nothing assumed in its closure).
*)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface3.
Require WgNoise.contracts.x_transport_send_nonce.
Require WgNoise.proof.harness.transport_send_nonce.tsn5_asm.

(* The harness calls no function of the code under test (the nonce draw is written out in it, DEVIATIONS.md L16):
   the law holds without the interfaces. *)
Theorem transport_send_nonce_safe5 :
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_transport_send_nonce.whole_prog.
Proof.
  intros _ _ _. exact WgNoise.proof.harness.transport_send_nonce.tsn5_asm.tsn5_safe.
Qed.
