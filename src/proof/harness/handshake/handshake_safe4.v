(* the law handshake over the interfaces v3 (wg3_iface3.v), for ANY lower pieces. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface3.
Require WgNoise.contracts.x_handshake.
Require Import WgNoise.proof.protocol.prot3c_bridge.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.handshake_from3c.

Theorem handshake_safe4 :
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_handshake.whole_prog.
Proof.
  intros B A X. apply handshake_safe3_from; [exact B | exact (prot3c_aead A) |].
  destruct (prot3c_x25519 X) as (G & x & XP & HP & HI & HC & HCC & CI & DA).
  exists G, x. unfold hhs3_comm, x25519_clamp_inv, x25519_dh_agree in *. tauto.
Qed.
