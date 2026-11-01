(* the law replay over the interfaces v3 (wg3_iface3.v), from
   replay_safe3_from (replay_safe3.v) with prot3c_bridge's prot3c_aead / prot3c_x25519. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface3.
Require WgNoise.contracts.x_replay.
Require Import WgNoise.proof.protocol.prot3c_bridge.
Require Import WgNoise.proof.harness.replay.replay_safe3.

Theorem replay_safe3c :
  blake2s3_ok -> aead3b_ok -> x25519_ok3c ->
  harness_safe WgNoise.contracts.x_replay.whole_prog.
Proof.
  intros B A X. apply replay_safe3_from; [exact B | exact (prot3c_aead A) |].
  destruct (prot3c_x25519 X) as (G & x & XP & HP & HI & HC & HCC & _ & _).
  exists G, x. tauto.
Qed.
