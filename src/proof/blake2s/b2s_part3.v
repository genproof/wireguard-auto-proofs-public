(* the BLAKE2s subtree: the BLAKE2s piece (interface wg3_iface.blake2s3_ok) and the law prim_blake2s. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface.
Require WgNoise.contracts.x_prim_blake2s.
Require WgNoise.proof.blake2s.b2s_piece3.
Require WgNoise.proof.harness.prim_blake2s.hb2s_safe.

Theorem blake2s_part3 :
  blake2s3_ok /\ harness_safe WgNoise.contracts.x_prim_blake2s.whole_prog.
Proof.
  split; [exact WgNoise.proof.blake2s.b2s_piece3.blake2s3_ok_proof
         | exact WgNoise.proof.harness.prim_blake2s.hb2s_safe.prim_blake2s_safe].
Qed.
