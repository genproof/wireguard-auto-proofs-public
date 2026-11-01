(* The law hs_response_state (harness/hs_response_state.c), closed: its program is safe.  The assembly of the hs_
   laws (hrs_asm.v: hs_asm.hs_harness_safe with the law's piece) and the helpers' bodies (hs_bodies.v). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require WgNoise.contracts.hs_response_state.
Require Import WgNoise.proof.harness.hs_common.hs_bodies.
Require Import WgNoise.proof.harness.hs_response_state.hrs_asm.

Theorem hs_response_state_safe : harness_safe WgNoise.contracts.hs_response_state.whole_prog.
Proof. exact (hrs_safe_of_helpers hs_common_bodies). Qed.
