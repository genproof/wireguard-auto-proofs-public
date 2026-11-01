(* The law hs_stale_response (harness/hs_stale_response.c), closed: its program is safe. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require WgNoise.contracts.hs_stale_response.
Require WgNoise.proof.harness.hs_common.hs_bodies.
Require WgNoise.proof.harness.hs_stale_response.hsr_piece.

(* the assembly of the hs_ laws (hs_asm.hs_harness_safe) applied to the law's piece (hsr_piece.v: main of
   hsr_main.v, the helpers it reaches) with the helpers' bodies *)
Theorem hs_stale_response_safe : harness_safe WgNoise.contracts.hs_stale_response.whole_prog.
Proof.
  exact (WgNoise.proof.harness.hs_stale_response.hsr_piece.hsr_safe_of_helpers
           WgNoise.proof.harness.hs_common.hs_bodies.hs_common_bodies).
Qed.
