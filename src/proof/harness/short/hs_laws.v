(* The eight short laws of the Noise handshake (hs_): two devices set up by
   harness/hs_laws.h run the handshake functions of noise.c, and each harness
   checks one property of the resulting states (matching keys, erasure on
   beginning a session, rejection of replayed, stale or failed messages without
   changing state).  Their conjunction, as it appears in `suite`
   (src/contracts/suite.v). *)
Require Import QuickProof.Contract.
Require WgNoise.contracts.hs_begin_session_state.
Require WgNoise.contracts.hs_matching_keys.
Require WgNoise.contracts.hs_reject_initiation.
Require WgNoise.contracts.hs_reject_response.
Require WgNoise.contracts.hs_replay_initiation.
Require WgNoise.contracts.hs_response_state.
Require WgNoise.contracts.hs_session_erases.
Require WgNoise.contracts.hs_stale_response.
Require WgNoise.proof.harness.hs_begin_session_state.hs_begin_session_state_safe.
Require WgNoise.proof.harness.hs_matching_keys.hs_matching_keys_safe.
Require WgNoise.proof.harness.hs_reject_initiation.hs_reject_initiation_safe.
Require WgNoise.proof.harness.hs_reject_response.hs_reject_response_safe.
Require WgNoise.proof.harness.hs_replay_initiation.hs_replay_initiation_safe.
Require WgNoise.proof.harness.hs_response_state.hs_response_state_safe.
Require WgNoise.proof.harness.hs_session_erases.hs_session_erases_safe.
Require WgNoise.proof.harness.hs_stale_response.hs_stale_response_safe.

Lemma hs_laws :
  harness_safe WgNoise.contracts.hs_begin_session_state.whole_prog /\
  harness_safe WgNoise.contracts.hs_matching_keys.whole_prog /\
  harness_safe WgNoise.contracts.hs_reject_initiation.whole_prog /\
  harness_safe WgNoise.contracts.hs_reject_response.whole_prog /\
  harness_safe WgNoise.contracts.hs_replay_initiation.whole_prog /\
  harness_safe WgNoise.contracts.hs_response_state.whole_prog /\
  harness_safe WgNoise.contracts.hs_session_erases.whole_prog /\
  harness_safe WgNoise.contracts.hs_stale_response.whole_prog.
Proof.
  exact (conj hs_begin_session_state_safe.hs_begin_session_state_safe (conj hs_matching_keys_safe.hs_matching_keys_safe (conj hs_reject_initiation_safe.hs_reject_initiation_safe (conj hs_reject_response_safe.hs_reject_response_safe (conj hs_replay_initiation_safe.hs_replay_initiation_safe (conj hs_response_state_safe.hs_response_state_safe (conj hs_session_erases_safe.hs_session_erases_safe hs_stale_response_safe.hs_stale_response_safe))))))).
Qed.
