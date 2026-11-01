(* The five short laws of the replay window (rp_): each harness feeds nonces to
   counter_validate (patch/counter_validate.c) and checks the verdicts LAWS.md
   states.  Their conjunction, as it appears in `suite` (src/contracts/suite.v). *)
Require Import QuickProof.Contract.
Require WgNoise.contracts.rp_any_order.
Require WgNoise.contracts.rp_duplicate.
Require WgNoise.contracts.rp_fresh.
Require WgNoise.contracts.rp_limit.
Require WgNoise.contracts.rp_too_old.
Require WgNoise.proof.harness.rp_any_order.rp_any_order_safe.
Require WgNoise.proof.harness.rp_duplicate.rp_duplicate_safe.
Require WgNoise.proof.harness.rp_fresh.rp_fresh_safe.
Require WgNoise.proof.harness.rp_limit.rp_limit_safe.
Require WgNoise.proof.harness.rp_too_old.rp_too_old_safe.

Lemma rp_laws :
  harness_safe WgNoise.contracts.rp_any_order.whole_prog /\
  harness_safe WgNoise.contracts.rp_duplicate.whole_prog /\
  harness_safe WgNoise.contracts.rp_fresh.whole_prog /\
  harness_safe WgNoise.contracts.rp_limit.whole_prog /\
  harness_safe WgNoise.contracts.rp_too_old.whole_prog.
Proof.
  exact (conj WgNoise.proof.harness.rp_any_order.rp_any_order_safe.rp_any_order_safe
        (conj WgNoise.proof.harness.rp_duplicate.rp_duplicate_safe.rp_duplicate_safe
        (conj WgNoise.proof.harness.rp_fresh.rp_fresh_safe.rp_fresh_safe
        (conj WgNoise.proof.harness.rp_limit.rp_limit_safe.rp_limit_safe
              WgNoise.proof.harness.rp_too_old.rp_too_old_safe.rp_too_old_safe)))).
Qed.
