(* Law ae_fail_untouched (harness/ae_fail_untouched.c): a failed chacha20poly1305_decrypt or
   xchacha20poly1305_decrypt leaves its output buffer as it was.  From the law's assembly (aefu_safe_kit.v) and
   the shared bodies of the wg_laws.h helpers. *)
Require Import QuickProof.Contract.
Require WgNoise.contracts.ae_fail_untouched.
Require Import WgNoise.proof.harness.wg_laws.wl_kit_proof.
Require Import WgNoise.proof.harness.wg_laws.wl_copy_of.
Require Import WgNoise.proof.harness.ae_fail_untouched.aefu_safe_kit.

Lemma ae_fail_untouched_safe : harness_safe WgNoise.contracts.ae_fail_untouched.whole_prog.
Proof. exact (ae_fail_untouched_safe_kit wl_kit_holds wl_copy_of_holds). Qed.
