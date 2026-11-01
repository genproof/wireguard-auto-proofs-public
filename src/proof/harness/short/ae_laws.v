(* The six short laws of authenticated encryption and the primitives (ae_):
   round trips of ChaCha20-Poly1305 and XChaCha20-Poly1305, a failed decryption
   leaves its output untouched, and BLAKE2s, ChaCha20 and Poly1305 give the same
   result over a message in one piece or in pieces.  Their conjunction, as it
   appears in `suite` (src/contracts/suite.v). *)
Require Import QuickProof.Contract.
Require WgNoise.contracts.ae_fail_untouched.
Require WgNoise.contracts.ae_roundtrip.
Require WgNoise.contracts.ae_split_blake2s.
Require WgNoise.contracts.ae_split_chacha20.
Require WgNoise.contracts.ae_split_poly1305.
Require WgNoise.contracts.ae_xroundtrip.
Require WgNoise.proof.harness.ae_fail_untouched.ae_fail_untouched_safe.
Require WgNoise.proof.harness.short.ae_laws_parts.

Lemma ae_laws :
  harness_safe WgNoise.contracts.ae_fail_untouched.whole_prog /\
  harness_safe WgNoise.contracts.ae_roundtrip.whole_prog /\
  harness_safe WgNoise.contracts.ae_split_blake2s.whole_prog /\
  harness_safe WgNoise.contracts.ae_split_chacha20.whole_prog /\
  harness_safe WgNoise.contracts.ae_split_poly1305.whole_prog /\
  harness_safe WgNoise.contracts.ae_xroundtrip.whole_prog.
Proof.
  exact (ae_laws_parts.ae_laws_of_fail_untouched ae_fail_untouched_safe.ae_fail_untouched_safe).
Qed.
