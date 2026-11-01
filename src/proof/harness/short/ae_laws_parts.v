(* The ae_ laws from their parts: five laws proved from the shared small bodies (wl_kit_holds), and the
   conjunction ae_laws of src/proof/harness/short/ae_laws.v given the sixth, ae_fail_untouched
   (src/proof/harness/ae_fail_untouched/ae_fail_untouched_safe.v). *)
Require Import QuickProof.Contract.
Require WgNoise.contracts.ae_fail_untouched.
Require WgNoise.contracts.ae_roundtrip.
Require WgNoise.contracts.ae_split_blake2s.
Require WgNoise.contracts.ae_split_chacha20.
Require WgNoise.contracts.ae_split_poly1305.
Require WgNoise.contracts.ae_xroundtrip.
Require Import WgNoise.proof.harness.wg_laws.wl_kit_proof.
Require WgNoise.proof.harness.ae_roundtrip.ae_roundtrip_safe.
Require WgNoise.proof.harness.ae_xroundtrip.ae_xroundtrip_safe.
Require WgNoise.proof.harness.ae_split_blake2s.ae_split_blake2s_safe.
Require WgNoise.proof.harness.ae_split_chacha20.ae_split_chacha20_safe.
Require WgNoise.proof.harness.ae_split_poly1305.ae_split_poly1305_safe.

Theorem ae_roundtrip_safe : harness_safe WgNoise.contracts.ae_roundtrip.whole_prog.
Proof. exact (ae_roundtrip_safe.ae_roundtrip_safe_kit wl_kit_holds). Qed.

Theorem ae_xroundtrip_safe : harness_safe WgNoise.contracts.ae_xroundtrip.whole_prog.
Proof. exact (ae_xroundtrip_safe.ae_xroundtrip_safe_kit wl_kit_holds). Qed.

Theorem ae_split_blake2s_safe : harness_safe WgNoise.contracts.ae_split_blake2s.whole_prog.
Proof. exact (ae_split_blake2s_safe.ae_split_blake2s_safe_kit wl_kit_holds). Qed.

Theorem ae_split_chacha20_safe : harness_safe WgNoise.contracts.ae_split_chacha20.whole_prog.
Proof. exact (ae_split_chacha20_safe.ae_split_chacha20_safe_kit wl_kit_holds). Qed.

Theorem ae_split_poly1305_safe : harness_safe WgNoise.contracts.ae_split_poly1305.whole_prog.
Proof. exact (ae_split_poly1305_safe.ae_split_poly1305_safe_kit wl_kit_holds). Qed.

(* ae_laws, the conjunction in the order of `suite`, from ae_fail_untouched *)
Theorem ae_laws_of_fail_untouched :
  harness_safe WgNoise.contracts.ae_fail_untouched.whole_prog ->
  harness_safe WgNoise.contracts.ae_fail_untouched.whole_prog /\
  harness_safe WgNoise.contracts.ae_roundtrip.whole_prog /\
  harness_safe WgNoise.contracts.ae_split_blake2s.whole_prog /\
  harness_safe WgNoise.contracts.ae_split_chacha20.whole_prog /\
  harness_safe WgNoise.contracts.ae_split_poly1305.whole_prog /\
  harness_safe WgNoise.contracts.ae_xroundtrip.whole_prog.
Proof.
  intro F. repeat split; auto using ae_roundtrip_safe, ae_split_blake2s_safe, ae_split_chacha20_safe,
    ae_split_poly1305_safe, ae_xroundtrip_safe.
Qed.
