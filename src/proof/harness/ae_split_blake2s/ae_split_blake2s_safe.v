(* Law ae_split_blake2s (harness/ae_split_blake2s.c): the whole program is safe, i.e. its checks hold in every execution, given the
   small shared bodies of wl_kit.v (proved once for all ae_ laws, wl_kit_proof.v, and given in ae_laws_parts.v). *)
Require Import QuickProof.Contract.
Require Import WgNoise.proof.harness.wg_laws.wl_kit.
Require WgNoise.contracts.ae_split_blake2s.
Require WgNoise.proof.harness.ae_split_blake2s.aesb_assembly.

Lemma ae_split_blake2s_safe_kit : wl_kit_ok -> harness_safe WgNoise.contracts.ae_split_blake2s.whole_prog.
Proof.
  exact WgNoise.proof.harness.ae_split_blake2s.aesb_assembly.aesb_safe.
Qed.
