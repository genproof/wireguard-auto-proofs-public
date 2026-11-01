(* the ChaCha20/Poly1305/AEAD subtree: the AEAD piece (interface wg3_iface.aead3_ok) and the laws prim_aead, prim_poly1305 (which may use the BLAKE2s piece: memzero_explicit, get_unaligned_le32). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import WgNoise.proof.common.wg3_iface.
Require WgNoise.contracts.x_prim_aead WgNoise.contracts.x_prim_poly1305.
Require Import WgNoise.proof.aead.aead_spec3.
Require WgNoise.proof.aead.aead_piece3 WgNoise.proof.aead.aead_models_props3.
Require WgNoise.proof.harness.prim_aead.haead_safe3 WgNoise.proof.harness.prim_poly1305.hp1305_safe3.

Theorem aead_part3 :
  aead3_ok /\
  (blake2s3_ok ->
   harness_safe WgNoise.contracts.x_prim_aead.whole_prog /\ harness_safe WgNoise.contracts.x_prim_poly1305.whole_prog).
Proof.
  destruct aead_piece3.aead_piece3 as [P C].
  destruct aead_models_props3.aead_models_ok3 as [A X].
  split.
  - exists aead_G3, aead_enc, aead_dec, xaead_enc, xaead_dec.
    split; [exact A|]. split; [exact X|]. split; [exact P|]. split; [exact aead_G3_ids | exact C].
  - intros B. split.
    + exact (haead_safe3.prim_aead_safe3 P B).
    + exact (hp1305_safe3.prim_poly1305_safe3 P B).
Qed.
