(* the AEAD piece as the protocol laws import it: aead3b_ok
   (wg3_iface2.v) = aead3_ok with the NULL-tolerant decryption templates of prot_dec3.v (an empty destination
   is emp: noise.c's consume_response calls chacha20poly1305_decrypt(NULL, src, 16, ...)) and cc_default. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.common.wg3_iface2.
Require Import WgNoise.proof.aead.aead_spec3b.
Require WgNoise.proof.aead.aead_piece3b WgNoise.proof.aead.aead_models_props3.

Theorem aead_part3b : aead3b_ok.
Proof.
  destruct aead_piece3b.aead_piece3b as [P C].
  destruct aead_models_props3.aead_models_ok3 as [A X].
  exists aead_G3b, aead_enc, aead_dec, xaead_enc, xaead_dec.
  split; [exact A |]. split; [exact X |]. split; [exact P |]. split; [exact aead_G3b_ids |].
  split; [exact C |].
  unfold cc_default_all, aead_G3b. repeat apply Forall_cons; try apply Forall_nil; reflexivity.
Qed.
