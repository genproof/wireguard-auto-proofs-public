(* the Curve25519 piece for the protocol laws (wg3_iface3.x25519_ok3c): x25519_part3b plus the clamp
   invariance (proved) and the DH agreement (x25519_dh.x25519_m_dh_agree, proved from fiat-crypto). *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.common.wg3_iface3.
Require Import WgNoise.proof.x25519.x25519_spec WgNoise.proof.x25519.x25519_model.
Require WgNoise.proof.x25519.x25519_part3 WgNoise.proof.x25519.x25519_dh.

Theorem x25519_part3c : x25519_ok3c.
Proof.
  exists x25_G, x25519_m.
  split; [exact x25519_m_length |].
  split; [exact WgNoise.proof.x25519.x25519_part3.x25519_piece3 |].
  split; [reflexivity |].
  split.
  - apply asm_covers_incl.
    + repeat constructor; simpl; intuition discriminate.
    + unfold x25519_iface3, x25_G. intros a Ha. simpl in Ha |- *. intuition (subst; tauto).
  - split; [unfold cc_default_all, x25_G; repeat constructor |].
    split; [exact WgNoise.proof.x25519.x25519_dh.x25519_m_clamp |].
    exact WgNoise.proof.x25519.x25519_dh.x25519_m_dh_agree.
Qed.
