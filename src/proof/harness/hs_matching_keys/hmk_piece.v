(* The law hs_matching_keys: its own piece, main (hmk_main.v) and the harness's copies of the hs_laws.h helpers
   (hs_bodies.v, lifted into the law's unit). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_iface3.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_asm.
Require Import WgNoise.proof.harness.hs_matching_keys.hmk_spec.
Require Import WgNoise.proof.harness.hs_common.hs_lift.
Require Import WgNoise.proof.harness.hs_common.hs_bodies.
Require Import WgNoise.proof.harness.hs_matching_keys.hmk_main.

Lemma hmk_CSh_W : cspecs_sub CSh W_hmk.
Proof. pose proof world_ok_hs_matching_keys as H. inversion H as [| ? ? _ H1]. inversion H1; assumption. Qed.

(* the piece from main's body and the helpers' bodies (callee-only contexts, lifted into the law's unit) *)
Lemma hmk_piece_of_helpers x25519 aead_enc aead_dec :
  x25519_props x25519 -> x25519_clamp_inv x25519 -> x25519_dh_agree x25519 -> hs_helpers_ok x25519 ->
  piece_ok [hmk_unit] (hmk_Il x25519 aead_enc aead_dec) (hs_main_spec hmk_prog :: hmk_Gl x25519).
Proof.
  intros Hx Hcl Hdh (B1 & B2 & B3 & B4 & B5 & B6 & _ & _).
  split; [repeat constructor; simpl; intuition discriminate |].
  assert (IN: In hmk_unit [hmk_unit]) by (left; reflexivity).
  repeat apply Forall_cons; try apply Forall_nil; exists hmk_unit; split; try exact IN.
  - exists HMK.f_main. split; [reflexivity |]. exact (hmk_main_body x25519 aead_enc aead_dec Hx Hcl Hdh).
  - eapply hs_helper_entry; [exact hmk_CSh_W | exact B1 | reflexivity | repeat constructor | hs_gsub | hs_vsub].
  - eapply hs_helper_entry; [exact hmk_CSh_W | exact B2 | reflexivity | repeat constructor | hs_gsub | hs_vsub].
  - eapply hs_helper_entry; [exact hmk_CSh_W | exact B3 | reflexivity | repeat constructor | hs_gsub | hs_vsub].
  - eapply hs_helper_entry; [exact hmk_CSh_W | exact B4 | reflexivity | repeat constructor | hs_gsub | hs_vsub].
  - eapply hs_helper_entry; [exact hmk_CSh_W | exact B5 | reflexivity | repeat constructor | hs_gsub | hs_vsub].
  - eapply hs_helper_entry; [exact hmk_CSh_W | exact B6 | reflexivity | repeat constructor | hs_gsub | hs_vsub].
Qed.

Theorem hmk_piece x25519 aead_enc aead_dec :
  x25519_props x25519 -> x25519_clamp_inv x25519 -> x25519_dh_agree x25519 -> aead_props aead_enc aead_dec ->
  piece_ok [hmk_unit] (hmk_Il x25519 aead_enc aead_dec) (hs_main_spec hmk_prog :: hmk_Gl x25519).
Proof.
  intros Hx Hcl Hdh _. exact (hmk_piece_of_helpers x25519 aead_enc aead_dec Hx Hcl Hdh (hs_common_bodies x25519 Hx)).
Qed.
