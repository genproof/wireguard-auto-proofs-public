(* law prim_aead: the TweetNaCl Poly1305 rp_* of common.h (the same Clight as law prim_poly1305's). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.harness.prim_aead.haead_spec3.
Require Import WgNoise.proof.harness.prim_aead.haead_lemmas3.
Require WgNoise.harness.x_prim_aead.code.
Require WgNoise.proof.harness.prim_aead.haead_rp_body3_a WgNoise.proof.harness.prim_aead.haead_rp_body3_m.

#[local] Existing Instance W_prim_aead.
Local Open Scope Z_scope.

Lemma haead_rp_bodies3 : haead_hyps ->
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_rp_add rp_add_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_rp_init rp_init_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_rp_mul rp_mul_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_rp_block rp_block_spec /\
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_rp_final rp_final_spec.
Proof.
  intros _. destruct haead_rp_body3_a.hra3_rp_bodies as [A [I [B F]]].
  split; [exact A |]. split; [exact I |]. split; [exact haead_rp_body3_m.hra3_rpmul_body |].
  split; [exact B | exact F].
Qed.
