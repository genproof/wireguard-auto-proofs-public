(* law prim_aead: check_decrypt_any of prim_aead.h. The body is cut into segments A..D
   (haead_cda_body3_defs.v), one file each. *)
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
Require Import WgNoise.proof.harness.prim_aead.haead_cda_body3_defs.
Require Import WgNoise.proof.harness.prim_aead.haead_cda_body3_A.
Require Import WgNoise.proof.harness.prim_aead.haead_cda_body3_B.
Require Import WgNoise.proof.harness.prim_aead.haead_cda_body3_C.
Require Import WgNoise.proof.harness.prim_aead.haead_cda_body3_D.

#[local] Existing Instance W_prim_aead.
Local Open Scope Z_scope.

Lemma haead_cda_body3 : haead_hyps ->
  semax_body haead_V haead_Gprog WgNoise.harness.x_prim_aead.code.f_check_decrypt_any check_decrypt_any_spec.
Proof.
  intros HH. start_function.
  unfold MORE_COMMANDS, abbreviate.
  match goal with |- semax _ _ ?s _ => change s with cda_body end. rewrite cda_body_eq.
  eapply semax_seq; [apply cda_A_ok; auto |].
  Intros c c2. apply cda_B_ok; auto. intros d2 db rd2.
  apply cda_C_ok; auto. intros bs. apply cda_D_ok; auto.
Qed.
