(* law keypairs: the end F (statements 30..40 of main: clear, the puts of the held references, the final CHECKs, the frees, return 0). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.keypairs.hkp5_op1.
Require Import WgNoise.proof.harness.keypairs.hkp5_spec.
Require Import WgNoise.proof.harness.keypairs.hkp5_segF_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_segF_A.
Require Import WgNoise.proof.harness.keypairs.hkp5_segF_H.
Require Import WgNoise.proof.harness.keypairs.hkp5_segF_C.
Require Import WgNoise.proof.harness.keypairs.hkp5_segF_Z.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

Lemma hkp5_segF_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps (O: hkp5_oth) (FR: mpred) :
  hkp5_model_facts -> x25519_props x25519 -> hkp5_oth_ok F V O ->
  semax (hkp5_Delta (hkp5_G_F x25519)) (hkp5_Inv x25519 F V steps (hkp5_othR x25519 F V O * FR)) hkp5_segF
    (overridePost FF (hkp5_R (f_gv F))).
Proof.
  intros MF HX HO.
  destruct hkp5F_shape as (E & EA & EH & EC & EZ & NA & NH & NC & NZ & N1 & N2).
  rewrite E.
  apply hkp5_seql_app with (Q := hkp5F_S x25519 F V steps O FR hkp5F_P1); auto.
  { rewrite <- EA. apply hkp5_segF_A_ok; auto. }
  apply hkp5_seql_app with (Q := hkp5F_S x25519 F V steps O FR hkp5F_P2); auto.
  { rewrite <- EH. apply hkp5_segF_H_ok; auto. }
  apply hkp5_seql_app with (Q := hkp5F_S x25519 F V steps O FR hkp5F_P2); auto.
  { rewrite <- EC. apply hkp5_segF_C_ok; auto. }
  rewrite <- EZ. apply hkp5_segF_Z_ok; auto.
Qed.
