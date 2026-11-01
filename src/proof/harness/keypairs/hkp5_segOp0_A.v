(* law keypairs, segment Op0 part A: statements 0..12 of op 0 (hkp5_o0_A: a0 / f0 / fr0,
   dead, k = malloc (continue if NULL), hs_randomize, st, the optional insert, p.is_dead, prm.is_dead, hs_take(&snap),
   r = begin_session(..)). "Op0". *)
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
Require Import WgNoise.proof.harness.keypairs.hkp5_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_A_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_A_1.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_A_2.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_A_3.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_A_ins.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

Lemma hkp5_segOp0_A_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i R :
  hkp5_model_facts -> x25519_props x25519 ->
  semax (hkp5_Delta hkp5_G_Op0) (hkp5_PL0 x25519 F V steps FR i 0) hkp5_o0_A
    (overridePost (EX O: hkp5_o0, hkp5_o0_M x25519 F V steps FR i O)
       (loop1_ret_assert (hkp5_Icont x25519 F V steps FR i) R)).
Proof.
  intros HF HX.
  pose proof hkp5_o0A_shape as (E & E1 & E2 & E3 & N1 & N2).
  rewrite E.
  eapply hkp5_semax_cut with (Q := EX Y: hkp5_dyn, EX dead: bool, EX k: val,
                                     hkp5_o0A_K x25519 F V steps FR i Y dead k);
    [exact N1 | rewrite <- E1, hkp5_overridePost2; apply hkp5_o0A_1_ok; assumption |].
  apply extract_exists_pre. intros Y. apply extract_exists_pre. intros dead.
  apply extract_exists_pre. intros k.
  eapply hkp5_semax_cut with (Q := EX Y': hkp5_dyn, EX E': entry, hkp5_o0A_N x25519 F V steps FR i Y' E' k);
    [exact N2 | rewrite <- E2; apply hkp5_o0A_2_ok; [assumption | assumption | exact hkp5_o0A_ins_ok] |].
  apply extract_exists_pre. intros Y'. apply extract_exists_pre. intros E'.
  rewrite <- E3. apply hkp5_o0A_3_ok; assumption.
Qed.
