(* law keypairs: the body of check_all. *)
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
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_head.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_slots.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_node.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_hs.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_onode.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_oloop.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_kfin.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_count.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_oth.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_all.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* check_all calls bytes_eq too: its context is hkc5_G = bytes_eq_spec :: hkp5_G_check (hkp5_check_body_defs.v) *)
Lemma hkp5_check_body x25519 :
  @semax_body hkp5_V hkc5_G W_keypairs KC.f_check_all (hk5_check_all_spec x25519).
Proof.
  apply hkc5_body_ok.
  intros F V O HO.
  destruct HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnd & _).
  exact Hnd.
Qed.
