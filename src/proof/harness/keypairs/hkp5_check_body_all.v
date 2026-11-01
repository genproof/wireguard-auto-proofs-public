(* law keypairs: check_all's body over hkc5_G = bytes_eq_spec :: hkp5_G_check, from
   the proven segments (children #370-#378), the live loop and the glue; the one remaining hypothesis is the
   distinctness of the other peers' handshake addresses and the kents' addresses. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
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
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_loop.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_glue.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_head.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_slots.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_node.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_hs.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_onode.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_oloop.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_kfin.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_count.
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_oth.

#[local] Existing Instance W_keypairs.

Lemma hkc5_body_ok x25519 :
  (forall F V O, hkp5_oth_ok F V O -> NoDup (map hs_addr (map peer_addr4 (o_PS O)) ++ map ke_addr (o_KE O))) ->
  @semax_body hkp5_V hkc5_G W_keypairs KC.f_check_all (hk5_check_all_spec x25519).
Proof.
  intros HND.
  apply hkc5_body_from; auto.
  - exact hkc5_head_ok.
  - exact hkc5_slots_ok.
  - exact hkc5_node_ok.
  - exact hkc5_hs_ok.
  - exact hkc5_onode_ok.
  - exact hkc5_oloop_ok.
  - exact hkc5_kfin_ok.
  - exact (proj1 hkc5_count_ok).
  - exact (proj2 hkc5_count_ok).
  - exact hkc5_oth_facts_ok.
Qed.
