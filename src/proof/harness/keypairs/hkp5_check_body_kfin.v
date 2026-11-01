(* law keypairs: the segment KFIN (kents check, table_len, kents_hashed).
*)
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

#[local] Existing Instance W_keypairs.
Local Open Scope Z_scope.

Lemma hkc5_kfin_ok : hkc5_kfin_stmt.
Proof.
  intros Espec F T kd KE VO n FR R HVO HKE HSB.
  unfold hkc5_PK, hkc5_PK', hkc5_kfin, hkc5_lv.
  destruct R as [Rn Rb Rc Rr]; unfold overridePost.
  abbreviate_semax.
  assert_PROP (is_pointer_or_null kd) as Hkd.
  { destruct KE as [|e KE']; simpl kents_rep.
    - entailer!.
    - Intros nx. unfold kent_cell. Intros. entailer!.
      apply isptr_is_pointer_or_null. destruct H0 as [Hp _]; exact Hp. }
  forward.
  forward_call (kd, KE, Tsh, f_t F, T, VO).
  rewrite HSB.
  forward_if.
  { discriminate. }
  forward_call (Tsh, f_t F, T).
  forward.
  forward_call (kd, KE, Tsh, f_t F, T).
  { eapply Forall_impl; [|exact HKE]; intros e [? _]; auto. }
  entailer!.
Qed.
