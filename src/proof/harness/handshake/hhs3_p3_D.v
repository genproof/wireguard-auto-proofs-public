(* law handshake, phase P3, segment D.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_conv.
Require Import WgNoise.proof.harness.handshake.hhs3_p3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_p3_D_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_p3_D_neg.
Require Import WgNoise.proof.harness.handshake.hhs3_p3_D_put.
Require Import WgNoise.proof.harness.handshake.hhs3_p3_D_ca.
Require Import WgNoise.proof.harness.handshake.hhs3_p3_D_cb.
Require Import WgNoise.proof.harness.handshake.hhs3_p3_D_cc.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Lemma hhs3_p3_D_eq :
  hhs3_p3_D = Sifthenelse (Eunop Onotbool (Etempvar HC._acc1 tint) tint) hhs3_p3_D_neg hhs3_p3_D_pos.
Proof. reflexivity. Qed.

Section P3D.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p3_D_ok {Espec: OracleKind} gv L FR :
  hhs3_p3_acc_stmt x25519 aead_dec -> hhs3_p3_crypto_stmt x25519 aead_enc aead_dec ->
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p3_SC x25519 aead_enc aead_dec gv L FR) hhs3_p3_D
    (overridePost (hhs3_p3_SD x25519 aead_enc aead_dec gv L FR) (hhs3_R gv)).
Proof.
  intros HACC HCRY HH.
  unfold hhs3_p3_SC, hhs3_p3_SBC.
  Intros R S m1 m2 a0 f0 l0 I M1 H1.
  Intros MI nowb Cin acc CI1 CI2.
  pose proof HH as (HX & HAe & _ & HCm & _).
  rewrite hhs3_p3_D_eq.
  destruct acc.
  2: {
    assert (EN: hhs3_cin x25519 aead_dec R L M1 nowb = None) by (apply (proj1 (HACC R L M1 nowb H)); auto).
    rewrite EN in H5. subst Cin.
    eapply semax_pre_simple; [apply andp_left2, now_later |].
    apply semax_ifthenelse_PQR' with (v := Vint Int.one); [reflexivity | entailer! | | |].
    { go_lowerx. apply prop_right. destruct H13 as [Ea _].
      unfold liftx in *; simpl in *. unfold lift_uncurry_open, lift in *; simpl in *. rewrite <- Ea. reflexivity. }
    2: { apply semax_extract_PROP; intro Hf; compute in Hf; discriminate Hf. }
    eapply semax_pre; [| eapply semax_post; [| | | | apply (hhs3_p3_D_neg_ok x25519 aead_enc aead_dec xaead_enc xaead_dec
         gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb (hhs3_R gv) HH)]].
    - unfold hhs3_p3_D_N, hhs3_p3_pa, peer_result. Intros. apply andp_left2. symmetry in H6.
      apply andp_right; [apply prop_right; simpl; tauto | apply andp_left2, derives_refl].
    - rewrite !overridePost_normal'. unfold hhs3_p3_D_N, hhs3_p3_SD, hhs3_p3_SDE. Intros.
      Exists R S m1 m2 a0 f0 l0 I M1 H1. Exists MI nowb false (hhs3_PA0 x25519 R L) CI1 CI2.
      unfold hhs3_cnt_temps, hhs3_lvars. cbn [app].
      entailer!.
    - simpl. intros. apply andp_left2, derives_refl.
    - simpl. intros. apply andp_left2, derives_refl.
    - simpl. intros. apply andp_left2, derives_refl. }
  destruct (H7 eq_refl) as [E1 E2].
  assert (EC: hhs3_cin x25519 aead_dec R L M1 nowb = Some (l_pa L, hhs3_p3_new x25519 R L M1 nowb CI2))
    by (apply (proj1 (proj2 (HACC R L M1 nowb H)) CI1 CI2); auto).
  assert (Hib: mi_ok (hhs3_IB x25519 R) = true).
  { unfold hhs3_p3_acc in H6. destruct (mi_ok (hhs3_IB x25519 R)); [reflexivity | discriminate]. }
  pose proof (proj1 (HCRY HCm HX HAe R L I M1 H1 MI nowb H H2 H3) CI1 CI2 Hib E1 E2) as Hts.
  assert (Hts': fst (fst CI2) = hhs3_ts I) by (destruct CI2 as [[t ck] h]; exact Hts).
  clear Hts.
  rewrite EC in H5. subst Cin.
  eapply semax_pre_simple; [apply andp_left2, now_later |].
  apply semax_ifthenelse_PQR' with (v := Vint Int.zero); [reflexivity | entailer! | | |].
  { go_lowerx. apply prop_right. destruct H13 as [Ea _].
    unfold liftx in *; simpl in *. unfold lift_uncurry_open, lift in *; simpl in *. rewrite <- Ea. reflexivity. }
  { apply semax_extract_PROP; intro Hf; compute in Hf; discriminate Hf. }
  rewrite hhs3_p3_D_pos_eq.
  rewrite seq_assoc.
  eapply semax_pre; [| eapply semax_seq; [apply (hhs3_p3_D_put_ok x25519 aead_enc aead_dec xaead_enc xaead_dec
         gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb CI1 CI2 _ HH) |]].
  { unfold hhs3_p3_D_P0, hhs3_p3_D_st, hhs3_p3_pa, peer_result. Intros. apply andp_left2. symmetry in H6.
    apply andp_right; [apply prop_right; simpl; tauto | apply andp_left2, derives_refl]. }
  rewrite seq_assoc, seq_assoc.
  eapply semax_seq.
  { apply -> seq_assoc. apply (hhs3_p3_D_ca_ok x25519 aead_enc aead_dec xaead_enc xaead_dec
         gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb CI1 CI2 _ HH). }
  rewrite seq_assoc, seq_assoc.
  eapply semax_seq.
  { apply -> seq_assoc. apply (hhs3_p3_D_cb_ok x25519 aead_enc aead_dec xaead_enc xaead_dec
         gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb CI1 CI2 _ HH). }
  eapply semax_post; [| | | | apply (hhs3_p3_D_cc_ok x25519 aead_enc aead_dec xaead_enc xaead_dec
         gv L FR R S m1 m2 a0 f0 l0 I M1 H1 MI nowb CI1 CI2 (hhs3_R gv) HH)].
  - rewrite !overridePost_normal'. unfold hhs3_p3_D_Q, hhs3_p3_D_st, hhs3_p3_SD, hhs3_p3_SDE. Intros.
    Exists R S m1 m2 a0 f0 l0 I M1 H1. Exists MI nowb true (hhs3_p3_new x25519 R L M1 nowb CI2) CI1 CI2.
    unfold hhs3_cnt_temps, hhs3_lvars. cbn [app].
    entailer!.
  - simpl. intros. apply andp_left2, derives_refl.
  - simpl. intros. apply andp_left2, derives_refl.
  - simpl. intros. apply andp_left2, derives_refl.
Qed.

End P3D.
