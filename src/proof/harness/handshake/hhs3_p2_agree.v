(* law handshake: main's phase P2, the pure agreement of create_initiation_model and m_create_initiation_model (hhs3_p2_agree_stmt).
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
Require Import WgNoise.proof.harness.handshake.hhs3_p2_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.

Lemma hhs3_p2_agree_clamp_nz (r: list byte) :
  Zlength r = 32 -> memneq_bool (clamp r) zeros32 = true.
Proof.
  intros Hr. unfold memneq_bool.
  destruct (list_eq_dec Byte.eq_dec (clamp r) zeros32) as [E|E]; [|reflexivity].
  exfalso.
  assert (H31: Znth 31 (clamp r) = Byte.or (Byte.and (Znth 31 r) (Byte.repr 127)) (Byte.repr 64)).
  { unfold clamp. rewrite upd_Znth_same; [reflexivity|].
    rewrite Zlength_upd_Znth. lia. }
  rewrite E in H31. unfold zeros32 in H31. rewrite Znth_Zrepeat in H31 by lia.
  assert (H64: Byte.and (Byte.repr 64) (Byte.or (Byte.repr 64) (Byte.and (Znth 31 r) (Byte.repr 127)))
               = Byte.repr 64) by apply Byte.and_or_absorb.
  rewrite Byte.or_commut, <- H31, Byte.and_zero in H64.
  discriminate H64.
Qed.

Lemma hhs3_p2_agree_memneq_is_zero (ss: list byte) :
  Zlength ss = 32 -> memneq_bool ss zeros32 = negb (is_zero ss).
Proof.
  intros H. unfold is_zero, bytes_eqb, memneq_bool. rewrite H.
  change (zeros 32) with zeros32.
  destruct (list_eq_dec Byte.eq_dec ss zeros32); reflexivity.
Qed.

Lemma hhs3_p2_agree_hs (H: handshake) e ck0 h0 ck1 h1 ck2 h2 ck3 h3 s :
  hs_set_state (hs_set_ckh (hs_set_ckh (hs_set_ckh (hs_set_eph (hs_set_ckh H ck0 h0) e) ck1 h1) ck2 h2) ck3 h3) s
  = hs_set_state (hs_set_ckh (hs_set_eph H e) ck3 h3) s.
Proof. destruct H; reflexivity. Qed.

Lemma hhs3_p2_agree_ok : hhs3_p2_agree_stmt x25519 aead_enc.
Proof.
  intros Hx R L I HR Hr Hok.
  assert (Hid: id_has (d_id (hhs3_DA x25519 R L)) = true) by exact Hok.
  assert (Hrs: hs_rstatic (p_hs (hhs3_PB0 x25519 R L)) = mi_pub (hhs3_IB x25519 R)) by reflexivity.
  assert (Hss: hs_ss (p_hs (hhs3_PB0 x25519 R L)) = hhs3_ssa x25519 R) by reflexivity.
  assert (Hssl: Zlength (hhs3_ssa x25519 R) = 32).
  { unfold hhs3_ssa, m_precomputed_model.
    destruct (andb _ _); [apply Hx | reflexivity]. }
  unfold hhs3_mi, hhs3_ci, create_initiation_model, m_create_initiation_model.
  rewrite Hid, Hrs, Hss, (hhs3_p2_agree_clamp_nz _ Hr).
  rewrite (hhs3_p2_agree_memneq_is_zero _ Hssl).
  cbv beta iota zeta.
  unfold dh_ok at 1.
  destruct (memneq_bool (x25519 (clamp (i_r I)) basepoint9) zeros32); [|reflexivity].
  cbv beta iota.
  destruct (dh_ok x25519 (clamp (i_r I)) (mi_pub (hhs3_IB x25519 R))); [|reflexivity].
  cbv beta iota.
  destruct (is_zero (hhs3_ssa x25519 R)); [reflexivity|].
  cbv beta iota.
  rewrite hhs3_p2_agree_hs. reflexivity.
Qed.

End Seg.
