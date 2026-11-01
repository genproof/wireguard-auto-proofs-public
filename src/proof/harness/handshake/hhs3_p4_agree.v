(* law handshake, phase P4: pure lemma agree.
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
Require Import WgNoise.proof.harness.handshake.hhs3_p4_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Lemma hhs3_p4_agree_clamp_nz (r: list byte) :
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

Lemma hhs3_p4_agree_memneq_is_zero (ss: list byte) :
  Zlength ss = 32 -> memneq_bool ss zeros32 = negb (is_zero ss).
Proof.
  intros H. unfold is_zero, bytes_eqb, memneq_bool. rewrite H.
  change (zeros 32) with zeros32.
  destruct (list_eq_dec Byte.eq_dec ss zeros32); reflexivity.
Qed.

Lemma hhs3_p4_agree_hs (H: handshake) e ck0 h0 ck1 h1 ck2 h2 ck3 h3 s :
  hs_set_state (hs_set_ckh (hs_set_ckh (hs_set_ckh (hs_set_eph (hs_set_ckh H ck0 h0) e) ck1 h1) ck2 h2) ck3 h3) s
  = hs_set_state (hs_set_ckh (hs_set_eph H e) ck3 h3) s.
Proof. destruct H; reflexivity. Qed.

Lemma hhs3_p4_agree_hs2 (H: handshake) e ck1 h1 ck2 h2 ck3 h3 s :
  hs_set_state (hs_set_ckh (hs_set_ckh (hs_set_ckh (hs_set_eph H e) ck1 h1) ck2 h2) ck3 h3) s
  = hs_set_state (hs_set_ckh (hs_set_eph H e) ck3 h3) s.
Proof. destruct H; reflexivity. Qed.

Section Agree.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.

(* the kernel's create_response vs the harness's m_create_response, on any handshake in CONSUMED_INITIATION *)
Lemma hhs3_p4_agree_core (H: handshake) (M: resp_msg) r idx :
  hs_state H = HS_CONSUMED_INITIATION -> Zlength r = 32 ->
  match m_create_response_model x25519 aead_enc (hs_ck H) (hs_hash H) (hs_reph H) (hs_rstatic H) (hs_psk H) r with
  | Some (E, encn, ep, ck, h) =>
      create_response_model x25519 aead_enc H M r idx =
        (true, mkRM (Int.repr 2) idx (hs_rindex H) E encn (rm_mac1 M) (rm_mac2 M),
         hs_set_state (hs_set_ckh (hs_set_eph H ep) ck h) HS_CREATED_RESPONSE) /\
      ep = clamp r /\ E = x25519 ep basepoint9
  | None => fst (fst (create_response_model x25519 aead_enc H M r idx)) = false
  end.
Proof.
  intros Hst Hr.
  unfold create_response_model, m_create_response_model.
  rewrite Hst, Int.eq_true, (hhs3_p4_agree_clamp_nz _ Hr).
  cbv beta iota zeta.
  unfold dh_ok at 1.
  destruct (memneq_bool (x25519 (clamp r) basepoint9) zeros32); [|reflexivity].
  cbv beta iota.
  destruct (dh_ok x25519 (clamp r) (hs_reph H)); [|reflexivity].
  cbv beta iota.
  destruct (dh_ok x25519 (clamp r) (hs_rstatic H)); [|reflexivity].
  cbv beta iota.
  split; [| split; reflexivity].
  rewrite hhs3_p4_agree_hs2. reflexivity.
Qed.

Lemma hhs3_p4_agree_none ck h ei si psk r :
  m_create_response_model x25519 aead_enc ck h ei si psk r = None ->
  dh_ok x25519 (clamp r) basepoint9 = false \/ dh_ok x25519 (clamp r) ei = false \/
  dh_ok x25519 (clamp r) si = false.
Proof.
  unfold m_create_response_model. cbv zeta.
  destruct (dh_ok x25519 (clamp r) basepoint9); [|auto]. cbv beta iota.
  destruct (dh_ok x25519 (clamp r) ei); [|auto]. cbv beta iota.
  destruct (dh_ok x25519 (clamp r) si); [|auto]. discriminate.
Qed.

(* P2's agreement *)
Lemma hhs3_p4_agree_p2 R L I :
  x25519_props x25519 -> hhs3_run_ok R -> Zlength (i_r I) = 32 -> mi_ok (hhs3_IA x25519 R) = true ->
  match hhs3_mi x25519 aead_enc R L I with
  | Some (E, encs, enct, ep, ck, h) =>
      hhs3_ci x25519 aead_enc R L I =
        (true, mkIM (Int.repr 1) (i_idx I) E encs enct (im_mac1 (i_M0 I)) (im_mac2 (i_M0 I)),
         hs_set_state (hs_set_ckh (hs_set_eph (p_hs (hhs3_PB0 x25519 R L)) ep) ck h) HS_CREATED_INITIATION)
  | None => fst (fst (hhs3_ci x25519 aead_enc R L I)) = false
  end.
Proof.
  intros Hx HR Hr Hok.
  assert (Hid: id_has (d_id (hhs3_DA x25519 R L)) = true) by exact Hok.
  assert (Hrs: hs_rstatic (p_hs (hhs3_PB0 x25519 R L)) = mi_pub (hhs3_IB x25519 R)) by reflexivity.
  assert (Hss: hs_ss (p_hs (hhs3_PB0 x25519 R L)) = hhs3_ssa x25519 R) by reflexivity.
  assert (Hssl: Zlength (hhs3_ssa x25519 R) = 32).
  { unfold hhs3_ssa, m_precomputed_model.
    destruct (andb _ _); [apply Hx | reflexivity]. }
  unfold hhs3_mi, hhs3_ci, create_initiation_model, m_create_initiation_model.
  rewrite Hid, Hrs, Hss, (hhs3_p4_agree_clamp_nz _ Hr).
  rewrite (hhs3_p4_agree_memneq_is_zero _ Hssl).
  cbv beta iota zeta.
  unfold dh_ok at 1.
  destruct (memneq_bool (x25519 (clamp (i_r I)) basepoint9) zeros32); [|reflexivity].
  cbv beta iota.
  destruct (dh_ok x25519 (clamp (i_r I)) (mi_pub (hhs3_IB x25519 R))); [|reflexivity].
  cbv beta iota.
  destruct (is_zero (hhs3_ssa x25519 R)); [reflexivity|].
  cbv beta iota.
  rewrite hhs3_p4_agree_hs. reflexivity.
Qed.

(* A's ephemeral public in m1 is the harness's mi.ephemeral *)
Lemma hhs3_p4_agree_mi R L I M1 H1 MI :
  x25519_props x25519 -> hhs3_run_ok R -> hhs3_after_init x25519 aead_enc R L I M1 H1 MI ->
  let '(E, _, _, _, _, _) := MI in E = im_eph M1.
Proof.
  intros Hx HR (Hok & Hci & Hmi & _ & _ & Hr & _).
  assert (HA := hhs3_p4_agree_p2 R L I Hx HR Hr Hok).
  rewrite Hmi in HA. destruct MI as [[[[[E encs] enct] ep] ck] h].
  rewrite Hci in HA. injection HA as HM _. rewrite HM. reflexivity.
Qed.

End Agree.

Lemma hhs3_p4_agree_ok x25519 aead_enc : hhs3_p4_agree_stmt x25519 aead_enc.
Proof.
  intros Hx R L I M1 H1 MI nowb CI2 Q HR HI Hr. cbv zeta.
  destruct CI2 as [[t ck2] h2].
  set (P := hhs3_p4_new x25519 R L M1 nowb (t, ck2, h2)).
  assert (Hst: hs_state (p_hs (hhs3_PA2 P)) = HS_CONSUMED_INITIATION) by reflexivity.
  assert (Hcore := hhs3_p4_agree_core x25519 aead_enc (p_hs (hhs3_PA2 P)) (s_M0 Q) (s_r Q) (s_idx Q) Hst Hr).
  assert (Emr: hhs3_mr x25519 aead_enc R P M1 (t, ck2, h2) Q =
               m_create_response_model x25519 aead_enc (hs_ck (p_hs (hhs3_PA2 P))) (hs_hash (p_hs (hhs3_PA2 P)))
                 (hs_reph (p_hs (hhs3_PA2 P))) (hs_rstatic (p_hs (hhs3_PA2 P))) (hs_psk (p_hs (hhs3_PA2 P))) (s_r Q))
    by reflexivity.
  assert (Ecr: hhs3_cr x25519 aead_enc P Q =
               create_response_model x25519 aead_enc (p_hs (hhs3_PA2 P)) (s_M0 Q) (s_r Q) (s_idx Q)) by reflexivity.
  assert (Eri: hs_rindex (p_hs (hhs3_PA2 P)) = im_sender M1) by reflexivity.
  rewrite <- Emr, <- Ecr, Eri in Hcore.
  split; [| split].
  - destruct (hhs3_mr x25519 aead_enc R P M1 (t, ck2, h2) Q) as [[[[[E encn] ep] ck] h]|].
    + destruct Hcore as (-> & _). reflexivity.
    + exact Hcore.
  - intros E encn ep ck h Hm. rewrite Hm in Hcore. exact Hcore.
  - intros Hm z1 z2 z3.
    rewrite Emr in Hm. apply hhs3_p4_agree_none in Hm.
    assert (Hreph: hs_reph (p_hs (hhs3_PA2 P)) = im_eph M1) by reflexivity.
    assert (Hrst: hs_rstatic (p_hs (hhs3_PA2 P)) = mi_pub (hhs3_IA x25519 R)) by reflexivity.
    rewrite Hreph, Hrst in Hm.
    assert (HE := hhs3_p4_agree_mi x25519 aead_enc R L I M1 H1 MI Hx HR HI).
    destruct MI as [[[[[Ei encs] enct] epi] cki] hi]. subst Ei.
    unfold hhs3_ok4.
    rewrite <- (hhs3_p4_agree_memneq_is_zero _ (Hx _ _)).
    change (memneq_bool (x25519 (clamp (s_r Q)) basepoint9) zeros32) with (dh_ok x25519 (clamp (s_r Q)) basepoint9).
    destruct Hm as [Hm | [Hm | Hm]]; rewrite Hm;
      rewrite ?andb_false_r, ?andb_false_l; reflexivity.
Qed.
