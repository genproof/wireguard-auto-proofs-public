(* law handshake, phase P6: pure lemma (A side after P5).
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
Require Import WgNoise.proof.harness.handshake.hhs3_p6_defs.
Require WgNoise.harness.x_handshake.code.

Local Open Scope Z_scope.

Section AccH.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

Lemma hhs3_p6_factsA_clamp_nz (r: list byte) :
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

Lemma hhs3_p6_factsA_memneq_is_zero (ss: list byte) :
  Zlength ss = 32 -> memneq_bool ss zeros32 = negb (is_zero ss).
Proof.
  intros H. unfold is_zero, bytes_eqb, memneq_bool. rewrite H.
  change (zeros 32) with zeros32.
  destruct (list_eq_dec Byte.eq_dec ss zeros32); reflexivity.
Qed.

Lemma hhs3_p6_factsA_hs (H: handshake) e ck0 h0 ck1 h1 ck2 h2 ck3 h3 s :
  hs_set_state (hs_set_ckh (hs_set_ckh (hs_set_ckh (hs_set_eph (hs_set_ckh H ck0 h0) e) ck1 h1) ck2 h2) ck3 h3) s
  = hs_set_state (hs_set_ckh (hs_set_eph H e) ck3 h3) s.
Proof. destruct H; reflexivity. Qed.

(* phase P2's agreement (hhs3_p2_agree_stmt): the kernel's handshake H1 from the harness's MI *)
Lemma hhs3_p6_factsA_agree R L I :
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
  rewrite Hid, Hrs, Hss, (hhs3_p6_factsA_clamp_nz _ Hr).
  rewrite (hhs3_p6_factsA_memneq_is_zero _ Hssl).
  cbv beta iota zeta.
  unfold dh_ok at 1.
  destruct (memneq_bool (x25519 (clamp (i_r I)) basepoint9) zeros32); [|reflexivity].
  cbv beta iota.
  destruct (dh_ok x25519 (clamp (i_r I)) (mi_pub (hhs3_IB x25519 R))); [|reflexivity].
  cbv beta iota.
  destruct (is_zero (hhs3_ssa x25519 R)); [reflexivity|].
  cbv beta iota.
  rewrite hhs3_p6_factsA_hs. reflexivity.
Qed.

(* consume_resp_crypto reads only the handshake's eph / psk / hash / ck and the message's eph / encn *)
Lemma hhs3_p6_factsA_crypto s H M :
  consume_resp_crypto x25519 aead_dec s H M =
  consume_resp_crypto x25519 aead_dec s
    (mkHS HS_ZEROED Int64.zero nullval (hs_eph H) [] [] [] (hs_psk H) (hs_hash H) (hs_ck H) [] Int.zero)
    (mkRM Int.zero Int.zero Int.zero (rm_eph M) (rm_encn M) [] []).
Proof. reflexivity. Qed.

Lemma hhs3_p6_factsA_sfind1 {A: Type} (P: A) (a: val) :
  sfind [(a, Tsh, P)] a = Some (Tsh, P).
Proof. simpl. rewrite if_true by reflexivity. reflexivity. Qed.

Lemma hhs3_p6_factsA_TA1 L I :
  hhs3_TA1 L I = mkT [(hs_addr (l_pb L), Tsh, mkEntry (l_pb L) IDX_HANDSHAKE (i_idx I))] [hs_addr (l_pb L)].
Proof.
  unfold hhs3_TA1, t_insert, t_set_index, hhs3_TA0.
  unfold t_entry. cbn [t_D t_L]. rewrite hhs3_p6_factsA_sfind1.
  unfold t_upd. cbn [t_D t_L supd vremove]. rewrite if_true by reflexivity. reflexivity.
Qed.

Lemma hhs3_p6_factsA_lookup L I rcv :
  t_lookup (hhs3_TA1 L I) IDX_HANDSHAKE rcv =
  if Int.eq (i_idx I) rcv then Some (hs_addr (l_pb L), mkEntry (l_pb L) IDX_HANDSHAKE (i_idx I)) else None.
Proof.
  rewrite hhs3_p6_factsA_TA1.
  unfold t_lookup, t_find_index, t_entry. cbn [t_D t_L]. rewrite hhs3_p6_factsA_sfind1.
  cbn [e_index].
  destruct (Int.eq (i_idx I) rcv); reflexivity.
Qed.

Lemma hhs3_p6_factsA_b2s_len key m : Zlength (model.blake2s key 32 m) = 32.
Proof. unfold model.blake2s, model.b2s_digest_stream, model.b2s_out. rewrite Zlength_map. reflexivity. Qed.

End AccH.

Lemma hhs3_p6_factsA_ok x25519 aead_enc aead_dec : hhs3_p6_factsA_stmt x25519 aead_enc aead_dec.
Proof.
  intros Hx Ha L V HC.
  destruct HC as (HR & _ & HAI & _ & _ & (Hcre & Hmcr & _) & _).
  destruct V as [R S m1 m2 a0 f0 l0 I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR nowa PB2 ST2].
  cbn [w_R w_S w_m1 w_m2 w_a0 w_f0 w_l0 w_I w_M1 w_H1 w_MI w_nowb w_PA1 w_CI1 w_CI2 w_Q w_M2 w_H2 w_MR w_nowa
       w_PB2 w_ST2] in *.
  unfold hhs3_p6_PB2n, hhs3_p6_ck.
  cbn [w_R w_S w_m1 w_m2 w_a0 w_f0 w_l0 w_I w_M1 w_H1 w_MI w_nowb w_PA1 w_CI1 w_CI2 w_Q w_M2 w_H2 w_MR w_nowa
       w_PB2 w_ST2].
  destruct HAI as (Hok & Hci & Hmi & _ & _ & Hr & _).
  pose proof (hhs3_p6_factsA_agree x25519 aead_enc R L I Hx HR Hr Hok) as Hag.
  rewrite Hmi, Hci in Hag.
  destruct MI as [[[[[E encs] enct] ep] ck] h].
  injection Hag as HM1 HH1.
  assert (Hst: hs_state H1 = HS_CREATED_INITIATION) by (rewrite HH1; reflexivity).
  assert (Heph: hs_eph H1 = ep) by (rewrite HH1; reflexivity).
  assert (Hck: hs_ck H1 = ck) by (rewrite HH1; reflexivity).
  assert (Hh: hs_hash H1 = h) by (rewrite HH1; reflexivity).
  assert (Hpsk: hs_psk H1 = r_psk R) by (rewrite HH1; reflexivity).
  assert (Hsid: hs_sid H1 = id_addr (l_wa L)) by (rewrite HH1; reflexivity).
  assert (Hsnd: im_sender M1 = i_idx I) by (rewrite HM1; reflexivity).
  clear HH1 HM1.
  assert (Hget: peer_get (hhs3_PB1 x25519 R L M1 H1) =
    Some (p_set_refs (hhs3_PB1 x25519 R L M1 H1) (rc_add1 (p_refs (hhs3_PB1 x25519 R L M1 H1)))))
    by reflexivity.
  (* the harness model's result: lengths *)
  assert (Hlen: Zlength (fst ST2) = 32 /\ Zlength (snd ST2) = 32).
  { unfold hhs3_mcr, m_consume_response_model, consume_resp_crypto in Hmcr. cbv zeta in Hmcr.
    repeat match type of Hmcr with
           | context [match ?e with _ => _ end] => destruct e eqn:?; try discriminate
           end.
    injection Hmcr as <-. split; cbn [fst snd];
      unfold kdf1, hmac, mix_hash, HASH; apply hhs3_p6_factsA_b2s_len. }
  (* the kernel's accepted peer *)
  unfold hhs3_cre, consume_response_model in Hcre.
  change (id_has (d_id (hhs3_DA x25519 R L))) with (mi_ok (hhs3_IA x25519 R)) in Hcre. rewrite Hok in Hcre.
  cbn [negb] in Hcre.
  rewrite hhs3_p6_factsA_lookup in Hcre.
  change (rm_receiver (hhs3_M2m x25519 R M2)) with (rm_receiver M2) in Hcre.
  destruct (Int.eq (i_idx I) (rm_receiver M2)); [| discriminate Hcre].
  cbn [e_peer] in Hcre. rewrite hhs3_p6_factsA_sfind1, Hget in Hcre.
  change (p_hs (hhs3_PB1 x25519 R L M1 H1)) with H1 in Hcre.
  rewrite Hst, Int.eq_true in Hcre. cbn [negb] in Hcre.
  rewrite hhs3_p6_factsA_crypto, Heph, Hpsk, Hh, Hck in Hcre.
  change (id_priv (d_id (hhs3_DA x25519 R L))) with (mi_priv (hhs3_IA x25519 R)) in Hcre.
  change (rm_eph (hhs3_M2m x25519 R M2)) with (rm_eph M2) in Hcre.
  change (rm_encn (hhs3_M2m x25519 R M2)) with (rm_encn M2) in Hcre.
  change (rm_sender (hhs3_M2m x25519 R M2)) with (rm_sender M2) in Hcre.
  unfold hhs3_mcr, m_consume_response_model in Hmcr.
  rewrite Hmcr in Hcre. destruct ST2 as [ck2 h2].
  injection Hcre as <-.
  split; [rewrite Heph, Hpsk; reflexivity | split; [apply Hlen | split; [apply Hlen | split; assumption]]].
Qed.
