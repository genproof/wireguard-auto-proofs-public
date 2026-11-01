(* law handshake, phase P6: pure lemma (key schedule completeness (hhs3_comm)).
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
Require Import WgNoise.proof.harness.handshake.hhs3_p6_factsA.
Require WgNoise.harness.x_handshake.code.

Local Open Scope Z_scope.

(* X25519 commutativity, used ONLY through this lemma (the final interface has the 32-byte premises) *)
Lemma hhs3_p6_dh x25519 :
  hhs3_comm x25519 -> forall a b, Zlength a = 32 -> Zlength b = 32 ->
  x25519 a (x25519 b basepoint9) = x25519 b (x25519 a basepoint9).
Proof. intros [_ H] a b Ha Hb. apply H; assumption. Qed.

Lemma hhs3_p6_ck_clamp_len s : Zlength (clamp s) = Zlength s.
Proof. unfold clamp. rewrite !Zlength_upd_Znth. reflexivity. Qed.

Ltac hhs3_p6_ck_split H :=
  repeat match goal with
         | Hh: context [match ?e with _ => _ end] |- _ => destruct e eqn:?; try discriminate
         end;
  repeat match goal with
         | Hh: Some _ = Some _ |- _ => inversion Hh; clear Hh; subst
         | Hh: (_, _) = (_, _) |- _ => inversion Hh; clear Hh; subst
         end.

(* the responder's consume_initiation on a one-peer list: its chaining key *)
Lemma hhs3_p6_ck_cin x25519 aead_dec ID a sh P0 M now a' P' :
  consume_initiation_model x25519 aead_dec ID [(a, sh, P0)] M now = Some (a', P') ->
  id_has ID = true /\
  hs_ck (p_hs P') = kdf1 (kdf1 (kdf1 init_ck (im_eph M)) (x25519 (id_priv ID) (im_eph M))) (hs_ss (p_hs P0)) /\
  hs_reph (p_hs P') = im_eph M /\ hs_rstatic (p_hs P') = hs_rstatic (p_hs P0) /\
  hs_psk (p_hs P') = hs_psk (p_hs P0).
Proof.
  intros H. unfold consume_initiation_model, consume_init_stage1, consume_init_stage2 in H. cbv zeta in H.
  simpl pk_find in H. unfold peer_get in H.
  hhs3_p6_ck_split H.
  all: apply negb_false_iff in Heqb; repeat split; auto.
Qed.

(* the responder's create_response: its chaining key and ephemeral *)
Lemma hhs3_p6_ck_cr x25519 aead_enc H M r idx M' H' :
  create_response_model x25519 aead_enc H M r idx = (true, M', H') ->
  hs_ck H' = kdf1 (kdf1 (kdf1 (kdf1 (hs_ck H) (x25519 (clamp r) basepoint9))
                               (x25519 (clamp r) (hs_reph H)))
                         (x25519 (clamp r) (hs_rstatic H))) (hs_psk H) /\
  rm_eph M' = x25519 (clamp r) basepoint9.
Proof.
  intros E. unfold create_response_model in E. cbv zeta in E.
  repeat match type of E with
         | context [if ?c then _ else _] => destruct c eqn:?; try discriminate
         end.
  inversion E; subst. split; reflexivity.
Qed.

(* the harness's m_consume_response: its chaining key *)
Lemma hhs3_p6_ck_mcr x25519 aead_dec ck h ep spriv psk e encn ST :
  m_consume_response_model x25519 aead_dec ck h ep spriv psk e encn = Some ST ->
  fst ST = kdf1 (kdf1 (kdf1 (kdf1 ck e) (x25519 ep e)) (x25519 spriv e)) psk.
Proof.
  intros E. unfold m_consume_response_model, consume_resp_crypto in E. cbv zeta in E. cbn [hs_ck hs_eph hs_psk hs_hash rm_eph rm_encn] in E.
  hhs3_p6_ck_split E. reflexivity.
Qed.

(* the harness's m_create_initiation: its ephemeral and chaining key *)
Lemma hhs3_p6_ck_mci x25519 aead_enc spub rpub ss eraw ts E encs enct ep ck h :
  m_create_initiation_model x25519 aead_enc spub rpub ss eraw ts = Some (E, encs, enct, ep, ck, h) ->
  ep = clamp eraw /\ E = x25519 (clamp eraw) basepoint9 /\
  ck = kdf1 (kdf1 (kdf1 init_ck E) (x25519 ep rpub)) ss.
Proof.
  intros H. unfold m_create_initiation_model in H. cbv zeta in H.
  repeat match type of H with
         | context [if ?c then _ else _] => destruct c eqn:?; try discriminate
         end.
  inversion H; subst. auto.
Qed.

Lemma hhs3_p6_ck_ok x25519 aead_enc aead_dec : hhs3_p6_ck_stmt x25519 aead_enc aead_dec.
Proof.
  intros Hc Hx Ha L V HC.
  pose proof (hhs3_p6_dh x25519 Hc) as Hdh. destruct Hc as [Hcl _].
  destruct HC as (HR & _ & HAI & (Hcin & _) & (Hcr & _ & _ & _ & Hr2) & (_ & Hmcr & _) & _).
  destruct V as [R S m1 m2 a0 f0 l0 I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR nowa PB2 ST2].
  unfold hhs3_p6_ck.
  cbn [w_R w_S w_m1 w_m2 w_a0 w_f0 w_l0 w_I w_M1 w_H1 w_MI w_nowb w_PA1 w_CI1 w_CI2 w_Q w_M2 w_H2 w_MR w_nowa
       w_PB2 w_ST2] in *.
  pose proof HR as (Hla & Hlb & _).
  destruct HAI as (Hok & Hci & Hmi & _ & _ & Hr1 & _).
  pose proof (hhs3_p6_factsA_agree x25519 aead_enc R L I Hx HR Hr1 Hok) as Hag.
  rewrite Hmi, Hci in Hag.
  destruct MI as [[[[[E encs] enct] ep] ck] h].
  injection Hag as HM1 _.
  (* A's chain after the initiation *)
  unfold hhs3_mi in Hmi. apply hhs3_p6_ck_mci in Hmi. destruct Hmi as (Hep & HE & Hck).
  (* B's chain after consume_initiation *)
  unfold hhs3_cin in Hcin. apply hhs3_p6_ck_cin in Hcin.
  destruct Hcin as (HokB & HckB & HrephB & HrsB & HpskB).
  change (id_has (d_id (hhs3_DB x25519 R L))) with (mi_ok (hhs3_IB x25519 R)) in HokB.
  change (id_priv (d_id (hhs3_DB x25519 R L))) with (mi_priv (hhs3_IB x25519 R)) in HckB.
  assert (Heph1: im_eph (hhs3_M1m x25519 R M1) = E) by (rewrite HM1; reflexivity).
  rewrite Heph1 in HckB, HrephB.
  change (hs_ss (p_hs (hhs3_PA0 x25519 R L))) with (hhs3_ssb x25519 R) in HckB.
  change (hs_rstatic (p_hs (hhs3_PA0 x25519 R L))) with (mi_pub (hhs3_IA x25519 R)) in HrsB.
  change (hs_psk (p_hs (hhs3_PA0 x25519 R L))) with (r_psk R) in HpskB.
  (* B's create_response *)
  unfold hhs3_cr in Hcr. apply hhs3_p6_ck_cr in Hcr. destruct Hcr as (HckH2 & HeM2).
  change (p_hs (hhs3_PA2 PA1)) with (p_hs PA1) in HckH2.
  rewrite HckH2, HckB, HrephB, HrsB, HpskB.
  (* A's consume_response *)
  unfold hhs3_mcr in Hmcr. rewrite (hhs3_p6_ck_mcr _ _ _ _ _ _ _ _ _ _ Hmcr), Hck, HeM2.
  (* the DH values agree *)
  set (r1 := i_r I) in *. set (r2 := s_r Q) in *.
  assert (Lr1: Zlength (clamp r1) = 32) by (rewrite hhs3_p6_ck_clamp_len; exact Hr1).
  assert (Lr2: Zlength (clamp r2) = 32) by (rewrite hhs3_p6_ck_clamp_len; exact Hr2).
  subst ep E.
  assert (D1: x25519 (mi_priv (hhs3_IB x25519 R)) (x25519 (clamp r1) basepoint9) =
              x25519 (clamp r1) (mi_pub (hhs3_IB x25519 R))).
  { unfold hhs3_IB, mident_of. cbn [mi_priv mi_pub]. rewrite (Hcl (r_rawb R)). apply Hdh; assumption. }
  assert (D2: hhs3_ssb x25519 R = hhs3_ssa x25519 R).
  { unfold hhs3_ssb, hhs3_ssa, m_precomputed_model, dh_ok.
    assert (X: x25519 (mi_priv (hhs3_IB x25519 R)) (mi_pub (hhs3_IA x25519 R)) =
               x25519 (mi_priv (hhs3_IA x25519 R)) (mi_pub (hhs3_IB x25519 R))).
    { unfold hhs3_IA, hhs3_IB, mident_of. cbn [mi_priv mi_pub]. rewrite (Hcl (r_rawb R)), (Hcl (r_rawa R)).
      apply Hdh; assumption. }
    rewrite X, Hok, HokB. reflexivity. }
  assert (D3: x25519 (clamp r2) (x25519 (clamp r1) basepoint9) =
              x25519 (clamp r1) (x25519 (clamp r2) basepoint9)) by (apply Hdh; assumption).
  assert (D4: x25519 (clamp r2) (mi_pub (hhs3_IA x25519 R)) =
              x25519 (mi_priv (hhs3_IA x25519 R)) (x25519 (clamp r2) basepoint9)).
  { unfold hhs3_IA, mident_of. cbn [mi_priv mi_pub]. rewrite (Hcl (r_rawa R)). apply Hdh; assumption. }
  rewrite D1, D2, D3, D4. reflexivity.
Qed.
