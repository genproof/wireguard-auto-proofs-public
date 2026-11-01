(* The law hs_matching_keys, in the model: when A's create_initiation, B's consume_initiation, B's
   create_response and A's consume_response all succeed on the pair of devices new_pair builds
   (hs_specs.v: hs_pair), both sides end with the same chaining key, A in state CONSUMED_RESPONSE and B in
   state CREATED_RESPONSE, both peers alive with empty keypair slots.  begin_session then derives the transport
   keys kdf1 / kdf2 of that chaining key in the initiator's and the responder's order (kp_new), so A's sending
   key is B's receiving key and vice versa.

   The chaining keys agree because each Diffie-Hellman value is computed on both sides from the same two
   scalars (X25519 commutes on multiples of the base point, x25519_dh_agree, and clamps its scalar,
   x25519_clamp_inv): ee, es, se, and ss (the precomputed static-static values of the two peers), and A's
   peer holds B's static public key X25519(b, 9) and B's peer A's, with the same preshared key. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.common.wg3_iface3.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol5.prot_repr5.
Require Import WgNoise.proof.protocol5.prot_specs5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.handshake.hhs3_p6_ck.

Local Open Scope Z_scope.

Section Model.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* create_initiation's success: the identity has a key; the new handshake holds the clamped ephemeral, the
   chaining key after mixing E = X25519(clamp r, 9), es = X25519(clamp r, remote static) and ss, state
   CREATED_INITIATION and the old preshared key; the message carries E *)
Lemma hmk_ci ID H M r ts idx M' H' :
  create_initiation_model x25519 aead_enc ID H M r ts idx = (true, M', H') ->
  id_has ID = true /\ hs_eph H' = clamp r /\ im_eph M' = x25519 (clamp r) basepoint9 /\
  hs_ck H' = kdf1 (kdf1 (kdf1 init_ck (x25519 (clamp r) basepoint9)) (x25519 (clamp r) (hs_rstatic H)))
                  (hs_ss H) /\
  hs_state H' = HS_CREATED_INITIATION /\ hs_psk H' = hs_psk H.
Proof.
  intros E. unfold create_initiation_model in E. cbv zeta in E.
  repeat match type of E with
         | context [if ?c then _ else _] => destruct c eqn:?; try discriminate
         end.
  inversion E; subst. apply negb_false_iff in Heqb. repeat split; auto.
Qed.

(* consume_initiation on a one-peer list accepts that peer, in state CONSUMED_INITIATION, with its liveness
   and keypair slots unchanged *)
Lemma hmk_cin_peer ID a sh P0 M now a' P' :
  consume_initiation_model x25519 aead_dec ID [(a, sh, P0)] M now = Some (a', P') ->
  a' = a /\ hs_state (p_hs P') = HS_CONSUMED_INITIATION /\
  p_dead P' = p_dead P0 /\ p_cur P' = p_cur P0 /\ p_prev P' = p_prev P0 /\ p_next P' = p_next P0.
Proof.
  intros H. unfold consume_initiation_model, consume_init_stage1, consume_init_stage2 in H. cbv zeta in H.
  simpl pk_find in H. unfold peer_get in H.
  hhs3_p6_ck_split H. all: repeat split; reflexivity.
Qed.

(* create_response's success: state CREATED_RESPONSE *)
Lemma hmk_cr_state H M r idx M' H' :
  create_response_model x25519 aead_enc H M r idx = (true, M', H') -> hs_state H' = HS_CREATED_RESPONSE.
Proof.
  intros E. unfold create_response_model in E. cbv zeta in E.
  repeat match type of E with
         | context [if ?c then _ else _] => destruct c eqn:?; try discriminate
         end.
  inversion E; subst. reflexivity.
Qed.

(* consume_response on a one-peer list: it accepts that peer, in state CONSUMED_RESPONSE, with the chaining
   key of the initiator's mixing of the responder's ephemeral e (ee with its ephemeral, se with its static
   key, then the preshared key), its liveness and keypair slots unchanged *)
Lemma hmk_cre ID T a sh P0 M a' P' :
  consume_response_model x25519 aead_dec ID T [(a, sh, P0)] M = Some (a', P') ->
  a' = a /\ hs_state (p_hs P') = HS_CONSUMED_RESPONSE /\
  hs_ck (p_hs P') = kdf1 (kdf1 (kdf1 (kdf1 (hs_ck (p_hs P0)) (rm_eph M))
                                     (x25519 (hs_eph (p_hs P0)) (rm_eph M)))
                               (x25519 (id_priv ID) (rm_eph M))) (hs_psk (p_hs P0)) /\
  p_dead P' = p_dead P0 /\ p_cur P' = p_cur P0 /\ p_prev P' = p_prev P0 /\ p_next P' = p_next P0.
Proof.
  intros H. unfold consume_response_model, consume_resp_crypto in H. cbv zeta in H.
  simpl sfind in H. unfold peer_get in H.
  hhs3_p6_ck_split H. all: repeat split; reflexivity.
Qed.

(* the four steps on the pair at p (private keys araw, braw, preshared key psk), from uninitialised message
   buffers; S1, S2: the shim at create_initiation / consume_initiation; r1, r2: the random bytes of the two
   ephemerals; TA: A's index table at consume_response *)
Lemma hmk_model :
  x25519_props x25519 -> x25519_clamp_inv x25519 -> x25519_dh_agree x25519 ->
  forall p sh araw braw psk S1 r1 idx1 M1 H1 S2 b' PB1 r2 idx2 M2 H2 TA a' PA2,
  Zlength araw = 32 -> Zlength braw = 32 -> Zlength psk = 32 -> Zlength r1 = 32 -> Zlength r2 = 32 ->
  ci_res x25519 aead_enc (pair_devA x25519 p araw) (pair_peerA x25519 p araw braw psk) (init_of None) S1 r1 idx1
    = (true, M1, H1) ->
  cin_res x25519 aead_dec (pair_devB x25519 p braw) [(pair_bp p, sh, pair_peerB x25519 p araw braw psk)] M1 S2
    = Some (b', PB1) ->
  cr_res x25519 aead_enc PB1 (resp_of None) r2 idx2 = (true, M2, H2) ->
  cre_res x25519 aead_dec (pair_devA x25519 p araw) TA
    [(pair_ap p, sh, p_set_hs (pair_peerA x25519 p araw braw psk) H1)] M2 = Some (a', PA2) ->
  b' = pair_bp p /\ a' = pair_ap p /\
  hs_state (p_hs PA2) = HS_CONSUMED_RESPONSE /\ hs_state H2 = HS_CREATED_RESPONSE /\
  hs_ck (p_hs PA2) = hs_ck H2 /\
  p_dead PA2 = false /\ p_cur PA2 = nullval /\ p_prev PA2 = nullval /\ p_next PA2 = nullval /\
  p_dead PB1 = false /\ p_cur PB1 = nullval /\ p_prev PB1 = nullval /\ p_next PB1 = nullval.
Proof.
  intros Hx Hcl Hdh p sh araw braw psk S1 r1 idx1 M1 H1 S2 b' PB1 r2 idx2 M2 H2 TA a' PA2
         Hla Hlb Hlpsk Hr1 Hr2 Hci Hcin Hcr Hcre.
  unfold ci_res, prot_specs4.ci_res in Hci. apply hmk_ci in Hci.
  destruct Hci as (HidA & Heph1 & HM1 & Hck1 & Hst1 & Hpsk1).
  unfold cin_res, prot_specs4.cin_res in Hcin.
  pose proof (hhs3_p6_ck_cin _ _ _ _ _ _ _ _ _ _ Hcin) as (HidB & HckB & HrephB & HrsB & HpskB).
  apply hmk_cin_peer in Hcin. destruct Hcin as (-> & HstB & HdB & HcB & HpB & HnB).
  unfold cr_res, prot_specs4.cr_res in Hcr. pose proof (hmk_cr_state _ _ _ _ _ _ Hcr) as HstH2.
  apply hhs3_p6_ck_cr in Hcr. destruct Hcr as (HckH2 & HeM2).
  unfold cre_res, prot_specs4.cre_res in Hcre. apply hmk_cre in Hcre.
  destruct Hcre as (-> & HstA & HckA & HdA & HcA & HpA & HnA).
  rewrite HdA, HcA, HpA, HnA, HdB, HcB, HpB, HnB.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact HstA|]. split; [exact HstH2|].
  split; [|repeat split; reflexivity].
  rewrite HckA, HckH2, HckB, HrephB, HrsB, HpskB.
  unfold p_set_hs in HckA |- *. cbn [p_hs] in HckA |- *.
  rewrite Hck1, Heph1, Hpsk1, HM1, HeM2.
  unfold pair_peerA, pair_peerB, pair_devA, pair_devB, hs_peer0, hs_dev in *. cbn [p_hs d_id] in *.
  unfold hs_initial, prot_specs4.hs_initial. cbn [hs_rstatic hs_ss hs_psk].
  change (id_priv (hs_id x25519 araw)) with (clamp araw).
  change (id_priv (hs_id x25519 braw)) with (clamp braw).
  (* both identities hold a key: their public keys are X25519(raw, 9) *)
  assert (PA: id_pub (hs_id x25519 araw) = x25519 araw basepoint9).
  { revert HidA. unfold hs_id, identity_of. cbn [id_pub id_has].
    destruct (memneq_bool araw zeros32); [reflexivity|discriminate]. }
  assert (PB: id_pub (hs_id x25519 braw) = x25519 braw basepoint9).
  { revert HidB. unfold hs_id, identity_of. cbn [id_pub id_has].
    destruct (memneq_bool braw zeros32); [reflexivity|discriminate]. }
  assert (Lr1: Zlength (clamp r1) = 32) by (rewrite hhs3_p6_ck_clamp_len; exact Hr1).
  assert (Lr2: Zlength (clamp r2) = 32) by (rewrite hhs3_p6_ck_clamp_len; exact Hr2).
  (* each DH value of A's chain is B's, computed from the same two scalars *)
  assert (D1: x25519 (clamp braw) (x25519 (clamp r1) basepoint9) =
              x25519 (clamp r1) (x25519 braw basepoint9)) by (rewrite Hcl; apply Hdh; assumption).
  assert (D2: precomputed x25519 (hs_id x25519 araw) (id_pub (hs_id x25519 braw)) =
              precomputed x25519 (hs_id x25519 braw) (id_pub (hs_id x25519 araw))).
  { unfold precomputed, dh_ok. rewrite HidA, HidB, PA, PB.
    change (id_priv (hs_id x25519 araw)) with (clamp araw).
    change (id_priv (hs_id x25519 braw)) with (clamp braw).
    rewrite !Hcl, (Hdh araw braw Hla Hlb). reflexivity. }
  assert (D3: x25519 (clamp r1) (x25519 (clamp r2) basepoint9) =
              x25519 (clamp r2) (x25519 (clamp r1) basepoint9)) by (apply Hdh; assumption).
  assert (D4: x25519 (clamp araw) (x25519 (clamp r2) basepoint9) =
              x25519 (clamp r2) (x25519 araw basepoint9)) by (rewrite Hcl; apply Hdh; assumption).
  rewrite D2, PA, PB, D1, D3, D4. reflexivity.
Qed.

End Model.
