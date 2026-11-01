(* law handshake_receive: COPY of consume_response_any's hcr5_model.v: the pure part of the law - the run's draws, the index
   table's pool as the harness sets it up (the kents' keypair entries, then the peers' handshake entries), the
   harness's model of the target block (common.h m_consume_response on the snapshot) and its agreement with the
   kernel's model (prot_model3's consume_response_model).  Pure Coq, independent of the common.h layer. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The run: the setup's draws                                              *)
(* ---------------------------------------------------------------------- *)

Record hrx5cr_run := mkRunCR5 {
  rcr5_rawa: list byte;    (* raw_a *)
  rcr5_rawb: list byte;    (* raw_b *)
  rcr5_seca: list byte;    (* the cookie secret drawn by setup_device(&wa ..) *)
  rcr5_boot0: int64 }.     (* the first boot clock *)

Definition hrx5cr_run_ok (R: hrx5cr_run) : Prop :=
  Zlength (rcr5_rawa R) = 32 /\ Zlength (rcr5_rawb R) = 32 /\ Zlength (rcr5_seca R) = 32 /\
  0 <= Int64.unsigned (rcr5_boot0 R) < 2 ^ 62.

Definition hrx5cr_paddr (x: val * share * peer) : val := match x with (a, _, _) => a end.

(* ---------------------------------------------------------------------- *)
(* The index table's pool                                                  *)
(* ---------------------------------------------------------------------- *)

(* a kent's keypair entry (kents_add: at the kent's address k, any peer of the list, type KEYPAIR) *)
Definition hrx5cr_ke_ok (PS: list (val * share * peer)) (k: val) (x: val * share * entry) : Prop :=
  match x with (a, sh, E) => a = k /\ sh = Ews /\ In (e_peer E) (map hrx5cr_paddr PS) /\ e_type E = IDX_KEYPAIR end.

(* a peer's handshake entry (setup_peer: at hs_addr p, peer p, type HANDSHAKE) *)
Definition hrx5cr_hs_ok (y: val * share * peer) (x: val * share * entry) : Prop :=
  match x, y with (a, sh, E), (p, _, _) => a = hs_addr p /\ sh = Ews /\ e_peer E = p /\ e_type E = IDX_HANDSHAKE end.

(* the pool of T: the kents' entries (at the addresses KA, list order = most recent first), then the peers'
   handshake entries (PS order) *)
Definition hrx5cr_pool (KA: list val) (PS: list (val * share * peer)) (T: tstate) : Prop :=
  Forall2 (hrx5cr_ke_ok PS) KA (firstn (length KA) (t_D T)) /\
  Forall2 hrx5cr_hs_ok PS (skipn (length KA) (t_D T)).

(* ---------------------------------------------------------------------- *)
(* The harness's model and the kernel's                                    *)
(* ---------------------------------------------------------------------- *)

Section Model.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* the harness's model identities *)
Definition hrx5cr_IA (R: hrx5cr_run) : mident := mident_of x25519 (rcr5_rawa R).
Definition hrx5cr_IB (R: hrx5cr_run) : mident := mident_of x25519 (rcr5_rawb R).

(* A after setup_device *)
Definition hrx5cr_DA (R: hrx5cr_run) (wa ita pta: val) : device :=
  setup_dev x25519 wa ita pta (rcr5_rawa R) (rcr5_seca R) (rcr5_boot0 R).

(* the harness's model (the target block): the accepted peer (address, its state before the call), the
   model's chaining key and hash; acceptance as common.h states it: A has an identity, the first entry of the
   table's list with the receiver index is a handshake entry, the node whose peer's handshake entry it is
   (= the entry's peer) has the snapshot state CREATED_INITIATION, and m_consume_response succeeds on the
   snapshot (= the peer before the call) *)
Definition hrx5cr_tgt (IA: mident) (T: tstate) (PS: list (val * share * peer)) (M: resp_msg)
  : option (val * peer * list byte * list byte) :=
  if mi_ok IA then
    match t_find_index T (t_L T) (rm_receiver M) with
    | None => None
    | Some (_, E) =>
      if Int.eq (e_type E) IDX_HANDSHAKE then
        match sfind PS (e_peer E) with
        | None => None
        | Some (_, P) =>
          let H := p_hs P in
          if Int.eq (hs_state H) HS_CREATED_INITIATION then
            match m_consume_response_model x25519 aead_dec (hs_ck H) (hs_hash H) (hs_eph H) (mi_priv IA)
                    (hs_psk H) (rm_eph M) (rm_encn M) with
            | Some (ck, h) => Some (e_peer E, P, ck, h)
            | None => None
            end
          else None
        end
      else None
    end
  else None.

(* the accepted peer's new state (the kernel's, in the harness's terms): one more reference *)
Definition hrx5cr_new (P: peer) (M: resp_msg) (ck h: list byte) : peer :=
  let H := p_hs P in
  p_set_hs (p_set_refs P (rc_add1 (p_refs P)))
    (mkHS HS_CONSUMED_RESPONSE (hs_lic H) (hs_sid H) (hs_eph H) (hs_rstatic H) (rm_eph M) (hs_ss H)
          (hs_psk H) h ck (hs_ts H) (rm_sender M)).

End Model.

(* ---------------------------------------------------------------------- *)
(* The agreement                                                           *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5cr_model_sfind_in {A: Type} (l: list (val * share * A)) a sh v :
  sfind l a = Some (sh, v) -> In (a, sh, v) l.
Proof.
  induction l as [|[[x sx] w] l IH]; simpl; [discriminate|].
  intros H; destruct (EqDec_val x a); [subst; inv H; auto | auto].
Qed.

Lemma hrx5cr_model_find_in T L idx a E :
  t_find_index T L idx = Some (a, E) -> t_entry T a = Some E.
Proof.
  induction L as [|b L IH]; simpl; [discriminate|].
  destruct (t_entry T b) eqn:HE; [|exact IH].
  destruct (Int.eq (e_index e) idx); [intros H; inv H; exact HE | exact IH].
Qed.

Lemma hrx5cr_model_F2_in_r {A B: Type} (P: A -> B -> Prop) l1 l2 y :
  Forall2 P l1 l2 -> In y l2 -> exists x, In x l1 /\ P x y.
Proof.
  induction 1; simpl; [tauto|].
  intros [<-|HI]; [eauto|]. destruct (IHForall2 HI) as [z [? ?]]; eauto.
Qed.

Lemma hrx5cr_model_pool_type KA PS T a sh E :
  hrx5cr_pool KA PS T -> In (a, sh, E) (t_D T) ->
  e_type E = IDX_KEYPAIR \/ e_type E = IDX_HANDSHAKE.
Proof.
  intros [H1 H2] HIn.
  rewrite <- (firstn_skipn (length KA) (t_D T)) in HIn.
  apply in_app_or in HIn as [HIn|HIn].
  - destruct (hrx5cr_model_F2_in_r _ _ _ _ H1 HIn) as [K [_ HK]].
    simpl in HK. left; tauto.
  - destruct (hrx5cr_model_F2_in_r _ _ _ _ H2 HIn) as [[[p sp] P] [_ HK]].
    simpl in HK. right; tauto.
Qed.

Lemma hrx5cr_model_crypto x25519 aead_dec s H M :
  m_consume_response_model x25519 aead_dec (hs_ck H) (hs_hash H) (hs_eph H) s (hs_psk H) (rm_eph M) (rm_encn M) =
  consume_resp_crypto x25519 aead_dec s H M.
Proof. reflexivity. Qed.

(* the kernel's consume_response (prot_model3) agrees with the harness's model on A's peers and table as the
   harness sets them up *)
Lemma hrx5cr_agree x25519 aead_dec R wa ita pta T KA PS M :
  peers_refs_ok PS -> hrx5cr_pool KA PS T ->
  consume_response_model x25519 aead_dec (d_id (hrx5cr_DA x25519 R wa ita pta)) T PS M =
  match hrx5cr_tgt x25519 aead_dec (hrx5cr_IA x25519 R) T PS M with
  | Some (a, P, ck, h) => Some (a, hrx5cr_new P M ck h)
  | None => None
  end.
Proof.
  intros HR HP.
  unfold consume_response_model, hrx5cr_tgt, hrx5cr_DA, hrx5cr_IA, setup_dev, setup_identity,
    identity_of, mident_of, t_lookup.
  cbn [d_id id_has id_priv mi_ok mi_priv].
  destruct (andb (memneq_bool (rcr5_rawa R) zeros32) (memneq_bool (x25519 (rcr5_rawa R) basepoint9) zeros32))
    eqn:Hok; [|reflexivity].
  cbn [negb].
  destruct (t_find_index T (t_L T) (rm_receiver M)) as [[a E]|] eqn:HF; [|reflexivity].
  assert (HT: e_type E = IDX_KEYPAIR \/ e_type E = IDX_HANDSHAKE).
  { apply hrx5cr_model_find_in in HF. unfold t_entry in HF.
    destruct (sfind (t_D T) a) as [[sh E']|] eqn:HS; [|discriminate].
    inv HF. eapply hrx5cr_model_pool_type; [exact HP|]. apply hrx5cr_model_sfind_in; exact HS. }
  destruct HT as [HT|HT]; rewrite HT.
  - reflexivity.
  - change (Int.eq (Int.and IDX_HANDSHAKE IDX_HANDSHAKE) Int.zero) with false.
    change (Int.eq IDX_HANDSHAKE IDX_HANDSHAKE) with true. cbv iota.
    destruct (sfind PS (e_peer E)) as [[sp P]|] eqn:HS; [|reflexivity].
    assert (HRP: 0 < Int.unsigned (p_refs P) < 2147483647).
    { apply hrx5cr_model_sfind_in in HS. unfold peers_refs_ok in HR.
      rewrite Forall_forall in HR. exact (HR _ HS). }
    unfold peer_get.
    replace (Int.eq (p_refs P) Int.zero) with false
      by (symmetry; apply Int.eq_false; intros E0; rewrite E0, Int.unsigned_zero in HRP; lia).
    destruct (Int.eq (hs_state (p_hs P)) HS_CREATED_INITIATION); cbn [negb]; [|reflexivity].
    rewrite hrx5cr_model_crypto.
    destruct (consume_resp_crypto x25519 aead_dec _ (p_hs P) M) as [[ck h]|]; reflexivity.
Qed.
