(* Law hs_reject_initiation: the separation facts main's body uses, between the harness's compspecs CSh (where
   main writes the message and B's handshake field by field) and noise.c's (where the representation is stated). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol5.prot_repr5.
Require WgNoise.proof.protocol4.prot_specs4 WgNoise.proof.protocol5.prot_specs5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Local Open Scope logic.

#[export] Instance hri_cce : change_composite_env Noise.CS CSh.
Proof. make_cs_preserve Noise.CS CSh. Defined.

(* create_initiation's insertion of the handshake entry into a table holding only that entry: still only it *)
Lemma hri_tD_insert a sh E L idx : exists E', t_D (t_insert (mkT [(a, sh, E)] L) a idx) = [(a, sh, E')].
Proof.
  unfold t_insert, t_set_index, t_entry, t_upd; simpl.
  repeat (rewrite if_true by reflexivity; simpl). eauto.
Qed.

Section Peer.
#[local] Existing Instance Noise.CS.

(* a peer without its handshake: main rewrites B's handshake field by field *)
Definition hri_peer_rest (sh: share) (p: val) (P: peer) : mpred :=
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer [StructField I._device] (p_device P) p *
   field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   field_at_ sh t_peer [StructField I._last_sent_handshake] p *
   field_at_ sh t_peer [StructField I._latest_cookie] p *
   field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at_ sh t_peer [StructField I._internal_id] p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma hri_peer_split sh p P : peer_rep5 sh p P = hri_peer_rest sh p P * hs_rep sh (hs_addr p) (p_hs P).
Proof.
  unfold peer_rep5, hri_peer_rest. apply pred_ext; entailer!.
Qed.

Lemma hri_peer_join sh p P H :
  hri_peer_rest sh p P * hs_rep sh (hs_addr p) H |-- peer_rep5 sh p (p_set_hs P H).
Proof.
  rewrite (hri_peer_split sh p (p_set_hs P H)). unfold hri_peer_rest. simpl. entailer!.
Qed.

(* a device without its static identity: same_peer reads B's identity pointer *)
Definition hri_dev_rest (sh: share) (wg: val) (D: device) : mpred :=
  !! field_compatible t_dev [] wg &&
  (field_at_ sh t_dev [StructField I._dev] wg *
   field_at_ sh t_dev [StructField I._cookie_checker] wg *
   field_at sh t_dev [StructField I._peer_hashtable] (d_ptab D) wg *
   field_at sh t_dev [StructField I._index_hashtable] (d_itab D) wg).

Lemma hri_dev_split sh wg D : device_rep5 sh wg D = hri_dev_rest sh wg D * identity_rep sh (id_addr wg) (d_id D).
Proof.
  unfold device_rep5, hri_dev_rest. apply pred_ext; entailer!.
Qed.

End Peer.

#[export] Instance hri_cce_back : change_composite_env CSh Noise.CS.
Proof. make_cs_preserve CSh Noise.CS. Defined.

(* a handshake whose fields main has written in its own compspecs (the byte arrays through nondet_bytes, at
   their addresses) is again hs_rep *)
Lemma hri_hs_fold sh h HS lk :
  hs_ok HS ->
  @field_at CSh sh t_hs (DOT I._state) (Vint (hs_state HS)) h *
  @field_at CSh sh t_hs (DOT I._last_initiation_consumption) (Vlong (hs_lic HS)) h *
  @field_at CSh sh t_hs (DOT I._static_identity) (hs_sid HS) h *
  @data_at CSh sh (tarray tuchar 32) (bytes (hs_eph HS)) (@field_address CSh t_hs (DOT I._ephemeral_private) h) *
  @field_at CSh sh t_hs (DOT I._remote_static) (bytes (hs_rstatic HS)) h *
  @data_at CSh sh (tarray tuchar 32) (bytes (hs_reph HS)) (@field_address CSh t_hs (DOT I._remote_ephemeral) h) *
  @field_at CSh sh t_hs (DOT I._precomputed_static_static) (bytes (hs_ss HS)) h *
  @field_at CSh sh t_hs (DOT I._preshared_key) (bytes (hs_psk HS)) h *
  @data_at CSh sh (tarray tuchar 32) (bytes (hs_hash HS)) (@field_address CSh t_hs (DOT I._hash) h) *
  @data_at CSh sh (tarray tuchar 32) (bytes (hs_ck HS)) (@field_address CSh t_hs (DOT I._chaining_key) h) *
  @data_at CSh sh (tarray tuchar 12) (bytes (hs_ts HS)) (@field_address CSh t_hs (DOT I._latest_timestamp) h) *
  @field_at CSh sh t_hs (DOT I._remote_index) (Vint (hs_rindex HS)) h *
  @field_at CSh sh t_hs (DOT I._lock) lk h *
  spacer sh 36 40 h * spacer sh 300 304 h
  |-- hs_rep sh h HS.
Proof.
  intros OK. unfold hs_rep. rewrite prop_true_andp by auto. Exists lk.
  repeat match goal with |- context [@field_at Noise.CS ?sh t_hs ?gfs ?v ?p] =>
    erewrite (@field_at_change_composite Noise.CS CSh _ sh t_hs gfs v v) by (first [apply JMeq_refl | reflexivity]) end.
  rewrite (@field_at_data_at CSh sh t_hs (DOT I._ephemeral_private)),
    (@field_at_data_at CSh sh t_hs (DOT I._remote_ephemeral)), (@field_at_data_at CSh sh t_hs (DOT I._hash)),
    (@field_at_data_at CSh sh t_hs (DOT I._chaining_key)), (@field_at_data_at CSh sh t_hs (DOT I._latest_timestamp)).
  simpl nested_field_type. cancel.
Qed.

(* a list of one peer *)
Lemma hri_peers1 a sh P : peers_rep5 [(a, sh, P)] = peer_rep5 sh a P.
Proof. unfold peers_rep5. simpl. rewrite sepcon_emp. reflexivity. Qed.

(* last_initiation_consumption = any_u64() >> 2: below 2^62, so the 20 ms addition does not overflow *)
Lemma hri_lic_ok (t: int64) :
  Int64.signed (Int64.shru t (Int64.repr (Int.unsigned (Int.repr 2)))) <= Int64.max_signed - 20000000.
Proof.
  change (Int.unsigned (Int.repr 2)) with 2.
  rewrite Int64.shru_div_two_p. change (two_p (Int64.unsigned (Int64.repr 2))) with 4.
  pose proof (Int64.unsigned_range t) as R.
  assert (0 <= Int64.unsigned t / 4 < 2 ^ 62) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; rep_lia).
  rewrite Int64.signed_repr by rep_lia. rep_lia.
Qed.

(* consume_initiation over one peer returns that peer, if any *)
Lemma hri_cin_some x25519 aead_dec D a0 sh P M S a P' :
  prot_specs5.cin_res x25519 aead_dec D [(a0, sh, P)] M S = Some (a, P') -> a = a0.
Proof.
  unfold prot_specs5.cin_res, prot_specs4.cin_res, consume_initiation_model. intros E.
  destruct (negb (id_has (d_id D))); [discriminate |].
  destruct (consume_init_stage1 _ _ (d_id D) M) as [[[[s x] ck1] h1] |]; [| discriminate].
  simpl in E. destruct (bytes_eqb (hs_rstatic (p_hs P)) s); [| discriminate].
  destruct (peer_get P); [| discriminate].
  match type of E with context [match ?c with _ => _ end] => destruct c as [[[t ck2] h2] |]; [| discriminate] end.
  match type of E with context [if ?c then _ else _] => destruct c; [discriminate |] end.
  inv E. auto.
Qed.

(* nondet_bytes's result as bytes *)
Lemma hri_bytes (l: list Z) :
  Forall (fun b => 0 <= b <= Byte.max_unsigned) l ->
  map (fun b => Vint (Int.repr b)) l = bytes (map Byte.repr l).
Proof.
  intros HF. unfold bytes. rewrite map_map. apply map_ext_Forall.
  eapply Forall_impl; [| exact HF]. intros b Hb. simpl.
  unfold Vubyte. rewrite Byte.unsigned_repr by auto. reflexivity.
Qed.

Section Msg.
#[local] Existing Instance CSh.

Definition t_msgh := Tstruct H._message_handshake_initiation noattr.

(* the message main fills with any bytes (header type t1, sender t2) *)
Definition hri_msg (t1 t2: Z) (eph encs enct: list Z) : init_msg :=
  mkIM (Int.repr t1) (Int.repr t2) (map Byte.repr eph) (map Byte.repr encs) (map Byte.repr enct) (zeros 16) (zeros 16).

Lemma hri_msg_fold sh m t1 t2 eph encs enct mac1 mac2 :
  Zlength eph = 32 -> Zlength encs = 48 -> Zlength enct = 28 ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) eph ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) encs ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) enct ->
  @field_at CSh sh t_msgh (DOT H._header) (Vint (Int.repr t1)) m *
  @field_at CSh sh t_msgh (DOT H._sender_index) (Vint (Int.repr t2)) m *
  @data_at CSh sh (tarray tuchar 32) (map (fun b => Vint (Int.repr b)) eph) (@field_address CSh t_msgh (DOT H._unencrypted_ephemeral) m) *
  @data_at CSh sh (tarray tuchar 48) (map (fun b => Vint (Int.repr b)) encs) (@field_address CSh t_msgh (DOT H._encrypted_static) m) *
  @data_at CSh sh (tarray tuchar 28) (map (fun b => Vint (Int.repr b)) enct) (@field_address CSh t_msgh (DOT H._encrypted_timestamp) m) *
  @data_at CSh sh (tarray tuchar 16) mac1 (@field_address CSh t_msgh [StructField H._mac1; StructField H._macs] m) *
  @data_at CSh sh (tarray tuchar 16) mac2 (@field_address CSh t_msgh [StructField H._mac2; StructField H._macs] m)
  |-- init_rep5 sh m (hri_msg t1 t2 eph encs enct).
Proof.
  intros L1 L2 L3 F1 F2 F3.
  assert_PROP (@field_compatible CSh t_msgh [] m) as FC.
  { entailer!. destruct H as (? & ? & ? & ? & ? & ?). split3; auto; split3; auto; exact I. }
  unfold init_rep5, hri_msg, im_ok5. simpl. rewrite prop_true_andp by (rewrite !Zlength_map; auto).
  rewrite !hri_bytes in * by auto.
  (* the representation's fields, stated in noise.c's compspecs, in the harness's *)
  unfold field_at_.
  repeat match goal with |- context [@field_at Noise.CS ?sh ?t ?gfs ?v ?p] =>
    erewrite (@field_at_change_composite Noise.CS CSh _ sh t gfs v v) by (first [apply JMeq_refl | reflexivity]) end.
  change t_init with t_msgh.
  change I._header with H._header. change I._sender_index with H._sender_index.
  change I._unencrypted_ephemeral with H._unencrypted_ephemeral. change I._encrypted_static with H._encrypted_static.
  change I._encrypted_timestamp with H._encrypted_timestamp. change I._macs with H._macs.
  match goal with |- context [@field_at ?cs sh t_msgh (DOT H._macs) ?v m] =>
    change (@field_at cs sh t_msgh (DOT H._macs) v m) with (@field_at_ CSh sh t_msgh (DOT H._macs) m) end.
  rewrite (@field_at_data_at CSh sh t_msgh (DOT H._unencrypted_ephemeral)),
    (@field_at_data_at CSh sh t_msgh (DOT H._encrypted_static)),
    (@field_at_data_at CSh sh t_msgh (DOT H._encrypted_timestamp)), (@field_at__data_at_ CSh sh t_msgh (DOT H._macs)).
  unfold t_msgh in *.
  (* the macs: their two arrays *)
  unfold_data_at (data_at_ sh (nested_field_type (Tstruct H._message_handshake_initiation noattr) (DOT H._macs)) _).
  match goal with |- context [field_at ?sh ?t (DOT code._mac1) ?v ?p] =>
    change (field_at sh t (DOT code._mac1) v p) with (field_at_ sh t (DOT code._mac1) p);
    rewrite (field_at__data_at_ sh t (DOT code._mac1) p) end.
  match goal with |- context [field_at ?sh ?t (DOT code._mac2) ?v ?p] =>
    change (field_at sh t (DOT code._mac2) v p) with (field_at_ sh t (DOT code._mac2) p);
    rewrite (field_at__data_at_ sh t (DOT code._mac2) p) end.
  change (Tstruct code._message_macs noattr) with (nested_field_type (Tstruct H._message_handshake_initiation noattr) (DOT H._macs)).
  rewrite <- !field_address_app. simpl app.
  sep_apply (data_at_data_at_ sh (tarray tuchar 16) mac1). sep_apply (data_at_data_at_ sh (tarray tuchar 16) mac2).
  simpl nested_field_type. cancel.
Qed.

(* &p->a_peer.handshake, &p->b_peer.handshake: the handshakes of the two peers of struct pair *)
Lemma hri_pair_hs_a p :
  field_compatible t_pair [] p ->
  field_address t_pair [StructField H._handshake; StructField H._a_peer] p = hs_addr (pair_ap p).
Proof.
  intros FC. unfold pair_ap, hs_addr.
  rewrite !field_address_offset by auto with field_compatible.
  rewrite offset_offset_val. reflexivity.
Qed.

Lemma hri_pair_hs_b p :
  field_compatible t_pair [] p ->
  field_address t_pair [StructField H._handshake; StructField H._b_peer] p = hs_addr (pair_bp p).
Proof.
  intros FC. unfold pair_bp, hs_addr.
  rewrite !field_address_offset by auto with field_compatible.
  rewrite offset_offset_val. reflexivity.
Qed.

End Msg.
