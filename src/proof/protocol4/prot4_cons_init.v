(* the body of wg_noise_handshake_consume_initiation against the v4
   specification (prot_specs4.v, context Gprot4): the port of v3's prot_body3_consume_init.v.  The
   refcount_t warnings stay w: the counts are below INT_MAX (peers_refs_ok), so the lookup's get and the put on
   rejection do not warn (rc_dec_warn_small). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_body3_shim_table1.
Require WgNoise.proof.blake2s.model.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

Section Prot4ConsumeInit.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.
Context (HX: x25519_props x25519) (HA: aead_props aead_enc aead_dec).

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Definition prot4_Gci := Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS.

(* ---------------------------------------------------------------------------------------------- *)
(* the message                                                                                     *)
(* ---------------------------------------------------------------------------------------------- *)

Definition prot4_cin_mrest (sh: share) (m: val) (M: init_msg) : mpred :=
  field_at sh t_init (DOT N._header) (Vint (im_type M)) m *
  field_at sh t_init (DOT N._macs) (bytes (im_mac1 M), bytes (im_mac2 M)) m.

Lemma prot4_cin_init_eq sh m M :
  init_rep sh m M =
  !! im_ok M &&
  (prot4_cin_mrest sh m M *
   field_at sh t_init (DOT N._sender_index) (Vint (im_sender M)) m *
   field_at sh t_init (DOT N._unencrypted_ephemeral) (bytes (im_eph M)) m *
   field_at sh t_init (DOT N._encrypted_static) (bytes (im_encs M)) m *
   field_at sh t_init (DOT N._encrypted_timestamp) (bytes (im_enct M)) m).
Proof.
  unfold init_rep, init_val, prot4_cin_mrest. f_equal. unfold_data_at (data_at _ _ _ m).
  apply pred_ext; cancel.
Qed.

Lemma prot4_cin_m_eph sh m bs : Zlength bs = 32 ->
  field_at sh t_init (DOT N._unencrypted_ephemeral) (bytes bs) m =
  bytes_at sh bs (field_address t_init (DOT N._unencrypted_ephemeral) m).
Proof. intros L. unfold bytes_at. rewrite L, field_at_data_at. reflexivity. Qed.

Lemma prot4_cin_m_encs sh m bs : Zlength bs = 48 ->
  field_at sh t_init (DOT N._encrypted_static) (bytes bs) m =
  prim_bytes sh bs (field_address t_init (DOT N._encrypted_static) m).
Proof. intros L. unfold prim_bytes. rewrite L. simpl. rewrite field_at_data_at. reflexivity. Qed.

Lemma prot4_cin_m_enct sh m bs : Zlength bs = 28 ->
  field_at sh t_init (DOT N._encrypted_timestamp) (bytes bs) m =
  prim_bytes sh bs (field_address t_init (DOT N._encrypted_timestamp) m).
Proof. intros L. unfold prim_bytes. rewrite L. simpl. rewrite field_at_data_at. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the device                                                                                      *)
(* ---------------------------------------------------------------------------------------------- *)

Definition prot4_cin_drest (sh: share) (wg: val) (D: device) : mpred :=
  field_at sh t_dev (DOT I._dev) (d_dev D) wg *
  checker_rep sh (cc_addr wg) (d_cc D) *
  field_at sh t_dev (DOT I._index_hashtable) (d_itab D) wg *
  (EX lk: val, field_at sh t_dev (DOT I._static_identity DOT I._lock) lk wg).

Lemma prot4_cin_dev_eq sh wg D :
  device_rep sh wg D =
  !! (field_compatible t_dev [] wg /\ id_ok (d_id D)) &&
  (prot4_cin_drest sh wg D *
   spacer sh 77 80 wg *
   field_at sh t_dev (DOT I._static_identity DOT I._has_identity) (Val.of_bool (id_has (d_id D))) wg *
   field_at sh t_dev (DOT I._static_identity DOT I._static_public) (bytes (id_pub (d_id D))) wg *
   field_at sh t_dev (DOT I._static_identity DOT I._static_private) (bytes (id_priv (d_id D))) wg *
   field_at sh t_dev (DOT I._peer_hashtable) (d_ptab D) wg).
Proof.
  unfold device_rep, identity_rep, prot4_cin_drest.
  assert (E: field_compatible t_dev [] wg -> forall v, data_at sh t_sid v (id_addr wg) =
             field_at sh t_dev (DOT I._static_identity) v wg).
  { intros FC v. rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible. reflexivity. }
  apply pred_ext.
  - Intros lk. apply andp_right; [apply prop_right; auto|].
    rewrite E by auto. unfold_field_at 2%nat. Exists lk. cancel.
  - Intros lk. apply andp_right; [apply prop_right; auto|].
    Exists lk. rewrite E by auto. unfold_field_at 9%nat. cancel.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the peers                                                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

(* the peer without its device field, refcount and handshake *)
Definition prot4_cin_prest (sh: share) (p: val) (P: peer) : mpred :=
  field_at sh t_peer (DOT I._is_dead) (Val.of_bool (p_dead P)) p *
  kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
  field_at sh t_peer (DOT I._last_sent_handshake) (Vlong (p_lsh P)) p *
  cookie_rep sh (cookie_addr p) (p_cookie P) *
  field_at sh t_peer (DOT I._internal_id) (Vlong (p_id P)) p *
  field_at sh t_peer (DOT I._pubkey_next) (p_pknext P) p *
  spacer sh 9 16 p * spacer sh 476 480 p.

Lemma prot4_cin_peer_eq sh p P :
  peer_rep sh p P =
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer (DOT I._device) (p_device P) p * peer_refs_rep sh p (p_refs P) *
   prot4_cin_prest sh p P * hs_rep sh (hs_addr p) (p_hs P)).
Proof. unfold peer_rep, prot4_cin_prest, peer_refs_rep. f_equal. apply pred_ext; cancel. Qed.

Lemma prot4_cin_prest_set_hs sh p P H : prot4_cin_prest sh p (p_set_hs P H) = prot4_cin_prest sh p P.
Proof. reflexivity. Qed.
Lemma prot4_cin_prest_set_refs sh p P r : prot4_cin_prest sh p (p_set_refs P r) = prot4_cin_prest sh p P.
Proof. reflexivity. Qed.

Lemma prot4_cin_glb sh1 sh2 :
  writable_share sh1 -> readable_share sh2 -> sepalg.nonidentity (Share.glb sh1 sh2).
Proof.
  intros [_ HW] HR N.
  apply HR.
  apply leq_join_sub, Share.ord_spec1 in HW.
  apply identity_share_bot in N.
  rewrite HW, Share.glb_assoc, N, Share.glb_bot.
  apply bot_identity.
Qed.

Lemma prot4_cin_dev_conflict sh sh' a v v' :
  writable_share sh -> writable_share sh' ->
  field_at sh t_peer (DOT I._device) v a * field_at sh' t_peer (DOT I._device) v' a |-- FF.
Proof.
  intros W W'. rewrite !field_at_data_at. apply data_at_conflict_glb.
  - apply prot4_cin_glb; auto.
  - simpl. lia.
Qed.

Lemma prot4_cin_peer_conflict sh sh' a P P' :
  writable_share sh -> writable_share sh' -> peer_rep sh a P * peer_rep sh' a P' |-- FF.
Proof.
  intros W W'. rewrite !prot4_cin_peer_eq. Intros.
  sep_apply (prot4_cin_dev_conflict sh sh' a (p_device P) (p_device P') W W').
  rewrite !FF_sepcon. auto.
Qed.

Lemma prot4_cin_nodup PS : peers_wf PS -> peers_rep PS |-- !! NoDup (saddrs PS).
Proof.
  induction PS as [|[[a sh] P] PS IH]; intros WF.
  - apply prop_right. constructor.
  - unfold peers_rep. simpl iter_sepcon. inversion WF; subst. fold (peers_rep PS).
    destruct (in_dec EqDec_val a (saddrs PS)) as [Hin|Hn].
    + destruct (prot3_shim_table1_sfind_in PS a Hin) as (sh' & P' & Hf).
      unfold peers_rep. rewrite (prot3_shim_table1_split PS a sh' P' _ Hf).
      assert (W': writable_share sh') by (eapply prot3_shim_table1_sfind_wr; eauto).
      unfold peer_item_rep at 1 2. rewrite <- sepcon_assoc.
      sep_apply (prot4_cin_peer_conflict sh sh' a P P' H1 W'). rewrite FF_sepcon. apply FF_left.
    + unfold peer_item_rep. sep_apply (IH H2). Intros. apply prop_right. simpl. constructor; auto.
Qed.

Lemma prot4_cin_pk_find_sfind PS s a P :
  NoDup (saddrs PS) -> pk_find PS s = Some (a, P) -> exists sh, sfind PS a = Some (sh, P).
Proof.
  induction PS as [|[[x shx] Px] PS IH]; simpl; intros ND H; [discriminate|].
  inversion ND; subst.
  destruct (bytes_eqb (hs_rstatic (p_hs Px)) s).
  - inv H. exists shx. destruct (EqDec_val a a); [reflexivity|congruence].
  - destruct (IH H3 H) as [sh Hs]. exists sh.
    destruct (EqDec_val x a); [|exact Hs].
    subst. exfalso. apply H2. eapply prot3_shim_table1_saddrs_in, prot3_shim_table1_sfind_In; eauto.
Qed.

Lemma prot4_cin_open PS a sh P :
  sfind PS a = Some (sh, P) -> forall P', peers_rep (supd PS a P') = peer_rep sh a P' * peers_rep (sdel PS a).
Proof.
  intros Hf P'. unfold peers_rep.
  rewrite (prot3_shim_table1_split (supd PS a P') a sh P' _ (prot3_shim_table1_supd_sfind_same PS a sh P' P Hf)).
  rewrite prot3_shim_table1_supd_sdel. reflexivity.
Qed.

Lemma prot4_cin_open0 PS a sh P :
  sfind PS a = Some (sh, P) -> peers_rep PS = peer_rep sh a P * peers_rep (sdel PS a).
Proof.
  intros Hf. rewrite <- (prot4_cin_open PS a sh P Hf P). rewrite (prot3_shim_table1_supd_same PS a sh P Hf). reflexivity.
Qed.

Lemma prot4_cin_valid sh a P : readable_share sh -> peer_rep sh a P |-- valid_pointer a.
Proof.
  intros R. rewrite prot4_cin_peer_eq. Intros.
  rewrite !sepcon_assoc. apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; [apply readable_nonidentity; auto | simpl; lia | reflexivity].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the handshake                                                                                   *)
(* ---------------------------------------------------------------------------------------------- *)

(* the handshake fields consume_initiation never touches *)
Definition prot4_cin_hrest (sh: share) (h: val) (sid: val) (eph rs psk: list byte) : mpred :=
  field_at sh t_hs (DOT I._static_identity) sid h *
  field_at sh t_hs (DOT I._ephemeral_private) (bytes eph) h *
  field_at sh t_hs (DOT I._remote_static) (bytes rs) h *
  field_at sh t_hs (DOT I._preshared_key) (bytes psk) h *
  (EX lk: val, field_at sh t_hs (DOT I._lock) lk h) *
  spacer sh 36 40 h * spacer sh 300 304 h.

Lemma prot4_cin_hs_eq sh h H :
  hs_rep sh h H =
  !! hs_ok H &&
  (prot4_cin_hrest sh h (hs_sid H) (hs_eph H) (hs_rstatic H) (hs_psk H) *
   field_at sh t_hs (DOT I._state) (Vint (hs_state H)) h *
   field_at sh t_hs (DOT I._last_initiation_consumption) (Vlong (hs_lic H)) h *
   field_at sh t_hs (DOT I._remote_ephemeral) (bytes (hs_reph H)) h *
   field_at sh t_hs (DOT I._precomputed_static_static) (bytes (hs_ss H)) h *
   field_at sh t_hs (DOT I._hash) (bytes (hs_hash H)) h *
   field_at sh t_hs (DOT I._chaining_key) (bytes (hs_ck H)) h *
   field_at sh t_hs (DOT I._latest_timestamp) (bytes (hs_ts H)) h *
   field_at sh t_hs (DOT I._remote_index) (Vint (hs_rindex H)) h).
Proof. unfold hs_rep, prot4_cin_hrest. f_equal. apply pred_ext; cancel. Qed.

Lemma prot4_cin_hs_reph sh h bs : Zlength bs = 32 ->
  field_at sh t_hs (DOT I._remote_ephemeral) (bytes bs) h = bytes_at sh bs (field_address t_hs (DOT I._remote_ephemeral) h).
Proof. intros L. unfold bytes_at. rewrite L, field_at_data_at. reflexivity. Qed.
Lemma prot4_cin_hs_ss sh h bs : Zlength bs = 32 ->
  field_at sh t_hs (DOT I._precomputed_static_static) (bytes bs) h = bytes_at sh bs (field_address t_hs (DOT I._precomputed_static_static) h).
Proof. intros L. unfold bytes_at. rewrite L, field_at_data_at. reflexivity. Qed.
Lemma prot4_cin_hs_hash sh h bs : Zlength bs = 32 ->
  field_at sh t_hs (DOT I._hash) (bytes bs) h = bytes_at sh bs (field_address t_hs (DOT I._hash) h).
Proof. intros L. unfold bytes_at. rewrite L, field_at_data_at. reflexivity. Qed.
Lemma prot4_cin_hs_ck sh h bs : Zlength bs = 32 ->
  field_at sh t_hs (DOT I._chaining_key) (bytes bs) h = bytes_at sh bs (field_address t_hs (DOT I._chaining_key) h).
Proof. intros L. unfold bytes_at. rewrite L, field_at_data_at. reflexivity. Qed.
Lemma prot4_cin_hs_ts sh h bs : Zlength bs = 12 ->
  field_at sh t_hs (DOT I._latest_timestamp) (bytes bs) h = bytes_at sh bs (field_address t_hs (DOT I._latest_timestamp) h).
Proof. intros L. unfold bytes_at. rewrite L, field_at_data_at. reflexivity. Qed.

Lemma prot4_cin_d_pub sh wg bs : Zlength bs = 32 ->
  field_at sh t_dev (DOT I._static_identity DOT I._static_public) (bytes bs) wg =
  bytes_at sh bs (field_address t_dev (DOT I._static_identity DOT I._static_public) wg).
Proof. intros L. unfold bytes_at. rewrite L, field_at_data_at. reflexivity. Qed.
Lemma prot4_cin_d_priv sh wg bs : Zlength bs = 32 ->
  field_at sh t_dev (DOT I._static_identity DOT I._static_private) (bytes bs) wg =
  bytes_at sh bs (field_address t_dev (DOT I._static_identity DOT I._static_private) wg).
Proof. intros L. unfold bytes_at. rewrite L, field_at_data_at. reflexivity. Qed.

(* byte buffers *)
Lemma prot4_cin_bytes32 sh bs p : Zlength bs = 32 -> bytes_at sh bs p = data_at sh (tarray tuchar 32) (map Vubyte bs) p.
Proof. intros L. unfold bytes_at, bytes. rewrite L. reflexivity. Qed.
Lemma prot4_cin_bytes12 sh bs p : Zlength bs = 12 -> bytes_at sh bs p = data_at sh (tarray tuchar 12) (map Vubyte bs) p.
Proof. intros L. unfold bytes_at, bytes. rewrite L. reflexivity. Qed.
Lemma prot4_cin_bytes32_ sh bs p : Zlength bs = 32 -> bytes_at sh bs p |-- data_at_ sh (tarray tuchar 32) p.
Proof. intros L. rewrite prot4_cin_bytes32 by auto. apply data_at_data_at_. Qed.
Lemma prot4_cin_bytes12_ sh bs p : Zlength bs = 12 -> bytes_at sh bs p |-- data_at_ sh (tarray tuchar 12) p.
Proof. intros L. rewrite prot4_cin_bytes12 by auto. apply data_at_data_at_. Qed.
Lemma prot4_cin_out32 sh p : out_bytes sh (Zrepeat Vundef 32) p = data_at_ sh (tarray tuchar 32) p.
Proof. reflexivity. Qed.
Lemma prot4_cin_out12 sh p : out_bytes sh (Zrepeat Vundef 12) p = data_at_ sh (tarray tuchar 12) p.
Proof. reflexivity. Qed.
Lemma prot4_cin_outb sh bs p : Zlength bs = 32 -> out_bytes sh (bytes bs) p = bytes_at sh bs p.
Proof. intros L. unfold out_bytes, bytes_at. replace (Zlength (bytes bs)) with (Zlength bs) by (unfold bytes; rewrite Zlength_map; auto). rewrite L. reflexivity. Qed.
Lemma prot4_cin_outb12 sh bs p : Zlength bs = 12 -> out_bytes sh (bytes bs) p = bytes_at sh bs p.
Proof. intros L. unfold out_bytes, bytes_at. replace (Zlength (bytes bs)) with (Zlength bs) by (unfold bytes; rewrite Zlength_map; auto). rewrite L. reflexivity. Qed.
Lemma prot4_cin_consts gv :
  spec.blake2s_globals gv * curve25519_globals gv * zero_page gv * cookie_globals gv |-- wg_consts gv.
Proof. unfold wg_consts. cancel. Qed.

Lemma prot4_cin_hash_len m : Zlength (HASH m) = 32.
Proof. unfold HASH, model.blake2s, model.b2s_digest_stream, model.b2s_out. rewrite Zlength_map. reflexivity. Qed.
Lemma prot4_cin_kdf1_len a b : Zlength (kdf1 a b) = 32.
Proof. unfold kdf1, hmac. cbv zeta. apply prot4_cin_hash_len. Qed.
Lemma prot4_cin_kdf2_len a b : Zlength (kdf2 a b) = 32.
Proof. unfold kdf2, hmac. cbv zeta. apply prot4_cin_hash_len. Qed.
Lemma prot4_cin_mix_hash_len a b : Zlength (mix_hash a b) = 32.
Proof. unfold mix_hash. apply prot4_cin_hash_len. Qed.
Lemma prot4_cin_init_ck_len : Zlength init_ck = 32.
Proof. unfold init_ck. apply prot4_cin_hash_len. Qed.
Lemma prot4_cin_init_hash_len : Zlength init_hash = 32.
Proof. unfold init_hash. apply prot4_cin_hash_len. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the model's exits                                                                               *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma prot4_cin_s1_dh ID M :
  dh_ok x25519 (id_priv ID) (im_eph M) = false -> consume_init_stage1 x25519 aead_dec ID M = None.
Proof. intros E. unfold consume_init_stage1. rewrite E. reflexivity. Qed.

Lemma prot4_cin_s1_dec ID M :
  dh_ok x25519 (id_priv ID) (im_eph M) = true ->
  aead_dec (kdf2 (kdf1 init_ck (im_eph M)) (x25519 (id_priv ID) (im_eph M))) 0
           (mix_hash (mix_hash init_hash (id_pub ID)) (im_eph M)) (im_encs M) = None ->
  consume_init_stage1 x25519 aead_dec ID M = None.
Proof. intros E1 E2. unfold consume_init_stage1. rewrite E1. cbv zeta. cbn [negb]. rewrite E2. reflexivity. Qed.

Lemma prot4_cin_s1_ok ID M s :
  dh_ok x25519 (id_priv ID) (im_eph M) = true ->
  aead_dec (kdf2 (kdf1 init_ck (im_eph M)) (x25519 (id_priv ID) (im_eph M))) 0
           (mix_hash (mix_hash init_hash (id_pub ID)) (im_eph M)) (im_encs M) = Some s ->
  consume_init_stage1 x25519 aead_dec ID M =
  Some (s, kdf2 (kdf1 init_ck (im_eph M)) (x25519 (id_priv ID) (im_eph M)),
        kdf1 (kdf1 init_ck (im_eph M)) (x25519 (id_priv ID) (im_eph M)),
        mix_hash (mix_hash (mix_hash init_hash (id_pub ID)) (im_eph M)) (im_encs M)).
Proof. intros E1 E2. unfold consume_init_stage1. rewrite E1. cbv zeta. cbn [negb]. rewrite E2. reflexivity. Qed.

Lemma prot4_cin_s2_ss ss c h M :
  memneq_bool ss zeros32 = false -> consume_init_stage2 aead_dec ss c h M = None.
Proof. intros E. unfold consume_init_stage2. rewrite E. reflexivity. Qed.

Lemma prot4_cin_s2_dec ss c h M :
  memneq_bool ss zeros32 = true -> aead_dec (kdf2 c ss) 0 h (im_enct M) = None ->
  consume_init_stage2 aead_dec ss c h M = None.
Proof. intros E1 E2. unfold consume_init_stage2. rewrite E1. cbv zeta. cbn [negb]. rewrite E2. reflexivity. Qed.

Lemma prot4_cin_s2_ok ss c h M t :
  memneq_bool ss zeros32 = true -> aead_dec (kdf2 c ss) 0 h (im_enct M) = Some t ->
  consume_init_stage2 aead_dec ss c h M = Some (t, kdf1 c ss, mix_hash h (im_enct M)).
Proof. intros E1 E2. unfold consume_init_stage2. rewrite E1. cbv zeta. cbn [negb]. rewrite E2. reflexivity. Qed.

Lemma prot4_cin_m0 ID PS M now :
  id_has ID = false -> consume_initiation_model x25519 aead_dec ID PS M now = None.
Proof. intros E. unfold consume_initiation_model. rewrite E. reflexivity. Qed.

Lemma prot4_cin_m1 ID PS M now :
  consume_init_stage1 x25519 aead_dec ID M = None -> consume_initiation_model x25519 aead_dec ID PS M now = None.
Proof. intros E. unfold consume_initiation_model. rewrite E. destruct (id_has ID); reflexivity. Qed.

Lemma prot4_cin_m2 ID PS M now s k c h :
  consume_init_stage1 x25519 aead_dec ID M = Some (s, k, c, h) -> pk_find PS s = None ->
  consume_initiation_model x25519 aead_dec ID PS M now = None.
Proof. intros E1 E2. unfold consume_initiation_model. rewrite E1, E2. destruct (id_has ID); reflexivity. Qed.

Lemma prot4_cin_m3 ID PS M now s k c h a P :
  consume_init_stage1 x25519 aead_dec ID M = Some (s, k, c, h) -> pk_find PS s = Some (a, P) ->
  Int.eq (p_refs P) Int.zero = true ->
  consume_initiation_model x25519 aead_dec ID PS M now = None.
Proof.
  intros E1 E2 E3. unfold consume_initiation_model. rewrite E1, E2. unfold peer_get. rewrite E3.
  destruct (id_has ID); reflexivity.
Qed.

Lemma prot4_cin_m4 ID PS M now s k c h a P :
  consume_init_stage1 x25519 aead_dec ID M = Some (s, k, c, h) -> pk_find PS s = Some (a, P) ->
  consume_init_stage2 aead_dec (hs_ss (p_hs P)) c h M = None ->
  consume_initiation_model x25519 aead_dec ID PS M now = None.
Proof.
  intros E1 E2 E3. unfold consume_initiation_model. rewrite E1, E2. unfold peer_get.
  destruct (Int.eq (p_refs P) Int.zero); [destruct (id_has ID); reflexivity|]. cbv zeta.
  cbn [p_hs p_set_refs]. rewrite E3. destruct (id_has ID); reflexivity.
Qed.

Lemma prot4_cin_m5 ID PS M now s k c h a P t c2 h2 :
  consume_init_stage1 x25519 aead_dec ID M = Some (s, k, c, h) -> pk_find PS s = Some (a, P) ->
  consume_init_stage2 aead_dec (hs_ss (p_hs P)) c h M = Some (t, c2, h2) ->
  orb (Z.leb (memcmp_Z t (hs_ts (p_hs P))) 0)
      (negb (s64_le (Int64.add (hs_lic (p_hs P)) (Int64.repr 20000000)) now)) = true ->
  consume_initiation_model x25519 aead_dec ID PS M now = None.
Proof.
  intros E1 E2 E3 E4. unfold consume_initiation_model. rewrite E1, E2. unfold peer_get.
  destruct (Int.eq (p_refs P) Int.zero); [destruct (id_has ID); reflexivity|]. cbv zeta.
  cbn [p_hs p_set_refs]. rewrite E3, E4. destruct (id_has ID); reflexivity.
Qed.

Lemma prot4_cin_m6 ID PS M now s k c h a P t c2 h2 :
  id_has ID = true ->
  consume_init_stage1 x25519 aead_dec ID M = Some (s, k, c, h) -> pk_find PS s = Some (a, P) ->
  Int.eq (p_refs P) Int.zero = false ->
  consume_init_stage2 aead_dec (hs_ss (p_hs P)) c h M = Some (t, c2, h2) ->
  orb (Z.leb (memcmp_Z t (hs_ts (p_hs P))) 0)
      (negb (s64_le (Int64.add (hs_lic (p_hs P)) (Int64.repr 20000000)) now)) = false ->
  consume_initiation_model x25519 aead_dec ID PS M now =
  Some (a, p_set_hs (p_set_refs P (rc_add1 (p_refs P)))
         (mkHS HS_CONSUMED_INITIATION
               (if Int64.lt (Int64.sub (hs_lic (p_hs P)) now) Int64.zero then now else hs_lic (p_hs P))
               (hs_sid (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P)) (im_eph M) (hs_ss (p_hs P))
               (hs_psk (p_hs P)) h2 c2 t (im_sender M))).
Proof.
  intros E0 E1 E2 E3 E4 E5. unfold consume_initiation_model. rewrite E0, E1, E2. unfold peer_get.
  rewrite E3. cbv zeta. cbn [p_hs p_set_refs negb]. rewrite E4, E5. reflexivity.
Qed.

(* the state at the end of the do-while block: the result res, the local `peer` pv *)
Definition prot4_cin_brk (PS: list (val * share * peer)) (res: option (val * peer)) (pv: val) : mpred :=
  match res with
  | Some (a, P') => !! (pv = a /\ exists sh P, sfind PS a = Some (sh, P) /\ writable_share sh) &&
                    peers_rep (supd PS a P')
  | None => if eq_dec pv nullval then peers_rep PS
            else EX sh: share, EX P: peer,
                 !! (sfind PS pv = Some (sh, P) /\ p_refs P <> Int.zero /\ writable_share sh) &&
                 peers_rep (supd PS pv (p_set_refs P (rc_add1 (p_refs P))))
  end.

Lemma prot4_cin_dev_valid sh a d : readable_share sh -> field_at sh t_peer (DOT I._device) d a |-- valid_pointer a.
Proof. intros R. apply field_at_valid_ptr0; [apply readable_nonidentity; auto | simpl; lia | reflexivity]. Qed.

Ltac prot4_cin_vp VP :=
  match goal with
  | |- ?A * ?B |-- valid_pointer _ =>
      first [apply sepcon_valid_pointer2; prot4_cin_vp VP | apply sepcon_valid_pointer1; prot4_cin_vp VP]
  | _ => apply VP
  end.

Lemma prot4_cin_sub_add r : Int.sub (Int.add r Int.one) Int.one = r.
Proof. rewrite Int.sub_add_opp, Int.add_assoc, Int.add_neg_zero, Int.add_zero. reflexivity. Qed.

(* the peers' counts are below INT_MAX (peers_refs_ok, L03) *)
Lemma prot4_cin_refs_bnd PS a sh P :
  peers_refs_ok PS -> sfind PS a = Some (sh, P) -> 0 < Int.unsigned (p_refs P) < 2147483647.
Proof.
  intros HR Hf. apply prot3_shim_table1_sfind_In in Hf. unfold peers_refs_ok in HR.
  rewrite Forall_forall in HR. exact (HR _ Hf).
Qed.

(* the put of the lookup's reference does not warn *)
Lemma prot4_cin_dec_add1 (r: int) (w: list int64) :
  0 < Int.unsigned r < 2147483647 -> rc_dec_warn (rc_add1 r) w = w.
Proof.
  intros H. rewrite rc_add1_small by lia. apply rc_dec_warn_small.
  unfold Int.add. rewrite Int.unsigned_one, Int.unsigned_repr; rep_lia.
Qed.

Lemma prot4_cin_refs_eta P : p_set_refs (p_set_refs P (rc_add1 (p_refs P))) (p_refs P) = P.
Proof. destruct P; reflexivity. Qed.

Definition prot4_cin_eqk {A: Type} (a b: A) : Prop := a = b.

Ltac prot4_cin_fold :=
  rewrite prot4_cin_dev_eq, prot4_cin_init_eq;
  match goal with
  | Lpub: Zlength (id_pub ?ID) = 32, Lpriv: Zlength (id_priv ?ID) = 32, Leph: Zlength (im_eph ?M) = 32,
    Lencs: Zlength (im_encs ?M) = 48, Lenct: Zlength (im_enct ?M) = 28, Hid: id_has ?ID = true |- _ =>
    rewrite Hid, (prot4_cin_d_pub _ _ _ Lpub), (prot4_cin_d_priv _ _ _ Lpriv), (prot4_cin_m_eph _ _ _ Leph),
      (prot4_cin_m_encs _ _ _ Lencs), (prot4_cin_m_enct _ _ _ Lenct)
  end.

Lemma prot4_cin_bytes_any sh X v : bytes_at sh X v |-- data_at_ sh (tarray tuchar (Zlength X)) v.
Proof. unfold bytes_at. apply data_at_data_at_. Qed.

Ltac prot4_cin_to_ :=
  repeat match goal with |- context [bytes_at Tsh ?X ?v] => sep_apply (prot4_cin_bytes_any Tsh X v) end.

Ltac prot4_cin_len :=
  rewrite ?prot4_cin_kdf1_len, ?prot4_cin_kdf2_len, ?prot4_cin_mix_hash_len;
  repeat match goal with H: Zlength ?X = _ |- context [Zlength ?X] => rewrite H end.

Ltac prot4_cin_hide t x ex lx lem :=
  remember t as x eqn:ex;
  assert (lx: Zlength x = 32) by (rewrite ex; apply lem);
  change (prot4_cin_eqk x t) in ex.

Ltac prot4_cin_arg :=
  apply prop_right; simpl; rewrite ?field_address_offset by auto with field_compatible; simpl;
  rewrite ?offset_offset_val;
  repeat match goal with H: Zlength _ = _ |- context [Zlength _] => rewrite H end; reflexivity.

Lemma prot4_cin_hs_fold sh h H :
  hs_ok H ->
  prot4_cin_hrest sh h (hs_sid H) (hs_eph H) (hs_rstatic H) (hs_psk H) *
  field_at sh t_hs (DOT I._state) (Vint (hs_state H)) h *
  field_at sh t_hs (DOT I._last_initiation_consumption) (Vlong (hs_lic H)) h *
  field_at sh t_hs (DOT I._remote_ephemeral) (bytes (hs_reph H)) h *
  field_at sh t_hs (DOT I._precomputed_static_static) (bytes (hs_ss H)) h *
  field_at sh t_hs (DOT I._hash) (bytes (hs_hash H)) h *
  field_at sh t_hs (DOT I._chaining_key) (bytes (hs_ck H)) h *
  field_at sh t_hs (DOT I._latest_timestamp) (bytes (hs_ts H)) h *
  field_at sh t_hs (DOT I._remote_index) (Vint (hs_rindex H)) h |-- hs_rep sh h H.
Proof. intros Hok. rewrite prot4_cin_hs_eq. entailer!. Qed.

Lemma prot4_cin_brk_ne PS a sh P :
  a <> nullval -> sfind PS a = Some (sh, P) -> p_refs P <> Int.zero -> writable_share sh ->
  field_compatible t_peer [] a ->
  field_at sh t_peer (DOT I._device) (p_device P) a * peer_refs_rep sh a (rc_add1 (p_refs P)) *
  prot4_cin_prest sh a P * hs_rep sh (hs_addr a) (p_hs P) * peers_rep (sdel PS a)
  |-- prot4_cin_brk PS None a.
Proof.
  intros N Hf Hr W FC. unfold prot4_cin_brk. destruct (eq_dec a nullval); [contradiction|].
  Exists sh P. rewrite (prot4_cin_open PS a sh P Hf), prot4_cin_peer_eq.
  cbn [p_device p_refs p_hs p_set_refs]. rewrite prot4_cin_prest_set_refs. entailer!.
Qed.

Lemma prot4_cin_brk_some PS a sh P r H :
  sfind PS a = Some (sh, P) -> writable_share sh -> field_compatible t_peer [] a ->
  field_at sh t_peer (DOT I._device) (p_device P) a * peer_refs_rep sh a r *
  prot4_cin_prest sh a P * hs_rep sh (hs_addr a) H * peers_rep (sdel PS a)
  |-- prot4_cin_brk PS (Some (a, p_set_hs (p_set_refs P r) H)) a.
Proof.
  intros Hf W FC. unfold prot4_cin_brk.
  rewrite (prot4_cin_open PS a sh P Hf), prot4_cin_peer_eq.
  cbn [p_device p_refs p_hs p_set_refs p_set_hs]. rewrite prot4_cin_prest_set_hs, prot4_cin_prest_set_refs.
  entailer!. eauto.
Qed.

Ltac prot4_cin_absurd :=
  exfalso; first [congruence | apply Int.one_not_zero; assumption | apply Int.one_not_zero; symmetry; assumption
                 | discriminate | contradiction].

Ltac prot4_cin_repl R old new :=
  match R with
  | old :: ?R' => constr:(new :: R')
  | ?x :: ?R' => let R2 := prot4_cin_repl R' old new in constr:(x :: R2)
  end.

Lemma prot4_cin_hs_fold_succ sh h H eph' lic' h2 ck2 t sidx :
  hs_ok H -> Zlength eph' = 32 -> Zlength h2 = 32 -> Zlength ck2 = 32 -> Zlength t = 12 ->
  prot4_cin_hrest sh h (hs_sid H) (hs_eph H) (hs_rstatic H) (hs_psk H) *
  field_at sh t_hs (DOT I._state) (Vint (Int.repr 2)) h *
  field_at sh t_hs (DOT I._last_initiation_consumption) (Vlong lic') h *
  data_at sh (tarray tuchar 32) (map Vubyte eph') (field_address t_hs (DOT I._remote_ephemeral) h) *
  bytes_at sh (hs_ss H) (field_address t_hs (DOT I._precomputed_static_static) h) *
  data_at sh (tarray tuchar 32) (map Vubyte h2) (field_address t_hs (DOT I._hash) h) *
  data_at sh (tarray tuchar 32) (map Vubyte ck2) (field_address t_hs (DOT I._chaining_key) h) *
  data_at sh (tarray tuchar 12) (map Vubyte t) (field_address t_hs (DOT I._latest_timestamp) h) *
  field_at sh t_hs (DOT I._remote_index) (Vint sidx) h
  |-- hs_rep sh h (mkHS HS_CONSUMED_INITIATION lic' (hs_sid H) (hs_eph H) (hs_rstatic H) eph' (hs_ss H)
                        (hs_psk H) h2 ck2 t sidx).
Proof.
  intros (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8) E1 E2 E3 E4.
  rewrite prot4_cin_hs_eq. cbn [hs_state hs_lic hs_sid hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts hs_rindex].
  rewrite (prot4_cin_hs_reph sh h eph' E1), (prot4_cin_hs_ss sh h _ L4), (prot4_cin_hs_hash sh h h2 E2),
    (prot4_cin_hs_ck sh h ck2 E3), (prot4_cin_hs_ts sh h t E4).
  rewrite <- (prot4_cin_bytes32 sh eph' _ E1), <- (prot4_cin_bytes32 sh h2 _ E2), <- (prot4_cin_bytes32 sh ck2 _ E3),
    <- (prot4_cin_bytes12 sh t _ E4).
  entailer!. unfold hs_ok; cbn [hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts]. repeat split; auto.
Qed.

Lemma prot4_cin_memcmp_range a b : -255 <= memcmp_Z a b <= 255.
Proof.
  revert b; induction a as [|x a IH]; intros [|y b]; simpl; try lia.
  destruct (Byte.eq_dec x y); [apply IH|].
  pose proof (Byte.unsigned_range x). pose proof (Byte.unsigned_range y).
  unfold Byte.modulus, Byte.wordsize, Wordsize_8.wordsize in *. change (two_power_nat 8) with 256 in *. lia.
Qed.

Lemma prot4_cin_rf tv ts lic now :
  orb (negb (Int.lt (Int.repr 0) (Int.repr (memcmp_Z tv ts))))
      (Int64.cmp Cgt (Int64.add lic (Int64.divs (Int64.repr 1000000000) (Int64.repr (Int.signed (Int.repr 50)))))
                 now) =
  orb (Z.leb (memcmp_Z tv ts) 0) (negb (s64_le (Int64.add lic (Int64.repr 20000000)) now)).
Proof.
  f_equal.
  - pose proof (prot4_cin_memcmp_range tv ts).
    unfold Int.lt. rewrite Int.signed_repr by rep_lia. rewrite Int.signed_repr by rep_lia.
    destruct (zlt 0 (memcmp_Z tv ts)); simpl.
    + symmetry. apply Z.leb_gt. lia.
    + symmetry. apply Z.leb_le. lia.
  - unfold s64_le. rewrite negb_involutive. reflexivity.
Qed.

Lemma prot4_cons_init_body :
  @semax_body (QPvarspecs Noise.qp) prot4_Gci Noise.CS
    WgNoise.noise.code.f_wg_noise_handshake_consume_initiation (wg_noise_handshake_consume_initiation_spec x25519 aead_dec).
Proof.
  start_function.
  match goal with Hx: peers_refs_ok PS |- _ => rename Hx into Hrefs end.
  forward. forward.
  forward_loop
    (PROP () LOCAL (temp N._ret_peer nullval; temp N._peer nullval;
       lvar N._t (tarray tuchar 12) v_t; lvar N._e (tarray tuchar 32) v_e; lvar N._s (tarray tuchar 32) v_s;
       lvar N._hash (tarray tuchar 32) v_hash; lvar N._chaining_key (tarray tuchar 32) v_chaining_key;
       lvar N._key (tarray tuchar 32) v_key; gvars gv; temp N._src m; temp N._wg wg)
     SEP (data_at_ Tsh (tarray tuchar 12) v_t; data_at_ Tsh (tarray tuchar 32) v_e;
       data_at_ Tsh (tarray tuchar 32) v_s; data_at_ Tsh (tarray tuchar 32) v_hash;
       data_at_ Tsh (tarray tuchar 32) v_chaining_key; data_at_ Tsh (tarray tuchar 32) v_key;
       init_rep shm m M; device_rep shd wg D; ptable shpt (d_ptab D) head; peers_rep PS;
       shim_state4 gv S w; noise_globals gv kc; wg_consts gv))
  continue: (EX pv: val,
    PROP () LOCAL (temp N._ret_peer (peer_result (cin_res x25519 aead_dec D PS M S)); temp N._peer pv;
       lvar N._t (tarray tuchar 12) v_t; lvar N._e (tarray tuchar 32) v_e; lvar N._s (tarray tuchar 32) v_s;
       lvar N._hash (tarray tuchar 32) v_hash; lvar N._chaining_key (tarray tuchar 32) v_chaining_key;
       lvar N._key (tarray tuchar 32) v_key; gvars gv; temp N._src m; temp N._wg wg)
     SEP (data_at_ Tsh (tarray tuchar 12) v_t; data_at_ Tsh (tarray tuchar 32) v_e;
       data_at_ Tsh (tarray tuchar 32) v_s; data_at_ Tsh (tarray tuchar 32) v_hash;
       data_at_ Tsh (tarray tuchar 32) v_chaining_key; data_at_ Tsh (tarray tuchar 32) v_key;
       init_rep shm m M; device_rep shd wg D; ptable shpt (d_ptab D) head;
       prot4_cin_brk PS (cin_res x25519 aead_dec D PS M S) pv;
       shim_state4 gv S w; noise_globals gv kc; wg_consts gv))%assert
  break: (EX pv: val,
    PROP () LOCAL (temp N._ret_peer (peer_result (cin_res x25519 aead_dec D PS M S)); temp N._peer pv;
       lvar N._t (tarray tuchar 12) v_t; lvar N._e (tarray tuchar 32) v_e; lvar N._s (tarray tuchar 32) v_s;
       lvar N._hash (tarray tuchar 32) v_hash; lvar N._chaining_key (tarray tuchar 32) v_chaining_key;
       lvar N._key (tarray tuchar 32) v_key; gvars gv; temp N._src m; temp N._wg wg)
     SEP (data_at_ Tsh (tarray tuchar 12) v_t; data_at_ Tsh (tarray tuchar 32) v_e;
       data_at_ Tsh (tarray tuchar 32) v_s; data_at_ Tsh (tarray tuchar 32) v_hash;
       data_at_ Tsh (tarray tuchar 32) v_chaining_key; data_at_ Tsh (tarray tuchar 32) v_key;
       init_rep shm m M; device_rep shd wg D; ptable shpt (d_ptab D) head;
       prot4_cin_brk PS (cin_res x25519 aead_dec D PS M S) pv;
       shim_state4 gv S w; noise_globals gv kc; wg_consts gv))%assert.
  { entailer!. }
  2: { Intros pv. forward. Exists pv. entailer!. }
  2: { Intros pv.
       forward_call (Tsh, v_key, 32).
       forward_call (Tsh, v_hash, 32).
       forward_call (Tsh, v_chaining_key, 32).
       destruct (cin_res x25519 aead_dec D PS M S) as [[a P']|] eqn:Hres.
       { unfold prot4_cin_brk. Intros. subst pv. destruct H3 as (sh & P0 & Hf & W).
         rewrite (prot4_cin_open PS a sh P0 Hf P'). cbn [peer_result].
         assert (VP := prot4_cin_valid sh a P' (writable_readable_share W)).
         forward_if True.
         { subst a. rewrite prot4_cin_peer_eq. Intros. destruct H2 as [Hp _]. inv Hp. }
         { forward. entailer!. }
         forward. unfold peers_after. rewrite (prot4_cin_open PS a sh P0 Hf P'). cancel. }
       unfold prot4_cin_brk. cbn [peer_result]. destruct (eq_dec pv nullval) as [->|Hn].
       { forward_if True.
         { forward_call (gv, S, w, Tsh, nullval, Int.zero, nullval).
           { destruct (eq_dec nullval nullval); [|congruence]. cancel. }
           destruct (eq_dec nullval nullval); [|congruence]. entailer!. }
         { congruence. }
         forward. unfold peers_after. cancel. }
       Intros sh P. rename H2 into Hf, H3 into Hr, H4 into W.
       rewrite (prot4_cin_open PS pv sh P Hf), prot4_cin_peer_eq; Intros.
       cbn [p_refs p_device p_hs p_set_refs]; rewrite prot4_cin_prest_set_refs.
       match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx _))) _ _ => forward_if (PROPx [] (LOCALx L (SEPx [
            data_at Tsh (tarray tuchar 32) (Zrepeat (Vubyte Byte.zero) 32) v_chaining_key;
            data_at Tsh (tarray tuchar 32) (Zrepeat (Vubyte Byte.zero) 32) v_hash;
            data_at Tsh (tarray tuchar 32) (Zrepeat (Vubyte Byte.zero) 32) v_key;
            data_at_ Tsh (tarray tuchar 12) v_t; data_at_ Tsh (tarray tuchar 32) v_e;
            data_at_ Tsh (tarray tuchar 32) v_s; init_rep shm m M; device_rep shd wg D; ptable shpt (d_ptab D) head;
            field_at sh t_peer (DOT I._device) (p_device P) pv; peer_refs_rep sh pv (p_refs P);
            prot4_cin_prest sh pv P; hs_rep sh (hs_addr pv) (p_hs P); peers_rep (sdel PS pv);
            shim_state4 gv S w; noise_globals gv kc; wg_consts gv]))) end.
       { forward_call (gv, S, w, sh, pv, rc_add1 (p_refs P), p_device P).
         { destruct (eq_dec pv nullval); [contradiction|]. cancel. }
         destruct (eq_dec pv nullval); [contradiction|].
         rewrite (prot4_cin_dec_add1 _ w (prot4_cin_refs_bnd PS pv sh P Hrefs Hf)).
         rewrite (rc_sub1_add1 _ (prot4_cin_refs_bnd PS pv sh P Hrefs Hf)). rewrite (Int.eq_false _ _ Hr).
         entailer!. }
       { congruence. }
       forward. unfold peers_after. rewrite (prot4_cin_open0 PS pv sh P Hf), (prot4_cin_peer_eq sh pv P).
       entailer!. }
  rewrite prot4_cin_dev_eq. Intros. rename H2 into FCd, H3 into IDok.
  assert_PROP (NoDup (saddrs PS)) as ND. { sep_apply (prot4_cin_nodup PS H). entailer!. }
  forward.
  { entailer!. destruct (id_has (d_id D)); simpl; auto. }
  forward_if.
  { destruct (id_has (d_id D)) eqn:Hid; [inv H2|].
    forward. Exists nullval. unfold cin_res. rewrite (prot4_cin_m0 _ PS M (s_boot S) Hid).
    unfold prot4_cin_brk. cbn [peer_result]. destruct (eq_dec nullval nullval) as [_|NN]; [|congruence].
    rewrite prot4_cin_dev_eq, Hid. entailer!. }
  destruct (id_has (d_id D)) eqn:Hid; [|inv H2]. clear H2.
  destruct IDok as [Lpub Lpriv].
  rewrite (prot4_cin_d_pub shd wg _ Lpub), (prot4_cin_d_priv shd wg _ Lpriv).
  set (pubp := field_address t_dev (DOT I._static_identity DOT I._static_public) wg).
  set (privp := field_address t_dev (DOT I._static_identity DOT I._static_private) wg).
  forward_call (gv, kc, Tsh, v_chaining_key, Tsh, v_hash, shd, pubp, id_pub (d_id D)).
  { unfold pubp. prot4_cin_arg. }
  assert (LICK: Zlength init_ck = 32) by apply prot4_cin_init_ck_len.
  remember init_ck as ICK eqn:EICK. remember init_hash as IH eqn:EIH.
  change (prot4_cin_eqk ICK init_ck) in EICK. change (prot4_cin_eqk IH init_hash) in EIH.
  assert_PROP (@field_compatible Noise.CS t_init [] m) as FCm. { unfold init_rep. Intros. entailer!. }
  rewrite prot4_cin_init_eq. Intros. rename H2 into IMok.
  destruct IMok as (Leph & Lencs & Lenct & Lmac1 & Lmac2).
  rewrite (prot4_cin_m_eph shm m _ Leph), (prot4_cin_m_encs shm m _ Lencs), (prot4_cin_m_enct shm m _ Lenct).
  set (ephp := field_address t_init (DOT N._unencrypted_ephemeral) m).
  set (encsp := field_address t_init (DOT N._encrypted_static) m).
  set (enctp := field_address t_init (DOT N._encrypted_timestamp) m).
  forward_call (gv, false, Tsh, v_e, shm, ephp, im_eph M, Tsh, v_chaining_key, ICK, Tsh, v_hash,
                mix_hash IH (id_pub (d_id D))).
  { unfold ephp. prot4_cin_arg. }
  { simpl. cancel. }
  prot4_cin_hide (kdf1 ICK (im_eph M)) CK0 ECK0 LCK0 prot4_cin_kdf1_len.
  prot4_cin_hide (mix_hash (mix_hash IH (id_pub (d_id D))) (im_eph M)) HS0 EHS0 LHS0 prot4_cin_mix_hash_len.
  assert_PROP (isptr v_key) as Pk by entailer!.
  assert (NK: v_key <> nullval) by (intro E; subst; inv Pk).
  forward_call (gv, Tsh, v_chaining_key, CK0, Tsh, v_key, shd, privp, id_priv (d_id D),
                Tsh, v_e, im_eph M).
  { unfold privp. prot4_cin_arg. }
  { destruct (eq_dec v_key nullval); [contradiction|]. cancel. }
  destruct (eq_dec v_key nullval) as [E|_]; [contradiction|].
  destruct (dh_ok x25519 (id_priv (d_id D)) (im_eph M)) eqn:Hdh.
  2: { forward_if.
       2: { exfalso. congruence. }
       forward. Exists nullval.
       unfold cin_res. rewrite (prot4_cin_m1 _ PS M (s_boot S) (prot4_cin_s1_dh _ _ Hdh)).
       unfold prot4_cin_brk; cbn [peer_result]. destruct (eq_dec nullval nullval) as [_|NN]; [|congruence].
       prot4_cin_fold. cbv iota. prot4_cin_to_. prot4_cin_len.
       subst pubp privp ephp encsp enctp.
       entailer!. unfold im_ok, id_ok; repeat split; auto. }
  forward_if.
  { exfalso. apply Int.one_not_zero. assumption. }
  cbv iota.
  prot4_cin_hide (kdf1 CK0 (x25519 (id_priv (d_id D)) (im_eph M))) CK1 ECK1 LCK1 prot4_cin_kdf1_len.
  prot4_cin_hide (kdf2 CK0 (x25519 (id_priv (d_id D)) (im_eph M))) K1 EK1 LK1 prot4_cin_kdf2_len.
  rewrite <- (prot4_cin_out32 Tsh v_s).
  forward_call (gv, Tsh, v_s, Zrepeat Vundef 32, shm, encsp, im_encs M, Tsh, v_key, K1, Tsh, v_hash, HS0).
  { unfold encsp. prot4_cin_arg. }
  { rewrite Lencs. reflexivity. }
  destruct (aead_dec K1 0 HS0 (im_encs M)) as [sv|] eqn:Hd.
  2: { forward_if.
       2: { exfalso. congruence. }
       assert (Hs1: consume_init_stage1 x25519 aead_dec (d_id D) M = None).
       { apply prot4_cin_s1_dec; [exact Hdh|]. unfold prot4_cin_eqk in *. subst K1 HS0 CK0 ICK IH. exact Hd. }
       forward. Exists nullval.
       unfold cin_res. rewrite (prot4_cin_m1 _ PS M (s_boot S) Hs1).
       unfold prot4_cin_brk; cbn [peer_result]. destruct (eq_dec nullval nullval) as [_|NN]; [|congruence].
       prot4_cin_fold. rewrite prot4_cin_out32. prot4_cin_to_. prot4_cin_len.
       subst pubp privp ephp encsp enctp.
       entailer!. unfold im_ok, id_ok; repeat split; auto. }
  forward_if.
  { exfalso. apply Int.one_not_zero. assumption. }
  assert (Ls: Zlength sv = 32) by (apply (aead_dec_length _ _ HA) in Hd; rewrite Lencs in Hd; lia).
  rewrite (prot4_cin_outb Tsh sv v_s Ls).
  prot4_cin_hide (mix_hash HS0 (im_encs M)) HS1 EHS1 LHS1 prot4_cin_mix_hash_len.
  assert (Hs1: consume_init_stage1 x25519 aead_dec (d_id D) M = Some (sv, K1, CK1, HS1)).
  { unfold prot4_cin_eqk in *. subst HS1 K1 CK1 HS0 CK0 ICK IH. apply prot4_cin_s1_ok; auto. }
  forward.
  { unfold ptable. entailer!. }
  forward_call (gv, S, w, shpt, d_ptab D, head, PS, Tsh, v_s, sv).
  forward.
  unfold pk_lookup.
  destruct (pk_find PS sv) as [[a P]|] eqn:Hpk.
  2: { cbn [fst snd]. forward_if.
       2: { exfalso. congruence. }
       forward. Exists nullval.
       unfold cin_res. rewrite (prot4_cin_m2 _ PS M (s_boot S) _ _ _ _ Hs1 Hpk).
       unfold prot4_cin_brk; cbn [peer_result]. destruct (eq_dec nullval nullval) as [_|NN]; [|congruence].
       prot4_cin_fold. prot4_cin_to_. prot4_cin_len.
       subst pubp privp ephp encsp enctp.
       entailer!. unfold im_ok, id_ok; repeat split; auto. }
  unfold peer_get. destruct (Int.eq (p_refs P) Int.zero) eqn:Hr; cbn [fst snd].
  { forward_if.
    2: { exfalso. congruence. }
    forward. Exists nullval.
    unfold cin_res. rewrite (prot4_cin_m3 _ PS M (s_boot S) _ _ _ _ _ _ Hs1 Hpk Hr).
    unfold prot4_cin_brk; cbn [peer_result]. destruct (eq_dec nullval nullval) as [_|NN]; [|congruence].
    prot4_cin_fold. prot4_cin_to_. prot4_cin_len.
    subst pubp privp ephp encsp enctp.
    entailer!. unfold im_ok, id_ok; repeat split; auto. }
  assert (Hr': p_refs P <> Int.zero) by (intro E; rewrite E, Int.eq_true in Hr; discriminate).
  destruct (prot4_cin_pk_find_sfind PS sv a P ND Hpk) as [sh Hf].
  assert (W: writable_share sh) by (eapply prot3_shim_table1_sfind_wr; [unfold peers_wf in H; exact H | exact Hf]).
  assert (Hlic: Int64.signed (hs_lic (p_hs P)) <= Int64.max_signed - 20000000).
  { apply prot3_shim_table1_sfind_In in Hf. rewrite Forall_forall in H1. exact (H1 _ Hf). }
  rewrite (prot4_cin_open PS a sh P Hf), prot4_cin_peer_eq. Intros.
  match goal with Hx: field_compatible t_peer [] a |- _ => rename Hx into FCp end.
  cbn [p_device p_refs p_hs p_set_refs]. rewrite prot4_cin_prest_set_refs.
  assert (VP := prot4_cin_dev_valid sh a (p_device P) (writable_readable_share W)).
  forward_if.
  { subst a. destruct FCp as [Hp _]. inv Hp. }
  forward.
  match goal with |- context [temp noise.code._handshake (offset_val ?o a)] =>
    change (offset_val o a) with (hs_addr a) end.
  rewrite prot4_cin_hs_eq. Intros.
  match goal with Hx: hs_ok (p_hs P) |- _ => rename Hx into Hhok end.
  pose proof Hhok as (Lheph & Lhrs & Lhreph & Lhss & Lhpsk & Lhhash & Lhck & Lhts).
  assert_PROP (field_compatible t_hs (DOT I._state) (hs_addr a)) as FCh0 by entailer!.
  assert (FCh: field_compatible t_hs [] (hs_addr a)).
  { apply field_compatible_cons in FCh0. destruct FCh0; auto. }
  rewrite (prot4_cin_hs_ss sh (hs_addr a) _ Lhss).
  set (ssp := field_address t_hs (DOT I._precomputed_static_static) (hs_addr a)).
  sep_apply (prot4_cin_bytes32_ Tsh K1 v_key LK1).
  forward_call (gv, kc, Tsh, v_chaining_key, CK1, Tsh, v_key, sh, ssp, hs_ss (p_hs P)).
  { unfold ssp. prot4_cin_arg. }
  destruct (memneq_bool (hs_ss (p_hs P)) zeros32) eqn:Hss.
  2: { forward_if.
       2: { exfalso. congruence. }
       subst ssp. rewrite <- (prot4_cin_hs_ss sh (hs_addr a) _ Lhss).
       sep_apply (prot4_cin_hs_fold sh (hs_addr a) (p_hs P) Hhok).
       sep_apply (prot4_cin_brk_ne PS a sh P H4 Hf Hr' W FCp).
       forward. Exists a.
       unfold cin_res. rewrite (prot4_cin_m4 _ PS M (s_boot S) _ _ _ _ _ _ Hs1 Hpk (prot4_cin_s2_ss _ _ _ _ Hss)).
       cbn [peer_result].
       prot4_cin_fold. prot4_cin_to_. prot4_cin_len.
       subst pubp privp ephp encsp enctp.
       entailer!. unfold im_ok, id_ok; repeat split; auto. }
  forward_if.
  { exfalso. apply Int.one_not_zero. assumption. }
  cbv iota.
  prot4_cin_hide (kdf1 CK1 (hs_ss (p_hs P))) CK2 ECK2 LCK2 prot4_cin_kdf1_len.
  prot4_cin_hide (kdf2 CK1 (hs_ss (p_hs P))) K2 EK2 LK2 prot4_cin_kdf2_len.
  rewrite <- (prot4_cin_out12 Tsh v_t).
  forward_call (gv, Tsh, v_t, Zrepeat Vundef 12, shm, enctp, im_enct M, Tsh, v_key, K2, Tsh, v_hash, HS1).
  { unfold enctp. prot4_cin_arg. }
  { rewrite Lenct. reflexivity. }
  destruct (aead_dec K2 0 HS1 (im_enct M)) as [tv|] eqn:Ht.
  2: { forward_if.
       2: { exfalso. congruence. }
       assert (Hs2: consume_init_stage2 aead_dec (hs_ss (p_hs P)) CK1 HS1 M = None).
       { apply prot4_cin_s2_dec; auto. unfold prot4_cin_eqk in EK2. subst K2. exact Ht. }
       subst ssp. rewrite <- (prot4_cin_hs_ss sh (hs_addr a) _ Lhss).
       sep_apply (prot4_cin_hs_fold sh (hs_addr a) (p_hs P) Hhok).
       sep_apply (prot4_cin_brk_ne PS a sh P H4 Hf Hr' W FCp).
       forward. Exists a.
       unfold cin_res. rewrite (prot4_cin_m4 _ PS M (s_boot S) _ _ _ _ _ _ Hs1 Hpk Hs2).
       cbn [peer_result].
       prot4_cin_fold. rewrite prot4_cin_out12. prot4_cin_to_. prot4_cin_len.
       subst pubp privp ephp encsp enctp.
       entailer!. unfold im_ok, id_ok; repeat split; auto. }
  assert (Lt: Zlength tv = 12) by (apply (aead_dec_length _ _ HA) in Ht; rewrite Lenct in Ht; lia).
  rewrite (prot4_cin_outb12 Tsh tv v_t Lt).
  prot4_cin_hide (mix_hash HS1 (im_enct M)) HS2 EHS2 LHS2 prot4_cin_mix_hash_len.
  assert (Hs2: consume_init_stage2 aead_dec (hs_ss (p_hs P)) CK1 HS1 M = Some (tv, CK2, HS2)).
  { unfold prot4_cin_eqk in *. subst CK2 K2 HS2. apply prot4_cin_s2_ok; auto. }
  forward_if.
  { exfalso. apply Int.one_not_zero. assumption. }
  rewrite (prot4_cin_hs_ts sh (hs_addr a) _ Lhts).
  set (tsp := field_address t_hs (DOT I._latest_timestamp) (hs_addr a)).
  rewrite (prot4_cin_bytes12 Tsh tv v_t Lt), (prot4_cin_bytes12 sh _ tsp Lhts).
  forward_call (Tsh, sh, v_t, tsp, 12, tv, hs_ts (p_hs P)).
  { unfold tsp. prot4_cin_arg. }
  forward.
  forward_call (gv, S, w).
  forward.
  forward.
  { entailer!. change (Int64.signed (Int64.divs (Int64.repr 1000000000) (Int64.repr 50))) with 20000000.
    pose proof (Int64.signed_range (hs_lic (p_hs P))). rep_lia. }
  set (rep := negb (Int.lt (Int.repr 0) (Int.repr (memcmp_Z tv (hs_ts (p_hs P)))))).
  set (fl := Int64.cmp Cgt (Int64.add (hs_lic (p_hs P))
               (Int64.divs (Int64.repr 1000000000) (Int64.repr (Int.signed (Int.repr 50))))) (s_boot S)).
  match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx [] (LOCALx (temp noise.code._t'8 (Vint (if orb rep fl then Int.one else Int.zero)) :: L)
                (SEPx R))) end.
  { forward. destruct rep; [|discriminate]. entailer!. }
  { forward. destruct rep; [discriminate|]. entailer!. destruct fl; reflexivity. }
  assert (Hrf := prot4_cin_rf tv (hs_ts (p_hs P)) (hs_lic (p_hs P)) (s_boot S)). fold rep fl in Hrf.
  destruct (orb rep fl) eqn:Hrf'.
  { forward_if.
    2: { prot4_cin_absurd. }
    subst ssp tsp. rewrite <- (prot4_cin_bytes12 sh _ _ Lhts), <- (prot4_cin_hs_ts sh (hs_addr a) _ Lhts),
      <- (prot4_cin_hs_ss sh (hs_addr a) _ Lhss), <- (prot4_cin_bytes12 Tsh tv v_t Lt).
    sep_apply (prot4_cin_hs_fold sh (hs_addr a) (p_hs P) Hhok).
    sep_apply (prot4_cin_brk_ne PS a sh P H4 Hf Hr' W FCp).
    forward. Exists a.
    unfold cin_res. rewrite (prot4_cin_m5 _ PS M (s_boot S) _ _ _ _ _ _ _ _ _ Hs1 Hpk Hs2 (eq_sym Hrf)).
    cbn [peer_result].
    prot4_cin_fold. prot4_cin_to_. prot4_cin_len.
    subst pubp privp ephp encsp enctp.
    entailer!. unfold im_ok, id_ok; repeat split; auto. }
  forward_if.
  { prot4_cin_absurd. }
  assert (Hrep: rep = false) by (destruct rep; [discriminate|reflexivity]).
  (* memcpy(handshake->remote_ephemeral, e, 32) *)
  rewrite (prot4_cin_hs_reph sh (hs_addr a) _ Lhreph).
  set (rep_p := field_address t_hs (DOT I._remote_ephemeral) (hs_addr a)).
  sep_apply (prot4_cin_bytes32_ sh _ rep_p Lhreph).
  rewrite (prot4_cin_bytes32 Tsh (im_eph M) v_e Leph).
  forward_call (sh, Tsh, rep_p, v_e, 32, im_eph M).
  { unfold rep_p. prot4_cin_arg. }
  (* memcmp(t, handshake->latest_timestamp, 12) > 0 *)
  forward_call (Tsh, sh, v_t, tsp, 12, tv, hs_ts (p_hs P)).
  { unfold tsp. prot4_cin_arg. }
  match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx ?R))) _ _ =>
    let R' := prot4_cin_repl R (data_at sh (tarray tuchar 12) (map Vubyte (hs_ts (p_hs P))) tsp)
                (data_at sh (tarray tuchar 12) (map Vubyte tv) tsp) in
    forward_if (PROPx [] (LOCALx L (SEPx R'))) end.
  { sep_apply (data_at_data_at_ sh (tarray tuchar 12) (map Vubyte (hs_ts (p_hs P))) tsp).
    forward_call (sh, Tsh, tsp, v_t, 12, tv).
    { unfold tsp. prot4_cin_arg. }
    entailer!. }
  { exfalso. unfold rep in Hrep. unfold Int.lt in Hrep.
    destruct (zlt (Int.signed (Int.repr 0)) (Int.signed (Int.repr (memcmp_Z tv (hs_ts (p_hs P)))))) as [Hl|Hl];
      simpl in Hrep; [|discriminate].
    change (Int.signed (Int.repr 0)) with 0 in Hl. lia. }
  (* memcpy(handshake->hash, hash, 32); memcpy(handshake->chaining_key, chaining_key, 32) *)
  rewrite (prot4_cin_hs_hash sh (hs_addr a) _ Lhhash).
  set (hp := field_address t_hs (DOT I._hash) (hs_addr a)).
  sep_apply (prot4_cin_bytes32_ sh _ hp Lhhash).
  rewrite (prot4_cin_bytes32 Tsh HS2 v_hash LHS2).
  forward_call (sh, Tsh, hp, v_hash, 32, HS2).
  { unfold hp. prot4_cin_arg. }
  rewrite (prot4_cin_hs_ck sh (hs_addr a) _ Lhck).
  set (ckp := field_address t_hs (DOT I._chaining_key) (hs_addr a)).
  sep_apply (prot4_cin_bytes32_ sh _ ckp Lhck).
  rewrite (prot4_cin_bytes32 Tsh CK2 v_chaining_key LCK2).
  forward_call (sh, Tsh, ckp, v_chaining_key, 32, CK2).
  { unfold ckp. prot4_cin_arg. }
  forward. forward.
  forward_call (gv, S, w).
  forward.
  match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx ?R))) _ _ =>
    let R' := prot4_cin_repl R (field_at sh t_hs (DOT I._last_initiation_consumption) (Vlong (hs_lic (p_hs P))) (hs_addr a))
                (field_at sh t_hs (DOT I._last_initiation_consumption)
                   (Vlong (if Int64.lt (Int64.sub (hs_lic (p_hs P)) (s_boot S)) Int64.zero then s_boot S else hs_lic (p_hs P))) (hs_addr a)) in
    forward_if (PROPx [] (LOCALx L (SEPx R'))) end.
  { forward. entailer!.
    assert (E: Int64.lt (Int64.sub (hs_lic (p_hs P)) (s_boot S)) Int64.zero = true)
      by (unfold Int64.lt; destruct zlt; auto; change (Int64.signed (Int64.repr 0)) with 0 in *;
          change (Int64.signed Int64.zero) with 0 in *; lia).
    rewrite E. apply derives_refl. }
  { forward. entailer!.
    assert (E: Int64.lt (Int64.sub (hs_lic (p_hs P)) (s_boot S)) Int64.zero = false)
      by (unfold Int64.lt; destruct zlt; auto; change (Int64.signed (Int64.repr 0)) with 0 in *;
          change (Int64.signed Int64.zero) with 0 in *; lia).
    rewrite E. apply derives_refl. }
  forward. forward.
  Exists a.
  unfold cin_res. rewrite (prot4_cin_m6 _ PS M (s_boot S) _ _ _ _ _ _ _ _ _ Hid Hs1 Hpk Hr Hs2 (eq_sym Hrf)).
  cbn [peer_result].
  subst ssp tsp rep_p hp ckp.
  sep_apply (prot4_cin_hs_fold_succ sh (hs_addr a) (p_hs P) (im_eph M)
     (if Int64.lt (Int64.sub (hs_lic (p_hs P)) (s_boot S)) Int64.zero then s_boot S else hs_lic (p_hs P))
     HS2 CK2 tv (im_sender M) Hhok Leph LHS2 LCK2 Lt).
  sep_apply (prot4_cin_brk_some PS a sh P (rc_add1 (p_refs P))
     (mkHS HS_CONSUMED_INITIATION
        (if Int64.lt (Int64.sub (hs_lic (p_hs P)) (s_boot S)) Int64.zero then s_boot S else hs_lic (p_hs P))
        (hs_sid (p_hs P)) (hs_eph (p_hs P)) (hs_rstatic (p_hs P)) (im_eph M) (hs_ss (p_hs P))
        (hs_psk (p_hs P)) HS2 CK2 tv (im_sender M)) Hf W FCp).
  prot4_cin_fold. prot4_cin_to_. prot4_cin_len.
  subst pubp privp ephp encsp enctp.
  entailer!. unfold im_ok, id_ok; repeat split; auto.
Qed.

End Prot4ConsumeInit.

Theorem prot4_cons_init_bodies :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_wg_noise_handshake_consume_initiation (wg_noise_handshake_consume_initiation_spec x25519 aead_dec)).
Proof.
  intros. eapply prot4_cons_init_body; eauto.
Qed.
