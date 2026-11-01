(* the body group `create_resp` of the protocol piece v4 = v3's
   prot_body3_create_resp.v re-proved against the v4 specifications (prot_specs4.v, context Gprot4 of prot_prog4.v: the
   shim's refcount_t warnings exact).  Owner of the statement: the config_any. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

Require Import VST.msl.iter_sepcon.
Require WgNoise.proof.protocol.prot_body3_shim_table1.
Require WgNoise.proof.blake2s.model.

Section CreateResp.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.
Context (HX: x25519_props x25519) (HA: aead_props aead_enc aead_dec).

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Definition Gn := Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS.

Lemma prot4_cr_resp_eq sh m M :
  resp_rep sh m M =
  !! rm_ok M &&
  (field_at sh t_resp (DOT N._header) (Vint (rm_type M)) m *
   field_at sh t_resp (DOT N._sender_index) (Vint (rm_sender M)) m *
   field_at sh t_resp (DOT N._receiver_index) (Vint (rm_receiver M)) m *
   field_at sh t_resp (DOT N._unencrypted_ephemeral) (bytes (rm_eph M)) m *
   field_at sh t_resp (DOT N._encrypted_nothing) (bytes (rm_encn M)) m *
   field_at sh t_resp (DOT N._macs) (bytes (rm_mac1 M), bytes (rm_mac2 M)) m).
Proof.
  unfold resp_rep, resp_val. f_equal. unfold_data_at (data_at _ _ _ m).
  apply pred_ext; cancel.
Qed.

Lemma prot4_cr_open sht tab T a E :
  t_entry T a = Some E -> field_compatible t_hs [] a ->
  itable sht tab T |--
  EX she: share, !! readable_share she &&
   (field_at she t_hs (DOT N._entry) (entry_val E (succ_in (t_L T) a) (vin a (t_L T))) a *
    (field_at she t_hs (DOT N._entry) (entry_val E (succ_in (t_L T) a) (vin a (t_L T))) a -*
     itable sht tab T)).
Proof.
  intros HE FC. unfold t_entry in HE.
  destruct (sfind (t_D T) a) as [[she E']|] eqn:HS; inv HE.
  unfold itable. Intros. rewrite (WgNoise.proof.protocol.prot_body3_shim_table1.prot3_shim_table1_split _ _ _ _ _ HS).
  assert (writable_share she) by (destruct H as (_ & _ & _ & HF); eapply WgNoise.proof.protocol.prot_body3_shim_table1.prot3_shim_table1_sfind_wr; eauto).
  Exists she.
  assert (EQ: field_at she t_hs (DOT N._entry) (entry_val E (succ_in (t_L T) a) (vin a (t_L T))) a =
              entry_at she a E (succ_in (t_L T) a) (vin a (t_L T))).
  { unfold entry_at. rewrite field_at_data_at. f_equal.
    rewrite field_address_offset by auto with field_compatible. simpl. apply isptr_offset_val_zero.
    apply field_compatible_isptr in FC; auto. }
  rewrite EQ. apply andp_right; [apply prop_right; auto|].
  unfold pool_item_rep at 1.
  set (X := entry_at she a E _ _). set (Y := iter_sepcon _ _). set (Z0 := data_at _ _ _ tab).
  rewrite <- sepcon_assoc, (sepcon_comm Z0 X), sepcon_assoc.
  apply sepcon_derives; [apply derives_refl|].
  apply -> wand_sepcon_adjoint. apply andp_right; [apply prop_right; auto|].
  unfold pool_item_rep at 1. fold X.
  rewrite (sepcon_comm (Z0 * Y) X), <- sepcon_assoc, (sepcon_comm X Z0), sepcon_assoc. apply derives_refl.
Qed.

(* the peer without its device field and handshake *)
Definition prot4_cr_prest (sh: share) (p: val) (P: peer) : mpred :=
  field_at sh t_peer (DOT I._is_dead) (Val.of_bool (p_dead P)) p *
  kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
  field_at sh t_peer (DOT I._last_sent_handshake) (Vlong (p_lsh P)) p *
  cookie_rep sh (cookie_addr p) (p_cookie P) *
  field_at sh t_peer (DOT I._refcount) (Vint (p_refs P)) p *
  field_at sh t_peer (DOT I._internal_id) (Vlong (p_id P)) p *
  field_at sh t_peer (DOT I._pubkey_next) (p_pknext P) p *
  spacer sh 9 16 p * spacer sh 476 480 p.

Lemma prot4_cr_peer_eq sh p P :
  peer_rep sh p P =
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer (DOT I._device) (p_device P) p * prot4_cr_prest sh p P * hs_rep sh (hs_addr p) (p_hs P)).
Proof. unfold peer_rep, prot4_cr_prest. f_equal. apply pred_ext; cancel. Qed.

Lemma prot4_cr_prest_set sh p P H : prot4_cr_prest sh p (p_set_hs P H) = prot4_cr_prest sh p P.
Proof. reflexivity. Qed.

(* the handshake fields create_response never touches *)
Definition prot4_cr_hrest (sh: share) (h: val) (lic: int64) (sid: val) (ss ts: list byte) : mpred :=
  field_at sh t_hs (DOT I._last_initiation_consumption) (Vlong lic) h *
  field_at sh t_hs (DOT I._static_identity) sid h *
  field_at sh t_hs (DOT I._precomputed_static_static) (bytes ss) h *
  field_at sh t_hs (DOT I._latest_timestamp) (bytes ts) h *
  (EX lk: val, field_at sh t_hs (DOT I._lock) lk h) *
  spacer sh 36 40 h * spacer sh 300 304 h.

Lemma prot4_cr_hs_eq sh h H :
  hs_rep sh h H =
  !! hs_ok H &&
  (prot4_cr_hrest sh h (hs_lic H) (hs_sid H) (hs_ss H) (hs_ts H) *
   field_at sh t_hs (DOT I._state) (Vint (hs_state H)) h *
   field_at sh t_hs (DOT I._ephemeral_private) (bytes (hs_eph H)) h *
   field_at sh t_hs (DOT I._remote_static) (bytes (hs_rstatic H)) h *
   field_at sh t_hs (DOT I._remote_ephemeral) (bytes (hs_reph H)) h *
   field_at sh t_hs (DOT I._preshared_key) (bytes (hs_psk H)) h *
   field_at sh t_hs (DOT I._hash) (bytes (hs_hash H)) h *
   field_at sh t_hs (DOT I._chaining_key) (bytes (hs_ck H)) h *
   field_at sh t_hs (DOT I._remote_index) (Vint (hs_rindex H)) h).
Proof. unfold hs_rep, prot4_cr_hrest. f_equal. apply pred_ext; cancel. Qed.

Lemma prot4_cr_hs_ephemeral_private sh h bs : Zlength bs = 32 ->
  field_at sh t_hs (DOT I._ephemeral_private) (bytes bs) h = bytes_at sh bs (field_address t_hs (DOT I._ephemeral_private) h).
Proof. intros L. unfold bytes_at. rewrite L, field_at_data_at. reflexivity. Qed.

Lemma prot4_cr_hs_remote_static sh h bs : Zlength bs = 32 ->
  field_at sh t_hs (DOT I._remote_static) (bytes bs) h = bytes_at sh bs (field_address t_hs (DOT I._remote_static) h).
Proof. intros L. unfold bytes_at. rewrite L, field_at_data_at. reflexivity. Qed.

Lemma prot4_cr_hs_remote_ephemeral sh h bs : Zlength bs = 32 ->
  field_at sh t_hs (DOT I._remote_ephemeral) (bytes bs) h = bytes_at sh bs (field_address t_hs (DOT I._remote_ephemeral) h).
Proof. intros L. unfold bytes_at. rewrite L, field_at_data_at. reflexivity. Qed.

Lemma prot4_cr_hs_preshared_key sh h bs : Zlength bs = 32 ->
  field_at sh t_hs (DOT I._preshared_key) (bytes bs) h = bytes_at sh bs (field_address t_hs (DOT I._preshared_key) h).
Proof. intros L. unfold bytes_at. rewrite L, field_at_data_at. reflexivity. Qed.

Lemma prot4_cr_hs_hash sh h bs : Zlength bs = 32 ->
  field_at sh t_hs (DOT I._hash) (bytes bs) h = bytes_at sh bs (field_address t_hs (DOT I._hash) h).
Proof. intros L. unfold bytes_at. rewrite L, field_at_data_at. reflexivity. Qed.

Lemma prot4_cr_hs_chaining_key sh h bs : Zlength bs = 32 ->
  field_at sh t_hs (DOT I._chaining_key) (bytes bs) h = bytes_at sh bs (field_address t_hs (DOT I._chaining_key) h).
Proof. intros L. unfold bytes_at. rewrite L, field_at_data_at. reflexivity. Qed.

Lemma prot4_cr_m_unencrypted_ephemeral sh m bs : Zlength bs = 32 ->
  field_at sh t_resp (DOT N._unencrypted_ephemeral) (bytes bs) m = bytes_at sh bs (field_address t_resp (DOT N._unencrypted_ephemeral) m).
Proof. intros L. unfold bytes_at. rewrite L, field_at_data_at. reflexivity. Qed.

Lemma prot4_cr_m_encrypted_nothing sh m bs : Zlength bs = 16 ->
  field_at sh t_resp (DOT N._encrypted_nothing) (bytes bs) m = bytes_at sh bs (field_address t_resp (DOT N._encrypted_nothing) m).
Proof. intros L. unfold bytes_at. rewrite L, field_at_data_at. reflexivity. Qed.

Lemma prot4_cr_bytes32 sh bs p : Zlength bs = 32 -> bytes_at sh bs p = data_at sh (tarray tuchar 32) (map Vubyte bs) p.
Proof. intros L. unfold bytes_at, bytes. rewrite L. reflexivity. Qed.

Lemma prot4_cr_bytes32' sh bs p : Zlength bs = 32 -> bytes_at sh bs p = data_at sh (tarray tuchar 32) (bytes bs) p.
Proof. intros L. unfold bytes_at. rewrite L. reflexivity. Qed.

Lemma prot4_cr_consts gv :
  spec.blake2s_globals gv * curve25519_globals gv * zero_page gv * cookie_globals gv |-- wg_consts gv.
Proof. unfold wg_consts. cancel. Qed.

Lemma prot4_cr_bytes16_ sh bs p : Zlength bs = 16 -> bytes_at sh bs p |-- data_at_ sh (tarray tuchar 16) p.
Proof. intros L. unfold bytes_at. rewrite L. apply data_at_data_at_. Qed.

Lemma prot4_cr_prim_nil sh p : prim_bytes sh [] p = emp.
Proof. reflexivity. Qed.

Lemma prot4_cr_enc16 sh bs p : Zlength bs = 16 ->
  data_at sh (tarray tuchar (Zlength (@nil byte) + 16)) (bytes bs) p = bytes_at sh bs p.
Proof. intros L. unfold bytes_at. rewrite L. reflexivity. Qed.

Lemma prot4_cr_bytes_ sh bs p : Zlength bs = 32 -> bytes_at sh bs p |-- data_at_ sh (tarray tuchar 32) p.
Proof. intros L. rewrite prot4_cr_bytes32 by auto. apply data_at_data_at_. Qed.

Lemma prot4_cr_hash_len m : Zlength (HASH m) = 32.
Proof. unfold HASH, model.blake2s, model.b2s_digest_stream, model.b2s_out. rewrite Zlength_map. reflexivity. Qed.

Lemma prot4_cr_kdf1_len a b : Zlength (kdf1 a b) = 32.
Proof. unfold kdf1, hmac. cbv zeta. apply prot4_cr_hash_len. Qed.
Lemma prot4_cr_kdf2_len a b : Zlength (kdf2 a b) = 32.
Proof. unfold kdf2, hmac. cbv zeta. apply prot4_cr_hash_len. Qed.
Lemma prot4_cr_kdf3_len a b : Zlength (kdf3 a b) = 32.
Proof. unfold kdf3, hmac. cbv zeta. apply prot4_cr_hash_len. Qed.
Lemma prot4_cr_mix_hash_len a b : Zlength (mix_hash a b) = 32.
Proof. unfold mix_hash. apply prot4_cr_hash_len. Qed.

(* the model's exits *)
Lemma prot4_cr_m0 H M r idx :
  Int.eq (hs_state H) HS_CONSUMED_INITIATION = false ->
  create_response_model x25519 aead_enc H M r idx = (false, M, H).
Proof. intros E. unfold create_response_model. rewrite E. reflexivity. Qed.

Lemma prot4_cr_m1 H M r idx :
  Int.eq (hs_state H) HS_CONSUMED_INITIATION = true ->
  andb (memneq_bool (clamp r) zeros32) (memneq_bool (x25519 (clamp r) basepoint9) zeros32) = false ->
  create_response_model x25519 aead_enc H M r idx =
  (false, mkRM (Int.repr 2) (rm_sender M) (hs_rindex H)
            (if memneq_bool (clamp r) zeros32 then x25519 (clamp r) basepoint9 else rm_eph M)
            (rm_encn M) (rm_mac1 M) (rm_mac2 M),
   hs_set_eph H (clamp r)).
Proof.
  intros E1 E2. unfold create_response_model. rewrite E1. cbn [negb].
  destruct (memneq_bool (clamp r) zeros32); cbn [negb andb] in *; [rewrite E2|]; reflexivity.
Qed.

Lemma prot4_cr_m2 H M r idx :
  Int.eq (hs_state H) HS_CONSUMED_INITIATION = true ->
  memneq_bool (clamp r) zeros32 = true -> memneq_bool (x25519 (clamp r) basepoint9) zeros32 = true ->
  dh_ok x25519 (clamp r) (hs_reph H) = false ->
  create_response_model x25519 aead_enc H M r idx =
  (false, mkRM (Int.repr 2) (rm_sender M) (hs_rindex H) (x25519 (clamp r) basepoint9)
            (rm_encn M) (rm_mac1 M) (rm_mac2 M),
   hs_set_ckh (hs_set_eph H (clamp r)) (kdf1 (hs_ck H) (x25519 (clamp r) basepoint9))
     (mix_hash (hs_hash H) (x25519 (clamp r) basepoint9))).
Proof.
  intros E1 E2 E3 E4. unfold create_response_model. rewrite E1, E2, E3, E4. reflexivity.
Qed.

Lemma prot4_cr_m3 H M r idx :
  Int.eq (hs_state H) HS_CONSUMED_INITIATION = true ->
  memneq_bool (clamp r) zeros32 = true -> memneq_bool (x25519 (clamp r) basepoint9) zeros32 = true ->
  dh_ok x25519 (clamp r) (hs_reph H) = true -> dh_ok x25519 (clamp r) (hs_rstatic H) = false ->
  create_response_model x25519 aead_enc H M r idx =
  (false, mkRM (Int.repr 2) (rm_sender M) (hs_rindex H) (x25519 (clamp r) basepoint9)
            (rm_encn M) (rm_mac1 M) (rm_mac2 M),
   hs_set_ckh (hs_set_eph H (clamp r))
     (kdf1 (kdf1 (hs_ck H) (x25519 (clamp r) basepoint9)) (x25519 (clamp r) (hs_reph H)))
     (mix_hash (hs_hash H) (x25519 (clamp r) basepoint9))).
Proof.
  intros E1 E2 E3 E4 E5. unfold create_response_model. rewrite E1, E2, E3, E4, E5. reflexivity.
Qed.

Lemma prot4_cr_m4 H M r idx :
  Int.eq (hs_state H) HS_CONSUMED_INITIATION = true ->
  memneq_bool (clamp r) zeros32 = true -> memneq_bool (x25519 (clamp r) basepoint9) zeros32 = true ->
  dh_ok x25519 (clamp r) (hs_reph H) = true -> dh_ok x25519 (clamp r) (hs_rstatic H) = true ->
  let E := x25519 (clamp r) basepoint9 in
  let ck3 := kdf1 (kdf1 (kdf1 (hs_ck H) E) (x25519 (clamp r) (hs_reph H))) (x25519 (clamp r) (hs_rstatic H)) in
  let h2 := mix_hash (mix_hash (hs_hash H) E) (kdf2 ck3 (hs_psk H)) in
  let encn := aead_enc (kdf3 ck3 (hs_psk H)) 0 h2 [] in
  create_response_model x25519 aead_enc H M r idx =
  (true, mkRM (Int.repr 2) idx (hs_rindex H) E encn (rm_mac1 M) (rm_mac2 M),
   hs_set_state (hs_set_ckh (hs_set_eph H (clamp r)) (kdf1 ck3 (hs_psk H)) (mix_hash h2 encn))
     HS_CREATED_RESPONSE).
Proof.
  intros E1 E2 E3 E4 E5. unfold create_response_model. rewrite E1, E2, E3, E4, E5. reflexivity.
Qed.

Ltac cr_arg ep rsp rep pskp hp ckp mep mnp := apply prop_right; unfold ep, rsp, rep, pskp, hp, ckp, mep, mnp; simpl;
  rewrite ?field_address_offset by auto with field_compatible; reflexivity.

Ltac cr_len HX HA :=
  match goal with
  | |- Zlength (kdf1 _ _) = _ => apply prot4_cr_kdf1_len
  | |- Zlength (kdf2 _ _) = _ => apply prot4_cr_kdf2_len
  | |- Zlength (kdf3 _ _) = _ => apply prot4_cr_kdf3_len
  | |- Zlength (mix_hash _ _) = _ => apply prot4_cr_mix_hash_len
  | |- Zlength (x25519 _ _) = _ => apply HX
  | |- Zlength (clamp _) = _ => unfold clamp; list_solve
  | |- Zlength (aead_enc _ _ _ []) = _ => rewrite (aead_enc_length _ _ HA); reflexivity
  | H: Zlength ?x = ?n |- Zlength ?x = ?n => exact H
  end.

Ltac cr_fold HX HA :=
  rewrite prot4_cr_resp_eq, prot4_cr_peer_eq, prot4_cr_hs_eq,
    prot4_cr_prest_set;
  cbn [p_hs p_device p_set_hs hs_set_eph hs_set_ckh hs_set_state hs_state hs_lic hs_sid hs_eph hs_rstatic
       hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts hs_rindex rm_type rm_sender rm_receiver rm_eph rm_encn
       rm_mac1 rm_mac2 fst snd];
  rewrite prot4_cr_hs_ephemeral_private by cr_len HX HA;
  rewrite prot4_cr_hs_remote_static by cr_len HX HA;
  rewrite prot4_cr_hs_remote_ephemeral by cr_len HX HA;
  rewrite prot4_cr_hs_preshared_key by cr_len HX HA;
  rewrite prot4_cr_hs_hash by cr_len HX HA;
  rewrite prot4_cr_hs_chaining_key by cr_len HX HA;
  rewrite prot4_cr_m_unencrypted_ephemeral by cr_len HX HA;
  rewrite prot4_cr_m_encrypted_nothing by cr_len HX HA;
  unfold wg_consts.

Ltac cr_ok HX HA := unfold rm_ok, hs_ok;
  cbn [p_hs p_device p_set_hs hs_set_eph hs_set_ckh hs_set_state hs_state hs_lic hs_sid hs_eph hs_rstatic
       hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts hs_rindex rm_type rm_sender rm_receiver rm_eph rm_encn
       rm_mac1 rm_mac2 fst snd];
  repeat split; cr_len HX HA.

Ltac cr_nn := repeat match goal with |- context [eq_dec nullval nullval] =>
  let NN := fresh "NN" in destruct (eq_dec nullval nullval) as [_|NN]; [|congruence] end.

Lemma prot4_cr_body :
  @semax_body (QPvarspecs Noise.qp) Gn Noise.CS
    WgNoise.noise.code.f_wg_noise_handshake_create_response (wg_noise_handshake_create_response_spec x25519 aead_enc).
Proof.
  start_function.
  forward.
  forward_loop
    (PROP () LOCAL (temp N._ret (Val.of_bool false); lvar N._key (tarray tuchar 32) v_key; gvars gv;
                    temp N._dst m; temp N._handshake (hs_addr p))
     SEP (data_at_ Tsh (tarray tuchar 32) v_key; resp_rep shm m M; peer_rep shp p P; device_rep shd wg D;
          itable sht (d_itab D) T; shim_state4 gv S w; wg_consts gv))
  continue: (EX r: list byte, EX idx: int,
     PROP (Zlength r = 32; fst (fst (cr_res x25519 aead_enc P M r idx)) = true -> t_fresh T (hs_addr p) idx)
     LOCAL (temp N._ret (Val.of_bool (fst (fst (cr_res x25519 aead_enc P M r idx))));
            lvar N._key (tarray tuchar 32) v_key; gvars gv)
     SEP (data_at_ Tsh (tarray tuchar 32) v_key;
          resp_rep shm m (snd (fst (cr_res x25519 aead_enc P M r idx)));
          peer_rep shp p (p_set_hs P (snd (cr_res x25519 aead_enc P M r idx)));
          device_rep shd wg D;
          itable sht (d_itab D) (if fst (fst (cr_res x25519 aead_enc P M r idx)) then t_insert T (hs_addr p) idx else T);
          shim_state4 gv (if Int.eq (hs_state (p_hs P)) HS_CONSUMED_INITIATION
                         then (if fst (fst (cr_res x25519 aead_enc P M r idx)) then shim_u32 (shim_draw S r) idx
                               else shim_draw S r)
                         else S) w;
          wg_consts gv))%assert
  break: (EX r: list byte, EX idx: int,
     PROP (Zlength r = 32; fst (fst (cr_res x25519 aead_enc P M r idx)) = true -> t_fresh T (hs_addr p) idx)
     LOCAL (temp N._ret (Val.of_bool (fst (fst (cr_res x25519 aead_enc P M r idx))));
            lvar N._key (tarray tuchar 32) v_key; gvars gv)
     SEP (data_at_ Tsh (tarray tuchar 32) v_key;
          resp_rep shm m (snd (fst (cr_res x25519 aead_enc P M r idx)));
          peer_rep shp p (p_set_hs P (snd (cr_res x25519 aead_enc P M r idx)));
          device_rep shd wg D;
          itable sht (d_itab D) (if fst (fst (cr_res x25519 aead_enc P M r idx)) then t_insert T (hs_addr p) idx else T);
          shim_state4 gv (if Int.eq (hs_state (p_hs P)) HS_CONSUMED_INITIATION
                         then (if fst (fst (cr_res x25519 aead_enc P M r idx)) then shim_u32 (shim_draw S r) idx
                               else shim_draw S r)
                         else S) w;
          wg_consts gv))%assert.
  { entailer!. }
  2: { Intros r idx. forward. Exists r idx. entailer!. }
  2: { Intros r idx. forward_call (Tsh, v_key, 32).
       forward. Exists r idx. entailer!.
       destruct (fst (fst (cr_res x25519 aead_enc P M r idx))); reflexivity. }
  rewrite prot4_cr_resp_eq, prot4_cr_peer_eq, prot4_cr_hs_eq. Intros.
  forward.
  forward_if.
  { forward. Exists zeros32 Int.zero.
    assert (Hs: Int.eq (hs_state (p_hs P)) HS_CONSUMED_INITIATION = false).
    { apply Int.eq_false. intro E. rewrite E in H4. contradiction. }
    unfold cr_res. rewrite (prot4_cr_m0 _ _ _ _ Hs), Hs. cbn [fst snd].
    rewrite prot4_cr_resp_eq, prot4_cr_peer_eq, prot4_cr_hs_eq,
      prot4_cr_prest_set.
    cbn [p_hs p_device p_set_hs]. entailer!. }
  assert (Hs: Int.eq (hs_state (p_hs P)) HS_CONSUMED_INITIATION = true).
  { rewrite H4. reflexivity. }
  forward. forward. forward.
  assert_PROP (field_compatible t_hs (DOT I._ephemeral_private) (hs_addr p)) as FCe by entailer!.
  assert_PROP (field_compatible t_resp (DOT N._unencrypted_ephemeral) m) as FCme by entailer!.
  destruct H3 as (Leph & Lrs & Lreph & Lss & Lpsk & Lhash & Lck & Lts).
  destruct H1 as (Lmeph & Lmencn & Lmmac1 & Lmmac2).
  rewrite (prot4_cr_hs_ephemeral_private shp _ _ Leph), (prot4_cr_hs_remote_static shp _ _ Lrs),
    (prot4_cr_hs_remote_ephemeral shp _ _ Lreph), (prot4_cr_hs_preshared_key shp _ _ Lpsk),
    (prot4_cr_hs_hash shp _ _ Lhash), (prot4_cr_hs_chaining_key shp _ _ Lck),
    (prot4_cr_m_unencrypted_ephemeral shm _ _ Lmeph), (prot4_cr_m_encrypted_nothing shm _ _ Lmencn).
  set (ep := field_address t_hs (DOT I._ephemeral_private) (hs_addr p)).
  set (rsp := field_address t_hs (DOT I._remote_static) (hs_addr p)).
  set (rep := field_address t_hs (DOT I._remote_ephemeral) (hs_addr p)).
  set (pskp := field_address t_hs (DOT I._preshared_key) (hs_addr p)).
  set (hp := field_address t_hs (DOT I._hash) (hs_addr p)).
  set (ckp := field_address t_hs (DOT I._chaining_key) (hs_addr p)).
  set (mep := field_address t_resp (DOT N._unencrypted_ephemeral) m).
  set (mnp := field_address t_resp (DOT N._encrypted_nothing) m).
  sep_apply (prot4_cr_bytes_ shp (hs_eph (p_hs P)) ep Leph).
  assert (FCh: field_compatible t_hs [] (hs_addr p)).
  { apply field_compatible_cons in FCe. destruct FCe; auto. }
  assert (FCm: field_compatible t_resp [] m).
  { apply field_compatible_cons in FCme. destruct FCme; auto. }
  forward_call (gv, S, w, shp, ep).
  { cr_arg ep rsp rep pskp hp ckp mep mnp. }
  Intros r.
  assert (Lcl: Zlength (clamp r) = 32) by (unfold clamp; list_solve).
  rewrite (prot4_cr_bytes32 shm (rm_eph M) mep Lmeph), (prot4_cr_bytes32 shp (clamp r) ep Lcl).
  unfold wg_consts.
  forward_call (shm, mep, bytes (rm_eph M), shp, ep, clamp r, gv).
  { cr_arg ep rsp rep pskp hp ckp mep mnp. }
  { cancel. }
  { unfold bytes; rewrite Zlength_map; auto. }
  destruct (andb (memneq_bool (clamp r) zeros32) (memneq_bool (x25519 (clamp r) basepoint9) zeros32)) eqn:Hgp.
  2: { forward_if.
       2: { exfalso. apply H3. reflexivity. }
       forward.
       Exists r Int.zero.
       unfold cr_res. rewrite (prot4_cr_m1 _ _ _ _ Hs Hgp), Hs.
       rewrite <- (prot4_cr_bytes32 shp (clamp r) ep Lcl).
       destruct (memneq_bool (clamp r) zeros32) eqn:Hm1.
       - rewrite <- (prot4_cr_bytes32 shm _ mep (HX _ _)).
         subst ep rsp rep pskp hp ckp mep mnp. cr_fold HX HA.
         entailer!. cr_ok HX HA.
       - rewrite <- (prot4_cr_bytes32' shm _ mep Lmeph).
         subst ep rsp rep pskp hp ckp mep mnp. cr_fold HX HA.
         entailer!. cr_ok HX HA. }
  forward_if.
  { exfalso. apply Int.one_not_zero. exact H3. }
  apply andb_prop in Hgp. destruct Hgp as [Hm1 Hm2]. rewrite Hm1.
  rewrite <- (prot4_cr_bytes32 shm _ mep (HX _ _)), <- (prot4_cr_bytes32 shp (clamp r) ep Lcl).
  sep_apply (prot4_cr_consts gv).
  assert (LE: Zlength (x25519 (clamp r) basepoint9) = 32) by apply HX.
  forward_call (gv, true, shm, mep, shm, mep, x25519 (clamp r) basepoint9, shp, ckp, hs_ck (p_hs P), shp, hp,
                hs_hash (p_hs P)).
  { cr_arg ep rsp rep pskp hp ckp mep mnp. }
  set (E := x25519 (clamp r) basepoint9) in *.
  forward_call (gv, shp, ckp, kdf1 (hs_ck (p_hs P)) E, shp, nullval, shp, ep, clamp r, shp, rep, hs_reph (p_hs P)).
  { cr_arg ep rsp rep pskp hp ckp mep mnp. }
  { cr_nn. cancel. }
  cr_nn.
  destruct (dh_ok x25519 (clamp r) (hs_reph (p_hs P))) eqn:Hd1.
  2: { forward_if.
       2: { exfalso. apply H5. reflexivity. }
       forward.
       Exists r Int.zero.
       unfold cr_res. rewrite (prot4_cr_m2 (p_hs P) M r Int.zero Hs Hm1 Hm2 Hd1), Hs.
       subst ep rsp rep pskp hp ckp mep mnp E. cr_fold HX HA.
       entailer!. cr_ok HX HA. }
  forward_if.
  { exfalso. apply Int.one_not_zero. exact H5. }
  forward_call (gv, shp, ckp, kdf1 (kdf1 (hs_ck (p_hs P)) E) (x25519 (clamp r) (hs_reph (p_hs P))), shp, nullval,
                shp, ep, clamp r, shp, rsp, hs_rstatic (p_hs P)).
  { cr_arg ep rsp rep pskp hp ckp mep mnp. }
  { cr_nn. cancel. }
  cr_nn.
  destruct (dh_ok x25519 (clamp r) (hs_rstatic (p_hs P))) eqn:Hd2.
  2: { forward_if.
       2: { exfalso. apply H6. reflexivity. }
       forward.
       Exists r Int.zero.
       unfold cr_res. rewrite (prot4_cr_m3 (p_hs P) M r Int.zero Hs Hm1 Hm2 Hd1 Hd2), Hs.
       subst ep rsp rep pskp hp ckp mep mnp E. cr_fold HX HA.
       entailer!. cr_ok HX HA. }
  forward_if.
  { exfalso. apply Int.one_not_zero. exact H6. }
  forward_call (gv, shp, ckp, kdf1 (kdf1 (kdf1 (hs_ck (p_hs P)) E) (x25519 (clamp r) (hs_reph (p_hs P))))
                                  (x25519 (clamp r) (hs_rstatic (p_hs P))),
                shp, hp, mix_hash (hs_hash (p_hs P)) E, Tsh, v_key, shp, pskp, hs_psk (p_hs P)).
  { cr_arg ep rsp rep pskp hp ckp mep mnp. }
  set (ck3 := kdf1 (kdf1 (kdf1 (hs_ck (p_hs P)) E) (x25519 (clamp r) (hs_reph (p_hs P))))
                   (x25519 (clamp r) (hs_rstatic (p_hs P)))) in *.
  set (h2 := mix_hash (mix_hash (hs_hash (p_hs P)) E) (kdf2 ck3 (hs_psk (p_hs P)))) in *.
  sep_apply (prot4_cr_bytes16_ shm (rm_encn M) mnp Lmencn).
  forward_call (gv, shm, mnp, Tsh, nullval, @nil byte, Tsh, v_key, kdf3 ck3 (hs_psk (p_hs P)), shp, hp, h2).
  { cr_arg ep rsp rep pskp hp ckp mep mnp. }
  { rewrite prot4_cr_prim_nil. cancel. }
  { rewrite Zlength_nil. rep_lia. }
  rewrite prot4_cr_prim_nil, prot4_cr_enc16 by (rewrite (aead_enc_length _ _ HA); reflexivity).
  destruct H0 as [Ee [HEe HEp]].
  assert (HIn: In (hs_addr p) (saddrs (t_D T))).
  { unfold t_entry in HEe. destruct (sfind (t_D T) (hs_addr p)) as [[she0 E0]|] eqn:HS; inv HEe.
    eapply WgNoise.proof.protocol.prot_body3_shim_table1.prot3_shim_table1_saddrs_in. apply WgNoise.proof.protocol.prot_body3_shim_table1.prot3_shim_table1_sfind_In. exact HS. }
  sep_apply (prot4_cr_open sht (d_itab D) T (hs_addr p) Ee HEe FCh). Intros she.
  unfold entry_val.
  forward.
  rewrite HEp.
  sep_apply (modus_ponens_wand (field_at she t_hs (DOT N._entry)
     (p, (succ_in (t_L T) (hs_addr p), (Val.of_bool (vin (hs_addr p) (t_L T)), (Vint (e_type Ee), Vint (e_index Ee)))))
     (hs_addr p)) (itable sht (d_itab D) T)).
  forward.
  { rewrite H. unfold device_rep. Intros. entailer!. }
  rewrite H.
  unfold device_rep. Intros.
  forward.
  { unfold itable. Intros. entailer!. }
  forward_call (gv, shim_draw S r, w, sht, d_itab D, T, hs_addr p, @None (share * entry)).
    { change (raw_rep (hs_addr p) None) with emp. rewrite emp_sepcon. cancel. }
  all: try (change (raw_ok T (hs_addr p) None) with (In (hs_addr p) (saddrs (t_D T))); auto).
  change (raw_add T (hs_addr p) None) with T. Intros idx.
  forward. forward. forward.
  Exists r idx.
  pose proof (prot4_cr_m4 (p_hs P) M r idx Hs Hm1 Hm2 Hd1 Hd2) as Hmod. cbv zeta in Hmod.
  unfold cr_res. rewrite Hmod, Hs.
  sep_apply (prot4_cr_bytes_ Tsh (kdf3 ck3 (hs_psk (p_hs P))) v_key (prot4_cr_kdf3_len _ _)).
  subst ep rsp rep pskp hp ckp mep mnp E ck3 h2. cr_fold HX HA.
  unfold device_rep.
  entailer!. cr_ok HX HA.
Qed.

End CreateResp.

Theorem prot4_cr_bodies :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_wg_noise_handshake_create_response (wg_noise_handshake_create_response_spec x25519 aead_enc)).
Proof.
  intros. eapply prot4_cr_body; eauto.
Qed.
