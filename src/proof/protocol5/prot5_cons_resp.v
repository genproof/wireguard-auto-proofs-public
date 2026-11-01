(* The body of wg_noise_handshake_consume_response against its v5 specification (prot_specs5.v) in the
   context Gprot5 (prot_prog5.v): v4's script (prot4_cons_resp.v) re-run, over the v5 representation.  The
   message's macs, the device's dev and cookie checker, and the peer's last_sent_handshake, latest_cookie and
   internal_id are any (field_at_): consume_response never reads them, they ride along as frame.  The helper
   lemmas that mention none of the changed predicates are v4's. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_body3_shim_table1.
Require WgNoise.proof.blake2s.model.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.protocol4.prot4_cons_resp.
Require WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require WgNoise.noise.code WgNoise.shim.code.

Section Prot5ConsumeResp.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.
Context (HX: x25519_props x25519) (HA: aead_props aead_enc aead_dec).

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Definition prot5_Gcr := Gprot5 x25519 aead_enc aead_dec CSw Noise.CS.

(* the message: header and macs (the latter any), apart from the fields consume_response reads *)
Definition prot5_cre_mrest (sh: share) (m: val) (M: resp_msg) : mpred :=
  field_at sh t_resp (DOT N._header) (Vint (rm_type M)) m *
  field_at_ sh t_resp (DOT N._macs) m.

Lemma prot5_cre_resp_eq sh m M :
  resp_rep5 sh m M =
  !! rm_ok5 M &&
  (prot5_cre_mrest sh m M *
   field_at sh t_resp (DOT N._sender_index) (Vint (rm_sender M)) m *
   field_at sh t_resp (DOT N._receiver_index) (Vint (rm_receiver M)) m *
   field_at sh t_resp (DOT N._unencrypted_ephemeral) (bytes (rm_eph M)) m *
   field_at sh t_resp (DOT N._encrypted_nothing) (bytes (rm_encn M)) m).
Proof. unfold resp_rep5, prot5_cre_mrest. f_equal. apply pred_ext; cancel. Qed.

(* the device without the identity's flag and private key and the index table *)
Definition prot5_cre_drest (sh: share) (wg: val) (D: device) : mpred :=
  field_at_ sh t_dev (DOT I._dev) wg *
  field_at_ sh t_dev (DOT I._cookie_checker) wg *
  field_at sh t_dev (DOT I._peer_hashtable) (d_ptab D) wg *
  field_at sh t_dev (DOT I._static_identity DOT I._static_public) (bytes (id_pub (d_id D))) wg *
  (EX lk: val, field_at sh t_dev (DOT I._static_identity DOT I._lock) lk wg) *
  spacer sh 77 80 wg.

Lemma prot5_cre_dev_eq sh wg D :
  device_rep5 sh wg D =
  !! (field_compatible t_dev [] wg /\ id_ok (d_id D)) &&
  (prot5_cre_drest sh wg D *
   field_at sh t_dev (DOT I._static_identity DOT I._has_identity) (Val.of_bool (id_has (d_id D))) wg *
   field_at sh t_dev (DOT I._static_identity DOT I._static_private) (bytes (id_priv (d_id D))) wg *
   field_at sh t_dev (DOT I._index_hashtable) (d_itab D) wg).
Proof.
  unfold device_rep5, identity_rep, prot5_cre_drest.
  assert (E: field_compatible t_dev [] wg -> forall v, data_at sh t_sid v (id_addr wg) =
             field_at sh t_dev (DOT I._static_identity) v wg).
  { intros FC v. rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible. reflexivity. }
  apply pred_ext.
  - Intros lk. apply andp_right; [apply prop_right; auto|].
    rewrite E by auto. unfold_field_at 1%nat. Exists lk. cancel.
  - Intros lk. apply andp_right; [apply prop_right; auto|].
    Exists lk. rewrite E by auto. unfold_field_at 7%nat. cancel.
Qed.

(* the peer without its device field, refcount and handshake *)
Definition prot5_cre_prest (sh: share) (p: val) (P: peer) : mpred :=
  field_at sh t_peer (DOT I._is_dead) (Val.of_bool (p_dead P)) p *
  kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
  field_at_ sh t_peer (DOT I._last_sent_handshake) p *
  field_at_ sh t_peer (DOT I._latest_cookie) p *
  field_at_ sh t_peer (DOT I._internal_id) p *
  field_at sh t_peer (DOT I._pubkey_next) (p_pknext P) p *
  spacer sh 9 16 p * spacer sh 476 480 p.

Lemma prot5_cre_peer_eq sh p P :
  peer_rep5 sh p P =
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer (DOT I._device) (p_device P) p * peer_refs_rep sh p (p_refs P) *
   prot5_cre_prest sh p P * hs_rep sh (hs_addr p) (p_hs P)).
Proof. unfold peer_rep5, prot5_cre_prest, peer_refs_rep. f_equal. apply pred_ext; cancel. Qed.

Lemma prot5_cre_prest_set_hs sh p P H : prot5_cre_prest sh p (p_set_hs P H) = prot5_cre_prest sh p P.
Proof. reflexivity. Qed.
Lemma prot5_cre_prest_set_refs sh p P r : prot5_cre_prest sh p (p_set_refs P r) = prot5_cre_prest sh p P.
Proof. reflexivity. Qed.

(* the peer at a in the list, after an update, and the others *)
Lemma prot5_cre_open PS a sh P :
  sfind PS a = Some (sh, P) -> forall P', peers_rep5 (supd PS a P') = peer_rep5 sh a P' * peers_rep5 (sdel PS a).
Proof.
  intros Hf P'. unfold peers_rep5.
  rewrite (prot3_shim_table1_split (supd PS a P') a sh P' _ (prot3_shim_table1_supd_sfind_same PS a sh P' P Hf)).
  rewrite prot3_shim_table1_supd_sdel. reflexivity.
Qed.

Lemma prot5_cre_open0 PS a sh P :
  sfind PS a = Some (sh, P) -> peers_rep5 PS = peer_rep5 sh a P * peers_rep5 (sdel PS a).
Proof.
  intros Hf. rewrite <- (prot5_cre_open PS a sh P Hf P). rewrite (prot3_shim_table1_supd_same PS a sh P Hf). reflexivity.
Qed.

Ltac prot5_cre_to_ :=
  repeat match goal with |- context [bytes_at Tsh ?X ?v] => sep_apply (prot4_cre_bytes_any Tsh X v) end.

Ltac prot5_cre_len :=
  rewrite ?prot4_cre_kdf1_len, ?prot4_cre_kdf2_len, ?prot4_cre_kdf3_len, ?prot4_cre_mix_hash_len;
  repeat match goal with H: Zlength ?X = _ |- context [Zlength ?X] => rewrite H end.

Ltac prot5_cre_arg :=
  apply prop_right;
  repeat match goal with x := field_address _ _ _ |- _ => subst x end; simpl; rewrite ?field_address_offset by auto with field_compatible; simpl;
  rewrite ?offset_offset_val;
  repeat match goal with H: Zlength _ = _ |- context [Zlength _] => rewrite H end; reflexivity.

Ltac prot5_cre_nn := repeat match goal with |- context [eq_dec nullval nullval] =>
  let NN := fresh "NN" in destruct (eq_dec nullval nullval) as [_|NN]; [|congruence] end.

Ltac prot5_cre_lenx HX :=
  match goal with
  | |- Zlength (kdf1 _ _) = _ => apply prot4_cre_kdf1_len
  | |- Zlength (kdf2 _ _) = _ => apply prot4_cre_kdf2_len
  | |- Zlength (kdf3 _ _) = _ => apply prot4_cre_kdf3_len
  | |- Zlength (mix_hash _ _) = _ => apply prot4_cre_mix_hash_len
  | |- Zlength (x25519 _ _) = _ => apply HX
  | H: Zlength ?x = ?n |- Zlength ?x = ?n => exact H
  end.

(* replace the contents of a local buffer by a variable (no BLAKE2s term left for the unifier) *)
Ltac prot5_cre_hide1 HX v :=
  match goal with
  | |- context [bytes_at Tsh ?X v] =>
      let L := fresh "L" in
      assert (L: Zlength X = 32) by prot5_cre_lenx HX;
      revert L; generalize X; intros ? ?
  | _ => idtac
  end.

(* fold the opened objects back (at the exits of the inner block) *)
Ltac prot5_cre_fold HX :=
  rewrite prot5_cre_peer_eq, prot5_cre_dev_eq, prot5_cre_resp_eq;
  cbn [prot4_cre_pin p_device p_refs p_hs p_set_refs p_set_hs prot4_cre_hs' hs_state hs_lic hs_sid hs_eph
       hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts hs_rindex];
  rewrite ?prot5_cre_prest_set_hs, ?prot5_cre_prest_set_refs;
  rewrite prot4_cre_hs_eq;
  cbn [prot4_cre_pin p_device p_refs p_hs p_set_refs p_set_hs prot4_cre_hs' hs_state hs_lic hs_sid hs_eph
       hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts hs_rindex];
  rewrite prot4_cre_hs_eph by prot5_cre_lenx HX;
  rewrite prot4_cre_hs_reph by prot5_cre_lenx HX;
  rewrite prot4_cre_hs_psk by prot5_cre_lenx HX;
  rewrite prot4_cre_hs_hash by prot5_cre_lenx HX;
  rewrite prot4_cre_hs_ck by prot5_cre_lenx HX;
  rewrite prot4_cre_m_eph by prot5_cre_lenx HX;
  rewrite prot4_cre_m_encn by prot5_cre_lenx HX;
  rewrite prot4_cre_d_priv by prot5_cre_lenx HX;
  prot5_cre_to_; prot5_cre_len.

Ltac prot5_cre_ok HX :=
  unfold rm_ok5, id_ok, hs_ok;
  cbn [prot4_cre_pin p_device p_refs p_hs p_set_refs p_set_hs prot4_cre_hs' hs_state hs_lic hs_sid hs_eph
       hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts hs_rindex];
  repeat split; prot5_cre_lenx HX.

Lemma prot5_cons_resp_body :
  @semax_body (QPvarspecs Noise.qp) prot5_Gcr Noise.CS
    WgNoise.noise.code.f_wg_noise_handshake_consume_response (wg_noise_handshake_consume_response_spec x25519 aead_dec).
Proof.
  start_function. unfold cre_res in *.
  match goal with Hx: peers_refs_ok PS |- _ => rename Hx into Hrefs end.
  forward. forward. forward. forward.
  forward_loop
    (PROP () LOCAL (temp N._quickproof_success (Vint Int.zero); temp N._ret_peer nullval;
       lvar N._preshared_key (tarray tuchar 32) v_preshared_key;
       lvar N._static_private (tarray tuchar 32) v_static_private;
       lvar N._ephemeral_private (tarray tuchar 32) v_ephemeral_private;
       lvar N._e (tarray tuchar 32) v_e; lvar N._chaining_key (tarray tuchar 32) v_chaining_key;
       lvar N._hash (tarray tuchar 32) v_hash; lvar N._key (tarray tuchar 32) v_key;
       lvar N._peer (tptr t_peer) v_peer; gvars gv; temp N._src m; temp N._wg wg)
     SEP (data_at_ Tsh (tarray tuchar 32) v_preshared_key; data_at_ Tsh (tarray tuchar 32) v_static_private;
       data_at_ Tsh (tarray tuchar 32) v_ephemeral_private; data_at_ Tsh (tarray tuchar 32) v_e;
       data_at_ Tsh (tarray tuchar 32) v_chaining_key; data_at_ Tsh (tarray tuchar 32) v_hash;
       data_at_ Tsh (tarray tuchar 32) v_key; data_at Tsh (tptr t_peer) nullval v_peer;
       resp_rep5 shm m M; device_rep5 shd wg D; itable sht (d_itab D) T; peers_rep5 PS;
       shim_state4 gv S w; wg_consts5 gv))
  continue: (EX pv: val,
    PROP () LOCAL (temp N._ret_peer (peer_result (prot_specs4.cre_res x25519 aead_dec D T PS M));
       lvar N._preshared_key (tarray tuchar 32) v_preshared_key;
       lvar N._static_private (tarray tuchar 32) v_static_private;
       lvar N._ephemeral_private (tarray tuchar 32) v_ephemeral_private;
       lvar N._e (tarray tuchar 32) v_e; lvar N._chaining_key (tarray tuchar 32) v_chaining_key;
       lvar N._hash (tarray tuchar 32) v_hash; lvar N._key (tarray tuchar 32) v_key;
       lvar N._peer (tptr t_peer) v_peer; gvars gv; temp N._src m; temp N._wg wg)
     SEP (data_at_ Tsh (tarray tuchar 32) v_preshared_key; data_at_ Tsh (tarray tuchar 32) v_static_private;
       data_at_ Tsh (tarray tuchar 32) v_ephemeral_private; data_at_ Tsh (tarray tuchar 32) v_e;
       data_at_ Tsh (tarray tuchar 32) v_chaining_key; data_at_ Tsh (tarray tuchar 32) v_hash;
       data_at_ Tsh (tarray tuchar 32) v_key; data_at Tsh (tptr t_peer) pv v_peer;
       resp_rep5 shm m M; device_rep5 shd wg D; itable sht (d_itab D) T;
       peers_rep5 (peers_after PS (prot_specs4.cre_res x25519 aead_dec D T PS M));
       shim_state4 gv S w; wg_consts5 gv))%assert
  break: (EX pv: val,
    PROP () LOCAL (temp N._ret_peer (peer_result (prot_specs4.cre_res x25519 aead_dec D T PS M));
       lvar N._preshared_key (tarray tuchar 32) v_preshared_key;
       lvar N._static_private (tarray tuchar 32) v_static_private;
       lvar N._ephemeral_private (tarray tuchar 32) v_ephemeral_private;
       lvar N._e (tarray tuchar 32) v_e; lvar N._chaining_key (tarray tuchar 32) v_chaining_key;
       lvar N._hash (tarray tuchar 32) v_hash; lvar N._key (tarray tuchar 32) v_key;
       lvar N._peer (tptr t_peer) v_peer; gvars gv; temp N._src m; temp N._wg wg)
     SEP (data_at_ Tsh (tarray tuchar 32) v_preshared_key; data_at_ Tsh (tarray tuchar 32) v_static_private;
       data_at_ Tsh (tarray tuchar 32) v_ephemeral_private; data_at_ Tsh (tarray tuchar 32) v_e;
       data_at_ Tsh (tarray tuchar 32) v_chaining_key; data_at_ Tsh (tarray tuchar 32) v_hash;
       data_at_ Tsh (tarray tuchar 32) v_key; data_at Tsh (tptr t_peer) pv v_peer;
       resp_rep5 shm m M; device_rep5 shd wg D; itable sht (d_itab D) T;
       peers_rep5 (peers_after PS (prot_specs4.cre_res x25519 aead_dec D T PS M));
       shim_state4 gv S w; wg_consts5 gv))%assert.
  { entailer!. }
  2: { Intros pv. forward. Exists pv. entailer!. }
  2: { Intros pv.
       forward_call (Tsh, v_key, 32).
       forward_call (Tsh, v_hash, 32).
       forward_call (Tsh, v_chaining_key, 32).
       forward_call (Tsh, v_ephemeral_private, 32).
       forward_call (Tsh, v_static_private, 32).
       forward_call (Tsh, v_preshared_key, 32).
       forward. entailer!. }
  rewrite prot5_cre_dev_eq. Intros. rename H1 into FCd, H2 into IDok.
  forward.
  { entailer!. destruct (id_has (d_id D)); simpl; auto. }
  forward_if.
  { destruct (id_has (d_id D)) eqn:Hid; [inv H1|].
    forward. Exists nullval. rewrite (prot4_cre_m0 x25519 aead_dec D T PS M Hid). cbn [peer_result peers_after].
    rewrite prot5_cre_dev_eq, Hid. entailer!. }
  destruct (id_has (d_id D)) eqn:Hid; [|inv H1]. clear H1.
  forward.
  { unfold itable. Intros. entailer!. }
  rewrite prot5_cre_resp_eq. Intros. rename H1 into RMok.
  forward.
  forward_call (gv, S, w, sht, d_itab D, T, PS, Int.repr 1, rm_receiver M, Tsh, v_peer, nullval).
  forward.
  destruct (t_lookup T (Int.repr 1) (rm_receiver M)) as [[a E]|] eqn:HL.
  2: { forward_if.
       2: { exfalso. congruence. }
       forward. Exists nullval. rewrite (prot4_cre_m1 x25519 aead_dec D T PS M HL). cbn [peer_result peers_after].
       rewrite prot5_cre_dev_eq, Hid, prot5_cre_resp_eq. entailer!. }
  destruct (prot4_cre_lookup T PS _ a E H HL) as (Ha & Ea & sh & P & Hf & Hr).
  assert (VP := prot3_shim_table1_valid sht (d_itab D) T a Ha).
  forward_if.
  { exfalso. subst a. unfold hs_addr in H1. destruct (e_peer E); inv H1. }
  subst a.
  assert (W: writable_share sh) by (eapply prot3_shim_table1_sfind_wr; [unfold peers_wf in H0; exact H0 | exact Hf]).
  unfold peers_ref. rewrite Hf, (prot5_cre_open PS (e_peer E) sh P Hf), prot5_cre_peer_eq. Intros.
  rename H2 into FCp.
  cbn [p_device p_refs p_hs p_set_refs]. rewrite prot5_cre_prest_set_refs.
  rewrite prot4_cre_hs_eq. Intros. rename H2 into HSok.
  set (p := e_peer E) in *. set (Hs := p_hs P) in *.
  assert_PROP (field_compatible t_hs (DOT I._state) (hs_addr p)) as FCs by entailer!.
  assert (FCh: field_compatible t_hs [] (hs_addr p)).
  { apply field_compatible_cons in FCs. destruct FCs; auto. }
  assert_PROP (field_compatible t_resp (DOT N._sender_index) m) as FCms by entailer!.
  assert (FCm: field_compatible t_resp [] m).
  { apply field_compatible_cons in FCms. destruct FCms; auto. }
  forward.
  destruct HSok as (Leph & Lrs & Lreph & Lss & Lpsk & Lhash & Lck & Lts).
  destruct RMok as (Lmeph & Lmencn).
  destruct IDok as (Lpub & Lpriv).
  rewrite (prot4_cre_hs_eph sh _ _ Leph), (prot4_cre_hs_reph sh _ _ Lreph), (prot4_cre_hs_psk sh _ _ Lpsk),
    (prot4_cre_hs_hash sh _ _ Lhash), (prot4_cre_hs_ck sh _ _ Lck),
    (prot4_cre_m_eph shm _ _ Lmeph), (prot4_cre_m_encn shm _ _ Lmencn), (prot4_cre_d_priv shd wg _ Lpriv).
  set (ep := field_address t_hs (DOT I._ephemeral_private) (hs_addr p)).
  set (rep := field_address t_hs (DOT I._remote_ephemeral) (hs_addr p)).
  set (pskp := field_address t_hs (DOT I._preshared_key) (hs_addr p)).
  set (hp := field_address t_hs (DOT I._hash) (hs_addr p)).
  set (ckp := field_address t_hs (DOT I._chaining_key) (hs_addr p)).
  set (mep := field_address t_resp (DOT N._unencrypted_ephemeral) m).
  set (mnp := field_address t_resp (DOT N._encrypted_nothing) m).
  set (privp := field_address t_dev (DOT I._static_identity DOT I._static_private) wg).
  rewrite (prot4_cre_bytes32 sh _ hp Lhash).
  forward_call (Tsh, sh, v_hash, hp, 32, hs_hash Hs).
  { prot5_cre_arg. }
  rewrite <- (prot4_cre_bytes32 sh _ hp Lhash), <- (prot4_cre_bytes32 Tsh _ v_hash Lhash).
  rewrite (prot4_cre_bytes32 sh _ ckp Lck).
  forward_call (Tsh, sh, v_chaining_key, ckp, 32, hs_ck Hs).
  { prot5_cre_arg. }
  rewrite <- (prot4_cre_bytes32 sh _ ckp Lck), <- (prot4_cre_bytes32 Tsh _ v_chaining_key Lck).
  rewrite (prot4_cre_bytes32 sh _ ep Leph).
  forward_call (Tsh, sh, v_ephemeral_private, ep, 32, hs_eph Hs).
  { prot5_cre_arg. }
  rewrite <- (prot4_cre_bytes32 sh _ ep Leph), <- (prot4_cre_bytes32 Tsh _ v_ephemeral_private Leph).
  rewrite (prot4_cre_bytes32 sh _ pskp Lpsk).
  forward_call (Tsh, sh, v_preshared_key, pskp, 32, hs_psk Hs).
  { prot5_cre_arg. }
  rewrite <- (prot4_cre_bytes32 sh _ pskp Lpsk), <- (prot4_cre_bytes32 Tsh _ v_preshared_key Lpsk).
  set (P1 := p_set_refs P (rc_add1 (p_refs P))).
  set (Rin := prot4_cre_rin x25519 aead_dec (id_priv (d_id D)) Hs M).
  forward_loop
    (PROP () LOCAL (temp N._quickproof_success (Vint Int.zero); temp N._ret_peer nullval;
       temp N._state (Vint (hs_state Hs)); temp N._handshake (hs_addr p);
       lvar N._preshared_key (tarray tuchar 32) v_preshared_key;
       lvar N._static_private (tarray tuchar 32) v_static_private;
       lvar N._ephemeral_private (tarray tuchar 32) v_ephemeral_private;
       lvar N._e (tarray tuchar 32) v_e; lvar N._chaining_key (tarray tuchar 32) v_chaining_key;
       lvar N._hash (tarray tuchar 32) v_hash; lvar N._key (tarray tuchar 32) v_key;
       lvar N._peer (tptr t_peer) v_peer; gvars gv; temp N._src m; temp N._wg wg)
     SEP (bytes_at Tsh (hs_psk Hs) v_preshared_key; data_at_ Tsh (tarray tuchar 32) v_static_private;
       bytes_at Tsh (hs_eph Hs) v_ephemeral_private; data_at_ Tsh (tarray tuchar 32) v_e;
       bytes_at Tsh (hs_ck Hs) v_chaining_key; bytes_at Tsh (hs_hash Hs) v_hash;
       data_at_ Tsh (tarray tuchar 32) v_key; data_at Tsh (tptr t_peer) p v_peer;
       itable sht (d_itab D) T;
       field_at sh t_peer (DOT I._device) (p_device P) p;
       peer_refs_rep sh p (rc_add1 (p_refs P));
       prot5_cre_prest sh p P;
       prot4_cre_hrest sh (hs_addr p) (hs_lic Hs) (hs_sid Hs) (hs_rstatic Hs) (hs_ss Hs) (hs_ts Hs);
       field_at sh t_hs (DOT I._state) (Vint (hs_state Hs)) (hs_addr p);
       bytes_at sh (hs_eph Hs) ep; bytes_at sh (hs_reph Hs) rep;
       bytes_at sh (hs_psk Hs) pskp; bytes_at sh (hs_hash Hs) hp; bytes_at sh (hs_ck Hs) ckp;
       field_at sh t_hs (DOT I._remote_index) (Vint (hs_rindex Hs)) (hs_addr p);
       peers_rep5 (sdel PS p);
       prot5_cre_mrest shm m M;
       field_at shm t_resp (DOT N._sender_index) (Vint (rm_sender M)) m;
       field_at shm t_resp (DOT N._receiver_index) (Vint (rm_receiver M)) m;
       bytes_at shm (rm_eph M) mep; prim_bytes shm (rm_encn M) mnp;
       prot5_cre_drest shd wg D;
       field_at shd t_dev (DOT I._static_identity DOT I._has_identity) (Val.of_bool true) wg;
       bytes_at shd (id_priv (d_id D)) privp;
       field_at shd t_dev (DOT I._index_hashtable) (d_itab D) wg;
       shim_state4 gv S w; wg_consts5 gv))
  continue: (
    PROP () LOCAL (temp N._quickproof_success (Val.of_bool (match Rin with Some _ => true | None => false end));
       temp N._ret_peer (match Rin with Some _ => p | None => nullval end);
       lvar N._preshared_key (tarray tuchar 32) v_preshared_key;
       lvar N._static_private (tarray tuchar 32) v_static_private;
       lvar N._ephemeral_private (tarray tuchar 32) v_ephemeral_private;
       lvar N._e (tarray tuchar 32) v_e; lvar N._chaining_key (tarray tuchar 32) v_chaining_key;
       lvar N._hash (tarray tuchar 32) v_hash; lvar N._key (tarray tuchar 32) v_key;
       lvar N._peer (tptr t_peer) v_peer; gvars gv; temp N._src m; temp N._wg wg)
     SEP (data_at_ Tsh (tarray tuchar 32) v_preshared_key; data_at_ Tsh (tarray tuchar 32) v_static_private;
       data_at_ Tsh (tarray tuchar 32) v_ephemeral_private; data_at_ Tsh (tarray tuchar 32) v_e;
       data_at_ Tsh (tarray tuchar 32) v_chaining_key; data_at_ Tsh (tarray tuchar 32) v_hash;
       data_at_ Tsh (tarray tuchar 32) v_key; data_at Tsh (tptr t_peer) p v_peer;
       resp_rep5 shm m M; device_rep5 shd wg D; itable sht (d_itab D) T;
       peer_rep5 sh p (prot4_cre_pin P1 Hs M Rin); peers_rep5 (sdel PS p);
       shim_state4 gv S w; wg_consts5 gv))%assert
  break: (
    PROP () LOCAL (temp N._quickproof_success (Val.of_bool (match Rin with Some _ => true | None => false end));
       temp N._ret_peer (match Rin with Some _ => p | None => nullval end);
       lvar N._preshared_key (tarray tuchar 32) v_preshared_key;
       lvar N._static_private (tarray tuchar 32) v_static_private;
       lvar N._ephemeral_private (tarray tuchar 32) v_ephemeral_private;
       lvar N._e (tarray tuchar 32) v_e; lvar N._chaining_key (tarray tuchar 32) v_chaining_key;
       lvar N._hash (tarray tuchar 32) v_hash; lvar N._key (tarray tuchar 32) v_key;
       lvar N._peer (tptr t_peer) v_peer; gvars gv; temp N._src m; temp N._wg wg)
     SEP (data_at_ Tsh (tarray tuchar 32) v_preshared_key; data_at_ Tsh (tarray tuchar 32) v_static_private;
       data_at_ Tsh (tarray tuchar 32) v_ephemeral_private; data_at_ Tsh (tarray tuchar 32) v_e;
       data_at_ Tsh (tarray tuchar 32) v_chaining_key; data_at_ Tsh (tarray tuchar 32) v_hash;
       data_at_ Tsh (tarray tuchar 32) v_key; data_at Tsh (tptr t_peer) p v_peer;
       resp_rep5 shm m M; device_rep5 shd wg D; itable sht (d_itab D) T;
       peer_rep5 sh p (prot4_cre_pin P1 Hs M Rin); peers_rep5 (sdel PS p);
       shim_state4 gv S w; wg_consts5 gv))%assert.
  { entailer!. }
  2: { forward. entailer!. }
  2: { assert (HM := prot4_cre_mS x25519 aead_dec D T PS M (hs_addr p) E sh P Hid HL Hf Hr).
       subst Rin P1 Hs ep rep pskp hp ckp mep mnp privp.
       destruct (prot4_cre_rin x25519 aead_dec (id_priv (d_id D)) (p_hs P) M) as [[ck h]|] eqn:HR.
       - forward_if.
         { exfalso. discriminate. }
         forward. Exists p. rewrite HM. cbn [peer_result peers_after].
         rewrite (prot5_cre_open PS p sh P Hf). entailer!.
       - rewrite prot5_cre_peer_eq. Intros. cbn [prot4_cre_pin p_device p_refs p_set_refs].
         forward_if.
         2: { exfalso. contradiction. }
         forward.
         forward_call (gv, S, w, sh, p, rc_add1 (p_refs P), p_device P).
         { destruct (eq_dec p nullval) as [e|]; [exfalso; destruct FCp as [Hp _]; rewrite e in Hp; inv Hp|]. cancel. }
         destruct (eq_dec p nullval) as [e|]; [exfalso; destruct FCp as [Hp _]; rewrite e in Hp; inv Hp|].
         rewrite (prot4_cre_dec_add1 _ w (prot4_cre_refs_bnd PS p sh P Hrefs Hf)).
         rewrite (rc_sub1_add1 _ (prot4_cre_refs_bnd PS p sh P Hrefs Hf)), (Int.eq_false _ _ Hr).
         Exists p. rewrite HM. cbn [peer_result peers_after].
         rewrite (prot5_cre_open0 PS p sh P Hf), (prot5_cre_peer_eq sh p P), prot5_cre_prest_set_refs.
         entailer!. apply derives_refl. }
  forward_if.
  { assert (Hs0: Int.eq (hs_state Hs) HS_CREATED_INITIATION = false) by (apply Int.eq_false; auto).
    forward.
    assert (ER: Rin = None) by (apply prot4_cre_r0; auto). rewrite ER.
    subst Rin P1 Hs ep rep pskp hp ckp mep mnp privp.
    prot5_cre_fold HX. rewrite Hid.
    entailer!. prot5_cre_ok HX. }
  assert (Hs0: Int.eq (hs_state Hs) HS_CREATED_INITIATION = true).
  { match goal with Hx: hs_state Hs = Int.repr 1 |- _ => rewrite Hx; reflexivity end. }
  forward_call (gv, false, Tsh, v_e, shm, mep, rm_eph M, Tsh, v_chaining_key, hs_ck Hs, Tsh, v_hash, hs_hash Hs).
  { prot5_cre_arg. }
  { simpl. cancel. }
  cbv iota.
  forward_call (gv, Tsh, v_chaining_key, kdf1 (hs_ck Hs) (rm_eph M), Tsh, nullval, Tsh, v_ephemeral_private,
                hs_eph Hs, Tsh, v_e, rm_eph M).
  { prot5_cre_nn. cancel. }
  prot5_cre_nn.
  destruct (dh_ok x25519 (hs_eph Hs) (rm_eph M)) eqn:Hd1.
  2: { forward_if.
       2: { exfalso. congruence. }
       forward.
       assert (ER: Rin = None) by (apply prot4_cre_r1; auto). rewrite ER.
       subst Rin P1 Hs ep rep pskp hp ckp mep mnp privp.
       prot5_cre_fold HX. rewrite Hid.
       entailer!. prot5_cre_ok HX. }
  forward_if.
  { exfalso. apply Int.one_not_zero. assumption. }
  forward_call (gv, Tsh, v_chaining_key, kdf1 (kdf1 (hs_ck Hs) (rm_eph M)) (x25519 (hs_eph Hs) (rm_eph M)),
                Tsh, nullval, shd, privp, id_priv (d_id D), Tsh, v_e, rm_eph M).
  { prot5_cre_arg. }
  { prot5_cre_nn. cancel. }
  prot5_cre_nn.
  destruct (dh_ok x25519 (id_priv (d_id D)) (rm_eph M)) eqn:Hd2.
  2: { forward_if.
       2: { exfalso. congruence. }
       forward.
       assert (ER: Rin = None) by (apply prot4_cre_r2; auto). rewrite ER.
       subst Rin P1 Hs ep rep pskp hp ckp mep mnp privp.
       prot5_cre_fold HX. rewrite Hid.
       entailer!. prot5_cre_ok HX. }
  forward_if.
  { exfalso. apply Int.one_not_zero. assumption. }
  set (ck3 := kdf1 (kdf1 (kdf1 (hs_ck Hs) (rm_eph M)) (x25519 (hs_eph Hs) (rm_eph M)))
                   (x25519 (id_priv (d_id D)) (rm_eph M))) in *.
  forward_call (gv, Tsh, v_chaining_key, ck3, Tsh, v_hash, mix_hash (hs_hash Hs) (rm_eph M), Tsh, v_key,
                Tsh, v_preshared_key, hs_psk Hs).
  set (h2 := mix_hash (mix_hash (hs_hash Hs) (rm_eph M)) (kdf2 ck3 (hs_psk Hs))) in *.
  forward_call (gv, Tsh, nullval, @nil val, shm, mnp, rm_encn M, Tsh, v_key, kdf3 ck3 (hs_psk Hs), Tsh, v_hash, h2).
  { prot5_cre_arg. }
  { rewrite Lmencn. reflexivity. }
  destruct (aead_dec (kdf3 ck3 (hs_psk Hs)) 0 h2 (rm_encn M)) as [pt|] eqn:Hdec.
  2: { forward_if.
       2: { exfalso. congruence. }
       forward.
       assert (ER: Rin = None).
       { unfold Rin. rewrite (prot4_cre_r3 x25519 aead_dec _ _ _ Hs0 Hd1 Hd2). cbv zeta. fold ck3 h2. rewrite Hdec. reflexivity. }
       rewrite ER.
       subst Rin P1 Hs ep rep pskp hp ckp mep mnp privp h2 ck3.
       prot5_cre_hide1 HX v_key; prot5_cre_hide1 HX v_hash; prot5_cre_hide1 HX v_chaining_key.
       prot5_cre_fold HX. rewrite Hid.
       entailer!. prot5_cre_ok HX. }
  forward_if.
  { exfalso. apply Int.one_not_zero. assumption. }
  assert (ER: Rin = Some (kdf1 ck3 (hs_psk Hs), mix_hash h2 (rm_encn M))).
  { unfold Rin. rewrite (prot4_cre_r3 x25519 aead_dec _ _ _ Hs0 Hd1 Hd2). cbv zeta. fold ck3 h2. rewrite Hdec. reflexivity. }
  set (ck4 := kdf1 ck3 (hs_psk Hs)) in *.
  set (h3 := mix_hash h2 (rm_encn M)) in *.
  set (key := kdf3 ck3 (hs_psk Hs)) in *.
  assert (Lck4: Zlength ck4 = 32) by apply prot4_cre_kdf1_len.
  assert (Lh3: Zlength h3 = 32) by apply prot4_cre_mix_hash_len.
  assert (Lkey: Zlength key = 32) by apply prot4_cre_kdf3_len.
  clearbody ck4 h3 key.
  assert (Ept: pt = []).
  { apply (aead_dec_length _ _ HA) in Hdec. rewrite Lmencn in Hdec. apply Zlength_nil_inv. exact Hdec. }
  subst pt. change (bytes []) with (@nil val). rewrite prot4_cre_out0.
  forward.
  forward_if.
  { exfalso. discriminate. }
  sep_apply (prot4_cre_bytes32_ sh (hs_reph Hs) rep Lreph).
  rewrite (prot4_cre_bytes32 Tsh (rm_eph M) v_e Lmeph).
  forward_call (sh, Tsh, rep, v_e, 32, rm_eph M).
  { prot5_cre_arg. }
  rewrite <- (prot4_cre_bytes32 Tsh (rm_eph M) v_e Lmeph), <- (prot4_cre_bytes32 sh (rm_eph M) rep Lmeph).
  sep_apply (prot4_cre_bytes32_ sh (hs_hash Hs) hp Lhash).
  rewrite (prot4_cre_bytes32 Tsh h3 v_hash Lh3).
  forward_call (sh, Tsh, hp, v_hash, 32, h3).
  { prot5_cre_arg. }
  rewrite <- (prot4_cre_bytes32 Tsh h3 v_hash Lh3), <- (prot4_cre_bytes32 sh h3 hp Lh3).
  sep_apply (prot4_cre_bytes32_ sh (hs_ck Hs) ckp Lck).
  rewrite (prot4_cre_bytes32 Tsh ck4 v_chaining_key Lck4).
  forward_call (sh, Tsh, ckp, v_chaining_key, 32, ck4).
  { prot5_cre_arg. }
  rewrite <- (prot4_cre_bytes32 Tsh ck4 v_chaining_key Lck4), <- (prot4_cre_bytes32 sh ck4 ckp Lck4).
  forward. forward. forward. forward. forward.
  rewrite ER.
  subst Rin P1 Hs ep rep pskp hp ckp mep mnp privp h2 ck3.
  prot5_cre_fold HX. rewrite Hid.
  entailer!. prot5_cre_ok HX.
Qed.

End Prot5ConsumeResp.
