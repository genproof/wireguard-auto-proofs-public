(* wg_cookie_message_consume (cookie.c): body proof.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_body3_shim_table1.
Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require Import WgNoise.proof.blake2s.model WgNoise.proof.blake2s.spec WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.protocol4.prot4_ck_msg_lib.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.
Require Import VST.msl.iter_sepcon.

Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the peers (Noise.CS)                                                                            *)
(* ---------------------------------------------------------------------------------------------- *)
Section NoisePart.
#[local] Existing Instance Noise.CS.

Lemma prot4_ckc_open PS a sh P :
  sfind PS a = Some (sh, P) -> forall P', peers_rep (supd PS a P') = peer_rep sh a P' * peers_rep (sdel PS a).
Proof.
  intros Hf P'. unfold peers_rep.
  rewrite (prot3_shim_table1_split (supd PS a P') a sh P' _ (prot3_shim_table1_supd_sfind_same PS a sh P' P Hf)).
  rewrite prot3_shim_table1_supd_sdel. reflexivity.
Qed.

Lemma prot4_ckc_open0 PS a sh P :
  sfind PS a = Some (sh, P) -> peers_rep PS = peer_rep sh a P * peers_rep (sdel PS a).
Proof.
  intros Hf. rewrite <- (prot4_ckc_open PS a sh P Hf P). rewrite (prot3_shim_table1_supd_same PS a sh P Hf). reflexivity.
Qed.

(* the peer without its device field, refcount and cookie *)
Definition prot4_ckc_prest (sh: share) (p: val) (P: peer) : mpred :=
  field_at sh t_peer (DOT I._is_dead) (Val.of_bool (p_dead P)) p *
  kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
  hs_rep sh (hs_addr p) (p_hs P) *
  field_at sh t_peer (DOT I._last_sent_handshake) (Vlong (p_lsh P)) p *
  field_at sh t_peer (DOT I._internal_id) (Vlong (p_id P)) p *
  field_at sh t_peer (DOT I._pubkey_next) (p_pknext P) p *
  spacer sh 9 16 p * spacer sh 476 480 p.

Lemma prot4_ckc_peer_eq sh p P :
  peer_rep sh p P =
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer (DOT I._device) (p_device P) p * peer_refs_rep sh p (p_refs P) *
   prot4_ckc_prest sh p P * cookie_rep sh (cookie_addr p) (p_cookie P)).
Proof. unfold peer_rep, prot4_ckc_prest, peer_refs_rep. f_equal. apply pred_ext; cancel. Qed.

Lemma prot4_ckc_prest_set_cookie sh p P C : prot4_ckc_prest sh p (p_set_cookie P C) = prot4_ckc_prest sh p P.
Proof. reflexivity. Qed.
Lemma prot4_ckc_prest_set_refs sh p P r : prot4_ckc_prest sh p (p_set_refs P r) = prot4_ckc_prest sh p P.
Proof. reflexivity. Qed.

Lemma prot4_ckc_sub_add r : Int.sub (Int.add r Int.one) Int.one = r.
Proof. rewrite Int.sub_add_opp, Int.add_assoc, Int.add_neg_zero, Int.add_zero. reflexivity. Qed.

(* the peers' counts are below INT_MAX (peers_refs_ok, L03) *)
Lemma prot4_ckc_refs_bnd PS a sh P :
  peers_refs_ok PS -> sfind PS a = Some (sh, P) -> 0 < Int.unsigned (p_refs P) < 2147483647.
Proof.
  intros HR Hf. apply prot3_shim_table1_sfind_In in Hf. unfold peers_refs_ok in HR.
  rewrite Forall_forall in HR. exact (HR _ Hf).
Qed.

End NoisePart.

(* ---------------------------------------------------------------------------------------------- *)
(* the table lookup                                                                                *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma prot4_ckc_find_index T L idx a E :
  t_find_index T L idx = Some (a, E) -> exists sh, sfind (t_D T) a = Some (sh, E).
Proof.
  induction L as [|x L IH]; simpl; intros H; [discriminate|].
  destruct (t_entry T x) as [Ex|] eqn:Hx; [|auto].
  destruct (Int.eq (e_index Ex) idx); [|auto].
  inv H. unfold t_entry in Hx. destruct (sfind (t_D T) a) as [[sh E']|]; inv Hx. eauto.
Qed.

Lemma prot4_ckc_lookup T PS mask idx a E :
  pool_peers_ok T PS -> t_lookup T mask idx = Some (a, E) ->
  In a (saddrs (t_D T)) /\ exists sh P, sfind PS (e_peer E) = Some (sh, P) /\ p_refs P <> Int.zero.
Proof.
  intros HP HL. unfold t_lookup in HL.
  destruct (t_find_index T (t_L T) idx) as [[a' E']|] eqn:HF; [|discriminate].
  destruct (Int.eq (Int.and (e_type E') mask) Int.zero) eqn:Hm; inv HL.
  destruct (prot4_ckc_find_index _ _ _ _ _ HF) as [she Hs].
  apply prot3_shim_table1_sfind_In in Hs.
  unfold pool_peers_ok in HP. rewrite Forall_forall in HP. specialize (HP _ Hs). cbv beta iota in HP.
  destruct HP as [Hpe _].
  split; [eapply prot3_shim_table1_saddrs_in; eauto|]. exact Hpe.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* objects of cookie.c's compspecs                                                                 *)
(* ---------------------------------------------------------------------------------------------- *)
Section CookiePart.
#[local] Existing Instance Cookie.CS.

(* the cookie's fields cookie_message_consume never touches: mac1 key, lock, padding *)
Definition prot4_ckc_crest (sh: share) (p: val) (mk: list byte) (lk: val) : mpred :=
  field_at sh t_peer (DOT C._latest_cookie DOT C._message_mac1_key) (bytes mk) p *
  field_at sh t_peer (DOT C._latest_cookie DOT C._lock) lk p *
  spacer sh 466 468 p.

(* the cookie's fields, as cookie_message_consume reads and writes them *)
Definition prot4_ckc_cf (sh: share) (p: val) (C: cookie) (lk: val) : mpred :=
  field_at sh t_peer (DOT C._latest_cookie DOT C._birthdate) (Vlong (ck_birth C)) p *
  field_at sh t_peer (DOT C._latest_cookie DOT C._is_valid) (Val.of_bool (ck_valid C)) p *
  data_at sh (tarray tuchar 16) (bytes (ck_cookie C)) (field_address t_peer (DOT C._latest_cookie DOT C._cookie) p) *
  field_at sh t_peer (DOT C._latest_cookie DOT C._have_sent_mac1) (Val.of_bool (ck_sent C)) p *
  data_at sh (tarray tuchar 16) (bytes (ck_last_mac1 C))
    (field_address t_peer (DOT C._latest_cookie DOT C._last_mac1_sent) p) *
  data_at sh (tarray tuchar 32) (bytes (ck_dkey C))
    (field_address t_peer (DOT C._latest_cookie DOT C._cookie_decryption_key) p) *
  prot4_ckc_crest sh p (ck_mkey C) lk.

Lemma prot4_ckc_cookie_eq sh p C lk :
  @field_compatible Noise.CS t_peer [] p ->
  @data_at Noise.CS sh t_cookie (cookie_val C lk) (cookie_addr p) = prot4_ckc_cf sh p C lk.
Proof.
  intros FCn.
  assert (FC: field_compatible t_peer [] p).
  { apply (@field_compatible_change_composite Noise.CS Cookie.CS _); [reflexivity | exact FCn]. }
  rewrite (data_at_cs_eq (cs1 := Noise.CS) (cs2 := Cookie.CS) sh t_cookie (cookie_val C lk) (cookie_val C lk))
    by (try apply JMeq_refl; reflexivity).
  assert (E: @data_at Cookie.CS sh t_cookie (cookie_val C lk) (cookie_addr p) =
             @field_at Cookie.CS sh t_peer (DOT C._latest_cookie) (cookie_val C lk) p).
  { rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible. reflexivity. }
  rewrite E. clear E.
  unfold cookie_val. unfold_field_at 1%nat.
  unfold prot4_ckc_cf, prot4_ckc_crest.
  rewrite (field_at_data_at sh t_peer (DOT C._latest_cookie DOT C._cookie)).
  rewrite (field_at_data_at sh t_peer (DOT C._latest_cookie DOT C._last_mac1_sent)).
  rewrite (field_at_data_at sh t_peer (DOT C._latest_cookie DOT C._cookie_decryption_key)).
  apply pred_ext; cancel.
Qed.

Definition prot4_ckc_drest (sh: share) (wg: val) (D: device) : mpred :=
  @field_at Noise.CS sh t_dev [StructField I._dev] (d_dev D) wg *
  identity_rep sh (id_addr wg) (d_id D) *
  checker_rep sh (cc_addr wg) (d_cc D) *
  @field_at Noise.CS sh t_dev [StructField I._peer_hashtable] (d_ptab D) wg.

Lemma prot4_ckc_dev_eq sh wg D :
  device_rep sh wg D =
  !! @field_compatible Noise.CS t_dev [] wg &&
  (field_at sh t_dev (DOT C._index_hashtable) (d_itab D) wg * prot4_ckc_drest sh wg D).
Proof.
  unfold device_rep, prot4_ckc_drest.
  rewrite (field_at_cs_eq (cs1 := Noise.CS) (cs2 := Cookie.CS) sh t_dev (DOT C._index_hashtable) (d_itab D) (d_itab D))
    by (try apply JMeq_refl; reflexivity).
  f_equal. apply pred_ext; cancel.
Qed.

Lemma prot4_ckc_msg_eq sh m M :
  cmsg_rep sh m M =
  !! (cm_ok M /\ field_compatible t_cmsg [] m) &&
  (field_at sh t_cmsg (DOT C._header DOT C._type) (Vint (cm_type M)) m *
   field_at sh t_cmsg (DOT C._receiver_index) (Vint (cm_receiver M)) m *
   data_at sh (tarray tuchar 24) (bytes (cm_nonce M)) (field_address t_cmsg (DOT C._nonce) m) *
   data_at sh (tarray tuchar 32) (bytes (cm_enc M)) (field_address t_cmsg (DOT C._encrypted_cookie) m)).
Proof.
  unfold cmsg_rep, cmsg_val.
  assert (Eq: field_compatible t_cmsg [] m ->
    data_at sh t_cmsg (Vint (cm_type M), (Vint (cm_receiver M), (bytes (cm_nonce M), bytes (cm_enc M)))) m =
    field_at sh t_cmsg (DOT C._header DOT C._type) (Vint (cm_type M)) m *
    field_at sh t_cmsg (DOT C._receiver_index) (Vint (cm_receiver M)) m *
    data_at sh (tarray tuchar 24) (bytes (cm_nonce M)) (field_address t_cmsg (DOT C._nonce) m) *
    data_at sh (tarray tuchar 32) (bytes (cm_enc M)) (field_address t_cmsg (DOT C._encrypted_cookie) m)).
  { intros FC. unfold_data_at (data_at sh t_cmsg _ m). unfold_field_at 1%nat.
    rewrite (field_at_data_at sh t_cmsg (DOT C._nonce)).
    rewrite (field_at_data_at sh t_cmsg (DOT C._encrypted_cookie)).
    rewrite !sepcon_assoc. reflexivity. }
  apply pred_ext.
  - Intros. assert_PROP (field_compatible t_cmsg [] m) as FC by entailer!.
    rewrite (Eq FC). entailer!.
  - Intros. rewrite (Eq H0). entailer!.
Qed.

Lemma prot4_ckc_zp gv : @zero_page Noise.CS gv = @zero_page Cookie.CS gv.
Proof. unfold zero_page. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Lemma prot4_ckc_pb sh (l: list byte) p n :
  Zlength l = n -> n <> 0 -> @data_at Cookie.CS sh (tarray tuchar n) (map Vubyte l) p = @prim_bytes Cookie.CS sh l p.
Proof. intros H Hn. subst n. unfold prim_bytes. rewrite if_false by auto. reflexivity. Qed.

Lemma prot4_ckc_po sh (l: list val) p n :
  Zlength l = n -> n <> 0 -> @data_at Cookie.CS sh (tarray tuchar n) l p = @prim_out Cookie.CS sh l p.
Proof. intros H Hn. subst n. unfold prim_out. rewrite if_false by auto. reflexivity. Qed.

Lemma prot4_ckc_ptr sh v p :
  @data_at Noise.CS sh (tptr t_peer) v p = @data_at Cookie.CS sh (tptr t_peer) v p.
Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

End CookiePart.

(* ---------------------------------------------------------------------------------------------- *)
(* the model                                                                                       *)
(* ---------------------------------------------------------------------------------------------- *)
Section Model.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Definition prot4_ckc_R (C: cookie) (M: cookie_msg) : option (list byte) :=
  if ck_sent C then xaead_dec (ck_dkey C) (cm_nonce M) (ck_last_mac1 C) (cm_enc M) else None.

Definition prot4_ckc_C2 (C: cookie) (M: cookie_msg) (now: int64) : cookie :=
  match prot4_ckc_R C M with
  | Some pt => mkCookie now true pt false (ck_last_mac1 C) (ck_dkey C) (ck_mkey C)
  | None => C
  end.

Lemma prot4_ckc_m_none T PS M S :
  t_lookup T (Int.or (Int.repr 1) (Int.repr 2)) (cm_receiver M) = None -> mcons_res xaead_dec T PS M S = None.
Proof. intros E. unfold mcons_res, message_consume_model. unfold IDX_HANDSHAKE, IDX_KEYPAIR. rewrite E. reflexivity. Qed.

Lemma prot4_ckc_m_some T PS M S a E sh P :
  t_lookup T (Int.or (Int.repr 1) (Int.repr 2)) (cm_receiver M) = Some (a, E) ->
  sfind PS (e_peer E) = Some (sh, P) ->
  peers_after PS (mcons_res xaead_dec T PS M S) =
  supd PS (e_peer E) (p_set_cookie P (prot4_ckc_C2 (p_cookie P) M (s_boot S))).
Proof.
  intros E1 E2. unfold mcons_res, message_consume_model. unfold IDX_HANDSHAKE, IDX_KEYPAIR. rewrite E1, E2.
  unfold prot4_ckc_C2, prot4_ckc_R.
  destruct (ck_sent (p_cookie P)); cbn [negb].
  - destruct (xaead_dec _ _ _ _); cbn [peers_after]; [reflexivity|].
    symmetry. destruct P as [? ? ? ? ? ? ? Ck ? ? ?]. cbn [p_cookie p_set_cookie].
    apply prot3_shim_table1_supd_same with (sh := sh). exact E2.
  - cbn [peers_after]. symmetry. destruct P as [? ? ? ? ? ? ? Ck ? ? ?]. cbn [p_cookie p_set_cookie].
    apply prot3_shim_table1_supd_same with (sh := sh). exact E2.
Qed.

End Model.

(* ---------------------------------------------------------------------------------------------- *)
(* the body                                                                                        *)
(* ---------------------------------------------------------------------------------------------- *)
Section Body.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.
Hypothesis HXA: xaead_props xaead_enc xaead_dec.

#[local] Existing Instance Cookie.CS.

Lemma prot4_ckc_body :
  @semax_body (QPvarspecs Cookie.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Cookie.CS) Cookie.CS
      WgNoise.cookie.code.f_wg_cookie_message_consume (wg_cookie_message_consume_spec xaead_dec).
Proof.
  start_function.
  match goal with Hx: peers_refs_ok PS |- _ => rename Hx into Hrefs end.
  forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  rewrite prot4_ckc_dev_eq. Intros. rename H1 into FCd.
  forward.
  { unfold itable. Intros. entailer!.
    match goal with Hf: field_compatible t_itab [] (d_itab D) |- _ => destruct Hf as [Hp _] end.
    destruct (d_itab D); try contradiction; simpl; auto. }
  rewrite prot4_ckc_msg_eq. Intros.
  forward.
  forward_call (gv, S, w, sht, d_itab D, T, PS, Int.or (Int.repr 1) (Int.repr 2), cm_receiver M, Tsh, v_peer, nullval).
  rename H1 into CMok, H2 into FCm.
  destruct (t_lookup T (Int.or (Int.repr 1) (Int.repr 2)) (cm_receiver M)) as [[a E]|] eqn:HL.
  2: { forward_if.
       2: { exfalso. congruence. }
       forward.
       rewrite (prot4_ckc_m_none _ T PS M S HL). cbn [peers_after].
       rewrite prot4_ckc_dev_eq, prot4_ckc_msg_eq. entailer!. }
  destruct (prot4_ckc_lookup T PS _ _ a E H HL) as (Ha & sh & P & Hf & Hr).
  assert (VP := prot3_shim_table1_valid sht (d_itab D) T a Ha).
  assert_PROP (isptr a) as Pa by (sep_apply (prot3_shim_table1_isptr sht (d_itab D) T a Ha); entailer!).
  forward_if.
  { exfalso. destruct a; try contradiction. discriminate. }
  assert (W: writable_share sh) by (eapply prot3_shim_table1_sfind_wr; [unfold peers_wf in H0; exact H0 | exact Hf]).
  unfold peers_ref. rewrite Hf, (prot4_ckc_open PS (e_peer E) sh P Hf), prot4_ckc_peer_eq. Intros.
  rename H2 into FCp.
  assert (FCc: @field_compatible Cookie.CS t_peer [] (e_peer E))
    by (apply (@field_compatible_change_composite Noise.CS Cookie.CS _); [reflexivity | exact FCp]).
  cbn [p_device p_refs p_cookie p_set_refs]. rewrite prot4_ckc_prest_set_refs.
  set (p := e_peer E) in *. set (C0 := p_cookie P) in *.
  unfold cookie_rep. Intros lk. rename H2 into Cok.
  rewrite (prot4_ckc_cookie_eq sh p C0 lk FCp).
  set (C2 := prot4_ckc_C2 xaead_dec C0 M (s_boot S)).
  forward_loop
    (PROP () LOCAL (lvar C._cookie__1 (tarray tuchar 16) v_cookie__1; lvar C._peer (tptr t_peer) v_peer;
       gvars gv; temp C._src m; temp C._wg wg)
     SEP (itable sht (d_itab D) T; peers_rep (sdel PS p); data_at Tsh (tptr t_peer) p v_peer;
       data_at_ Tsh (tarray tuchar 16) v_cookie__1;
       field_at shm t_cmsg (DOT C._header DOT C._type) (Vint (cm_type M)) m;
       field_at shm t_cmsg (DOT C._receiver_index) (Vint (cm_receiver M)) m;
       data_at shm (tarray tuchar 24) (bytes (cm_nonce M)) (field_address t_cmsg (DOT C._nonce) m);
       data_at shm (tarray tuchar 32) (bytes (cm_enc M)) (field_address t_cmsg (DOT C._encrypted_cookie) m);
       field_at shd t_dev (DOT C._index_hashtable) (d_itab D) wg;
       prot4_ckc_drest shd wg D; shim_state4 gv S w; wg_consts gv;
       @field_at Noise.CS sh t_peer (DOT I._device) (p_device P) p;
       peer_refs_rep sh p (rc_add1 (p_refs P)); prot4_ckc_prest sh p P;
       prot4_ckc_cf sh p C0 lk))
  continue:
    (PROP () LOCAL (lvar C._cookie__1 (tarray tuchar 16) v_cookie__1; lvar C._peer (tptr t_peer) v_peer;
       gvars gv; temp C._src m; temp C._wg wg)
     SEP (itable sht (d_itab D) T; peers_rep (sdel PS p); data_at Tsh (tptr t_peer) p v_peer;
       data_at_ Tsh (tarray tuchar 16) v_cookie__1;
       field_at shm t_cmsg (DOT C._header DOT C._type) (Vint (cm_type M)) m;
       field_at shm t_cmsg (DOT C._receiver_index) (Vint (cm_receiver M)) m;
       data_at shm (tarray tuchar 24) (bytes (cm_nonce M)) (field_address t_cmsg (DOT C._nonce) m);
       data_at shm (tarray tuchar 32) (bytes (cm_enc M)) (field_address t_cmsg (DOT C._encrypted_cookie) m);
       field_at shd t_dev (DOT C._index_hashtable) (d_itab D) wg;
       prot4_ckc_drest shd wg D; shim_state4 gv S w; wg_consts gv;
       @field_at Noise.CS sh t_peer (DOT I._device) (p_device P) p;
       peer_refs_rep sh p (rc_add1 (p_refs P)); prot4_ckc_prest sh p P;
       prot4_ckc_cf sh p C2 lk))
  break:
    (PROP () LOCAL (lvar C._cookie__1 (tarray tuchar 16) v_cookie__1; lvar C._peer (tptr t_peer) v_peer;
       gvars gv; temp C._src m; temp C._wg wg)
     SEP (itable sht (d_itab D) T; peers_rep (sdel PS p); data_at Tsh (tptr t_peer) p v_peer;
       data_at_ Tsh (tarray tuchar 16) v_cookie__1;
       field_at shm t_cmsg (DOT C._header DOT C._type) (Vint (cm_type M)) m;
       field_at shm t_cmsg (DOT C._receiver_index) (Vint (cm_receiver M)) m;
       data_at shm (tarray tuchar 24) (bytes (cm_nonce M)) (field_address t_cmsg (DOT C._nonce) m);
       data_at shm (tarray tuchar 32) (bytes (cm_enc M)) (field_address t_cmsg (DOT C._encrypted_cookie) m);
       field_at shd t_dev (DOT C._index_hashtable) (d_itab D) wg;
       prot4_ckc_drest shd wg D; shim_state4 gv S w; wg_consts gv;
       @field_at Noise.CS sh t_peer (DOT I._device) (p_device P) p;
       peer_refs_rep sh p (rc_add1 (p_refs P)); prot4_ckc_prest sh p P;
       prot4_ckc_cf sh p C2 lk)).
  { entailer!. }
  2: { forward. entailer!. }
  2: { assert (Cok2: cookie_ok C2).
       { unfold C2, prot4_ckc_C2, prot4_ckc_R. destruct (ck_sent C0); [|exact Cok].
         destruct (xaead_dec _ _ _ _) as [pt|] eqn:Hd; [|exact Cok].
         apply (xaead_dec_length _ _ HXA) in Hd. destruct CMok as [_ Le]. rewrite Le in Hd.
         destruct Cok as (L1 & L2 & L3 & L4). unfold cookie_ok; cbn [ck_cookie ck_last_mac1 ck_dkey ck_mkey].
         repeat split; auto. }
       forward.
       forward_call (gv, S, w, sh, p, rc_add1 (p_refs P), p_device P).
       { destruct (eq_dec p nullval) as [e|]; [exfalso; destruct FCp as [Hp _]; rewrite e in Hp; inv Hp|]. cancel. }
       destruct (eq_dec p nullval) as [e|]; [exfalso; destruct FCp as [Hp _]; rewrite e in Hp; inv Hp|].
       rewrite (rc_sub1_add1 _ (prot4_ckc_refs_bnd PS p sh P Hrefs Hf)), (Int.eq_false _ _ Hr).
       rewrite (rc_dec_warn_small (rc_add1 (p_refs P)) w)
         by (pose proof (prot4_ckc_refs_bnd PS p sh P Hrefs Hf); rewrite rc_add1_small by lia;
             unfold Int.add; rewrite Int.unsigned_one, Int.unsigned_repr; rep_lia).
       rewrite (prot4_ckc_m_some _ T PS M S a E sh P HL Hf). change (e_peer E) with p.
       rewrite (prot4_ckc_open PS p sh P Hf).
       rewrite prot4_ckc_peer_eq, prot4_ckc_prest_set_cookie. cbn [p_device p_refs p_cookie p_set_cookie].
       unfold cookie_rep.
       rewrite <- (prot4_ckc_cookie_eq sh p C2 lk FCp).
       rewrite prot4_ckc_dev_eq, prot4_ckc_msg_eq.
       entailer!.
       Exists lk. apply derives_refl. }
  unfold prot4_ckc_cf. Intros.
  forward.
  forward.
  { entailer!. destruct (ck_sent C0); simpl; auto. }
  destruct (ck_sent C0) eqn:Hs.
  2: { forward_if.
       2: { exfalso. auto. }
       forward.
       assert (EC: C2 = C0) by (unfold C2, prot4_ckc_C2, prot4_ckc_R; rewrite Hs; reflexivity).
       rewrite EC. unfold prot4_ckc_cf. rewrite Hs. entailer!. }
  forward_if.
  { exfalso. discriminate. }
  forward. forward.
  change (data_at_ Tsh (tarray tuchar 16) v_cookie__1) with (data_at Tsh (tarray tuchar 16) (Zrepeat Vundef 16) v_cookie__1).
  destruct Cok as (Lck & Lm1 & Ldk & Lmk). destruct CMok as (Ln & Le).
  rewrite (prot4_ckc_po Tsh (Zrepeat Vundef 16) v_cookie__1 16) by (reflexivity || lia).
  unfold bytes.
  rewrite (prot4_ckc_pb shm (cm_enc M) (field_address t_cmsg (DOT C._encrypted_cookie) m) 32 Le) by lia.
  rewrite (prot4_ckc_pb sh (ck_last_mac1 C0) (field_address t_peer (DOT C._latest_cookie DOT C._last_mac1_sent) p) 16 Lm1)
    by lia.
  unfold wg_consts. Intros. rewrite prot4_ckc_zp.
  forward_call (Tsh, v_cookie__1, Zrepeat Vundef 16, shm, field_address t_cmsg (DOT C._encrypted_cookie) m, cm_enc M,
     sh, field_address t_peer (DOT C._latest_cookie DOT C._last_mac1_sent) p, ck_last_mac1 C0,
     shm, field_address t_cmsg (DOT C._nonce) m, cm_nonce M,
     sh, field_address t_peer (DOT C._latest_cookie DOT C._cookie_decryption_key) p, ck_dkey C0, gv).
  { entailer!. rewrite Le, Lm1. simpl. unfold field_address. rewrite !if_true by auto with field_compatible.
    simpl. rewrite !offset_offset_val. reflexivity. }
  { rewrite Le. reflexivity. }
  forward.
  destruct (xaead_dec (ck_dkey C0) (cm_nonce M) (ck_last_mac1 C0) (cm_enc M)) as [pt|] eqn:Hd.
  - assert (Lpt: Zlength pt = 16) by (apply (xaead_dec_length _ _ HXA) in Hd; lia).
    forward_if.
    2: { exfalso. discriminate. }
    forward.
    rewrite <- (prot4_ckc_po Tsh (map Vubyte pt) v_cookie__1 16) by (rewrite ?Zlength_map; lia).
    sep_apply (data_at_data_at_ sh (tarray tuchar 16) (map Vubyte (ck_cookie C0))
                 (field_address t_peer (DOT C._latest_cookie DOT C._cookie) p)).
    forward_call (sh, Tsh, field_address t_peer (DOT C._latest_cookie DOT C._cookie) p, v_cookie__1, 16, pt).
    forward_call (gv, S, w).
    forward. forward.
    forward. forward.
    forward. forward.
    assert (EC: C2 = mkCookie (s_boot S) true pt false (ck_last_mac1 C0) (ck_dkey C0) (ck_mkey C0))
      by (unfold C2, prot4_ckc_C2, prot4_ckc_R; rewrite Hs, Hd; reflexivity).
    rewrite EC. unfold prot4_ckc_cf, wg_consts, bytes.
    cbn [ck_birth ck_valid ck_cookie ck_sent ck_last_mac1 ck_dkey ck_mkey].
    rewrite <- (prot4_ckc_pb shm (cm_enc M) _ 32 Le) by lia.
    rewrite <- (prot4_ckc_pb sh (ck_last_mac1 C0) _ 16 Lm1) by lia.
    rewrite prot4_ckc_zp.
    sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (map Vubyte pt) v_cookie__1).
    entailer!.
  - forward_if.
    { exfalso. discriminate. }
    forward.
    assert (EC: C2 = C0) by (unfold C2, prot4_ckc_C2, prot4_ckc_R; rewrite Hs, Hd; reflexivity).
    rewrite EC. unfold prot4_ckc_cf, wg_consts, bytes. rewrite Hs.
    rewrite <- (prot4_ckc_pb shm (cm_enc M) _ 32 Le) by lia.
    rewrite <- (prot4_ckc_pb sh (ck_last_mac1 C0) _ 16 Lm1) by lia.
    rewrite <- (prot4_ckc_po Tsh (Zrepeat Vundef 16) v_cookie__1 16) by (reflexivity || lia).
    rewrite prot4_ckc_zp.
    entailer!.
Qed.

End Body.
