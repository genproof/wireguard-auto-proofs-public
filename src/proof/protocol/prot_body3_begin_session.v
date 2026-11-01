(* Body proofs of the protocol piece, group begin_session.
   Target: prot_bodies3_begin_session.  Prove each function's body against its specification (prot_specs3.v) in the
   compspecs of its unit, with the context Gprot3 (prot_prog3.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.
Require Import VST.msl.iter_sepcon.
Require Import WgNoise.proof.protocol.prot3_begin_session_lemmas.
Require WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.protocol.prot3_begin_session_pool.
Require Import WgNoise.proof.protocol.prot3_begin_session_free.
Require Import WgNoise.proof.protocol.prot3_begin_session_hsdisj.

Section BeginSession.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Definition Gn := Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS.

Lemma prot3_begin_session_hs_fc p : field_compatible t_peer [] p -> field_compatible t_hs [] (hs_addr p).
Proof.
  intros FC.
  assert (F: field_compatible t_peer (DOT I._handshake) p) by auto with field_compatible.
  apply field_compatible_nested_field in F.
  exact F.
Qed.

Lemma prot3_begin_session_fold_hs sh h H lk :
  hs_ok H ->
  field_at sh t_hs (DOT I._state) (Vint (hs_state H)) h *
  field_at sh t_hs (DOT I._last_initiation_consumption) (Vlong (hs_lic H)) h *
  field_at sh t_hs (DOT I._static_identity) (hs_sid H) h *
  field_at sh t_hs (DOT I._ephemeral_private) (bytes (hs_eph H)) h *
  field_at sh t_hs (DOT I._remote_static) (bytes (hs_rstatic H)) h *
  field_at sh t_hs (DOT I._remote_ephemeral) (bytes (hs_reph H)) h *
  field_at sh t_hs (DOT I._precomputed_static_static) (bytes (hs_ss H)) h *
  field_at sh t_hs (DOT I._preshared_key) (bytes (hs_psk H)) h *
  field_at sh t_hs (DOT I._hash) (bytes (hs_hash H)) h *
  field_at sh t_hs (DOT I._chaining_key) (bytes (hs_ck H)) h *
  field_at sh t_hs (DOT I._latest_timestamp) (bytes (hs_ts H)) h *
  field_at sh t_hs (DOT I._remote_index) (Vint (hs_rindex H)) h *
  field_at sh t_hs (DOT I._lock) lk h *
  spacer sh 36 40 h * spacer sh 300 304 h |-- hs_rep sh h H.
Proof. intros. unfold hs_rep. Exists lk. entailer!. Qed.

Lemma prot3_begin_session_fold_peer sh p P :
  field_compatible t_peer [] p ->
  field_at sh t_peer (DOT I._device) (p_device P) p *
  field_at sh t_peer (DOT I._is_dead) (Val.of_bool (p_dead P)) p *
  kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
  hs_rep sh (hs_addr p) (p_hs P) *
  field_at sh t_peer (DOT I._last_sent_handshake) (Vlong (p_lsh P)) p *
  cookie_rep sh (cookie_addr p) (p_cookie P) *
  field_at sh t_peer (DOT I._refcount) (Vint (p_refs P)) p *
  field_at sh t_peer (DOT I._internal_id) (Vlong (p_id P)) p *
  field_at sh t_peer (DOT I._pubkey_next) (p_pknext P) p *
  spacer sh 9 16 p * spacer sh 476 480 p |-- peer_rep sh p P.
Proof. intros. unfold peer_rep. entailer!. Qed.

Lemma prot3_begin_session_fold_peer_hs sh p P H' :
  field_compatible t_peer [] p ->
  field_at sh t_peer (DOT I._device) (p_device P) p *
  field_at sh t_peer (DOT I._is_dead) (Val.of_bool (p_dead P)) p *
  kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
  hs_rep sh (hs_addr p) H' *
  field_at sh t_peer (DOT I._last_sent_handshake) (Vlong (p_lsh P)) p *
  cookie_rep sh (cookie_addr p) (p_cookie P) *
  field_at sh t_peer (DOT I._refcount) (Vint (p_refs P)) p *
  field_at sh t_peer (DOT I._internal_id) (Vlong (p_id P)) p *
  field_at sh t_peer (DOT I._pubkey_next) (p_pknext P) p *
  spacer sh 9 16 p * spacer sh 476 480 p |-- peer_rep sh p (p_set_hs P H').
Proof. intros. unfold peer_rep, p_set_hs. simpl. entailer!. Qed.

Local Transparent denote_tc_test_eq.
Lemma prot3_begin_session_tc_null (R: mpred) k :
  isptr k -> (R |-- valid_pointer k) -> R |-- denote_tc_test_eq k (Vlong Int64.zero).
Proof.
  intros Pk VP. destruct k; try contradiction. unfold denote_tc_test_eq. simpl.
  apply andp_right; [apply prop_right; auto|]. apply valid_pointer_weak'. exact VP.
Qed.
Local Opaque denote_tc_test_eq.

Lemma prot3_begin_session_entry_vp sh k E :
  readable_share sh -> entry_out sh k E |-- valid_pointer k.
Proof. intros. unfold entry_out, entry_at. apply data_at_valid_ptr; [auto | simpl; lia]. Qed.

Ltac prot3_begin_session_vp VP :=
  repeat first [ exact VP | simple apply (sepcon_valid_pointer2 _ _ _ VP) | apply sepcon_valid_pointer1 ].

Lemma prot3_begin_session_ck_bytes sh l a :
  Zlength l = 32 -> data_at sh (nested_field_type t_hs (DOT I._chaining_key)) (bytes l) a = bytes_at sh l a.
Proof. intros E. unfold bytes_at. rewrite E. reflexivity. Qed.

Lemma prot3_begin_session_b2s_len key m : Zlength (WgNoise.proof.blake2s.model.blake2s key 32 m) = 32.
Proof.
  unfold WgNoise.proof.blake2s.model.blake2s, WgNoise.proof.blake2s.model.b2s_digest_stream,
    WgNoise.proof.blake2s.model.b2s_out.
  rewrite Zlength_map. reflexivity.
Qed.

Lemma prot3_begin_session_hmac_len key m : Zlength (hmac key m) = 32.
Proof. unfold hmac. cbv zeta. unfold HASH. apply prot3_begin_session_b2s_len. Qed.

Lemma prot3_begin_session_fold_kp k H kc1 now lk2 r2 :
  field_compatible t_kp [] k ->
  @malloc_token CSw Ews (tarray tuchar SIZEOF_KEYPAIR) k *
  field_at Ews t_kp (DOT I._sending)
    (symkey_val (mkSym (if Int.eq (hs_state H) (Int.repr 4) then kdf1 (hs_ck H) [] else kdf2 (hs_ck H) [])
                       now true)) k *
  field_at Ews t_kp (DOT I._sending_counter) (Vlong Int64.zero) k *
  field_at Ews t_kp (DOT I._receiving)
    (symkey_val (mkSym (if Int.eq (hs_state H) (Int.repr 4) then kdf2 (hs_ck H) [] else kdf1 (hs_ck H) [])
                       now true)) k *
  field_at Ews t_kp (DOT I._receiving_counter) (Vlong Int64.zero, (lk2, map Vlong (Zrepeat Int64.zero 128))) k *
  field_at Ews t_kp (DOT I._remote_index) (Vint (hs_rindex H)) k *
  field_at Ews t_kp (DOT I._i_am_the_initiator) (bool2val (Int.eq (hs_state H) (Int.repr 4))) k *
  field_at Ews t_kp (DOT I._refcount) (Vint Int.one) k *
  field_at Ews t_kp (DOT I._rcu) r2 k *
  field_at Ews t_kp (DOT I._internal_id) (Vlong kc1) k *
  spacer Ews 1181 1184 k
  |-- keypair_rep CSw k (kp_new H kc1 now).
Proof.
  intros FC. unfold keypair_rep, kp_new. cbv zeta.
  apply andp_right.
  { apply prop_right. split; [exact FC|]. unfold kp_ok.
    cbn [kp_send kp_recv sk_key kp_backtrack].
    destruct (Int.eq (hs_state H) HS_CONSUMED_RESPONSE); unfold kdf1, kdf2;
      rewrite !prot3_begin_session_hmac_len; split; auto. }
  cbn [kp_send kp_recv kp_scounter kp_rcounter kp_backtrack kp_rindex kp_init kp_refs kp_id].
  unfold HS_CONSUMED_RESPONSE.
  replace (bool2val (Int.eq (hs_state H) (Int.repr 4))) with (Val.of_bool (Int.eq (hs_state H) (Int.repr 4)))
    by (destruct (Int.eq (hs_state H) (Int.repr 4)); reflexivity).
  repeat (rewrite exp_sepcon1 || rewrite exp_sepcon2).
  apply exp_right with r2.
  repeat (rewrite exp_sepcon1 || rewrite exp_sepcon2).
  apply exp_right with lk2. cancel.
Qed.

Definition prot3_begin_session_ok (H: handshake) : bool :=
  orb (Int.eq (hs_state H) HS_CREATED_RESPONSE) (Int.eq (hs_state H) HS_CONSUMED_RESPONSE).

Lemma prot3_begin_session_res_state P p k kc KS T S :
  prot3_begin_session_ok (p_hs P) = false -> bs_res P p k kc KS T S = (false, P, mkKW KS T S, kc).
Proof. intros E. unfold bs_res, begin_session_model. unfold prot3_begin_session_ok in E. rewrite E. reflexivity. Qed.

Lemma prot3_begin_session_res_null P p kc KS T S :
  prot3_begin_session_ok (p_hs P) = true ->
  bs_res P p nullval kc KS T S = (false, P, mkKW KS T (shim_alloc_fail S), kc).
Proof. intros E. unfold bs_res, begin_session_model. unfold prot3_begin_session_ok in E. rewrite E. reflexivity. Qed.

Lemma prot3_begin_session_res_dead P p k kc KS T S :
  prot3_begin_session_ok (p_hs P) = true -> k <> nullval -> p_dead P = true ->
  bs_res P p k kc KS T S =
  (false, p_set_hs P (hs_zero (p_hs P)), mkKW KS T (shim_free (shim_alloc_ok S)), Int64.add kc Int64.one).
Proof.
  intros E Nk Ed. unfold bs_res, begin_session_model. unfold prot3_begin_session_ok in E. rewrite E.
  destruct (eq_dec k nullval); [contradiction|]. cbv zeta. rewrite Ed. reflexivity.
Qed.

Definition prot3_begin_session_A (P: peer) (p k: val) (kc: int64) (KS: list (val * keypair)) (T: tstate) (S: shim) :=
  add_new_keypair_model (p_set_hs P (hs_zero (p_hs P))) k
    (kp_init (kp_new (p_hs P) (Int64.add kc Int64.one) (s_boot S)))
    (mkKW ((k, kp_new (p_hs P) (Int64.add kc Int64.one) (s_boot S)) :: KS)
          (t_add T k Ews (mkEntry p IDX_KEYPAIR Int.zero)) (shim_alloc_ok S)).

Lemma prot3_begin_session_res_alive P p k kc KS T S :
  prot3_begin_session_ok (p_hs P) = true -> k <> nullval -> p_dead P = false -> hs_in_pool T p ->
  bs_res P p k kc KS T S =
  (fst (t_replace (kw_T (snd (prot3_begin_session_A P p k kc KS T S))) (hs_addr p) k),
   fst (prot3_begin_session_A P p k kc KS T S),
   mkKW (kw_KS (snd (prot3_begin_session_A P p k kc KS T S)))
        (snd (t_replace (kw_T (snd (prot3_begin_session_A P p k kc KS T S))) (hs_addr p) k))
        (kw_S (snd (prot3_begin_session_A P p k kc KS T S))),
   Int64.add kc Int64.one).
Proof.
  intros E Nk Ed HP. unfold bs_res, begin_session_model. unfold prot3_begin_session_ok in E. rewrite E.
  destruct (eq_dec k nullval); [contradiction|]. cbv zeta. rewrite Ed.
  rewrite (prot3_begin_session_e_peer_of_hs KS T S p HP).
  unfold prot3_begin_session_A.
  destruct (add_new_keypair_model _ _ _ _) as [P2 W2]. simpl.
  destruct (t_replace (kw_T W2) (hs_addr p) k). reflexivity.
Qed.

Lemma prot3_begin_session_add_device P new init W :
  p_device (fst (add_new_keypair_model P new init W)) = p_device P.
Proof.
  unfold add_new_keypair_model. destruct init; [destruct (negb (eq_dec (p_next P) nullval))|]; reflexivity.
Qed.

Lemma prot3_begin_session_wand_intro (A R P: mpred) : A * R |-- P -> A * R |-- A * (A -* P).
Proof. intros H. apply sepcon_derives; [auto|]. apply wand_sepcon_adjoint. rewrite sepcon_comm. auto. Qed.

Lemma prot3_begin_session_peer_device sh p P :
  peer_rep sh p P |-- field_at sh t_peer (DOT I._device) (p_device P) p *
                      (field_at sh t_peer (DOT I._device) (p_device P) p -* peer_rep sh p P).
Proof.
  unfold peer_rep at 1. Intros. rewrite !sepcon_assoc. apply prot3_begin_session_wand_intro.
  unfold peer_rep. entailer!.
Qed.

Lemma prot3_begin_session_dev_itab sh wg D :
  device_rep sh wg D |-- field_at sh t_dev (DOT I._index_hashtable) (d_itab D) wg *
                         (field_at sh t_dev (DOT I._index_hashtable) (d_itab D) wg -* device_rep sh wg D).
Proof.
  unfold device_rep at 1. Intros.
  rewrite (sepcon_comm _ (@field_at Noise.CS sh t_dev (DOT I._index_hashtable) (d_itab D) wg)).
  apply prot3_begin_session_wand_intro. unfold device_rep. entailer!.
Qed.

Lemma prot3_begin_session_ks_cons k K KS :
  keypair_rep CSw k K * keypairs_rep CSw KS |-- keypairs_rep CSw ((k, K) :: KS).
Proof. unfold keypairs_rep. simpl. cancel. Qed.

(* forward_call's frame step runs VST's change_compspecs on the callee's precondition: it would rewrite the
   kfree_sensitive token @malloc_token CSw into Noise.CS through malloc_token_change_composite with an
   unsolvable change_composite_env CSw Noise.CS (left shelved).  Every predicate here is already at the
   right compspecs: no conversion in this file. *)
Local Ltac change_compspecs cs ::= idtac.

Lemma prot3_begin_session_body :
  @semax_body (QPvarspecs Noise.qp) Gn Noise.CS
    WgNoise.noise.code.f_wg_noise_handshake_begin_session (wg_noise_handshake_begin_session_spec CSw).
Proof.
  start_function.
  forward.
  set (Hh := p_hs P) in *.
  set (b := prot3_begin_session_ok Hh).
  pose proof (prot3_begin_session_hs_fc p H0) as FCH.
  destruct H1 as [E [HE HEP]].
  destruct (prot3_begin_session_t_entry_sfind _ _ _ HE) as [sh0 HE0].
  unfold peer_rep, hs_rep. Intros lk.
  match goal with |- semax _ ?Pre _ _ =>
    forward_loop Pre continue: (EX k: val,
      PROP (s_failnext S = true -> k = nullval; k <> nullval -> ~ In k (saddrs (t_D T)) /\ ~ In k (map fst KS))
      LOCAL (temp I._ret (Val.of_bool (fst (fst (fst (bs_res P p k kc KS T S))))); gvars gv)
      SEP (mem_mgr gv; shim_state gv (kw_S (snd (fst (bs_res P p k kc KS T S))));
           noise_globals gv (snd (bs_res P p k kc KS T S)); wg_consts gv;
           keypairs_rep CSw (kw_KS (snd (fst (bs_res P p k kc KS T S))));
           peer_rep shp p (snd (fst (fst (bs_res P p k kc KS T S))));
           device_rep shd wg D;
           itable sht (d_itab D) (kw_T (snd (fst (bs_res P p k kc KS T S))))))
    break: (EX k: val,
      PROP (s_failnext S = true -> k = nullval; k <> nullval -> ~ In k (saddrs (t_D T)) /\ ~ In k (map fst KS))
      LOCAL (temp I._ret (Val.of_bool (fst (fst (fst (bs_res P p k kc KS T S))))); gvars gv)
      SEP (mem_mgr gv; shim_state gv (kw_S (snd (fst (bs_res P p k kc KS T S))));
           noise_globals gv (snd (bs_res P p k kc KS T S)); wg_consts gv;
           keypairs_rep CSw (kw_KS (snd (fst (bs_res P p k kc KS T S))));
           peer_rep shp p (snd (fst (fst (bs_res P p k kc KS T S))));
           device_rep shd wg D;
           itable sht (d_itab D) (kw_T (snd (fst (bs_res P p k kc KS T S))))))
  end.
  { apply ENTAIL_refl. }
  2: { Intros k. forward. Exists k. entailer!. }
  forward.
  match goal with |- semax _ (PROPx ?Pr (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx Pr (LOCALx (temp I._t'1 (Val.of_bool (negb b)) :: L) (SEPx R)))
  end.
  { forward. forward. entailer!.
    unfold b, Hh, prot3_begin_session_ok, HS_CREATED_RESPONSE, HS_CONSUMED_RESPONSE.
    rewrite Int.eq_false by auto. simpl. destruct (Int.eq (hs_state (p_hs P)) (Int.repr 4)); reflexivity. }
  { forward. entailer!.
    unfold b, Hh, prot3_begin_session_ok, HS_CREATED_RESPONSE. rewrite H5, Int.eq_true. reflexivity. }
  forward_if.
  { (* wrong state *)
    forward. Exists nullval.
    assert (Eb: b = false) by (destruct b; [inversion H5 | reflexivity]).
    rewrite prot3_begin_session_res_state by exact Eb.
    sep_apply (prot3_begin_session_fold_hs shp (hs_addr p) (p_hs P) lk H1).
    sep_apply (prot3_begin_session_fold_peer shp p P H0).
    entailer!. simpl. cancel. }
  2: { Intros k. forward. Exists k. entailer!. destruct (fst (fst (fst (bs_res P (e_peer E) k kc KS T S)))); reflexivity. }
  (* the state is CREATED_RESPONSE or CONSUMED_RESPONSE *)
  assert (Eb: b = true) by (destruct b; [reflexivity | inversion H5]).
  sep_apply (prot3_begin_session_pool_peer sht (d_itab D) T (hs_addr p) sh0 E HE0 FCH). Intros.
  rewrite HEP.
  forward.
  sep_apply (modus_ponens_wand (field_at sh0 t_hs (DOT I._entry DOT I._peer) p (hs_addr p))).
  forward_call (gv, S, kc, p).
  Intros k.
  forward.
  destruct (eq_dec k nullval) as [Ek|Nk].
  { (* the allocation failed *)
    subst k.
    forward_if (PROP (False) LOCAL () SEP ()).
    { forward. Exists nullval.
      rewrite prot3_begin_session_res_null by exact Eb.
      sep_apply (prot3_begin_session_fold_hs shp (hs_addr p) (p_hs P) lk H1).
      sep_apply (prot3_begin_session_fold_peer shp p P H0).
      entailer!. simpl. cancel. }
    { match goal with Hn: ?x <> ?x |- _ => contradiction (Hn eq_refl) end. } }
  Intros.
  set (kc' := Int64.add kc Int64.one).
  set (EK := mkEntry p IDX_KEYPAIR Int.zero).
  assert_PROP (isptr k) as Pk by (unfold entry_out, entry_at; entailer!).
  assert_PROP (~ In k (saddrs (t_D T))) as NkT.
  { sep_apply (prot3_begin_session_pool_add sht (d_itab D) T k EK). entailer!. }
  assert_PROP (~ In k (map fst KS)) as NkK.
  { sep_apply (prot3_begin_session_kp_notin CSw KS k (kp_fresh kc')). entailer!. }
  match goal with |- semax _ (PROPx ?Pr (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx Pr (LOCALx L (SEPx R)))
  end.
  { apply prot3_begin_session_tc_null; [auto|].
    pose proof (prot3_begin_session_entry_vp Ews k EK ltac:(auto)) as VP.
    prot3_begin_session_vp VP. }
  { forward. entailer!. }
  { forward. entailer!. }
  unfold keypair_rep. Intros lk2 r2.
  forward. forward. forward. forward. forward.
  { entailer!. destruct (Int.eq (hs_state (p_hs P)) (Int.repr 4)); simpl; auto. }
  freeze [0;2;3;5;7;8;9;10;11;12;13;14;15;17;18;19;20;21;22;23;24;25;26;27;28;29;31;32;33;34;35;36;37;38;39;40;41;42;43] FR.
  set (init := Int.eq (hs_state (p_hs P)) (Int.repr 4)).
  set (ck := hs_ck (p_hs P)).
  assert (Hck: Zlength ck = 32) by (destruct H1 as [? [? [? [? [? [? [? ?]]]]]]]; auto).
  match goal with |- semax _ (PROPx _ (LOCALx ?L _)) _ _ =>
    forward_if (PROPx [] (LOCALx L
      (SEPx [FRZL FR; shim_state gv (shim_alloc_ok S);
            field_at Ews t_kp (DOT I._sending)
              (symkey_val (mkSym (if init then kdf1 ck [] else kdf2 ck []) (s_boot S) true)) k;
            field_at Ews t_kp (DOT I._receiving)
              (symkey_val (mkSym (if init then kdf2 ck [] else kdf1 ck []) (s_boot S) true)) k;
            wg_consts gv;
            field_at shp t_hs (DOT I._chaining_key) (bytes ck) (hs_addr p)])))
  end.
  { rewrite (field_at_data_at Ews t_kp (DOT I._sending)), (field_at_data_at Ews t_kp (DOT I._receiving)),
      (field_at_data_at shp t_hs (DOT I._chaining_key)).
    sep_apply (data_at_data_at_ Ews (nested_field_type t_kp (DOT I._sending))).
    sep_apply (data_at_data_at_ Ews (nested_field_type t_kp (DOT I._receiving))).
    rewrite (prot3_begin_session_ck_bytes shp ck _ Hck).
    forward_call (gv, shim_alloc_ok S, Ews, field_address t_kp (DOT I._sending) k, Ews,
                  field_address t_kp (DOT I._receiving) k, shp,
                  field_address t_hs (DOT I._chaining_key) (hs_addr p), ck).
    assert (Ei: init = true) by (destruct init; [reflexivity | inversion H10]).
    rewrite Ei. unfold symkey_rep.
    rewrite <- (prot3_begin_session_ck_bytes shp ck _ Hck).
    rewrite (field_at_data_at Ews t_kp (DOT I._sending)), (field_at_data_at Ews t_kp (DOT I._receiving)),
      (field_at_data_at shp t_hs (DOT I._chaining_key)).
    entailer!. }
  { rewrite (field_at_data_at Ews t_kp (DOT I._sending)), (field_at_data_at Ews t_kp (DOT I._receiving)),
      (field_at_data_at shp t_hs (DOT I._chaining_key)).
    sep_apply (data_at_data_at_ Ews (nested_field_type t_kp (DOT I._sending))).
    sep_apply (data_at_data_at_ Ews (nested_field_type t_kp (DOT I._receiving))).
    rewrite (prot3_begin_session_ck_bytes shp ck _ Hck).
    forward_call (gv, shim_alloc_ok S, Ews, field_address t_kp (DOT I._receiving) k, Ews,
                  field_address t_kp (DOT I._sending) k, shp,
                  field_address t_hs (DOT I._chaining_key) (hs_addr p), ck).
    assert (Ei: init = false) by (destruct init; [inversion H10 | reflexivity]).
    rewrite Ei. unfold symkey_rep.
    rewrite <- (prot3_begin_session_ck_bytes shp ck _ Hck).
    rewrite (field_at_data_at Ews t_kp (DOT I._sending)), (field_at_data_at Ews t_kp (DOT I._receiving)),
      (field_at_data_at shp t_hs (DOT I._chaining_key)).
    entailer!. }
  thaw FR.
  sep_apply (prot3_begin_session_fold_hs shp (hs_addr p) (p_hs P) lk H1).
  forward_call (shp, hs_addr p, p_hs P).
  assert (Ep: force_val (sem_sub_pl tschar (hs_addr p) (Vlong (Int64.repr 48))) = field_address t_peer [] p).
  { rewrite field_compatible_field_address by auto.
    assert (Pp: isptr p) by auto with field_compatible.
    destruct p; try contradiction. unfold hs_addr, OFS_PEER_HANDSHAKE. simpl. f_equal.
    rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc.
    unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by rep_lia.
    rewrite Ptrofs.mul_commut, Ptrofs.mul_one, Ptrofs.add_neg_zero, !Ptrofs.add_zero. reflexivity. }
  forward.
  { entailer!. destruct (p_dead P); simpl; auto. }
  unfold kp_fresh. cbn [kp_scounter kp_rcounter kp_backtrack kp_refs kp_id].
  subst init ck.
  sep_apply (prot3_begin_session_fold_kp k (p_hs P) kc' (s_boot S) lk2 r2 H8).
  set (K := kp_new (p_hs P) kc' (s_boot S)).
  destruct (p_dead P) eqn:Ed.
  { forward_if.
    { exfalso. apply Int.one_not_zero. assumption. }
    { (* the peer is dead: the new keypair is freed *)
      sep_apply (prot3_begin_session_kp_free CSw k K EK).
      forward_call (gv, shim_alloc_ok S, k, SIZEOF_KEYPAIR).
      { rewrite if_false by auto.
        rewrite (@WgNoise.proof.libc.libc_bytes.data_at__tarray_tuchar_cs CSw Noise.CS). cancel. }
      rewrite if_false by auto.
      Exists k.
      rewrite (prot3_begin_session_res_dead P p k kc KS T S) by auto.
      replace (Val.of_bool true) with (Val.of_bool (p_dead P)) by (rewrite Ed; auto).
      sep_apply (prot3_begin_session_fold_peer_hs shp p P (hs_zero (p_hs P)) H0).
      entailer!. simpl. unfold kc'. cancel. } }
  (* the peer is alive *)
  assert_PROP (itable_wf T) as WfT by (unfold itable; entailer!).
  assert_PROP (~ In (hs_addr p) (map fst KS)) as NhK.
  { sep_apply (prot3_begin_session_hs_notin CSw KS shp (hs_addr p) (hs_zero (p_hs P)) SH). entailer!. }
  sep_apply (prot3_begin_session_pool_add sht (d_itab D) T k EK). Intros.
  sep_apply (prot3_begin_session_ks_cons k K KS).
  replace (Val.of_bool false) with (Val.of_bool (p_dead P)) by (rewrite Ed; auto).
  sep_apply (prot3_begin_session_fold_peer_hs shp p P (hs_zero (p_hs P)) H0).
  assert (Pp: isptr p) by auto with field_compatible.
  assert (Hha: hs_addr p <> nullval) by (destruct p; try contradiction; discriminate).
  destruct (prot3_begin_session_slots_other P KS (hs_addr p) H3 Hha NhK) as [Nc [Np Nn]].
  destruct (prot3_begin_session_slots_new P KS k H3 Nk NkK) as [Kc [Kp Kn]].
  pose proof (prot3_begin_session_pool_cons T p KS k K H2 NkK) as HP1.
  pose proof (prot3_begin_session_slots_cons P (hs_zero (p_hs P)) KS k K H3) as HS1.
  assert (HF1: afind ((k, K) :: KS) k = Some K) by (simpl; destruct (EqDec_val k k); congruence).
  assert (Hin_h: In (hs_addr p) (saddrs (t_D T))) by exact (prot3_begin_session_sfind_in _ _ _ HE0).
  assert (Nkh: k <> hs_addr p) by (intros Ekh; rewrite Ekh in NkT; contradiction).
  forward_if.
  2: { exfalso. match goal with Hx: typed_false _ (match sem_unary_operation _ _ _ with _ => _ end) |- _ =>
         rewrite Ed in Hx; simpl in Hx; inversion Hx end. }
  forward_call (gv, shim_alloc_ok S, (k, K) :: KS, t_add T k Ews EK, shp, p,
                p_set_hs P (hs_zero (p_hs P)), shd, wg, D, sht, k, K).
  change (add_new_keypair_model (p_set_hs P (hs_zero (p_hs P))) k (kp_init K)
            {| kw_KS := (k, K) :: KS; kw_T := t_add T k Ews EK; kw_S := shim_alloc_ok S |})
    with (prot3_begin_session_A P p k kc KS T S).
  set (A := prot3_begin_session_A P p k kc KS T S).
  set (T2 := kw_T (snd A)).
  pose proof (prot3_begin_session_add_keeps (p_set_hs P (hs_zero (p_hs P))) k (kp_init K)
    (mkKW ((k, K) :: KS) (t_add T k Ews EK) (shim_alloc_ok S)) (hs_addr p) Nc Np Nn) as [HT2h HL2].
  pose proof (prot3_begin_session_add_keeps (p_set_hs P (hs_zero (p_hs P))) k (kp_init K)
    (mkKW ((k, K) :: KS) (t_add T k Ews EK) (shim_alloc_ok S)) k Kc Kp Kn) as [HT2k _].
  change (snd (add_new_keypair_model (p_set_hs P (hs_zero (p_hs P))) k (kp_init K)
    (mkKW ((k, K) :: KS) (t_add T k Ews EK) (shim_alloc_ok S)))) with (snd A) in HT2h, HL2, HT2k.
  fold T2 in HT2h, HL2, HT2k.
  simpl in HT2h, HT2k, HL2.
  destruct (EqDec_val k (hs_addr p)); [contradiction|].
  destruct (EqDec_val k k); [|congruence].
  rewrite HE0 in HT2h.
  sep_apply (prot3_begin_session_pool_peer sht (d_itab D) T2 (hs_addr p) sh0 E HT2h FCH). Intros.
  rewrite HEP.
  forward.
  sep_apply (modus_ponens_wand (field_at sh0 t_hs (DOT I._entry DOT I._peer) p (hs_addr p))).
  assert (HdA: p_device (fst A) = wg)
    by (unfold A, prot3_begin_session_A; rewrite prot3_begin_session_add_device; exact H).
  sep_apply (prot3_begin_session_peer_device shp p (fst A)). rewrite HdA. Intros.
  forward.
  { unfold device_rep. Intros. entailer!. }
  sep_apply (modus_ponens_wand (field_at shp t_peer (DOT I._device) wg p)).
  sep_apply (prot3_begin_session_dev_itab shd wg D). Intros.
  forward.
  { unfold itable. Intros. entailer!. }
  sep_apply (modus_ponens_wand (field_at shd t_dev (DOT I._index_hashtable) (d_itab D) wg)).
  assert (Ih2: In (hs_addr p) (saddrs (t_D T2))) by exact (prot3_begin_session_sfind_in _ _ _ HT2h).
  assert (Ik2: In k (saddrs (t_D T2))) by exact (prot3_begin_session_sfind_in _ _ _ HT2k).
  assert (Nk2: ~ In k (t_L T2))
    by (intros Hk; apply HL2 in Hk; destruct WfT as [_ [Hincl _]]; apply Hincl in Hk; contradiction).
  forward_call (sht, d_itab D, T2, hs_addr p, k).
  forward.
  Exists k.
  rewrite (prot3_begin_session_res_alive P p k kc KS T S Eb Nk Ed (ex_intro _ E (conj HE HEP))).
  fold A. fold T2.
  entailer!.
  - match goal with |- Val.of_bool ?x = bool2val ?x => destruct x; reflexivity end.
  - simpl. unfold kc'. cancel.
Qed.

End BeginSession.

Theorem prot_bodies3_begin_session :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_wg_noise_handshake_begin_session (wg_noise_handshake_begin_session_spec CSw)).
Proof.
  intros. apply prot3_begin_session_body.
Qed.
