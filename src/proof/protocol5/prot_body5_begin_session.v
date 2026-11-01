(* The bodies of the protocol piece v5, group `begin_session`: wg_noise_handshake_begin_session; port of prot4_bs_body.v (peer_rep5, device_rep5).
   Each function against its v5 specification (prot_specs5.v) in its unit's compspecs, with the context
   Gprot5 (prot_prog5.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import VST.msl.iter_sepcon.
Require Import WgNoise.proof.protocol.prot3_begin_session_lemmas.
Require WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.protocol.prot3_begin_session_pool.
Require Import WgNoise.proof.protocol.prot3_begin_session_free.
Require Import WgNoise.proof.protocol.prot3_begin_session_hsdisj.
Require Import WgNoise.proof.protocol4.prot4_bs_body.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require WgNoise.noise.code WgNoise.shim.code.


Section BeginSession5.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Definition Gn5 := Gprot5 x25519 aead_enc aead_dec CSw Noise.CS.

(* v4's folding lemmas of peer_rep, for peer_rep5 (last_sent_handshake, latest_cookie and internal_id any) *)
Lemma prot5_bs_fold_peer sh p P :
  field_compatible t_peer [] p ->
  field_at sh t_peer (DOT I._device) (p_device P) p *
  field_at sh t_peer (DOT I._is_dead) (Val.of_bool (p_dead P)) p *
  kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
  hs_rep sh (hs_addr p) (p_hs P) *
  field_at_ sh t_peer (DOT I._last_sent_handshake) p *
  field_at_ sh t_peer (DOT I._latest_cookie) p *
  field_at sh t_peer (DOT I._refcount) (Vint (p_refs P)) p *
  field_at_ sh t_peer (DOT I._internal_id) p *
  field_at sh t_peer (DOT I._pubkey_next) (p_pknext P) p *
  spacer sh 9 16 p * spacer sh 476 480 p |-- peer_rep5 sh p P.
Proof. intros. unfold peer_rep5. entailer!. Qed.

(* the same with the handshake replaced by H' *)
Lemma prot5_bs_fold_peer_hs sh p P H' :
  field_compatible t_peer [] p ->
  field_at sh t_peer (DOT I._device) (p_device P) p *
  field_at sh t_peer (DOT I._is_dead) (Val.of_bool (p_dead P)) p *
  kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
  hs_rep sh (hs_addr p) H' *
  field_at_ sh t_peer (DOT I._last_sent_handshake) p *
  field_at_ sh t_peer (DOT I._latest_cookie) p *
  field_at sh t_peer (DOT I._refcount) (Vint (p_refs P)) p *
  field_at_ sh t_peer (DOT I._internal_id) p *
  field_at sh t_peer (DOT I._pubkey_next) (p_pknext P) p *
  spacer sh 9 16 p * spacer sh 476 480 p |-- peer_rep5 sh p (p_set_hs P H').
Proof. intros. unfold peer_rep5, p_set_hs. simpl. entailer!. Qed.

Ltac prot5_bs_vp VP :=
  repeat first [ exact VP | simple apply (sepcon_valid_pointer2 _ _ _ VP) | apply sepcon_valid_pointer1 ].

(* the peer's device pointer, borrowed from peer_rep5 *)
Lemma prot5_bs_peer_device sh p P :
  peer_rep5 sh p P |-- field_at sh t_peer (DOT I._device) (p_device P) p *
                       (field_at sh t_peer (DOT I._device) (p_device P) p -* peer_rep5 sh p P).
Proof.
  unfold peer_rep5 at 1. Intros. rewrite !sepcon_assoc. apply prot4_bs_wand_intro.
  unfold peer_rep5. entailer!.
Qed.

(* the device's index table pointer, borrowed from device_rep5 *)
Lemma prot5_bs_dev_itab sh wg D :
  device_rep5 sh wg D |-- field_at sh t_dev (DOT I._index_hashtable) (d_itab D) wg *
                          (field_at sh t_dev (DOT I._index_hashtable) (d_itab D) wg -* device_rep5 sh wg D).
Proof.
  unfold device_rep5 at 1. Intros.
  rewrite (sepcon_comm _ (@field_at Noise.CS sh t_dev (DOT I._index_hashtable) (d_itab D) wg)).
  apply prot4_bs_wand_intro. unfold device_rep5. entailer!.
Qed.

(* as in v4: every predicate is already at the right compspecs, no conversion by forward_call *)
Local Ltac change_compspecs cs ::= idtac.

Lemma prot5_bs_body :
  @semax_body (QPvarspecs Noise.qp) Gn5 Noise.CS
    WgNoise.noise.code.f_wg_noise_handshake_begin_session (wg_noise_handshake_begin_session_spec CSw).
Proof.
  start_function.
  forward.
  set (Hh := p_hs P) in *.
  set (b := prot4_bs_ok Hh).
  pose proof (prot4_bs_hs_fc p H0) as FCH.
  destruct H1 as [E [HE HEP]].
  destruct (prot3_begin_session_t_entry_sfind _ _ _ HE) as [sh0 HE0].
  unfold peer_rep5, hs_rep. Intros lk.
  match goal with |- semax _ ?Pre _ _ =>
    forward_loop Pre continue: (EX k: val,
      PROP (s_failnext S = true -> k = nullval; k <> nullval -> ~ In k (saddrs (t_D T)) /\ ~ In k (map fst KS))
      LOCAL (temp I._ret (Val.of_bool (fst (fst (fst (bs_res P p k kc KS T S))))); gvars gv)
      SEP (mem_mgr gv; shim_state4 gv (kw_S (snd (fst (bs_res P p k kc KS T S)))) (begin_session_warn P (hs_addr p) k kc (mkKW KS T S) w);
           noise_globals gv (snd (bs_res P p k kc KS T S)); wg_consts5 gv;
           keypairs_rep CSw (kw_KS (snd (fst (bs_res P p k kc KS T S))));
           peer_rep5 shp p (snd (fst (fst (bs_res P p k kc KS T S))));
           device_rep5 shd wg D;
           itable sht (d_itab D) (kw_T (snd (fst (bs_res P p k kc KS T S))))))
    break: (EX k: val,
      PROP (s_failnext S = true -> k = nullval; k <> nullval -> ~ In k (saddrs (t_D T)) /\ ~ In k (map fst KS))
      LOCAL (temp I._ret (Val.of_bool (fst (fst (fst (bs_res P p k kc KS T S))))); gvars gv)
      SEP (mem_mgr gv; shim_state4 gv (kw_S (snd (fst (bs_res P p k kc KS T S)))) (begin_session_warn P (hs_addr p) k kc (mkKW KS T S) w);
           noise_globals gv (snd (bs_res P p k kc KS T S)); wg_consts5 gv;
           keypairs_rep CSw (kw_KS (snd (fst (bs_res P p k kc KS T S))));
           peer_rep5 shp p (snd (fst (fst (bs_res P p k kc KS T S))));
           device_rep5 shd wg D;
           itable sht (d_itab D) (kw_T (snd (fst (bs_res P p k kc KS T S))))))
  end.
  { apply ENTAIL_refl. }
  2: { Intros k. forward. Exists k. entailer!. }
  forward.
  match goal with |- semax _ (PROPx ?Pr (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx Pr (LOCALx (temp I._t'1 (Val.of_bool (negb b)) :: L) (SEPx R)))
  end.
  { forward. forward. entailer!.
    unfold b, Hh, prot4_bs_ok, HS_CREATED_RESPONSE, HS_CONSUMED_RESPONSE.
    rewrite Int.eq_false by auto. simpl. destruct (Int.eq (hs_state (p_hs P)) (Int.repr 4)); reflexivity. }
  { forward. entailer!.
    unfold b, Hh, prot4_bs_ok, HS_CREATED_RESPONSE. rewrite H4, Int.eq_true. reflexivity. }
  forward_if.
  { (* wrong state *)
    forward. Exists nullval.
    assert (Eb: b = false) by (destruct b; [inversion H4 | reflexivity]).
    unfold bs_res. rewrite prot4_bs_res_state by exact Eb.
    rewrite prot4_bs_warn_state by exact Eb.
    sep_apply (prot4_bs_fold_hs shp (hs_addr p) (p_hs P) lk H1).
    sep_apply (prot5_bs_fold_peer shp p P H0).
    entailer!. simpl. cancel. }
  2: { Intros k. forward. Exists k. entailer!. destruct (fst (fst (fst (bs_res P (e_peer E) k kc KS T S)))); reflexivity. }
  (* the state is CREATED_RESPONSE or CONSUMED_RESPONSE *)
  assert (Eb: b = true) by (destruct b; [reflexivity | inversion H4]).
  sep_apply (prot3_begin_session_pool_peer sht (d_itab D) T (hs_addr p) sh0 E HE0 FCH). Intros.
  rewrite HEP.
  forward.
  sep_apply (modus_ponens_wand (field_at sh0 t_hs (DOT I._entry DOT I._peer) p (hs_addr p))).
  forward_call (gv, S, w, kc, p).
  Intros k.
  forward.
  destruct (eq_dec k nullval) as [Ek|Nk].
  { (* the allocation failed *)
    subst k.
    forward_if (PROP (False) LOCAL () SEP ()).
    { forward. Exists nullval.
      unfold bs_res. rewrite prot4_bs_res_null by exact Eb.
      rewrite prot4_bs_warn_null.
      sep_apply (prot4_bs_fold_hs shp (hs_addr p) (p_hs P) lk H1).
      sep_apply (prot5_bs_fold_peer shp p P H0).
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
  { apply prot4_bs_tc_null; [auto|].
    pose proof (prot4_bs_entry_vp Ews k EK ltac:(auto)) as VP.
    prot5_bs_vp VP. }
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
      (SEPx [FRZL FR; shim_state4 gv (shim_alloc_ok S) w;
            field_at Ews t_kp (DOT I._sending)
              (symkey_val (mkSym (if init then kdf1 ck [] else kdf2 ck []) (s_boot S) true)) k;
            field_at Ews t_kp (DOT I._receiving)
              (symkey_val (mkSym (if init then kdf2 ck [] else kdf1 ck []) (s_boot S) true)) k;
            wg_consts5 gv;
            field_at shp t_hs (DOT I._chaining_key) (bytes ck) (hs_addr p)])))
  end.
  { rewrite (field_at_data_at Ews t_kp (DOT I._sending)), (field_at_data_at Ews t_kp (DOT I._receiving)),
      (field_at_data_at shp t_hs (DOT I._chaining_key)).
    sep_apply (data_at_data_at_ Ews (nested_field_type t_kp (DOT I._sending))).
    sep_apply (data_at_data_at_ Ews (nested_field_type t_kp (DOT I._receiving))).
    rewrite (prot4_bs_ck_bytes shp ck _ Hck).
    forward_call (gv, shim_alloc_ok S, w, Ews, field_address t_kp (DOT I._sending) k, Ews,
                  field_address t_kp (DOT I._receiving) k, shp,
                  field_address t_hs (DOT I._chaining_key) (hs_addr p), ck).
    assert (Ei: init = true) by (destruct init; [reflexivity | inversion H9]).
    rewrite Ei. unfold symkey_rep.
    rewrite <- (prot4_bs_ck_bytes shp ck _ Hck).
    rewrite (field_at_data_at Ews t_kp (DOT I._sending)), (field_at_data_at Ews t_kp (DOT I._receiving)),
      (field_at_data_at shp t_hs (DOT I._chaining_key)).
    entailer!. }
  { rewrite (field_at_data_at Ews t_kp (DOT I._sending)), (field_at_data_at Ews t_kp (DOT I._receiving)),
      (field_at_data_at shp t_hs (DOT I._chaining_key)).
    sep_apply (data_at_data_at_ Ews (nested_field_type t_kp (DOT I._sending))).
    sep_apply (data_at_data_at_ Ews (nested_field_type t_kp (DOT I._receiving))).
    rewrite (prot4_bs_ck_bytes shp ck _ Hck).
    forward_call (gv, shim_alloc_ok S, w, Ews, field_address t_kp (DOT I._receiving) k, Ews,
                  field_address t_kp (DOT I._sending) k, shp,
                  field_address t_hs (DOT I._chaining_key) (hs_addr p), ck).
    assert (Ei: init = false) by (destruct init; [inversion H9 | reflexivity]).
    rewrite Ei. unfold symkey_rep.
    rewrite <- (prot4_bs_ck_bytes shp ck _ Hck).
    rewrite (field_at_data_at Ews t_kp (DOT I._sending)), (field_at_data_at Ews t_kp (DOT I._receiving)),
      (field_at_data_at shp t_hs (DOT I._chaining_key)).
    entailer!. }
  thaw FR.
  sep_apply (prot4_bs_fold_hs shp (hs_addr p) (p_hs P) lk H1).
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
  sep_apply (prot4_bs_fold_kp CSw k (p_hs P) kc' (s_boot S) lk2 r2 H7).
  set (K := kp_new (p_hs P) kc' (s_boot S)).
  destruct (p_dead P) eqn:Ed.
  { forward_if.
    { exfalso. apply Int.one_not_zero. assumption. }
    { (* the peer is dead: the new keypair is freed *)
      sep_apply (prot3_begin_session_kp_free CSw k K EK).
      forward_call (gv, shim_alloc_ok S, w, k, SIZEOF_KEYPAIR).
      { rewrite if_false by auto.
        rewrite (@WgNoise.proof.libc.libc_bytes.data_at__tarray_tuchar_cs CSw Noise.CS). cancel. }
      rewrite if_false by auto.
      Exists k.
      unfold bs_res. rewrite (prot4_bs_res_dead P p k kc KS T S) by auto.
      rewrite (prot4_bs_warn_dead P (hs_addr p) k kc (mkKW KS T S) w) by auto.
      replace (Val.of_bool true) with (Val.of_bool (p_dead P)) by (rewrite Ed; auto).
      sep_apply (prot5_bs_fold_peer_hs shp p P (hs_zero (p_hs P)) H0).
      entailer!. simpl. unfold kc'. cancel. } }
  (* the peer is alive *)
  assert_PROP (itable_wf T) as WfT by (unfold itable; entailer!).
  assert_PROP (~ In (hs_addr p) (map fst KS)) as NhK.
  { sep_apply (prot3_begin_session_hs_notin CSw KS shp (hs_addr p) (hs_zero (p_hs P)) SH). entailer!. }
  sep_apply (prot3_begin_session_pool_add sht (d_itab D) T k EK). Intros.
  sep_apply (prot4_bs_ks_cons CSw k K KS).
  replace (Val.of_bool false) with (Val.of_bool (p_dead P)) by (rewrite Ed; auto).
  sep_apply (prot5_bs_fold_peer_hs shp p P (hs_zero (p_hs P)) H0).
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
  forward_call (gv, shim_alloc_ok S, w, (k, K) :: KS, t_add T k Ews EK, shp, p,
                p_set_hs P (hs_zero (p_hs P)), shd, wg, D, sht, k, K).
  change (add_new_keypair_model (p_set_hs P (hs_zero (p_hs P))) k (kp_init K)
            {| kw_KS := (k, K) :: KS; kw_T := t_add T k Ews EK; kw_S := shim_alloc_ok S |})
    with (prot4_bs_A P p k kc KS T S).
  set (A := prot4_bs_A P p k kc KS T S).
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
    by (unfold A, prot4_bs_A; rewrite prot4_bs_add_device; exact H).
  sep_apply (prot5_bs_peer_device shp p (fst A)). rewrite HdA. Intros.
  forward.
  { unfold device_rep5. Intros. entailer!. }
  sep_apply (modus_ponens_wand (field_at shp t_peer (DOT I._device) wg p)).
  sep_apply (prot5_bs_dev_itab shd wg D). Intros.
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
  unfold bs_res. rewrite (prot4_bs_res_alive P p k kc KS T S Eb Nk Ed (ex_intro _ E (conj HE HEP))).
  rewrite (prot4_bs_warn_alive P p k kc KS T S w Eb Nk Ed (ex_intro _ E (conj HE HEP))).
  fold A. fold T2.
  entailer!.
  - match goal with |- Val.of_bool ?x = bool2val ?x => destruct x; reflexivity end.
  - simpl. unfold kc'. cancel. apply derives_refl.
Qed.

End BeginSession5.

Theorem prot_bodies5_begin_session :
  forall x25519 aead_enc aead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_wg_noise_handshake_begin_session (wg_noise_handshake_begin_session_spec CSw).
Proof.
  intros. apply prot5_bs_body.
Qed.
