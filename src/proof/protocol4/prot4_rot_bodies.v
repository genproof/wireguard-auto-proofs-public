(* the body group noise_rot (keypairs_clear, expire_current_peer_keypairs,
   add_new_keypair, received_with_keypair) against the v4 specifications (prot_specs4.v: exact refcount_t
   warnings, received_with_keypair of NULL or any pool entry) = v3's prot3_noise_rot_{clear,expire,add,recv}.v
   ported.  The v3 helper modules (no specifications in them) are imported BEFORE prot_prog4. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_body3_shim_table1.
Require Import WgNoise.proof.protocol.prot3_noise_rot_lemmas.
Require Import WgNoise.proof.protocol4.prot4_rot_lemmas.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

Section NoiseRot4.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Definition Gn4rot := Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS.

Lemma prot4_rot_body_clear :
  @semax_body (QPvarspecs Noise.qp) Gn4rot Noise.CS
    WgNoise.noise.code.f_wg_noise_keypairs_clear (wg_noise_keypairs_clear_spec CSw).
Proof.
  start_function.
  destruct (prot3_noise_rot_slots _ _ H1) as (Hc & Hp & Hn & Dc & Dp).
  assert_PROP (forall k, In k (map fst KS) -> isptr k) as HKS by (sep_apply prot3_noise_rot_ks_ptrs; entailer!).
  pose proof (prot3_noise_rot_slot_ptr _ _ HKS Hc) as Pc.
  pose proof (prot3_noise_rot_slot_ptr _ _ HKS Hp) as Pp.
  pose proof (prot3_noise_rot_slot_ptr _ _ HKS Hn) as Pn.
  rewrite prot3_noise_rot_peer_split. unfold kps_rep. Intros lk.
  forward. forward.
  forward_call (gv, S, w, KS, T, p_next P, true, shp, p, p_set_slots P (p_cur P) (p_prev P) nullval, shd, wg, D, sht).
  { rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Exists lk. simpl. entailer!. }
  pose proof (prot3_noise_rot_put_in_pool _ _ _ S (p_next P) true H0) as HW1.
  assert (Hp1: p_prev P = nullval \/ In (p_prev P) (map fst (kw_KS (kp_put (p_next P) true (mkKW KS T S))))).
  { destruct (EqDec_val (p_prev P) nullval) as [E|NE]; [left; auto | right].
    destruct Hp as [E|Hin]; [contradiction|]. apply prot3_noise_rot_put_keeps; auto. }
  assert (Hc1: p_cur P = nullval \/ In (p_cur P) (map fst (kw_KS (kp_put (p_next P) true (mkKW KS T S))))).
  { destruct (EqDec_val (p_cur P) nullval) as [E|NE]; [left; auto | right].
    destruct Hc as [E|Hin]; [contradiction|]. apply prot3_noise_rot_put_keeps; auto. apply Dc; auto. }
  set (W0 := mkKW KS T S) in *.
  set (W1 := kp_put (p_next P) true W0) in *.
  set (w1 := kp_put_warn (p_next P) KS w).
  rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Intros lk1.
  simpl p_cur; simpl p_prev; simpl p_next.
  forward. forward.
  forward_call (gv, kw_S W1, w1, kw_KS W1, kw_T W1, p_prev P, true, shp, p, p_set_slots P (p_cur P) nullval nullval, shd, wg, D, sht).
  { rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Exists lk1. simpl. entailer!. }
  pose proof (prot3_noise_rot_put_in_pool _ _ _ (kw_S W1) (p_prev P) true HW1) as HW2.
  assert (Hc2: p_cur P = nullval \/ In (p_cur P) (map fst (kw_KS (kp_put (p_prev P) true (mkKW (kw_KS W1) (kw_T W1) (kw_S W1)))))).
  { destruct (EqDec_val (p_cur P) nullval) as [E|NE]; [left; auto | right].
    destruct Hc1 as [E|Hin]; [contradiction|]. apply prot3_noise_rot_put_keeps; auto. apply Dc; auto. }
  rewrite prot3_noise_rot_kw_eta in HW2, Hc2 |- *.
  set (W2 := kp_put (p_prev P) true W1) in *.
  set (w2 := kp_put_warn (p_prev P) (kw_KS W1) w1).
  rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Intros lk2.
  simpl p_cur; simpl p_prev; simpl p_next.
  forward. forward.
  forward_call (gv, kw_S W2, w2, kw_KS W2, kw_T W2, p_cur P, true, shp, p, p_set_slots P nullval nullval nullval, shd, wg, D, sht).
  { rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Exists lk2. simpl. entailer!. }
  rewrite prot3_noise_rot_kw_eta.
  entailer!.
  all: rewrite prot4_rot_clear_warn; unfold W2, w2, W1, w1, W0; apply derives_refl.
Qed.

Lemma prot4_rot_body_expire :
  @semax_body (QPvarspecs Noise.qp) Gn4rot Noise.CS
    WgNoise.noise.code.f_wg_noise_expire_current_peer_keypairs (wg_noise_expire_current_peer_keypairs_spec CSw).
Proof.
  start_function.
  destruct (prot3_noise_rot_slots _ _ H2) as (Hc & Hp & Hn & Dc & Dp).
  assert_PROP (forall k, In k (map fst KS) -> isptr k) as HKS by (sep_apply prot3_noise_rot_ks_ptrs; entailer!).
  pose proof (prot3_noise_rot_slot_ptr _ _ HKS Hc) as Pc.
  pose proof (prot3_noise_rot_slot_ptr _ _ HKS Hn) as Pn.
  assert_PROP (field_compatible t_peer [] p) as FC by (unfold peer_rep; entailer!).
  forward_call (shp, p, P, shd, wg, D, sht, T).
  rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_lsh. unfold kps_rep. Intros lk.
  forward_call (gv, S, w, shp, field_address t_peer [StructField I._last_sent_handshake] p).
  rewrite (prot3_noise_rot_kps_field _ _ _ FC).
  forward.
  simpl p_cur; simpl p_prev; simpl p_next.
  forward_if (PROP () LOCAL (gvars gv; temp I._peer p)
    SEP (shim_state4 gv S w;
         data_at shp t_atomic64 (Vlong (reset_lsh (s_boot S))) (field_address t_peer (DOT I._last_sent_handshake) p);
         field_at shp t_peer (DOT I._keypairs) (p_cur P, (p_prev P, (p_next P, lk))) p;
         prot3_noise_rot_peer_rest2 shp p (p_set_hs P (hs_zero (p_hs P)));
         device_rep shd wg D; itable sht (d_itab D) (t_remove T (hs_addr p));
         keypairs_rep CSw (prot3_noise_rot_inv KS (p_next P)))).
  { apply prot3_noise_rot_tc_null. destruct Hn as [E|Hin]; [left; auto | right].
    pose proof (prot3_noise_rot_kp_valid sht (d_itab D) (t_remove T (hs_addr p)) p KS _ H1 Hin) as VP.
    split; [apply HKS; auto | prot3_vp VP]. }
  { change (isptr (p_next P)) in H3.
    destruct Hn as [E|Hin]; [rewrite E in H3; contradiction|].
    destruct (prot3_noise_rot_afind_in _ _ Hin) as [K HK].
    rewrite (prot3_noise_rot_ks_split _ _ _ _ HK). unfold keypair_rep at 1. Intros lkr r.
    unfold symkey_val at 1.
    forward.
    unfold prot3_noise_rot_inv. rewrite if_false by (intro E; rewrite E in H3; exact H3). rewrite HK.
    rewrite (prot3_noise_rot_ks_upd _ _ _ _ _ HK). unfold keypair_rep at 1. Exists r lkr.
    entailer!. }
  { change (p_next P = nullval) in H3.
    forward. unfold prot3_noise_rot_inv. rewrite H3, if_true by auto. entailer!. }
  assert (Hc1: p_cur P = nullval \/ In (p_cur P) (map fst (prot3_noise_rot_inv KS (p_next P))))
    by (rewrite prot3_noise_rot_inv_map_fst; auto).
  set (KS1 := prot3_noise_rot_inv KS (p_next P)) in *.
  forward.
  forward_if (PROP () LOCAL (gvars gv; temp I._peer p)
    SEP (shim_state4 gv S w;
         data_at shp t_atomic64 (Vlong (reset_lsh (s_boot S))) (field_address t_peer (DOT I._last_sent_handshake) p);
         field_at shp t_peer (DOT I._keypairs) (p_cur P, (p_prev P, (p_next P, lk))) p;
         prot3_noise_rot_peer_rest2 shp p (p_set_hs P (hs_zero (p_hs P)));
         device_rep shd wg D; itable sht (d_itab D) (t_remove T (hs_addr p));
         keypairs_rep CSw (prot3_noise_rot_inv KS1 (p_cur P)))).
  { apply prot3_noise_rot_tc_null. destruct Hc as [E|Hin]; [left; auto | right].
    pose proof (prot3_noise_rot_kp_valid sht (d_itab D) (t_remove T (hs_addr p)) p KS _ H1 Hin) as VP.
    split; [apply HKS; auto | prot3_vp VP]. }
  { change (isptr (p_cur P)) in H3.
    destruct Hc1 as [E|Hin]; [rewrite E in H3; contradiction|].
    destruct (prot3_noise_rot_afind_in _ _ Hin) as [K HK].
    rewrite (prot3_noise_rot_ks_split _ _ _ _ HK). unfold keypair_rep at 1. Intros lkr r.
    unfold symkey_val at 1.
    forward.
    unfold prot3_noise_rot_inv at 1. rewrite if_false by (intro E; rewrite E in H3; exact H3). rewrite HK.
    rewrite (prot3_noise_rot_ks_upd _ _ _ _ _ HK). unfold keypair_rep at 1. Exists r lkr.
    entailer!. }
  { change (p_cur P = nullval) in H3.
    forward. unfold prot3_noise_rot_inv at 1. rewrite H3, if_true by auto. entailer!. }
  rewrite prot3_noise_rot_expire_KS, prot3_noise_rot_expire_P, prot3_noise_rot_expire_T.
  rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_lsh, prot3_noise_rot_peer_rest2_lsh.
  entailer!. unfold kps_rep. Exists lk. rewrite (prot3_noise_rot_kps_field _ _ _ FC). entailer!.
  unfold KS1. apply derives_refl.
Qed.

Lemma prot4_rot_body_add :
  @semax_body (QPvarspecs Noise.qp) Gn4rot Noise.CS
    WgNoise.noise.code.f_add_new_keypair (add_new_keypair_spec CSw).
Proof.
  start_function.
  destruct (prot3_noise_rot_slots _ _ H1) as (Hc & Hp & Hn & Dc & Dp).
  assert_PROP (forall k, In k (map fst KS) -> isptr k) as HKS by (sep_apply prot3_noise_rot_ks_ptrs; entailer!).
  pose proof (prot3_noise_rot_slot_ptr _ _ HKS Hc) as Pc.
  pose proof (prot3_noise_rot_slot_ptr _ _ HKS Hp) as Pp.
  pose proof (prot3_noise_rot_slot_ptr _ _ HKS Hn) as Pn.
  rewrite prot3_noise_rot_peer_split. unfold kps_rep. Intros lk.
  forward. forward. forward.
  rewrite (prot3_noise_rot_ks_split _ _ _ _ H2), prot3_noise_rot_kp_init_split. Intros.
  forward. { entailer!. destruct (kp_init K); simpl; auto. }
  gather_SEP (field_at Ews t_kp (DOT I._i_am_the_initiator) _ new) (prot3_noise_rot_kp_rest _ new K).
  rewrite <- prot3_noise_rot_kp_init_split.
  gather_SEP (keypair_rep _ new K) (keypairs_rep _ (adel KS new)).
  rewrite <- (prot3_noise_rot_ks_split _ _ _ _ H2).
  destruct (kp_init K) eqn:HI.
  - forward_if.
    2: { exfalso. unfold typed_false in *. simpl in *. discriminate. }
    destruct (EqDec_val (p_next P) nullval) as [En|En].
    + forward_if (PROP () LOCAL (temp I._current_keypair (p_cur P); temp I._next_keypair (p_next P);
             temp I._previous_keypair (p_prev P); gvars gv; temp I._keypairs (kps_addr p); temp I._new_keypair new)
        SEP (keypairs_rep CSw KS; mem_mgr gv; shim_state4 gv S w;
             peer_rep shp p (p_set_slots P (p_cur P) (p_cur P) (p_next P));
             device_rep shd wg D; itable sht (d_itab D) T)).
      { apply prot3_noise_rot_tc_null. left; auto. }
      { change (isptr (p_next P)) in H7. rewrite En in H7. contradiction. }
      { forward. rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Exists lk.
        entailer!. }
      forward_call (gv, S, w, KS, T, p_prev P, true, shp, p, p_set_slots P (p_cur P) (p_cur P) (p_next P), shd, wg, D, sht).
      rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Intros lk1.
      unfold p_set_slots at 1 2 3; cbn [p_cur p_prev p_next].
      forward.
      rewrite (prot3_noise_rot_add_init_null _ _ _ En), (prot4_rot_add_warn_init_null _ _ _ _ En).
      entailer!. rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Exists lk1.
      simpl. entailer!. rewrite En. apply derives_refl.
    + forward_if (PROP () LOCAL (temp I._current_keypair (p_cur P); temp I._next_keypair (p_next P);
             temp I._previous_keypair (p_prev P); gvars gv; temp I._keypairs (kps_addr p); temp I._new_keypair new)
        SEP (keypairs_rep CSw (kw_KS (kp_put (p_cur P) true (mkKW KS T S))); mem_mgr gv;
             shim_state4 gv (kw_S (kp_put (p_cur P) true (mkKW KS T S))) (kp_put_warn (p_cur P) KS w);
             peer_rep shp p (p_set_slots P (p_cur P) (p_next P) nullval);
             device_rep shd wg D; itable sht (d_itab D) (kw_T (kp_put (p_cur P) true (mkKW KS T S))))).
      { apply prot3_noise_rot_tc_null. right. destruct Hn as [E|Hin]; [contradiction|].
        pose proof (prot3_noise_rot_kp_valid sht (d_itab D) T p KS _ H0 Hin) as VP.
        split; [apply HKS; auto | prot3_vp VP]. }
      { forward. forward.
        forward_call (gv, S, w, KS, T, p_cur P, true, shp, p, p_set_slots P (p_cur P) (p_next P) nullval, shd, wg, D, sht).
        { rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Exists lk. simpl. entailer!. }
        entailer!. }
      { change (p_next P = nullval) in H7. contradiction. }
      pose proof (prot3_noise_rot_put_in_pool _ _ _ S (p_cur P) true H0) as HW1.
      assert (Hp1: p_prev P = nullval \/ In (p_prev P) (map fst (kw_KS (kp_put (p_cur P) true (mkKW KS T S))))).
      { destruct (EqDec_val (p_prev P) nullval) as [E|NE]; [left; auto | right].
        destruct Hp as [E|Hin]; [contradiction|]. apply prot3_noise_rot_put_keeps; auto.
        destruct (EqDec_val (p_cur P) nullval) as [Ec|Nc]; [rewrite Ec; auto|]. apply not_eq_sym, Dc; auto. }
      set (W1 := kp_put (p_cur P) true (mkKW KS T S)) in *.
      forward_call (gv, kw_S W1, kp_put_warn (p_cur P) KS w, kw_KS W1, kw_T W1, p_prev P, true, shp, p, p_set_slots P (p_cur P) (p_next P) nullval, shd, wg, D, sht).
      rewrite prot3_noise_rot_kw_eta.
      rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Intros lk1.
      unfold p_set_slots at 1 2 3; cbn [p_cur p_prev p_next].
      forward.
      rewrite (prot3_noise_rot_add_init_next _ _ _ En), (prot4_rot_add_warn_init_next _ _ _ _ En).
      entailer!. rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Exists lk1.
      simpl. entailer!. unfold W1. apply derives_refl.
  - forward_if.
    { exfalso. unfold typed_true in *. simpl in *. discriminate. }
    forward.
    forward_call (gv, S, w, KS, T, p_next P, true, shp, p, p_set_slots P (p_cur P) (p_prev P) new, shd, wg, D, sht).
    { rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Exists lk. simpl. entailer!. }
    pose proof (prot3_noise_rot_put_in_pool _ _ _ S (p_next P) true H0) as HW1.
    assert (Hp1: p_prev P = nullval \/ In (p_prev P) (map fst (kw_KS (kp_put (p_next P) true (mkKW KS T S))))).
    { destruct (EqDec_val (p_prev P) nullval) as [E|NE]; [left; auto | right].
      destruct Hp as [E|Hin]; [contradiction|]. apply prot3_noise_rot_put_keeps; auto. }
    set (W1 := kp_put (p_next P) true (mkKW KS T S)) in *.
    rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Intros lk1.
    unfold p_set_slots at 1 2 3; cbn [p_cur p_prev p_next].
    forward.
    forward_call (gv, kw_S W1, kp_put_warn (p_next P) KS w, kw_KS W1, kw_T W1, p_prev P, true, shp, p, p_set_slots P (p_cur P) nullval new, shd, wg, D, sht).
    { rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Exists lk1. simpl. entailer!. }
    rewrite prot3_noise_rot_kw_eta, prot3_noise_rot_add_resp, prot4_rot_add_warn_resp.
    entailer!. try (unfold W1; apply derives_refl).
Qed.

Lemma prot4_rot_body_recv :
  @semax_body (QPvarspecs Noise.qp) Gn4rot Noise.CS
    WgNoise.noise.code.f_wg_noise_received_with_keypair (wg_noise_received_with_keypair_spec CSw).
Proof.
  start_function.
  destruct (prot3_noise_rot_slots _ _ H1) as (Hc & Hp & Hn & Dc & Dp).
  assert_PROP (forall k, In k (map fst KS) -> isptr k) as HKS by (sep_apply prot3_noise_rot_ks_ptrs; entailer!).
  pose proof (prot3_noise_rot_slot_ptr _ _ HKS Hc) as Pc.
  pose proof (prot3_noise_rot_slot_ptr _ _ HKS Hp) as Pp.
  pose proof (prot3_noise_rot_slot_ptr _ _ HKS Hn) as Pn.
  assert_PROP (k = nullval \/ isptr k) as Pk.
  { destruct H2 as [E|Hin]; [apply prop_right; left; auto|].
    sep_apply (prot4_rot_pool_isptr sht (d_itab D) T k Hin). entailer!. }
  assert (Hk: k = nullval \/ (isptr k /\ In k (saddrs (t_D T)))).
  { destruct H2 as [E|Hin]; [left; auto|]. destruct Pk as [E|Pk]; [left; auto | right; auto]. }
  clear H2.
  rewrite prot3_noise_rot_peer_split. unfold kps_rep. Intros lk.
  forward. forward.
  { entailer!. apply prot4_rot_tc_ptrs.
    - destruct Hk as [E|[Pk' Hin]]; [left; auto | right].
      pose proof (prot3_shim_table1_valid sht (d_itab D) T k Hin) as VK.
      split; [assumption | prot3_vp VK].
    - destruct Hn as [E|Hin]; [left; auto | right].
      pose proof (prot3_noise_rot_kp_valid sht (d_itab D) T p KS _ H0 Hin) as VN.
      split; [apply HKS; auto | prot3_vp VN]. }
  assert (Hn': p_next P = nullval \/ isptr (p_next P)) by (destruct Hn as [E|Hin]; [left; auto | right; apply HKS; auto]).
  rewrite (prot4_rot_cmp_eq _ _ _ Pk Hn').
  destruct (eq_dec k (p_next P)) as [E|NE].
  - forward_if.
    { exfalso. unfold typed_true in *. simpl in *. discriminate. }
    forward.
    forward_if.
    { entailer!. apply prot4_rot_tc_ptrs;
      (destruct Hn as [E'|Hin]; [left; auto | right];
       pose proof (prot3_noise_rot_kp_valid sht (d_itab D) T p KS _ H0 Hin) as VN;
       split; [apply HKS; auto | prot3_vp VN]). }
    { contradiction. }
    forward. forward. forward.
    forward_call (gv, S, w, KS, T, p_prev P, true, shp, p, p_set_slots P (p_cur P) (p_cur P) (p_next P), shd, wg, D, sht).
    { rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Exists lk. simpl. entailer!. }
    rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Intros lk1.
    unfold p_set_slots at 1 2 3; cbn [p_cur p_prev p_next].
    forward. forward. forward.
    rewrite (prot3_noise_rot_recv_eq _ _ _ eq_refl), (prot4_rot_recv_warn_eq _ _ _ _ eq_refl).
    entailer!. rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Exists lk1.
    simpl. entailer!.
  - forward_if.
    { forward. rewrite (prot3_noise_rot_recv_neq _ _ _ NE), (prot4_rot_recv_warn_neq _ _ _ _ NE).
      entailer!. rewrite prot3_noise_rot_peer_split. unfold kps_rep. Exists lk. entailer!. apply derives_refl. }
    { exfalso. match goal with H: Int.zero <> Int.zero |- _ => apply H; reflexivity end. }
Qed.

End NoiseRot4.

(* the group statement of prot_body4_noise_rot.v *)
Theorem prot4_rot_bodies_noise_rot :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_wg_noise_keypairs_clear (wg_noise_keypairs_clear_spec CSw)) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_wg_noise_expire_current_peer_keypairs (wg_noise_expire_current_peer_keypairs_spec CSw)) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_add_new_keypair (add_new_keypair_spec CSw)) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_wg_noise_received_with_keypair (wg_noise_received_with_keypair_spec CSw)).
Proof.
  intros. split; [|split; [|split]].
  - apply prot4_rot_body_clear.
  - apply prot4_rot_body_expire.
  - apply prot4_rot_body_add.
  - apply prot4_rot_body_recv.
Qed.
