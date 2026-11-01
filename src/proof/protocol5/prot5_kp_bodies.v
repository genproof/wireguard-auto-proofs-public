(* The bodies of keypair_free_kref, wg_noise_keypair_put and add_new_keypair against their v5 specifications
   (prot_specs5.v: peer_rep5 / device_rep5), with the context Gprot5.  The scripts are those of v4
   (prot4_kp_bodies.v, prot4_rot_bodies.v); the helper lemmas that mention neither the context nor the peer or
   device representation are v3's and v4's, reused as they are.  The v3 helper modules are imported BEFORE
   prot_prog5, so that the v5 names win. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_body3_shim_table1.
Require Import WgNoise.proof.protocol.prot3_noise_kp_lemmas.
Require Import WgNoise.proof.protocol.prot3_noise_rot_lemmas.
Require Import WgNoise.proof.protocol4.prot4_rot_lemmas.
Require WgNoise.proof.protocol4.prot4_kp_bodies.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require WgNoise.noise.code WgNoise.shim.code.

Module KP4 := WgNoise.proof.protocol4.prot4_kp_bodies.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

(* the v5 peer without its keypair slots (prot3_noise_rot_peer_rest with the fields of peer_rep5) *)
Definition prot5_peer_rest (sh: share) (p: val) (P: peer) : mpred :=
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer [StructField I._device] (p_device P) p *
   field_at sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   hs_rep sh (hs_addr p) (p_hs P) *
   field_at_ sh t_peer [StructField I._last_sent_handshake] p *
   field_at_ sh t_peer [StructField I._latest_cookie] p *
   field_at sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   field_at_ sh t_peer [StructField I._internal_id] p *
   field_at sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma prot5_peer_split sh p P :
  peer_rep5 sh p P =
  kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) * prot5_peer_rest sh p P.
Proof.
  unfold peer_rep5, prot5_peer_rest. apply pred_ext; entailer!; cancel.
Qed.

(* the rest does not depend on the slots *)
Lemma prot5_peer_rest_slots sh p P a b c :
  prot5_peer_rest sh p (p_set_slots P a b c) = prot5_peer_rest sh p P.
Proof. reflexivity. Qed.

Section NoiseKP5.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Definition Gn5kp := Gprot5 x25519 aead_enc aead_dec CSw Noise.CS.

(* kfree_sensitive's token is at CSw: keep forward_call from converting it *)
Local Ltac change_compspecs cs ::= idtac.

Lemma prot5_kp_body_free_kref :
  @semax_body (QPvarspecs Noise.qp) Gn5kp Noise.CS
    WgNoise.noise.code.f_keypair_free_kref (keypair_free_kref_spec CSw).
Proof.
  start_function.
  assert_PROP (field_compatible t_kp [] k) as FC by (unfold keypair_rep; entailer!).
  assert (Hp: isptr k) by (destruct FC; auto).
  forward.
  match goal with |- context [temp I._keypair ?v] => replace v with k end.
  2:{ destruct k; try contradiction. simpl. rewrite KP4.prot4_kp_ofs by rep_lia. reflexivity. }
  rewrite (prot3_noise_kp_open sht (d_itab D) T k Ews E FC H0).
  unfold peer_rep5, device_rep5. Intros.
  forward.
  match goal with |- context [temp I._t'1 ?v] => replace v with p by (rewrite <- H1; reflexivity) end.
  forward. rewrite H.
  forward.
  { unfold prot3_noise_kp_irest. Intros. entailer!. }
  sep_apply (derives_refl' _ _ (eq_sym (prot3_noise_kp_open sht (d_itab D) T k Ews E FC H0))).
  assert (Hin: In k (saddrs (t_D T))) by (eapply prot3_noise_kp_sfind_saddrs; eauto).
  forward_call (sht, d_itab D, T, k, @None (share * entry)).
  { change (prot_specs4.raw_rep k None) with emp. rewrite emp_sepcon. cancel. }
  all: try (change (prot_specs4.raw_ok T k None) with (In k (saddrs (t_D T))); exact Hin).
  change (prot_specs4.raw_rep k None) with emp.
  assert (HE': sfind (t_D (t_remove T k)) k = Some (Ews, E)) by exact H0.
  sep_apply (prot3_noise_kp_pool_free sht (d_itab D) (t_remove T k) k Ews E HE'
               (prot3_shim_table1_vremove_notin' k (t_L T))).
  rewrite KP4.prot4_kp_tfree.
  sep_apply (prot3_noise_kp_whole CSw k K E).
  forward_call (gv, S, w, k).
  { entailer!. }
  unfold peer_rep5, device_rep5. rewrite H. entailer!.
Qed.

Lemma prot5_kp_body_put :
  @semax_body (QPvarspecs Noise.qp) Gn5kp Noise.CS
    WgNoise.noise.code.f_wg_noise_keypair_put (wg_noise_keypair_put_spec CSw).
Proof.
  start_function.
  destruct H1 as [Hk|Hk].
  { subst k. forward_if (PROP (False) LOCAL () SEP ()).
    { forward. }
    { exfalso. apply H1; reflexivity. }
    }
  destruct (prot3_noise_kp_afind_in _ _ Hk) as [K HK].
  destruct (prot3_noise_kp_inpool _ _ _ _ H0 Hk) as (E & HE & HEp).
  assert (Hin: In k (saddrs (t_D T))) by (eapply prot3_noise_kp_sfind_saddrs; eauto).
  unfold keypairs_rep. rewrite (prot3_noise_kp_split _ _ _ _ HK).
  change (keypair_item_rep CSw (k, K)) with (keypair_rep CSw k K).
  rewrite prot3_noise_kp_rc_split.
  assert_PROP (field_compatible t_kp [] k) as FC by (sep_apply prot3_noise_kp_krest_fc; entailer!).
  assert (Hnn: k <> nullval) by (intro; subst k; destruct FC; contradiction).
  assert (EWw: kp_put_warn k KS w = rc_dec_warn (kp_refs K) w).
  { unfold kp_put_warn. rewrite if_false by auto. rewrite HK. reflexivity. }
  forward_if (PROP () LOCAL (gvars gv; temp I._keypair k; temp I._unreference_now (Val.of_bool unref))
    SEP (mem_mgr gv; shim_state4 gv S w; field_at Ews t_kp (DOT I._refcount) (Vint (kp_refs K)) k;
         prot3_noise_kp_krest CSw k K; iter_sepcon (keypair_item_rep CSw) (adel KS k);
         peer_rep5 shp p P; device_rep5 shd wg D; itable sht (d_itab D) T)).
  { apply denote_tc_test_eq_split; [|apply valid_pointer_null].
    pull_left (itable sht (d_itab D) T). repeat apply sepcon_valid_pointer1.
    apply prot3_shim_table1_valid; auto. }
  { contradiction. }
  { forward. entailer!. }
  forward_if (PROP () LOCAL (gvars gv; temp I._keypair k)
    SEP (mem_mgr gv; shim_state4 gv S w; field_at Ews t_kp (DOT I._refcount) (Vint (kp_refs K)) k;
         prot3_noise_kp_krest CSw k K; iter_sepcon (keypair_item_rep CSw) (adel KS k);
         peer_rep5 shp p P; device_rep5 shd wg D;
         itable sht (d_itab D) (if unref then t_remove T k else T))).
  { destruct unref; [| unfold typed_true in H1; simpl in H1; discriminate].
    rewrite (prot3_noise_kp_open sht (d_itab D) T k Ews E FC HE).
    unfold peer_rep5, device_rep5. Intros.
    forward.
    match goal with |- context [temp I._t'2 ?v] => replace v with p by (rewrite <- HEp; reflexivity) end.
    forward. rewrite H.
    forward.
    { unfold prot3_noise_kp_irest. Intros. entailer!. }
    sep_apply (derives_refl' _ _ (eq_sym (prot3_noise_kp_open sht (d_itab D) T k Ews E FC HE))).
    forward_call (sht, d_itab D, T, k, @None (share * entry)).
    { change (prot_specs4.raw_rep k None) with emp. rewrite emp_sepcon. cancel. }
    all: try (change (prot_specs4.raw_ok T k None) with (In k (saddrs (t_D T))); eapply prot3_noise_kp_sfind_saddrs; eauto).
    change (prot_specs4.raw_rep k None) with emp.
    unfold peer_rep5, device_rep5. rewrite H. entailer!. }
  { forward. destruct unref; [unfold typed_false in H1; simpl in H1; discriminate|]. entailer!. }
  set (T1 := if unref then t_remove T k else T).
  assert (HE1: sfind (t_D T1) k = Some (Ews, E)) by (subst T1; destruct unref; exact HE).
  set (r' := rc_sub1 (kp_refs K)).
  set (w' := rc_dec_warn (kp_refs K) w).
  assert (EW: kp_put k unref (mkKW KS T S) =
     if Int.eq r' Int.zero then mkKW (adel KS k) (t_free T1 k) (shim_free S)
     else mkKW (aupd KS k (kp_set_refs K r')) T1 S).
  { unfold kp_put. rewrite if_false by auto. cbn [kw_KS kw_T kw_S]. rewrite HK. reflexivity. }
  forward_loop (PROP () LOCAL (gvars gv; temp I._keypair k)
    SEP (mem_mgr gv; shim_state4 gv S w; field_at Ews t_kp (DOT I._refcount) (Vint (kp_refs K)) k;
         prot3_noise_kp_krest CSw k K; iter_sepcon (keypair_item_rep CSw) (adel KS k);
         peer_rep5 shp p P; device_rep5 shd wg D; itable sht (d_itab D) T1))
    continue: (PROP () LOCAL ()
      SEP (mem_mgr gv; shim_state4 gv (kw_S (kp_put k unref (mkKW KS T S))) w';
           keypairs_rep CSw (kw_KS (kp_put k unref (mkKW KS T S)));
           peer_rep5 shp p P; device_rep5 shd wg D; itable sht (d_itab D) (kw_T (kp_put k unref (mkKW KS T S)))))
    break: (PROP () LOCAL ()
      SEP (mem_mgr gv; shim_state4 gv (kw_S (kp_put k unref (mkKW KS T S))) w';
           keypairs_rep CSw (kw_KS (kp_put k unref (mkKW KS T S)));
           peer_rep5 shp p P; device_rep5 shd wg D; itable sht (d_itab D) (kw_T (kp_put k unref (mkKW KS T S))))).
  { entailer!. }
  pose proof (KP4.prot4_kp_fc_rc k FC) as FCr.
  rewrite KP4.prot4_kp_rc_uint.
  unfold shim_state4. Intros.
  forward_call (gv, w, Ews, field_address t_kp (DOT I._refcount DOT I._refcount) k, kp_refs K).
  rewrite <- KP4.prot4_kp_rc_uint. fold r'. fold w'.
  sep_apply (KP4.prot4_kp_fold_shim gv S w').
  forward_if.
  { change (Int.repr 0) with Int.zero in *.
    repeat match goal with Hx: context [rc_sub1 (kp_refs K)] |- _ => fold r' in Hx end. fold r'.
    destruct (Int.eq r' Int.zero) eqn:Hz; [| unfold typed_true in *; simpl in *; discriminate].
    rewrite <- (prot3_noise_kp_krest_refs CSw k K r').
    sep_apply (derives_refl' _ _ (eq_sym (prot3_noise_kp_rc_split CSw k (kp_set_refs K r')))).
    forward_call (gv, S, w', k, kp_set_refs K r', E, shp, p, P, shd, wg, D, sht, T1).
    rewrite EW. cbn [kw_S kw_KS kw_T].
    unfold keypairs_rep. entailer!. }
  { change (Int.repr 0) with Int.zero in *.
    repeat match goal with Hx: context [rc_sub1 (kp_refs K)] |- _ => fold r' in Hx end. fold r'.
    destruct (Int.eq r' Int.zero) eqn:Hz; [unfold typed_false in *; simpl in *; discriminate |].
    forward. rewrite EW. cbn [kw_S kw_KS kw_T].
    unfold keypairs_rep. rewrite (prot3_noise_kp_upd _ _ K _ _ HK).
    change (keypair_item_rep CSw (k, kp_set_refs K r')) with (keypair_rep CSw k (kp_set_refs K r')).
    rewrite prot3_noise_kp_rc_split, prot3_noise_kp_krest_refs.
    change (kp_refs (kp_set_refs K r')) with r'. entailer!. }
  forward. entailer!.
  unfold POSTCONDITION, abbreviate. simpl RA_normal. rewrite EWw. unfold stackframe_of; simpl. intro rho.
  unfold PROPx, LOCALx, SEPx, local, lift1, liftx, lift; simpl. rewrite sepcon_emp. entailer!.
  all: unfold w'; apply derives_refl.
Qed.

Lemma prot5_kp_body_add :
  @semax_body (QPvarspecs Noise.qp) Gn5kp Noise.CS
    WgNoise.noise.code.f_add_new_keypair (add_new_keypair_spec CSw).
Proof.
  start_function.
  destruct (prot3_noise_rot_slots _ _ H1) as (Hc & Hp & Hn & Dc & Dp).
  assert_PROP (forall k, In k (map fst KS) -> isptr k) as HKS by (sep_apply prot3_noise_rot_ks_ptrs; entailer!).
  pose proof (prot3_noise_rot_slot_ptr _ _ HKS Hc) as Pc.
  pose proof (prot3_noise_rot_slot_ptr _ _ HKS Hp) as Pp.
  pose proof (prot3_noise_rot_slot_ptr _ _ HKS Hn) as Pn.
  rewrite prot5_peer_split. unfold kps_rep. Intros lk.
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
             peer_rep5 shp p (p_set_slots P (p_cur P) (p_cur P) (p_next P));
             device_rep5 shd wg D; itable sht (d_itab D) T)).
      { apply prot3_noise_rot_tc_null. left; auto. }
      { change (isptr (p_next P)) in H7. rewrite En in H7. contradiction. }
      { forward. rewrite prot5_peer_split, prot5_peer_rest_slots. unfold kps_rep. Exists lk.
        entailer!. }
      forward_call (gv, S, w, KS, T, p_prev P, true, shp, p, p_set_slots P (p_cur P) (p_cur P) (p_next P), shd, wg, D, sht).
      rewrite prot5_peer_split, prot5_peer_rest_slots. unfold kps_rep. Intros lk1.
      unfold p_set_slots at 1 2 3; cbn [p_cur p_prev p_next].
      forward.
      rewrite (prot3_noise_rot_add_init_null _ _ _ En), (prot4_rot_add_warn_init_null _ _ _ _ En).
      entailer!. rewrite prot5_peer_split, prot5_peer_rest_slots. unfold kps_rep. Exists lk1.
      simpl. entailer!. rewrite En. apply derives_refl.
    + forward_if (PROP () LOCAL (temp I._current_keypair (p_cur P); temp I._next_keypair (p_next P);
             temp I._previous_keypair (p_prev P); gvars gv; temp I._keypairs (kps_addr p); temp I._new_keypair new)
        SEP (keypairs_rep CSw (kw_KS (kp_put (p_cur P) true (mkKW KS T S))); mem_mgr gv;
             shim_state4 gv (kw_S (kp_put (p_cur P) true (mkKW KS T S))) (kp_put_warn (p_cur P) KS w);
             peer_rep5 shp p (p_set_slots P (p_cur P) (p_next P) nullval);
             device_rep5 shd wg D; itable sht (d_itab D) (kw_T (kp_put (p_cur P) true (mkKW KS T S))))).
      { apply prot3_noise_rot_tc_null. right. destruct Hn as [E|Hin]; [contradiction|].
        pose proof (prot3_noise_rot_kp_valid sht (d_itab D) T p KS _ H0 Hin) as VP.
        split; [apply HKS; auto | prot3_vp VP]. }
      { forward. forward.
        forward_call (gv, S, w, KS, T, p_cur P, true, shp, p, p_set_slots P (p_cur P) (p_next P) nullval, shd, wg, D, sht).
        { rewrite prot5_peer_split, prot5_peer_rest_slots. unfold kps_rep. Exists lk. simpl. entailer!. }
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
      rewrite prot5_peer_split, prot5_peer_rest_slots. unfold kps_rep. Intros lk1.
      unfold p_set_slots at 1 2 3; cbn [p_cur p_prev p_next].
      forward.
      rewrite (prot3_noise_rot_add_init_next _ _ _ En), (prot4_rot_add_warn_init_next _ _ _ _ En).
      entailer!. rewrite prot5_peer_split, prot5_peer_rest_slots. unfold kps_rep. Exists lk1.
      simpl. entailer!. unfold W1. apply derives_refl.
  - forward_if.
    { exfalso. unfold typed_true in *. simpl in *. discriminate. }
    forward.
    forward_call (gv, S, w, KS, T, p_next P, true, shp, p, p_set_slots P (p_cur P) (p_prev P) new, shd, wg, D, sht).
    { rewrite prot5_peer_split, prot5_peer_rest_slots. unfold kps_rep. Exists lk. simpl. entailer!. }
    pose proof (prot3_noise_rot_put_in_pool _ _ _ S (p_next P) true H0) as HW1.
    assert (Hp1: p_prev P = nullval \/ In (p_prev P) (map fst (kw_KS (kp_put (p_next P) true (mkKW KS T S))))).
    { destruct (EqDec_val (p_prev P) nullval) as [E|NE]; [left; auto | right].
      destruct Hp as [E|Hin]; [contradiction|]. apply prot3_noise_rot_put_keeps; auto. }
    set (W1 := kp_put (p_next P) true (mkKW KS T S)) in *.
    rewrite prot5_peer_split, prot5_peer_rest_slots. unfold kps_rep. Intros lk1.
    unfold p_set_slots at 1 2 3; cbn [p_cur p_prev p_next].
    forward.
    forward_call (gv, kw_S W1, kp_put_warn (p_next P) KS w, kw_KS W1, kw_T W1, p_prev P, true, shp, p, p_set_slots P (p_cur P) nullval new, shd, wg, D, sht).
    { rewrite prot5_peer_split, prot5_peer_rest_slots. unfold kps_rep. Exists lk1. simpl. entailer!. }
    rewrite prot3_noise_rot_kw_eta, prot3_noise_rot_add_resp, prot4_rot_add_warn_resp.
    entailer!. try (unfold W1; apply derives_refl).
Qed.

End NoiseKP5.
