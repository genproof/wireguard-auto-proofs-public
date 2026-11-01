(* Group noise_rot: the body of add_new_keypair. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.protocol.prot3_noise_rot_lemmas.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

Section NoiseRotAdd.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Definition Gn_rot_add := Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS.

Lemma prot3_noise_rot_body_add :
  @semax_body (QPvarspecs Noise.qp) Gn_rot_add Noise.CS
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
        SEP (keypairs_rep CSw KS; mem_mgr gv; shim_state gv S;
             peer_rep shp p (p_set_slots P (p_cur P) (p_cur P) (p_next P));
             device_rep shd wg D; itable sht (d_itab D) T)).
      { apply prot3_noise_rot_tc_null. left; auto. }
      { change (isptr (p_next P)) in H7. rewrite En in H7. contradiction. }
      { forward. rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Exists lk.
        entailer!. }
      forward_call (gv, S, KS, T, p_prev P, true, shp, p, p_set_slots P (p_cur P) (p_cur P) (p_next P), shd, wg, D, sht).
      rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Intros lk1.
      unfold p_set_slots at 1 2 3; cbn [p_cur p_prev p_next].
      forward.
      rewrite (prot3_noise_rot_add_init_null _ _ _ En).
      entailer!. rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Exists lk1.
      simpl. entailer!. rewrite En. apply derives_refl.
    + forward_if (PROP () LOCAL (temp I._current_keypair (p_cur P); temp I._next_keypair (p_next P);
             temp I._previous_keypair (p_prev P); gvars gv; temp I._keypairs (kps_addr p); temp I._new_keypair new)
        SEP (keypairs_rep CSw (kw_KS (kp_put (p_cur P) true (mkKW KS T S))); mem_mgr gv;
             shim_state gv (kw_S (kp_put (p_cur P) true (mkKW KS T S)));
             peer_rep shp p (p_set_slots P (p_cur P) (p_next P) nullval);
             device_rep shd wg D; itable sht (d_itab D) (kw_T (kp_put (p_cur P) true (mkKW KS T S))))).
      { apply prot3_noise_rot_tc_null. right. destruct Hn as [E|Hin]; [contradiction|].
        pose proof (prot3_noise_rot_kp_valid sht (d_itab D) T p KS _ H0 Hin) as VP.
        split; [apply HKS; auto | prot3_vp VP]. }
      { forward. forward.
        forward_call (gv, S, KS, T, p_cur P, true, shp, p, p_set_slots P (p_cur P) (p_next P) nullval, shd, wg, D, sht).
        { rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Exists lk. simpl. entailer!. }
        entailer!. }
      { change (p_next P = nullval) in H7. contradiction. }
      pose proof (prot3_noise_rot_put_in_pool _ _ _ S (p_cur P) true H0) as HW1.
      assert (Hp1: p_prev P = nullval \/ In (p_prev P) (map fst (kw_KS (kp_put (p_cur P) true (mkKW KS T S))))).
      { destruct (EqDec_val (p_prev P) nullval) as [E|NE]; [left; auto | right].
        destruct Hp as [E|Hin]; [contradiction|]. apply prot3_noise_rot_put_keeps; auto.
        destruct (EqDec_val (p_cur P) nullval) as [Ec|Nc]; [rewrite Ec; auto|]. apply not_eq_sym, Dc; auto. }
      set (W1 := kp_put (p_cur P) true (mkKW KS T S)) in *.
      forward_call (gv, kw_S W1, kw_KS W1, kw_T W1, p_prev P, true, shp, p, p_set_slots P (p_cur P) (p_next P) nullval, shd, wg, D, sht).
      rewrite prot3_noise_rot_kw_eta.
      rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Intros lk1.
      unfold p_set_slots at 1 2 3; cbn [p_cur p_prev p_next].
      forward.
      rewrite (prot3_noise_rot_add_init_next _ _ _ En).
      entailer!. rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Exists lk1.
      simpl. entailer!. unfold W1. apply derives_refl.
  - forward_if.
    { exfalso. unfold typed_true in *. simpl in *. discriminate. }
    forward.
    forward_call (gv, S, KS, T, p_next P, true, shp, p, p_set_slots P (p_cur P) (p_prev P) new, shd, wg, D, sht).
    { rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Exists lk. simpl. entailer!. }
    pose proof (prot3_noise_rot_put_in_pool _ _ _ S (p_next P) true H0) as HW1.
    assert (Hp1: p_prev P = nullval \/ In (p_prev P) (map fst (kw_KS (kp_put (p_next P) true (mkKW KS T S))))).
    { destruct (EqDec_val (p_prev P) nullval) as [E|NE]; [left; auto | right].
      destruct Hp as [E|Hin]; [contradiction|]. apply prot3_noise_rot_put_keeps; auto. }
    set (W1 := kp_put (p_next P) true (mkKW KS T S)) in *.
    rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Intros lk1.
    unfold p_set_slots at 1 2 3; cbn [p_cur p_prev p_next].
    forward.
    forward_call (gv, kw_S W1, kw_KS W1, kw_T W1, p_prev P, true, shp, p, p_set_slots P (p_cur P) nullval new, shd, wg, D, sht).
    { rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Exists lk1. simpl. entailer!. }
    rewrite prot3_noise_rot_kw_eta, prot3_noise_rot_add_resp.
    entailer!. try (unfold W1; apply derives_refl).
Qed.

End NoiseRotAdd.
