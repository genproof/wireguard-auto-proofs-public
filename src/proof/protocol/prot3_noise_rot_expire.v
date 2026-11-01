(* Group noise_rot: the body of wg_noise_expire_current_peer_keypairs. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.protocol.prot3_noise_rot_lemmas.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

Section NoiseRotExpire.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Definition Gn_rot_expire := Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS.

Lemma prot3_noise_rot_body_expire :
  @semax_body (QPvarspecs Noise.qp) Gn_rot_expire Noise.CS
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
  forward_call (gv, S, shp, field_address t_peer [StructField I._last_sent_handshake] p).
  rewrite (prot3_noise_rot_kps_field _ _ _ FC).
  forward.
  simpl p_cur; simpl p_prev; simpl p_next.
  forward_if (PROP () LOCAL (gvars gv; temp I._peer p)
    SEP (shim_state gv S;
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
    SEP (shim_state gv S;
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

End NoiseRotExpire.
