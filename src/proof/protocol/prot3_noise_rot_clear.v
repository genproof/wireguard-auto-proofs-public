(* Group noise_rot: the body of wg_noise_keypairs_clear. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.protocol.prot3_noise_rot_lemmas.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

Section NoiseRotClear.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Definition Gn_rot_clear := Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS.

Lemma prot3_noise_rot_body_clear :
  @semax_body (QPvarspecs Noise.qp) Gn_rot_clear Noise.CS
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
  forward_call (gv, S, KS, T, p_next P, true, shp, p, p_set_slots P (p_cur P) (p_prev P) nullval, shd, wg, D, sht).
  { rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Exists lk. simpl. entailer!. }
  pose proof (prot3_noise_rot_put_in_pool _ _ _ S (p_next P) true H0) as HW1.
  assert (Hp1: p_prev P = nullval \/ In (p_prev P) (map fst (kw_KS (kp_put (p_next P) true (mkKW KS T S))))).
  { destruct (EqDec_val (p_prev P) nullval) as [E|NE]; [left; auto | right].
    destruct Hp as [E|Hin]; [contradiction|]. apply prot3_noise_rot_put_keeps; auto. }
  assert (Hc1: p_cur P = nullval \/ In (p_cur P) (map fst (kw_KS (kp_put (p_next P) true (mkKW KS T S))))).
  { destruct (EqDec_val (p_cur P) nullval) as [E|NE]; [left; auto | right].
    destruct Hc as [E|Hin]; [contradiction|]. apply prot3_noise_rot_put_keeps; auto. apply Dc; auto. }
  set (W1 := kp_put (p_next P) true (mkKW KS T S)) in *.
  rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Intros lk1.
  simpl p_cur; simpl p_prev; simpl p_next.
  forward. forward.
  forward_call (gv, kw_S W1, kw_KS W1, kw_T W1, p_prev P, true, shp, p, p_set_slots P (p_cur P) nullval nullval, shd, wg, D, sht).
  { rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Exists lk1. simpl. entailer!. }
  pose proof (prot3_noise_rot_put_in_pool _ _ _ (kw_S W1) (p_prev P) true HW1) as HW2.
  assert (Hc2: p_cur P = nullval \/ In (p_cur P) (map fst (kw_KS (kp_put (p_prev P) true (mkKW (kw_KS W1) (kw_T W1) (kw_S W1)))))).
  { destruct (EqDec_val (p_cur P) nullval) as [E|NE]; [left; auto | right].
    destruct Hc1 as [E|Hin]; [contradiction|]. apply prot3_noise_rot_put_keeps; auto. apply Dc; auto. }
  rewrite prot3_noise_rot_kw_eta in HW2, Hc2 |- *.
  set (W2 := kp_put (p_prev P) true W1) in *.
  rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Intros lk2.
  simpl p_cur; simpl p_prev; simpl p_next.
  forward. forward.
  forward_call (gv, kw_S W2, kw_KS W2, kw_T W2, p_cur P, true, shp, p, p_set_slots P nullval nullval nullval, shd, wg, D, sht).
  { rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Exists lk2. simpl. entailer!. }
  rewrite prot3_noise_rot_kw_eta.
  entailer!.
Qed.

End NoiseRotClear.
