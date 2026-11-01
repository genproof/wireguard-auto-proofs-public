(* Group noise_rot: the body of wg_noise_received_with_keypair. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.protocol.prot3_noise_rot_lemmas.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

Section NoiseRotRecv.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Definition Gn_rot_recv := Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS.

Ltac tc_kn :=
  match goal with
  | H0: kps_in_pool ?T ?p ?KS, H2: In ?k (map fst ?KS), Hn: ?n = nullval \/ In ?n (map fst ?KS),
    HKS: forall k, In k (map fst ?KS) -> isptr k |- _ |-- denote_tc_test_eq ?k ?n =>
    match goal with |- context [itable ?sht ?tab T] =>
      pose proof (prot3_noise_rot_kp_valid sht tab T p KS _ H0 H2) as VK;
      apply prot3_noise_rot_tc_ptrs; [auto | prot3_vp VK |];
      destruct Hn as [E|Hin]; [left; auto | right];
      pose proof (prot3_noise_rot_kp_valid sht tab T p KS _ H0 Hin) as VN;
      split; [apply HKS; auto | prot3_vp VN]
    end
  end.

Lemma prot3_noise_rot_body_recv :
  @semax_body (QPvarspecs Noise.qp) Gn_rot_recv Noise.CS
    WgNoise.noise.code.f_wg_noise_received_with_keypair (wg_noise_received_with_keypair_spec CSw).
Proof.
  start_function.
  destruct (prot3_noise_rot_slots _ _ H1) as (Hc & Hp & Hn & Dc & Dp).
  assert_PROP (forall k, In k (map fst KS) -> isptr k) as HKS by (sep_apply prot3_noise_rot_ks_ptrs; entailer!).
  pose proof (prot3_noise_rot_slot_ptr _ _ HKS Hc) as Pc.
  pose proof (prot3_noise_rot_slot_ptr _ _ HKS Hp) as Pp.
  pose proof (prot3_noise_rot_slot_ptr _ _ HKS Hn) as Pn.
  pose proof (HKS _ H2) as Pk.
  rewrite prot3_noise_rot_peer_split. unfold kps_rep. Intros lk.
  forward. forward.
  { entailer!. tc_kn. }
  assert (Hn': p_next P = nullval \/ isptr (p_next P)) by (destruct Hn as [E|Hin]; [left; auto | right; apply HKS; auto]).
  rewrite (prot3_noise_rot_cmp_eq _ _ _ Pk Hn').
  destruct (eq_dec k (p_next P)) as [E|NE].
  - forward_if.
    { exfalso. unfold typed_true in *. simpl in *. discriminate. }
    forward.
    forward_if.
    { entailer!. tc_kn. }
    { contradiction. }
    forward. forward. forward.
    forward_call (gv, S, KS, T, p_prev P, true, shp, p, p_set_slots P (p_cur P) (p_cur P) (p_next P), shd, wg, D, sht).
    { rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Exists lk. simpl. entailer!. }
    rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Intros lk1.
    unfold p_set_slots at 1 2 3; cbn [p_cur p_prev p_next].
    forward. forward. forward.
    rewrite (prot3_noise_rot_recv_eq _ _ _ eq_refl).
    entailer!. rewrite prot3_noise_rot_peer_split, prot3_noise_rot_peer_rest_slots. unfold kps_rep. Exists lk1.
    simpl. entailer!.
  - forward_if.
    { forward. rewrite (prot3_noise_rot_recv_neq _ _ _ NE).
      entailer!. rewrite prot3_noise_rot_peer_split. unfold kps_rep. Exists lk. entailer!. apply derives_refl. }
    { exfalso. match goal with H: Int.zero <> Int.zero |- _ => apply H; reflexivity end. }
Qed.

End NoiseRotRecv.
