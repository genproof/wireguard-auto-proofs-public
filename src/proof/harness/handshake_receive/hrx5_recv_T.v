(* law handshake_receive, body recv:
   segment T of wg_receive_handshake_packet: the common tail: update_rx_stats, the two timers, wg_peer_put.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_recv_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_recv_lem.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_recv_T_lem.
Local Open Scope logic.

#[local] Existing Instance HRX.

Definition hrx5_rvT_hide : Type := compspecs.

Lemma hrx5_rv_T_ok : hrx5_rv_T_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg HY.
  change hrx5_rvT_hide in CSw.
  unfold hrx5_rv_Delta, hrx5_rv_Qtail, hrx5_rv_TAIL. simplify_func_tycontext.
  unfold hrx5_rv_R, hrx5_rv_post. abbreviate_semax.
  Intros d W2 a.
  rename H into Hd, H0 into HM, H1 into HT.
  destruct HT as (Ha & Hrx & sh & P & HF & Hsh).
  unfold rxw_rep. Intros.
  unfold peers_rep. rewrite (prot_rep3_split _ a sh P _ HF).
  cbn [peer_item_rep]. rewrite hrx5_rvT_peer_split.
  assert_PROP (@field_compatible Noise.CS t_peer [] a) as FCa by (unfold hrx5_rvT_prest; entailer!).
  assert (Hpa: isptr a) by (destruct FCa; auto).
  forward_if.
  { apply denote_tc_test_eq_split; [| apply valid_pointer_null].
    match goal with |- _ |-- valid_pointer ?x =>
      eapply derives_trans with (rx_pfield sh x (p_device P) * TT); [cancel|] end.
    apply sepcon_valid_pointer1, hrx5_rvT_vp; auto. }
  { exfalso. subst a. contradiction. }
  repeat flatten_sepcon_in_SEP.
  destruct HY as (Hx & Hae & Hxa & Hshd & Hshs & Hshm & Hf & (Hlen & Hmc) & Hok).
  unfold skb_rep at 1. Intros. rewrite hrx5_rvl_skb_cs. forward.
  forward_call (gv, rw_rx W2, a, sh, p_device P, Int64.repr (Int.unsigned (sk_len s))).
  forward_call (gv, rx_update_stats (rw_rx W2) a (Int64.repr (Int.unsigned (sk_len s))), a, sh, p_device P).
  { right. apply hrx5_rvT_stats; auto. }
  forward_call (gv, rx_auth_received (rx_update_stats (rw_rx W2) a (Int64.repr (Int.unsigned (sk_len s)))) a, a, sh, p_device P).
  { right. apply hrx5_rvT_recv, hrx5_rvT_stats; auto. }
  forward_call (gv, rw_S W2, rw_w W2, sh, a, p_refs P, p_device P).
  { rewrite if_false by auto. unfold rx_pfield. cancel. }
  rewrite !if_false by auto.
  Exists d.
  rewrite HM. unfold hrx5_rv_tailw. rewrite HF.
  unfold rxw_rep; cbn [rw_D rw_T rw_PS rw_KS rw_S rw_w rw_kc rw_lul rw_rx].
  unfold peers_rep.
  rewrite (prot_rep3_split _ a sh (p_set_refs P (rc_sub1 (p_refs P))) _ (hrx5_rvT_sfind_supd _ _ _ _ _ HF)).
  rewrite hrx5_rvT_sdel_supd. cbn [peer_item_rep]. rewrite hrx5_rvT_peer_split, hrx5_rvT_prest_refs.
  unfold p_set_refs at 1 2; cbn [p_device p_refs].
  unfold skb_rep. rewrite hrx5_rvl_skb_cs. unfold rx_pfield, rx_tail.
  entailer!.
Qed.
