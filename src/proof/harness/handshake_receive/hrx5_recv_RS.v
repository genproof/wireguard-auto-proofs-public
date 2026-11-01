(* law handshake_receive, body recv:
   segment RS of wg_receive_handshake_packet: case 2 after the cookie test: consume_response, endpoint, begin_session (session timers, keepalive), break.
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_recv_RS_lem.
Local Open Scope logic.

#[local] Existing Instance HRX.

Definition hrx5_rvRS_hide : Type := compspecs.

Lemma hrx5_rv_RS_ok : hrx5_rv_RS_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg r HY.
  change hrx5_rvRS_hide in CSw.
  unfold hrx5_rv_Delta, hrx5_rv_SC, hrx5_rv_RREST, hrx5_rv_Qtail, hrx5_rv_R, hrx5_rv_post.
  simplify_func_tycontext. abbreviate_semax.
  destruct HY as (Hx & Ha & Hxa & Hshd & Hshs & Hshm & Hf & (Hlen & Hmc) & Hok).
  destruct Hok as (Hch & (Hwf & Hrefs & Hpool & Hall) & HKS & Hrx).
  apply semax_extract_PROP; intro H32. apply semax_extract_PROP; intros [HT HC].
  assert (L92 := hrx5_rvRS_len msg Hf HT).
  rewrite (hrx5_rvRS_resp shm msg (sk_data s) L92 Hmc).
  set (W1 := hrx5_rv_W1 W q s msg r).
  unfold rxw_rep. Intros.
  forward_call (gv, rw_S W1, rw_w W1, shm, sk_data s, rm_of msg, shd, wg, rw_D W1, shd, rw_T W1, rw_PS W1).
  change (rw_T W1) with (rw_T W) in *. change (rw_PS W1) with (rw_PS W) in *.
  assert (HMD := hrx5_rvRS_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg
                   (mkRD r (Zrepeat Byte.zero 24) (Zrepeat Byte.zero 32) nullval) HT HC).
  cbn [rd_r rd_k] in HMD. fold W1 in HMD.
  destruct (cre_res x25519 aead_dec (rw_D W1) (rw_T W) (rw_PS W) (rm_of msg)) as [[a P1]|] eqn:HCR.
  2:{ (* rejected: return *)
    cbn [peer_result peers_after].
    forward_if.
    - forward.
      Exists (mkRD r (Zrepeat Byte.zero 24) (Zrepeat Byte.zero 32) nullval).
      rewrite HMD.
      rewrite <- (hrx5_rvRS_resp shm msg (sk_data s) L92 Hmc).
      unfold rxw_rep. entailer!.
      all: first [apply derives_refl | split; [|split; [|split]]; auto; congruence].
    - match goal with H: Int64.zero <> Int64.zero |- _ => contradiction H; reflexivity end. }
  destruct (hrx5_rvRS_cre_in _ _ _ _ _ _ _ _ HCR) as (sh & P & HPf & HPd & HPc & HPp & HPn).
  destruct (hrx5_rvRS_pok _ _ _ _ _ _ Hall HPf) as (Hdev & Hcur & Hprev & Hnext & Hhs & Hlic).
  assert (Hw := hrx5_rvRS_wf _ _ _ _ Hwf HPf).
  cbn [peer_result peers_after].
  rewrite (hrx5_rvRS_peers_supd _ _ _ _ P1 HPf).
  rewrite (hrx5_rvRS_peer_split sh a P1).
  assert_PROP (@field_compatible Noise.CS t_peer [] a) as FCa by (unfold hrx5_rvRS_prest; entailer!).
  clear HMD. assert (Hrs: readable_share sh) by auto.
  forward_if.
  { apply denote_tc_test_eq_split; [|apply valid_pointer_null].
    do 12 apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. apply hrx5_rvRS_pfield_valid; auto. }
  { exfalso. destruct FCa as [Hp _]. subst a. exact Hp. }
  (* wg_socket_set_peer_endpoint_from_skb(peer, skb) *)
  repeat flatten_sepcon_in_SEP.
  forward_call (gv, rw_rx W1, a, sh, p_device P1, sp).
  gather_SEP (rx_pfield sh a (p_device P1)) (hrx5_rvRS_prest sh a P1).
  rewrite <- (hrx5_rvRS_peer_split sh a P1).
  (* t'9 = wg_noise_handshake_begin_session(&peer->handshake, &peer->keypairs) *)
  change (rw_KS W1) with (rw_KS W). rewrite HKS.
  forward_call (gv, rw_S W1, rw_w W1, rw_kc W1, @nil (val * keypair), rw_T W, sh, a, P1, shd, wg, rw_D W1, shd).
  { destruct FCa as [Hp _]. split; exact Hp. }
  { split.
    - split; constructor.
    - unfold slots_ok. rewrite HPc, HPp, HPn, Hcur, Hprev, Hnext. cbn [filter].
      destruct (eq_dec nullval nullval); [| congruence].
      split; [repeat constructor; auto | constructor]. }
  Intros k.
  set (B := bs_res P1 a k (rw_kc W1) [] (rw_T W) (rw_S W1)).
  set (X1 := rx_set_endpoint (rw_rx W1) a sp).
  set (w2 := begin_session_warn P1 (hs_addr a) k (rw_kc W1) {| kw_KS := []; kw_T := rw_T W; kw_S := rw_S W1 |}
               (rw_w W1)).
  forward_if (PROP () LOCAL (temp HRC._peer a; gvars gv; temp HRC._skb sp)
    SEP (mem_mgr gv; shim_state4 gv (kw_S (snd (fst B))) w2; noise_globals gv (snd B); wg_consts gv;
         keypairs_rep CSw (kw_KS (snd (fst B))); peer_rep sh a (snd (fst (fst B)));
         device_rep shd wg (rw_D W1); itable shd (d_itab (rw_D W1)) (kw_T (snd (fst B)));
         rxlog_rep gv (if fst (fst (fst B)) then rx_send_keepalive (rx_handshake_complete (rx_session_derived X1 a) a) a
                       else X1);
         resp_rep shm (sk_data s) (rm_of msg); iter_sepcon.iter_sepcon peer_item_rep (sdel (rw_PS W) a);
         ptable shd (d_ptab (rw_D W1)) head; lul_rep gv (rw_lul W1); qlen_rep gv q; skb_rep shs sp s)).
  - (* the session was made: the timers and the keepalive *)
    match goal with Hx: typed_true tbool _ |- _ => rename Hx into Hbt end.
    assert (Hok: fst (fst (fst B)) = true)
      by (destruct (fst (fst (fst B))); [reflexivity | revert Hbt; vm_compute; discriminate]).
    assert (HX1: rx_peer X1 = a) by (unfold X1, rx_set_endpoint; apply hrx5_rvRS_note_same; auto).
    rewrite (hrx5_rvRS_peer_split sh a). repeat flatten_sepcon_in_SEP.
    forward_call (gv, X1, a, sh, p_device (snd (fst (fst B)))).
    forward_call (gv, rx_session_derived X1 a, a, sh, p_device (snd (fst (fst B)))).
    { right; unfold rx_session_derived; apply hrx5_rvRS_note_same; auto. }
    forward_call (gv, rx_handshake_complete (rx_session_derived X1 a) a, a, sh, p_device (snd (fst (fst B)))).
    { right; unfold rx_handshake_complete; apply hrx5_rvRS_note_same; [right|auto].
      unfold rx_session_derived; apply hrx5_rvRS_note_same; auto. }
    rewrite Hok.
    gather_SEP (rx_pfield sh a _) (hrx5_rvRS_prest sh a _).
    rewrite <- (hrx5_rvRS_peer_split sh a).
    entailer!.
  - (* no session *)
    match goal with Hx: typed_false tbool _ |- _ => rename Hx into Hbf end.
    assert (Hok: fst (fst (fst B)) = false)
      by (destruct (fst (fst (fst B))); [revert Hbf; vm_compute; discriminate | reflexivity]).
    forward. rewrite Hok. entailer!.
  - (* break: the world before the tail *)
    forward.
    assert (HMD := hrx5_rvRS_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg
                     (mkRD r (Zrepeat Byte.zero 24) (Zrepeat Byte.zero 32) k) HT HC).
    cbn [rd_r rd_k] in HMD. fold W1 in HMD. rewrite HCR in HMD.
    rewrite (hrx5_rvRS_tail _ _ _ _ _ _ _ _ _ _ _ HPf) in HMD.
    assert (HTO := hrx5_rvRS_tail_ok W (rw_D W1) (rw_S W1) (rw_lul W1) a P1 k sp sh P H Hrx HPf Hw).
    Exists (mkRD r (Zrepeat Byte.zero 24) (Zrepeat Byte.zero 32) k)
           (hrx5_rvRS_W2 W (rw_D W1) (rw_S W1) (rw_lul W1) a P1 k sp) a.
    unfold rxw_rep, hrx5_rvRS_W2. cbn [rw_D rw_T rw_PS rw_KS rw_S rw_w rw_kc rw_lul rw_rx].
    rewrite HKS. change (rw_kc W) with (rw_kc W1). fold B. fold X1. fold w2.
    rewrite (hrx5_rvRS_peers_supd _ _ _ _ (snd (fst (fst B))) HPf).
    rewrite <- (hrx5_rvRS_resp shm msg (sk_data s) L92 Hmc).
    unfold hrx5_rvRS_W2 in HMD, HTO. rewrite HKS in HMD, HTO.
    entailer!.
    + unfold rxdraw_ok; cbn [rd_r rd_nonce rd_r2 rd_k].
      split; [exact H32|]. split; [reflexivity|]. split; [reflexivity|].
      intros Hk. apply (proj1 (H1 Hk)).
    + apply derives_refl.
Qed.
