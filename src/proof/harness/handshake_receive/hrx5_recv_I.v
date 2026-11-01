(* law handshake_receive, body recv:
   segment I of wg_receive_handshake_packet: case 1 after the cookie test: consume_initiation, endpoint, send_response, break.
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_recv_I_lem.
Local Open Scope logic.

#[local] Existing Instance HRX.

Definition hrx5_rvI_hide : Type := compspecs.

Lemma hrx5_rv_I_ok : hrx5_rv_I_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg r HY.
  change hrx5_rvI_hide in CSw.
  unfold hrx5_rv_Delta, hrx5_rv_SC, hrx5_rv_IREST. simplify_func_tycontext. abbreviate_semax.
  destruct HY as (Hx & Ha & Hxa & Hshd & Hshs & Hshm & Hf & (Hlen & Hmc) & Hok).
  destruct Hok as (Hch & (Hwf & Hrefs & Hpool & Hall) & HKS & Hrx).
  Intros. rename H into Hr32, H0 into HT, H1 into HC.
  assert (L148 := hrx5_rvI_len msg Hf HT).
  rewrite (hrx5_rvI_init shm msg (sk_data s) L148 Hmc).
  set (W1 := hrx5_rv_W1 W q s msg r).
  unfold rxw_rep. Intros.
  assert (Hlic: Forall (fun x => match x with (_, _, P) =>
                    Int64.signed (hs_lic (p_hs P)) <= Int64.max_signed - 20000000 end) (rw_PS W1)).
  { eapply Forall_impl; [|exact Hall]. intros [[p0 sh0] P0] H0. apply H0. }
  forward_call (gv, rw_S W1, rw_w W1, rw_kc W1, shm, sk_data s, im_of msg, shd, wg, rw_D W1, shd, head, rw_PS W1).
  destruct (cin_res x25519 aead_dec (rw_D W1) (rw_PS W1) (im_of msg) (rw_S W1)) as [[a P1]|] eqn:HCI;
    cbn [peer_result peers_after].
  2: { (* rejected: return *)
    forward_if; [| exfalso; congruence]. unfold POSTCONDITION, abbreviate, hrx5_rv_R, hrx5_rv_post. forward.
    Exists (mkRD r (zeros 24) (zeros 32) nullval).
    rewrite (hrx5_rvI_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg (mkRD r (zeros 24) (zeros 32) nullval) HT HC).
    cbn [rd_r]. fold W1. change (rw_PS W) with (rw_PS W1). rewrite HCI.
    unfold rxw_rep. rewrite <- (hrx5_rvI_init shm msg (sk_data s) L148 Hmc).
    entailer!.
    unfold rxdraw_ok, zeros; cbn [rd_r rd_nonce rd_r2 rd_k]. repeat split; try reflexivity; auto; congruence. }
  (* accepted *)
  assert (Hin := hrx5_rvI_cin_in _ _ _ _ _ _ _ _ HCI).
  destruct (prot_rep3_sfind_in _ _ Hin) as (sh & P & HF).
  assert (Hsh := hrx5_rvI_wf _ _ _ _ Hwf HF).
  unfold peers_rep. rewrite (prot_rep3_split _ a sh P1 _ (hrx5_rvI_sfind_supd _ _ _ _ P1 HF)).
  cbn [peer_item_rep]. rewrite hrx5_rvI_peer_split.
  assert_PROP (@field_compatible Noise.CS t_peer [] a) as FCa by (unfold hrx5_rvI_prest; entailer!).
  assert (Hpa: isptr a) by (destruct FCa; auto).
  forward_if.
  { apply denote_tc_test_eq_split; [| apply valid_pointer_null].
    eapply derives_trans with (rx_pfield sh a (p_device P1) * TT); [cancel|].
    apply sepcon_valid_pointer1, hrx5_rvI_vp; auto. }
  { exfalso. subst a. contradiction. }
  repeat flatten_sepcon_in_SEP.
  forward_call (gv, rw_rx W1, a, sh, p_device P1, sp).
  forward_call (gv, rx_set_endpoint (rw_rx W1) a sp, a, sh, p_device P1).
  { right. apply hrx5_rvI_peer_set; auto. }
  unfold POSTCONDITION, abbreviate, hrx5_rv_Qtail.
  forward.
  cbv beta iota delta [switch_ret_assert hrx5_rv_R frame_ret_assert function_body_ret_assert RA_break RA_normal].
  set (d := mkRD r (zeros 24) (zeros 32) nullval).
  set (W2 := mkRW (rw_D W1) (rw_T W1) (supd (rw_PS W1) a P1) (rw_KS W1) (rw_S W1) (rw_w W1) (rw_kc W1) (rw_lul W1)
                  (rx_send_response (rx_set_endpoint (rw_rx W1) a sp) a)).
  assert (Hd: rxdraw_ok (rw_T W) d).
  { unfold rxdraw_ok, d, zeros; cbn [rd_r rd_nonce rd_r2 rd_k]. repeat split; try reflexivity; auto; congruence. }
  assert (HM: rx_packet x25519 aead_dec xaead_enc xaead_dec W q sp s msg d = hrx5_rv_tailw W2 a (sk_len s)).
  { rewrite (hrx5_rvI_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg d HT HC).
    cbn [rd_r d]. fold W1. change (rw_PS W) with (rw_PS W1). rewrite HCI.
    exact (hrx5_rvI_tail W _ _ _ a P1 sp (sk_len s) sh P HF). }
  assert (HTO: hrx5_rv_tail_ok W2 a) by (eapply hrx5_rvI_tail_ok; eauto).
  Exists d W2 a.
  unfold rxw_rep, W2. cbn [rw_D rw_T rw_PS rw_KS rw_S rw_w rw_kc rw_lul rw_rx].
  unfold peers_rep. rewrite (prot_rep3_split _ a sh P1 _ (hrx5_rvI_sfind_supd _ _ _ _ P1 HF)).
  cbn [peer_item_rep]. rewrite hrx5_rvI_peer_split.
  rewrite <- (hrx5_rvI_init shm msg (sk_data s) L148 Hmc).
  entailer!.
Qed.
