(* law handshake_receive, body recv:
   segment C of wg_receive_handshake_packet: the cookie reply (type 3): wg_cookie_message_consume, return.
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_recv_C_lem.
Local Open Scope logic.

#[local] Existing Instance HRX.

Definition hrx5_rvC_hide : Type := compspecs.

Lemma hrx5_rvC_len msg : hrx5_fwd msg = true -> Int.eq (hrx5_tw msg) (Int.repr 3) = true -> Zlength msg = 64.
Proof.
  intros F T. apply Int.same_if_eq in T. unfold hrx5_fwd in F. rewrite T in F.
  apply andb_prop in F as [_ F]. cbn in F. apply Z.eqb_eq. destruct (Zlength msg =? 64); auto.
Qed.

Definition hrx5_rvC_d0 : rxdraw := mkRD (zeros 32) (zeros 24) (zeros 32) nullval.
Lemma hrx5_rvC_d0_ok T : rxdraw_ok T hrx5_rvC_d0.
Proof. unfold rxdraw_ok, hrx5_rvC_d0, zeros; cbn [rd_r rd_nonce rd_r2 rd_k]. repeat split; try reflexivity. congruence. Qed.

Lemma hrx5_rv_C_ok : hrx5_rv_C_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg HY HT.
  change hrx5_rvC_hide in CSw.
  unfold hrx5_rv_Delta, hrx5_rv_S0, hrx5_rv_COOKIE, hrx5_rv_retonly, hrx5_rv_R, hrx5_rv_post.
  simplify_func_tycontext. abbreviate_semax.
  destruct HY as (Hx & Ha & Hxa & Hshd & Hshs & Hshm & Hf & (Hlen & Hmc) & Hok).
  assert (L64 := hrx5_rvC_len msg Hf HT).
  destruct Hok as (Hch & (Hwf & Hrefs & Hpool & Hall) & HKS & Hrx).
  unfold skb_rep. Intros. rewrite hrx5_rvl_skb_cs. unfold skb_val.
  assert (Pd: isptr (sk_data s)) by (destruct (sk_data s); try contradiction; exact I).
  forward.
  rewrite (hrx5_rvC_msg shm msg (sk_data s)) by (auto; congruence). unfold rxw_rep. Intros.
  forward_call (gv, rw_S W, rw_w W, shm, sk_data s, cm_of msg, shd, wg, rw_D W, shd, rw_T W, rw_PS W).
  forward. Exists hrx5_rvC_d0.
  rewrite <- (hrx5_rvC_msg shm msg (sk_data s)) by (auto; congruence).
  unfold rx_packet. rewrite HT. unfold rxw_rep, skb_rep. cbn [rw_D rw_T rw_PS rw_KS rw_S rw_w rw_kc rw_lul rw_rx].
  rewrite hrx5_rvl_skb_cs. unfold skb_val.
  entailer!. apply hrx5_rvC_d0_ok.
Qed.
