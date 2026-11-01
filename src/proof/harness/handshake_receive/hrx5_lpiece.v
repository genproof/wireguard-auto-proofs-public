(* law handshake_receive: the law's local piece = the
   harness unit's functions but main (receive.c's two functions, the S23 shim, the harness's helpers), at the unit's
   compspecs HRX, from the five body groups hrx5_body_<g>.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_body_s23.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_body_vhl.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_body_help.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_body_k.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_body_recv.
Require WgNoise.harness.x_handshake_receive.code.

Module HL := WgNoise.harness.x_handshake_receive.code.

Ltac hrx5_one f B :=
  exists u_hrx5l; split; [left; reflexivity | exists f; split; [reflexivity | exact B]].

Theorem hrx5_lpiece : hrx5_lpiece_stmt.
Proof.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec CSw H1 H2 H3.
  destruct (hrx5_grp_s23 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw H1 H2 H3)
    as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
  destruct (hrx5_grp_vhl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw H1 H2 H3) as (V1 & V2).
  destruct (hrx5_grp_help x25519 aead_enc aead_dec xaead_enc xaead_dec CSw H1 H2 H3) as (P1 & P2 & P3 & P4).
  destruct (hrx5_grp_k x25519 aead_enc aead_dec xaead_enc xaead_dec CSw H1 H2 H3) as (K1 & K2).
  pose proof (hrx5_grp_recv x25519 aead_enc aead_dec xaead_enc xaead_dec CSw H1 H2 H3) as R1.
  split.
  - unfold hrx5_G_local. simpl map. repeat constructor; simpl; intuition discriminate.
  - unfold hrx5_G_local at 1.
    constructor; [hrx5_one HL.f_wg_shim_rx_peer S1 |].
    constructor; [hrx5_one HL.f_wg_packet_send_handshake_cookie S2 |].
    constructor; [hrx5_one HL.f_wg_socket_set_peer_endpoint_from_skb S3 |].
    constructor; [hrx5_one HL.f_wg_packet_send_handshake_response S4 |].
    constructor; [hrx5_one HL.f_wg_timers_session_derived S5 |].
    constructor; [hrx5_one HL.f_wg_timers_handshake_complete S6 |].
    constructor; [hrx5_one HL.f_wg_packet_send_keepalive S7 |].
    constructor; [hrx5_one HL.f_wg_timers_any_authenticated_packet_received S8 |].
    constructor; [hrx5_one HL.f_wg_timers_any_authenticated_packet_traversal S9 |].
    constructor; [hrx5_one HL.f_update_rx_stats S10 |].
    constructor; [hrx5_one HL.f_validate_header_len V1 |].
    constructor; [hrx5_one HL.f_wg_receive_handshake_packet R1 |].
    constructor; [hrx5_one HL.f_m_expired P1 |].
    constructor; [hrx5_one HL.f_m_cookie P2 |].
    constructor; [hrx5_one HL.f_rx_reset S11 |].
    constructor; [hrx5_one HL.f_rx_only_cookie S12 |].
    constructor; [hrx5_one HL.f_rx_authenticated S13 |].
    constructor; [hrx5_one HL.f_dispatch V2 |].
    constructor; [hrx5_one HL.f_draw_type P3 |].
    constructor; [hrx5_one HL.f_k_initiation K1 |].
    constructor; [hrx5_one HL.f_k_response K2 |].
    constructor; [hrx5_one HL.f_draw_macs P4 |].
    constructor.
Qed.
