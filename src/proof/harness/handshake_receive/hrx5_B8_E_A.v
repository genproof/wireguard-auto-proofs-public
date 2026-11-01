(* law handshake_receive, phase B8, branch E: part A: the log checks (rx_only_cookie, cookie_index), Q1 -> Q1.
   Statement: hrx5_B8_E_defs.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_cut.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require WgNoise.contracts.x_handshake_receive.
Require WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_conv.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_ilem.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_E_defs.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Lemma hrx5_B8EA_peer path o : rx_peer (hrx5_B8E_log path o) = nullval.
Proof. unfold hrx5_B8E_log. destruct (Z.eq_dec path 2); reflexivity. Qed.

Lemma hrx5_B8EA_c1 path o : path = 2 -> rx_only_cookie_b (hrx5_B8E_log path o) (Int.repr 1) = true.
Proof. intros ->. reflexivity. Qed.

Lemma hrx5_B8EA_c0 path o : path <> 2 -> rx_only_cookie_b (hrx5_B8E_log path o) (Int.repr 0) = true.
Proof. intros Hp. unfold hrx5_B8E_log. rewrite if_false by exact Hp. reflexivity. Qed.

Lemma hrx5_B8EA_ci path o : path = 2 -> rx_cindex (hrx5_B8E_log path o) = hrx5_B8E_sidx o.
Proof. intros ->. reflexivity. Qed.

#[local] Instance hrx5_B8EA_cceH : change_composite_env HRX W_handshake_receive.
Proof. make_cs_preserve HRX W_handshake_receive. Defined.
#[local] Instance hrx5_B8EA_cceN : change_composite_env Noise.CS W_handshake_receive.
Proof. make_cs_preserve Noise.CS W_handshake_receive. Defined.

Lemma hrx5_B8EA_log_cs gv X :
  rxlog_rep gv X = @data_at W_handshake_receive Ews t_rxlog (rxlog_val X) (gv HRC._wg_shim_rx).
Proof.
  unfold rxlog_rep.
  apply (f_equal (fun f => f (gv HRC._wg_shim_rx))).
  apply (@data_at_change_composite HRX W_handshake_receive _); [apply JMeq_refl | reflexivity].
Qed.

Lemma hrx5_B8EA_init_cs sh M p :
  @data_at Noise.CS sh t_init (init_val M) p = @data_at W_handshake_receive sh t_init (init_val M) p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite Noise.CS W_handshake_receive _); [apply JMeq_refl | reflexivity].
Qed.

Lemma hrx5_B8EA_resp_cs sh M p :
  @data_at Noise.CS sh t_resp (resp_val M) p = @data_at W_handshake_receive sh t_resp (resp_val M) p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite Noise.CS W_handshake_receive _); [apply JMeq_refl | reflexivity].
Qed.

Ltac hrx5_B8EA_fif t v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Lc (SEPx ?Sp))) _ _ =>
    forward_if (PROPx P (LOCALx (temp t v :: Lc) (SEPx Sp))) end.

Ltac hrx5_B8EA_chk o :=
  unfold rxlog_val at 1; cbv beta iota;
  match goal with H: ?path = 2 |- _ => rewrite (hrx5_B8EA_ci path o H) end;
  cbn [hrx5_B8E_sidx];
  forward_if;
  [ exfalso;
    match goal with H: Int.repr (Z.b2z (Int.eq ?x ?x)) = Int.zero |- _ =>
      rewrite Int.eq_true in H; exact (Int.one_not_zero H) end
  | forward; rewrite <- hrx5_B8EA_log_cs; entailer! ].

Lemma hrx5_B8E_A_ok : hrx5_B8E_A_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc q proto
    ip4 ip6 port o dp img tg ai ar sec1 birth1 S1 lul1 path HY.
  unfold hrx5_Delta, hrx5_B8E_Q1, hrx5_B8E_A.
  unfold hrx5_lvars, hrx5_ptrs, hrx5_rest, hrx5_cglobs, hrx5_scr5; cbn [app].
  abbreviate_semax.
  Intros.
  unfold rxw_rep, hrx5_B8E_W. cbn [rw_D rw_T rw_PS rw_KS rw_S rw_w rw_kc rw_lul rw_rx].
  repeat flatten_sepcon_in_SEP.
  unfold POSTCONDITION, abbreviate. destruct (hrx5_RB x25519 gv L FR) as [rn rb rc rr]. unfold overridePost.
  match goal with |- semax _ ?Pre _ _ => forward_if Pre end.
  -
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
    { apply ENTAIL_refl. }
    { forward_call (gv, hrx5_B8E_log path o, Int.repr 1).
      { apply hrx5_B8EA_peer. }
      rewrite (hrx5_B8EA_c1 path o H10).
      forward_if.
      { exfalso. apply Int.one_not_zero. assumption. }
      forward. entailer!. }
    forward. entailer!.
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
    { apply ENTAIL_refl. }
    { pose proof (H4 H10) as Hk.
      destruct o as [b | M | M | M]; cbv beta iota in *; cbn [obj_kind] in Hk; try (exfalso; lia).
      + hrx5_B8EA_fif HRM._t'220 (Vint (im_sender M)).
        { unfold obj_rep, init_rep. Intros.
          rewrite hrx5_B8EA_init_cs.
          forward.
          forward.
          rewrite <- hrx5_B8EA_init_cs.
          entailer!.
          unfold obj_rep, init_rep. entailer!. }
        { exfalso. match goal with Hf: ?x <> ?x |- _ => exact (Hf eq_refl) end. }
        rewrite hrx5_B8EA_log_cs.
        forward.
        hrx5_B8EA_chk (OInit M).
      + hrx5_B8EA_fif HRM._t'220 (Vint (rm_sender M)).
        { exfalso. match goal with Hf: 2 = 1 |- _ => discriminate Hf end. }
        { unfold obj_rep, resp_rep. Intros.
          rewrite hrx5_B8EA_resp_cs.
          forward.
          forward.
          rewrite <- hrx5_B8EA_resp_cs.
          entailer!.
          unfold obj_rep, resp_rep. entailer!. }
        rewrite hrx5_B8EA_log_cs.
        forward.
        hrx5_B8EA_chk (OResp M). }
    forward. entailer!. apply ENTAIL_refl.
  - match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
    { apply ENTAIL_refl. }
    { forward_call (gv, hrx5_B8E_log path o, Int.repr 0).
      { apply hrx5_B8EA_peer. }
      rewrite (hrx5_B8EA_c0 path o H10).
      forward_if.
      { exfalso. apply Int.one_not_zero. assumption. }
      forward. entailer!. }
    forward. entailer!. apply ENTAIL_refl.
  - unfold rxw_rep, hrx5_B8E_W. cbn [rw_D rw_T rw_PS rw_KS rw_S rw_w rw_kc rw_lul rw_rx].
    entailer!.
Qed.
