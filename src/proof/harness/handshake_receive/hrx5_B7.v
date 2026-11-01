(* law handshake_receive: main's phase B7 = body statements 39..40: CHECK(skb_same && packet unchanged), CHECK(dev_same).
   From hrx5_S6 to hrx5_S6 (hrx5_defs.v; the cut: hrx5_cut.v). *)
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
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B7_lem.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* the ret_asserts of forward_if / forward_loop joins under hrx5_RB: reduce them (hrx5_RB's states stay folded) *)
Ltac hrx5_b7_ra :=
  cbv beta iota delta [loop_nocontinue_ret_assert hrx5_RB loop1_ret_assert overridePost hrx5_R frame_ret_assert
                       function_body_ret_assert RA_break RA_normal].

Section B7.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_B7_ok {Espec: OracleKind} gv L FR :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_S6 x25519 aead_dec xaead_enc xaead_dec gv L FR) hrx5_B7
    (overridePost (hrx5_S6 x25519 aead_dec xaead_enc xaead_dec gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HH. unfold hrx5_S6, hrx5_Delta. simplify_func_tycontext. abbreviate_semax.
  Intros R sec birth S w NS. Intros PS T head nk KE st. Intros i kc lul q proto.
  Intros ip4 ip6 port o dp. Intros img tg ai ar d.
  match goal with Hw: itable_wf T |- _ => rename Hw into Hhrx5_itwf end.
  unfold hrx5_B7.
  set (W0 := hrx5_W0 (hrx5_DL x25519 R L sec birth) T PS S w kc lul).
  set (s := hrx5_skb dp o proto ip4 ip6 port).
  set (W1 := rx_model x25519 aead_dec xaead_enc xaead_dec W0 q (l_skb L) s (obj_bytes o) d).
  unfold hrx5_cglobs, hrx5_scr5, hrx5_lvars, hrx5_ptrs, hrx5_rest. cbn [app].
  pose proof (hrx5_b7_rx_dev x25519 aead_dec xaead_enc xaead_dec W0 q (l_skb L) s (obj_bytes o) d) as HD.
  fold W1 in HD. unfold hrx5_b7_dptrs in HD. injection HD as HD1 HD2 HD3 HD4.
  pose proof (hrx5_b7_rx_ash x25519 aead_dec xaead_enc xaead_dec W0 q (l_skb L) s (obj_bytes o) d) as HA.
  fold W1 in HA.
  rewrite (hrx5_b7_obj_open dp o H3 H4).
  pose proof (hrx5_b7_obj_len o H3) as Hlen.
  freeze [1;2;3;4;5;6;7;8;9;10;11;12;13;14;18;20;22;23;24;25;26;27;28;29;30;31;32] FA.
  assert_PROP (skb_ok s) as Hskb by (unfold skb_rep; entailer!).
  destruct (Z.eq_dec (Zlength (obj_bytes o)) 0) as [Hz | Hnz].
  { pose proof (hrx5_b7_empty o H3 Hz) as Ho.
  assert (Ht: hrx5_b7_tok dp o = @malloc_token W Ews (tarray tuchar 0) dp) by (rewrite Ho; reflexivity).
  rewrite Ht, (hrx5_b7_vot dp). flatten_sepcon_in_SEP.
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  - entailer!.
  - forward_call (Tsh, l_sks L, s, Tsh, l_skb L, s, [VTok Ews (tarray tuchar 0) dp]).
    { split.
      - constructor; [apply hrx5_b7_vtok_ok | constructor].
      - constructor; [right; cbn; left; reflexivity | constructor; [right; cbn; left; reflexivity | constructor]]. }
    rewrite hrx5_b7_skb_eqb_refl.
    forward_if (temp HM._t'110 (Vint Int.one)).
    + unfold skb_rep. Intros. rewrite hrx5_b7_skb_cs.
      assert (Hdp: isptr dp) by (clear - H4; unfold malloc_compatible in H4; destruct dp; try contradiction; exact I).
      change (skb_val s) with (dp, snd (skb_val s)).
      forward.
      change (dp, snd (skb_val s)) with (skb_val s). rewrite <- hrx5_b7_skb_cs.
      rewrite hrx5_b7_hbytes.
      unfold img_rep. Intros.
      forward_call (Ews, dp, obj_bytes o, Ews, img, obj_bytes o).
      rewrite hrx5_b7_bytes_eqb_refl. forward.
      unfold skb_rep, img_rep.
      rewrite <- (hrx5_b7_hbytes Ews (obj_bytes o) dp).
      hrx5_b7_ra. entailer!.
    + exfalso. apply Int.one_not_zero. assumption.
    + forward_if True; [discriminate | forward | ]; [hrx5_b7_ra; entailer! |].
      forward. hrx5_b7_ra. entailer!.
  - (* 40: CHECK(dev_same(&ds, &wd)) *)
    assert (Hhead: head = nullval \/ In head (map peer_addr4 (rw_PS W1))).
    { rewrite (hrx5_b7_ash_addrs (rw_PS W0) (rw_PS W1) HA).
      destruct H0 as (_ & _ & _ & Hch & _). exact (hrx5_b7_head_in head PS Hch). }
    assert (Hvok: vobj_ok (VPeers (rw_PS W1))).
    { apply hrx5_b7_vok. apply (hrx5_b7_ash_ews (rw_PS W0) (rw_PS W1) HA).
      destruct H0 as (Hpok & _). eapply Forall_impl; [| exact Hpok]. intros [[a sh] P] Hx. apply Hx. }
    unfold rxw_rep. repeat flatten_sepcon_in_SEP.
    gather_SEP (itable _ _ _) (peers_rep _). rewrite hrx5_b7_vo2.
    match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
    + entailer!.
    + forward_call (Tsh, l_ds L, rw_D W1, head, Tsh, l_wd L, rw_D W1, Tsh, head,
                    [VItab Tsh (d_itab (rw_D W1)) (rw_T W1); VPeers (rw_PS W1)]).
      { split; [constructor; [cbn; apply writable_readable, writable_share_top |
                              constructor; [exact Hvok | constructor]] |].
        apply (hrx5_b7_dpre (l_wd L) (d_itab (rw_D W1)) (d_ptab (rw_D W1)) head (rw_T W1) (rw_PS W1) (rw_D W1)
                 HD1 HD4 eq_refl eq_refl Hhead). }
      rewrite hrx5_b7_dev_eqb_refl.
      forward_if True; [discriminate | forward | ]; [hrx5_b7_ra; entailer! |].
      forward. hrx5_b7_ra. entailer!.
    + rewrite <- hrx5_b7_vo2.
      hrx5_b7_ra. thaw FA.
      rewrite <- (hrx5_b7_vot dp), <- Ht.
      sep_apply (derives_refl' _ _ (eq_sym (hrx5_b7_obj_open dp o H3 H4))).
      Exists R sec birth S w NS. Exists PS T head nk KE st. Exists i kc lul q proto.
      Exists ip4 ip6 port o dp. Exists img tg ai ar d.
      fold W0. fold s. fold W1.
      unfold hrx5_rest, hrx5_cglobs, hrx5_scr5, hrx5_lvars, hrx5_ptrs, rxw_rep. cbn [app].
      entailer!.
  }
  rewrite (hrx5_b7_vo1 Ews (obj_bytes o) dp). flatten_sepcon_in_SEP.
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  - entailer!.
  - forward_call (Tsh, l_sks L, s, Tsh, l_skb L, s, [VBytes Ews (obj_bytes o) dp]).
    { split.
      - constructor; [cbn; split; [apply writable_readable, writable_Ews | lia] | constructor].
      - constructor; [right; cbn; left; reflexivity | constructor; [right; cbn; left; reflexivity | constructor]]. }
    rewrite hrx5_b7_skb_eqb_refl.
    forward_if (temp HM._t'110 (Vint Int.one)).
    + unfold skb_rep. Intros. rewrite hrx5_b7_skb_cs.
      assert (Hdp: isptr dp) by (clear - H4; unfold malloc_compatible in H4; destruct dp; try contradiction; exact I).
      change (skb_val s) with (dp, snd (skb_val s)).
      forward.
      change (dp, snd (skb_val s)) with (skb_val s). rewrite <- hrx5_b7_skb_cs.
      rewrite <- (hrx5_b7_vo1 Ews (obj_bytes o) dp), hrx5_b7_hbytes.
      unfold img_rep. Intros.
      forward_call (Ews, dp, obj_bytes o, Ews, img, obj_bytes o).
      rewrite hrx5_b7_bytes_eqb_refl. forward.
      unfold skb_rep, img_rep.
      rewrite <- (hrx5_b7_hbytes Ews (obj_bytes o) dp), (hrx5_b7_vo1 Ews (obj_bytes o) dp).
      hrx5_b7_ra. entailer!.
    + exfalso. apply Int.one_not_zero. assumption.
    + forward_if True; [discriminate | forward | ]; [hrx5_b7_ra; entailer! |].
      forward. hrx5_b7_ra. entailer!.
  - (* 40: CHECK(dev_same(&ds, &wd)) *)
    assert (Hhead: head = nullval \/ In head (map peer_addr4 (rw_PS W1))).
    { rewrite (hrx5_b7_ash_addrs (rw_PS W0) (rw_PS W1) HA).
      destruct H0 as (_ & _ & _ & Hch & _). exact (hrx5_b7_head_in head PS Hch). }
    assert (Hvok: vobj_ok (VPeers (rw_PS W1))).
    { apply hrx5_b7_vok. apply (hrx5_b7_ash_ews (rw_PS W0) (rw_PS W1) HA).
      destruct H0 as (Hpok & _). eapply Forall_impl; [| exact Hpok]. intros [[a sh] P] Hx. apply Hx. }
    unfold rxw_rep. repeat flatten_sepcon_in_SEP.
    gather_SEP (itable _ _ _) (peers_rep _). rewrite hrx5_b7_vo2.
    match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
    + entailer!.
    + forward_call (Tsh, l_ds L, rw_D W1, head, Tsh, l_wd L, rw_D W1, Tsh, head,
                    [VItab Tsh (d_itab (rw_D W1)) (rw_T W1); VPeers (rw_PS W1)]).
      { split; [constructor; [cbn; apply writable_readable, writable_share_top |
                              constructor; [exact Hvok | constructor]] |].
        apply (hrx5_b7_dpre (l_wd L) (d_itab (rw_D W1)) (d_ptab (rw_D W1)) head (rw_T W1) (rw_PS W1) (rw_D W1)
                 HD1 HD4 eq_refl eq_refl Hhead). }
      rewrite hrx5_b7_dev_eqb_refl.
      forward_if True; [discriminate | forward | ]; [hrx5_b7_ra; entailer! |].
      forward. hrx5_b7_ra. entailer!.
    + rewrite <- hrx5_b7_vo2.
      hrx5_b7_ra. thaw FA.
      rewrite <- (hrx5_b7_vo1 Ews (obj_bytes o) dp).
      sep_apply (derives_refl' _ _ (eq_sym (hrx5_b7_obj_open dp o H3 H4))).
      Exists R sec birth S w NS. Exists PS T head nk KE st. Exists i kc lul q proto.
      Exists ip4 ip6 port o dp. Exists img tg ai ar d.
      fold W0. fold s. fold W1.
      unfold hrx5_rest, hrx5_cglobs, hrx5_scr5, hrx5_lvars, hrx5_ptrs, rxw_rep. cbn [app].
      entailer!.
Qed.

End B7.
