(* law handshake_receive, B3 kind 3, segment P, part P2: have_sent_mac1 = true,
   nondet_bytes(ck, 16), xchacha20poly1305_encrypt, back to hrx5_K3_F (cut and states: hrx5_B3_K3_P_defs.v). *)
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
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_defs.
Local Open Scope logic.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K3_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K3_P_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K3_P_2_lem.
Require Import WgNoise.proof.libc.libc_bytes.
Local Open Scope logic.

Lemma hrx5_k3p2m_pb sh bs p : 0 < Zlength bs ->
  @prim_bytes W sh bs p = @data_at W sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p.
Proof. intros. unfold prim_bytes. rewrite if_false by lia. reflexivity. Qed.

Lemma hrx5_k3p2m_out sh n v p : @data_at W sh (tarray tuchar n) v p |-- hout sh n p.
Proof. unfold hout. rewrite <- (@data_at__tarray_tuchar_cs W HCS). apply data_at_data_at_. Qed.

Section K3P2.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_K3P_2_ok : hrx5_K3P_2_stmt x25519 aead_enc aead_dec xaead_enc xaead_dec.
Proof.
  unfold hrx5_K3P_2_stmt; intros Espec gv L FR R sec birth S1 w NS PS T1 head nk KE st i kc lul q proto ip4 ip6 port mc
    img M1 j P HLEM HY.
  unfold hrx5_K3P_Q1, hrx5_K3P_st, hrx5_K3P_props, hrx5_Delta, hrx5_K3P_S2, hrx5_ltemps, hrx5_lvars, hrx5_wcore,
    hrx5_rest, hrx5_globs, hrx5_scr, hrx5_K3_XF; cbn [app].
  unfold hrx5_RB, hrx5_R.
  abbreviate_semax.
  Intros.
  assert (HinN: In (Znth j NS) NS) by (apply Znth_In; lia).
  pose proof HLEM as (HL1 & _ & HL3 & _).
  destruct (HL3 _ _ _ _ _ _ _ _ _ H0 HinN) as (P' & HP' & Hpok & _).
  rewrite H6 in HP'. injection HP' as <-.
  assert (Hinv': hrx5_inv x25519 R L NS (supd PS (hn_p (Znth j NS)) (hrx5_K3P_peer P)) KE T1 head nk).
  { apply (HL1 R L NS PS KE T1 head nk (hn_p (Znth j NS)) Ews P (hrx5_K3P_peer P) H0 H6).
    - destruct P; exact Hpok.
    - destruct P; reflexivity. }
  sep_apply (hrx5_k3p2_node (hrx5_head NS) NS (Znth j NS) (hn_p (Znth j NS)) HinN eq_refl).
  unfold peers_rep. rewrite (hrx5_k3p2_split PS (hn_p (Znth j NS)) Ews P peer_item_rep H6). cbn [peer_item_rep].
  sep_apply (hrx5_k3p2_peer_open Ews (hn_p (Znth j NS)) P). Intros lk.
  forward.
  forward.
  replace (hout Tsh 16 (l_ck L)) with (@data_at_ W Tsh (tarray tuchar 16) (l_ck L))
    by (unfold hout; apply data_at__tarray_tuchar_cs).
  forward_call (l_ck L, 16, Tsh).
  Intros bs.
  rewrite (hrx5_k3p2_nd Tsh 16 bs (l_ck L)) by assumption.
  forward.
  forward.
  rewrite hrx5_k3p2_cm_open. Intros. unfold hrx5_k3p2_cm.
  unfold wg_consts. rewrite hrx5_k3p2_zero_page.
  pose proof H4 as (Lno & Len).
  pose proof H7 as (Lck & Llm & Ldk & Lmk).
  set (ckb := map Byte.repr bs).
  assert (Lckb: Zlength ckb = 16) by (subst ckb; rewrite Zlength_map; assumption).
  replace (@data_at W Ews (tarray tuchar 32) (bytes (cm_enc M1)) (offset_val 32 mc))
    with (@data_at W Ews (tarray tuchar (Zlength ckb + 16)) (bytes (cm_enc M1)) (offset_val 32 mc))
    by (rewrite Lckb; reflexivity).
  sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength ckb + 16)) (bytes (cm_enc M1)) (offset_val 32 mc)).
  replace (@data_at W Tsh (tarray tuchar 16) (bytes ckb) (l_ck L)) with (@prim_bytes W Tsh ckb (l_ck L))
    by (unfold prim_bytes; rewrite if_false by lia; rewrite Lckb; reflexivity).
  replace (@data_at W Ews (tarray tuchar 16) (bytes (ck_last_mac1 (p_cookie P))) (offset_val 386 (hn_p (Znth j NS))))
    with (@prim_bytes W Ews (ck_last_mac1 (p_cookie P)) (offset_val 386 (hn_p (Znth j NS))))
    by (unfold prim_bytes; rewrite if_false by lia; rewrite Llm; reflexivity).
  assert_PROP (isptr (hn_p (Znth j NS))) as Pp.
  { entailer!. }
  forward_call (Ews, offset_val 32 mc, Tsh, l_ck L, ckb, Ews, offset_val 386 (hn_p (Znth j NS)),
                ck_last_mac1 (p_cookie P), Ews, offset_val 8 mc, cm_nonce M1, Ews,
                offset_val 402 (hn_p (Znth j NS)), ck_dkey (p_cookie P), gv).
  { apply prop_right. rewrite Lckb, Llm. destruct mc; try contradiction.
    destruct (hn_p (Znth j NS)); try contradiction. simpl. rewrite !Ptrofs.add_assoc. reflexivity. }
  pose proof HY as (_ & _ & HX).
  assert (HM2: cm_ok (mkCM (cm_type M1) (cm_receiver M1) (cm_nonce M1)
                  (xaead_enc (ck_dkey (p_cookie P)) (cm_nonce M1) (ck_last_mac1 (p_cookie P)) ckb))).
  { unfold cm_ok; cbn [cm_nonce cm_enc]. rewrite (xaead_enc_length _ _ HX). lia. }
  replace (Zlength ckb + 16) with 32 by lia.
  assert (HF := hrx5_k3p2_cm_fold Ews mc _ HM2 H10).
  unfold hrx5_k3p2_cm, bytes in HF. cbn [cm_type cm_receiver cm_nonce cm_enc] in HF.
  sep_apply HF. clear HF.
  rewrite (hrx5_k3p2m_pb Ews (ck_last_mac1 (p_cookie P))) by lia. rewrite Llm.
  assert (HC := hrx5_k3p2_peer_close Ews (hn_p (Znth j NS)) P lk H7). unfold bytes in HC.
  sep_apply HC. clear HC.
  fold (hrx5_K3P_peer P).
  assert (HS := hrx5_k3p2_supd PS (hn_p (Znth j NS)) Ews P (hrx5_K3P_peer P) peer_item_rep H6).
  cbn [peer_item_rep] in HS.
  sep_apply (derives_refl' _ _ (eq_sym HS)). clear HS.
  sep_apply (modus_ponens_wand (field_at Ews t_hnode4 (DOT HC._p) (hn_p (Znth j NS)) (hn_addr (Znth j NS)))
               (hnodes_rep4 W (hrx5_head NS) NS)).
  rewrite <- hrx5_k3p2_zero_page.
  rewrite (hrx5_k3p2m_pb Tsh ckb) by lia.
  sep_apply (hrx5_k3p2m_out Tsh (Zlength ckb) (map Vubyte ckb) (l_ck L)). rewrite Lckb.
  rewrite hrx5_K3P_F_eq. unfold hrx5_K3P_st, hrx5_K3P_props.
  Exists R sec birth S1 w NS (supd PS (hn_p (Znth j NS)) (hrx5_K3P_peer P)) T1.
  Exists head nk KE st i kc lul q.
  Exists proto ip4 ip6 port mc img (mkCM (cm_type M1) (cm_receiver M1) (cm_nonce M1)
                  (xaead_enc (ck_dkey (p_cookie P)) (cm_nonce M1) (ck_last_mac1 (p_cookie P)) ckb)).
  unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_K3_XF, wg_consts, peers_rep;
    cbn [app].
  go_lower.
  apply andp_right.
  { apply prop_right. refine (conj H (conj Hinv' (conj H1 (conj H2 (conj H3 (conj HM2 _)))))). repeat split; auto. }
  cancel.
Qed.

End K3P2.
