(* law handshake_receive, phase B4, segment R: statement 25 (the model block) for a response object OResp M: hrx5_B4_Q -> hrx5_S4. *)
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
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_pure.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_sep.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_W.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_E.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_N.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_K.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_C.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_M.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_O.
Local Open Scope logic.

(* the response branch RS from the parts W E N K C M (port of hcr5_q3_all) *)
Lemma hrx5_B4_R_core : hrx5_B4_R_core_stmt.
Proof.
  unfold hrx5_B4_R_core_stmt.
  intros Espec x25519 aead_dec xaead_enc xaead_dec gv L nk KE st i S lul m img n tw IA KA NS PS T M FX Rr
    Hok HlIA Hwf Hptr Hpool Hhp HndP Hhs Hfc0 HptrN.
  destruct hrx5_B4_R_pure_ok as (Pfind & Phs & Ppool & Plm & Pnode & Psnap & _).
  pose proof Hwf as (HwL & HwI & HwD & HwS).
  set (NSs := hnodes_snapped4 T NS PS) in *.
  rewrite hrx5_B4_R_rb_eq.
  eapply semax_seq; [apply hrx5_B4_R_W_ok |].
  destruct (t_find_index T (t_L T) (rm_receiver M)) as [[a E] |] eqn:Hfind.
  2: { apply (proj1 (@hrx5_B4_R_E_ok Espec x25519 aead_dec xaead_enc xaead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX Rr)); assumption. }
  destruct (@hrx5_B4_R_E_ok Espec x25519 aead_dec xaead_enc xaead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX Rr)
    as (E1 & E2 & E3).
  destruct (@hrx5_B4_R_K_ok Espec x25519 aead_dec xaead_enc xaead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX Rr)
    as (K1 & K2 & K3).
  destruct (@hrx5_B4_R_M_ok Espec x25519 aead_dec xaead_enc xaead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX Rr)
    as (M1 & M2).
  destruct (Int.eq (e_type E) IDX_HANDSHAKE) eqn:Hty.
  2: { eapply E2; eassumption. }
  apply (E3 a E Hfind Hty).
  destruct (Pfind T (t_L T) (rm_receiver M) a E Hfind) as [Ha HtE].
  assert (HtyE: e_type E = IDX_HANDSHAKE) by (apply Int.same_if_eq; exact Hty).
  destruct (Phs KA PS T a E Hpool HwD HtE HtyE) as (Hae & shp & P & HsfP & HinP).
  destruct (Psnap T NS PS Hhp) as (HsA & HsP & HsH).
  assert (HfcP: forall q, In q (map hn_p NSs) ->
            @field_compatible W t_peer [] q /\ In (hs_addr q) (saddrs (t_D T))).
  { intros q Hq. unfold NSs in Hq. rewrite HsP in Hq. pose proof Hhp as Hhp'. unfold hnodes_peers4 in Hhp'.
    rewrite Hhp' in Hq. split.
    - rewrite in_map_iff in Hq. destruct Hq as (x & <- & Hx).
      rewrite Forall_forall in Hfc0. apply (Hfc0 x Hx).
    - rewrite in_map_iff in Hq. destruct Hq as ([[q' shq] Q] & Hq' & Hx). simpl in Hq'. subst q'.
      eapply Ppool; eauto. }
  assert (HaD: In a (saddrs (t_D T))) by (apply HwI; exact Ha).
  assert (Hpa: isptr (hs_addr (e_peer E))).
  { rewrite <- Hae. rewrite Forall_forall in Hptr. apply Hptr. exact HaD. }
  rewrite hrx5_B4_R_hs_eq.
  eapply semax_seq; [eapply hrx5_B4_R_N_ok; eassumption |].
  assert (Hlm: hrx5_B4_R_lm NSs a = hrx5_nfind NS (e_peer E)) by (rewrite Hae; apply Plm; auto).
  destruct (Pnode T NS PS (e_peer E) shp P Hhp HsfP)
    as (NSa & N0 & NSb & HNS0 & HaN0 & HpN0 & HsnN0 & _).
  fold NSs in HNS0.
  assert (HpA0: isptr (hn_addr N0)).
  { rewrite Forall_forall in HptrN. apply HptrN. rewrite HNS0, map_app. apply in_or_app. right. left. reflexivity. }
  assert (HinN0: In (hn_addr N0) (map hn_addr NS)).
  { rewrite <- HsA. fold NSs. rewrite HNS0, map_app. apply in_or_app. right. left. reflexivity. }
  assert (HhsP: hs_ok (p_hs P)).
  { rewrite Forall_forall in Hhs. apply (Hhs _ HinP). }
  assert (Hp0: hrx5_B4_R_lm NSs a = hn_addr N0) by (rewrite Hlm, HaN0; reflexivity).
  rewrite Hp0.
  destruct (@hrx5_B4_R_K_ok Espec x25519 aead_dec xaead_enc xaead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX
    (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX) Rr)) as (K1' & _ & _).
  eapply semax_seq; [eapply K1'; eassumption |].
  destruct (Int.eq (hs_state (p_hs P)) HS_CREATED_INITIATION) eqn:Hst.
  2: { eapply K2; eassumption. }
  apply K3.
  rewrite hrx5_B4_R_call_eq.
  eapply hrx5_B4_R_C_ok; try eassumption.
  destruct (@hrx5_B4_R_M_ok Espec x25519 aead_dec xaead_enc xaead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX
    (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX) Rr)) as (M1' & _).
  eapply semax_seq; [eapply M1'; eassumption |].
  eapply M2; eassumption.
Qed.

Lemma hrx5_B4_R_ok : hrx5_B4_R_stmt.
Proof.
  unfold hrx5_B4_R_stmt, hrx5_B4_M_stmt.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port o dp img HH Ho.
  destruct o; cbn in Ho; try contradiction.
  eapply hrx5_B4_R_O_ok; [exact HH | exact hrx5_B4_R_core].
Qed.
