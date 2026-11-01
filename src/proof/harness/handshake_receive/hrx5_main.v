(* law handshake_receive: main's body, from the prologue
   (initial globals, stack frame) and the phases PA .. PE, the packet loop PL (hrx5_loop.v) and PZ. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_globals.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_PA.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_PB.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_PC.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_PD.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_PE.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_loop.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_PZ.

#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Section Main.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_main_body :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax_body hrx5_V (hrx5_Gprog x25519 aead_dec xaead_enc xaead_dec) HM.f_main hrx5_main_spec.
Proof.
  intros HH.
  unfold hrx5_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred
    (shim_state gv hrx5_shim0 * noise_globals_raw gv zeros32 zeros32 Int64.zero * wg_consts gv *
     hrx5_consts gv * lul_rep gv Int64.zero *
     @data_at_ HRX Ews t_rxlog (gv HM._wg_shim_rx) *
     @data_at_ HRX Ews tint (gv HM._wg_shim_handshake_queue_len) * TT)%logic);
    [apply hrx5_init_globals | reflexivity
    | apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; subst x; vm_compute; exact I | ].
  process_stackframe_of.
  set (FR0 := (TT * has_ext tt)%logic).
  set (L := mkLocR5 v_wd v_itd v_ptd v_id v_ik v_raw_d v_raw_k v_pub v_mk1 v_ss_k v_peers v_ds v_ss v_sks v_skb
              v_ci v_st v_secret v_c v_mac v_pt v_t v_t__1 v_ck v_sst v_before).
  eapply semax_pre with (P' := hrx5_S0 gv L FR0).
  { unfold hrx5_S0, hrx5_lvars, hrx5_rglobs, hrx5_skb0, hrx5_scr. subst L.
    cbn [app l_wd l_itd l_ptd l_id l_ik l_rawd l_rawk l_pub l_mk1 l_ssk l_peers l_ds l_ss l_sks l_skb l_ci l_st
         l_secret l_c l_mac l_pt l_t l_t1 l_ck l_sst l_before].
    rewrite !hrx5_conv_dev, !hrx5_conv_itab, !hrx5_conv_ptab, !hrx5_conv_mident, !hrx5_conv_devsnap,
      !hrx5_conv_shimsnap, !hrx5_conv_skbsnap, !hrx5_conv_skb, !hrx5_conv_mcinit, !hrx5_conv_mstate,
      !hrx5_conv_init, !hrx5_conv_resp, !hrx5_conv_bytes.
    sep_apply (create_mem_mgr gv). unfold FR0. entailer!. }
  rewrite hrx5_body_eq.
  destruct hrx5_phases_eq as (EA & EB & EC & ED & EE & EZ).
  eapply semax_seq with (Q := FF); [| apply semax_ff].
  eapply hrx5_semax_cut with (Q := hrx5_SA x25519 gv L FR0);
    [discriminate | rewrite hrx5_overridePost2, <- EA; apply (hrx5_PA_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH |].
  eapply hrx5_semax_cut with (Q := hrx5_SB x25519 gv L FR0);
    [discriminate | rewrite hrx5_overridePost2, <- EB; apply (hrx5_PB_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH |].
  eapply hrx5_semax_cut with (Q := hrx5_SB x25519 gv L FR0);
    [discriminate | rewrite hrx5_overridePost2, <- EC; apply (hrx5_PC_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH |].
  eapply hrx5_semax_cut with (Q := hrx5_SB x25519 gv L FR0);
    [discriminate | rewrite hrx5_overridePost2, <- ED; apply (hrx5_PD_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH |].
  eapply hrx5_semax_cut with (Q := hrx5_SE x25519 gv L FR0);
    [discriminate | rewrite hrx5_overridePost2, <- EE; apply (hrx5_PE_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH |].
  eapply semax_seq with (Q := hrx5_SX x25519 gv L FR0).
  - rewrite hrx5_overridePost2. apply (hrx5_PL_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH.
  - rewrite <- EZ. apply (hrx5_PZ_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH.
Qed.

End Main.
