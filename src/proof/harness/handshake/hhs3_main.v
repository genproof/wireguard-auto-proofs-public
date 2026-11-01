(* law handshake: main's body, from the prologue (initial globals, stack frame) and the six phases. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_conv.
Require Import WgNoise.proof.harness.handshake.hhs3_globals.
Require Import WgNoise.proof.harness.handshake.hhs3_P1.
Require Import WgNoise.proof.harness.handshake.hhs3_P2.
Require Import WgNoise.proof.harness.handshake.hhs3_P3.
Require Import WgNoise.proof.harness.handshake.hhs3_P4.
Require Import WgNoise.proof.harness.handshake.hhs3_P5.
Require Import WgNoise.proof.harness.handshake.hhs3_P6.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Section Main.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_main_body :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax_body hhs3_V (hhs3_Gprog x25519 aead_enc aead_dec xaead_enc xaead_dec) HC.f_main hhs3_main_spec.
Proof.
  intros HH.
  unfold hhs3_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (shim_state gv hhs3_shim0 * noise_globals_raw gv zeros32 zeros32 Int64.zero *
                              wg_consts gv * hhs3_consts gv * TT)%logic);
    [apply hhs3_init_globals | reflexivity
    | apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; subst x; vm_compute; exact I | ].
  process_stackframe_of.
  set (FR0 := (TT * has_ext tt)%logic).
  set (L := mkLoc v_wa v_wb v_ita v_itb v_pta v_ptb v_pb v_pa v_ia v_ib v_raw_a v_raw_b v_psk v_ssa v_ssb
              v_tmp v_ts v_img v_img_before v_rimg v_rimg_before v_mi v_ci v_mr v_st2 v_snap v_d1 v_d2
              v_d1__1 v_d2__1 v_first v_second).
  eapply semax_pre with (P' := hhs3_S0 gv L FR0).
  { unfold hhs3_S0, hhs3_lvars, hhs3_scr_tmp. subst L.
    cbn [app l_wa l_wb l_ita l_itb l_pta l_ptb l_pb l_pa l_ia l_ib l_rawa l_rawb l_psk l_ssa l_ssb l_tmp l_ts
         l_img l_imgb l_rimg l_rimgb l_mi l_ci l_mr l_st2 l_snap l_d1 l_d2 l_d1b l_d2b l_first l_second].
    rewrite !hhs3_conv_dev, !hhs3_conv_itab, !hhs3_conv_ptab, !hhs3_conv_peer, !hhs3_conv_mident,
      !hhs3_conv_minit, !hhs3_conv_mcinit, !hhs3_conv_mresp, !hhs3_conv_mstate, !hhs3_conv_hsnap,
      !hhs3_conv_bytes.
    sep_apply (create_mem_mgr gv). unfold FR0. entailer!. }
  rewrite hhs3_body_eq.
  destruct hhs3_phases_eq as (E1 & E2 & E3 & E4 & E5 & E6).
  eapply semax_seq with (Q := FF); [| apply semax_ff].
  eapply hhs3_semax_cut with (Q := hhs3_S1 x25519 gv L FR0);
    [discriminate | rewrite hhs3_overridePost2, <- E1; apply hhs3_P1_ok; exact HH |].
  eapply hhs3_semax_cut with (Q := hhs3_S2 x25519 aead_enc gv L FR0);
    [discriminate | rewrite hhs3_overridePost2, <- E2; apply hhs3_P2_ok; exact HH |].
  eapply hhs3_semax_cut with (Q := hhs3_S3 x25519 aead_enc aead_dec gv L FR0);
    [discriminate | rewrite hhs3_overridePost2, <- E3; apply hhs3_P3_ok; exact HH |].
  eapply hhs3_semax_cut with (Q := hhs3_S4 x25519 aead_enc aead_dec gv L FR0);
    [discriminate | rewrite hhs3_overridePost2, <- E4; apply hhs3_P4_ok; exact HH |].
  eapply hhs3_semax_cut with (Q := hhs3_S5 x25519 aead_enc aead_dec gv L FR0);
    [discriminate | rewrite hhs3_overridePost2, <- E5; apply hhs3_P5_ok; exact HH |].
  rewrite <- E6. apply hhs3_P6_ok; exact HH.
Qed.

End Main.
