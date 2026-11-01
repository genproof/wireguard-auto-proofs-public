(* law consume_initiation_any: main's body, from the prologue (initial globals, stack
   frame) and the nine phases. *)
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
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_cut.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_globals.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_conv.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_close.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_P1.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_P2.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_P3.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_PK.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_P4.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_P5.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_P6.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_P7.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_P8.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

Section Main.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_main_body :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax_body hci5_V (hci5_Gprog x25519 aead_enc aead_dec) HC.f_main hci5_main_spec.
Proof.
  intros HH.
  assert (HC: hci5_closeH) by (apply hci5_close_ok; apply HH).
  unfold hci5_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (shim_state gv hci5_shim0 * noise_globals_raw gv zeros32 zeros32 Int64.zero *
                              wg_consts gv * hci5_consts gv * TT)%logic);
    [apply hci5_init_globals | reflexivity
    | apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; subst x; vm_compute; exact I | ].
  process_stackframe_of.
  set (FR0 := (TT * has_ext tt)%logic).
  set (L := mkLoc5 v_wb v_itb v_ptb v_ia v_ib v_raw_a v_raw_b v_pub v_ts v_img v_img_after v_peers v_ds v_ss
              v_ci v_mi v_eraw v_ss__1 v_ss__2).
  eapply semax_pre with (P' := hci5_S0 gv L FR0).
  { unfold hci5_S0, hci5_lvars, hci5_snaps0, hci5_scr. subst L.
    cbn [app l_wb l_itb l_ptb l_ia l_ib l_rawa l_rawb l_pub l_ts l_img l_imga l_peers l_ds l_ss l_ci l_mi l_eraw
         l_ss1 l_ss2].
    rewrite !hci5_conv_dev, !hci5_conv_itab, !hci5_conv_ptab, !hci5_conv_mident, !hci5_conv_minit,
      !hci5_conv_mcinit, !hci5_conv_devsnap, !hci5_conv_shimsnap, !hci5_conv_bytes.
    sep_apply (create_mem_mgr gv). unfold FR0. entailer!. }
  rewrite hci5_body_eq.
  destruct hci5_phases_eq as (E1 & E2 & E3 & EK & E4 & E5 & E6 & E7 & E8).
  eapply semax_seq with (Q := FF); [| apply semax_ff].
  eapply hci5_semax_cut with (Q := hci5_SA x25519 gv L FR0);
    [discriminate | rewrite hci5_overridePost2, <- E1; apply (hci5_P1_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH |].
  eapply hci5_semax_cut with (Q := hci5_SA x25519 gv L FR0);
    [discriminate | rewrite hci5_overridePost2, <- E2; apply (hci5_P2_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH |].
  eapply hci5_semax_cut with (Q := hci5_SA x25519 gv L FR0);
    [discriminate | rewrite hci5_overridePost2, <- E3; apply (hci5_P3_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH |].
  eapply hci5_semax_cut with (Q := hci5_SK x25519 gv L FR0);
    [discriminate | rewrite hci5_overridePost2, <- EK; apply (hci5_PK_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH |].
  eapply hci5_semax_cut with (Q := hci5_S4 x25519 gv L FR0);
    [discriminate | rewrite hci5_overridePost2, <- E4; apply (hci5_P4_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); auto |].
  eapply hci5_semax_cut with (Q := hci5_S5 x25519 gv L FR0);
    [discriminate | rewrite hci5_overridePost2, <- E5; apply (hci5_P5_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH |].
  eapply hci5_semax_cut with (Q := hci5_S6 x25519 aead_dec gv L FR0);
    [discriminate | rewrite hci5_overridePost2, <- E6; apply (hci5_P6_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH |].
  eapply hci5_semax_cut with (Q := hci5_S7 x25519 aead_dec gv L FR0);
    [discriminate | rewrite hci5_overridePost2, <- E7; apply (hci5_P7_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH |].
  rewrite <- E8. apply (hci5_P8_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); auto.
Qed.

End Main.
