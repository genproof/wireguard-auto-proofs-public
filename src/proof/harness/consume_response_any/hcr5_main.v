(* law consume_response_any: main's body, from the prologue (initial globals, stack
   frame) and the phases P1 .. P7. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_cut.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_conv.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_globals.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_close.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_P1.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_P2.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_P3.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_PK.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_P5.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_P6.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_P7.
Require WgNoise.harness.x_consume_response_any.code.

#[local] Existing Instance W_consume_response_any.
Local Open Scope Z_scope.

Section Main.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcr5_main_body :
  hcr5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax_body hcr5_V (hcr5_Gprog x25519 aead_enc aead_dec xaead_enc xaead_dec) HR5.f_main hcr5_main_spec.
Proof.
  intros HH.
  assert (HC: hcr5_closeH) by (apply hcr5_close_ok; apply HH).
  unfold hcr5_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (shim_state4 gv hcr5_shim0 hcr5_w0 * noise_globals_raw gv zeros32 zeros32 Int64.zero *
                              wg_consts gv * hcr5_consts gv * TT)%logic);
    [apply hcr5_init_globals | reflexivity
    | apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; subst x; vm_compute; exact I | ].
  process_stackframe_of.
  set (FR0 := (TT * has_ext tt)%logic).
  set (L := mkLoc5 v_wa v_ita v_pta v_ia v_ib v_raw_a v_raw_b v_pub v_img v_img_after v_peers v_ds v_ss v_st v_mr
              v_cur v_eraw v_ei v_before).
  eapply semax_pre with (P' := hcr5_S0 gv L FR0).
  { unfold hcr5_S0, hcr5_lvars, hcr5_snaps0, hcr5_scr. subst L.
    cbn [app l_wa l_ita l_pta l_ia l_ib l_rawa l_rawb l_pub l_img l_imga l_peers l_ds l_ss l_st l_mr l_cur l_eraw
         l_ei l_before].
    rewrite !hcr5_conv_dev, !hcr5_conv_itab, !hcr5_conv_ptab, !hcr5_conv_mident, !hcr5_conv_mstate,
      !hcr5_conv_mresp, !hcr5_conv_bytes, !hcr5_conv_devsnap, !hcr5_conv_shimsnap.
    sep_apply (create_mem_mgr gv). unfold FR0. entailer!. }
  rewrite hcr5_body_eq.
  destruct hcr5_phases_eq as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
  eapply semax_seq with (Q := FF); [| apply semax_ff].
  eapply hcr5_semax_cut with (Q := hcr5_SA x25519 gv L FR0);
    [discriminate | rewrite hcr5_overridePost2, <- E1; apply hcr5_P1_ok; exact HH |].
  eapply hcr5_semax_cut with (Q := hcr5_SA x25519 gv L FR0);
    [discriminate | rewrite hcr5_overridePost2, <- E2; apply hcr5_P2_ok; exact HH |].
  eapply hcr5_semax_cut with (Q := hcr5_SA x25519 gv L FR0);
    [discriminate | rewrite hcr5_overridePost2, <- E3; apply hcr5_P3_ok; exact HH |].
  eapply hcr5_semax_cut with (Q := hcr5_SK x25519 gv L FR0);
    [discriminate | rewrite hcr5_overridePost2, <- E4; apply hcr5_PK_ok; exact HH |].
  eapply hcr5_semax_cut with (Q := hcr5_S5 x25519 gv L FR0);
    [discriminate | rewrite hcr5_overridePost2, <- E5; apply hcr5_P5_ok; exact HH |].
  eapply hcr5_semax_cut with (Q := hcr5_SE x25519 gv L FR0);
    [discriminate | rewrite hcr5_overridePost2, <- E6; apply hcr5_P6_ok; auto |].
  rewrite <- E7. apply hcr5_P7_ok; auto.
Qed.

End Main.
