(* law handshake_clear: main's body, from the prologue (initial globals, stack frame)
   and the nine phases. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_world.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_cut.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_spec.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_globals.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_defs.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_conv.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_close.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_P1.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_P2.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_P3.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_P4.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_PK.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_P5.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_P6.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_P7.
Require Import WgNoise.proof.harness.handshake_clear.hcl5_P8.
Require WgNoise.harness.x_handshake_clear.code.

#[local] Existing Instance W_handshake_clear.
Local Open Scope Z_scope.

Section Main.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcl5_main_body :
  hcl5_hyps x25519 ->
  semax_body hcl5_V (hcl5_Gprog x25519) HC.f_main hcl5_main_spec.
Proof.
  intros HH.
  assert (HC: hcl5_closeH) by (apply hcl5_close_ok; apply HH).
  unfold hcl5_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (shim_state gv hcl5_shim0 * wg_consts gv * TT)%logic);
    [apply hcl5_init_globals | reflexivity
    | apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; subst x; vm_compute; exact I | ].
  process_stackframe_of.
  set (FR0 := (TT * has_ext tt)%logic).
  set (L := mkLoc5 v_w v_it v_pt v_raw v_pub v_peers v_ds v_ss).
  eapply semax_pre with (P' := hcl5_S0 gv L FR0).
  { unfold hcl5_S0, hcl5_lvars, hcl5_snaps0, hcl5_scr. subst L.
    cbn [app l_w l_it l_pt l_raw l_pub l_peers l_ds l_ss].
    rewrite !hcl5_conv_dev, !hcl5_conv_itab, !hcl5_conv_ptab, !hcl5_conv_devsnap, !hcl5_conv_shimsnap,
      !hcl5_conv_bytes.
    sep_apply (create_mem_mgr gv). unfold FR0. entailer!. }
  rewrite hcl5_body_eq.
  destruct hcl5_phases_eq as (E1 & E2 & E3 & E4 & EK & E5 & E6 & E7 & E8).
  eapply semax_seq with (Q := FF); [| apply semax_ff].
  eapply hcl5_semax_cut with (Q := hcl5_SA x25519 gv L FR0);
    [discriminate | rewrite hcl5_overridePost2, <- E1; apply (hcl5_P1_ok x25519); exact HH |].
  eapply hcl5_semax_cut with (Q := hcl5_SA x25519 gv L FR0);
    [discriminate | rewrite hcl5_overridePost2, <- E2; apply (hcl5_P2_ok x25519); exact HH |].
  eapply hcl5_semax_cut with (Q := hcl5_SB x25519 gv L FR0);
    [discriminate | rewrite hcl5_overridePost2, <- E3; apply (hcl5_P3_ok x25519); auto |].
  eapply hcl5_semax_cut with (Q := hcl5_SB x25519 gv L FR0);
    [discriminate | rewrite hcl5_overridePost2, <- E4; apply (hcl5_P4_ok x25519); exact HH |].
  eapply hcl5_semax_cut with (Q := hcl5_SK x25519 gv L FR0);
    [discriminate | rewrite hcl5_overridePost2, <- EK; apply (hcl5_PK_ok x25519); exact HH |].
  eapply hcl5_semax_cut with (Q := hcl5_S5 x25519 gv L FR0);
    [discriminate | rewrite hcl5_overridePost2, <- E5; apply (hcl5_P5_ok x25519); exact HH |].
  eapply hcl5_semax_cut with (Q := hcl5_S5 x25519 gv L FR0);
    [discriminate | rewrite hcl5_overridePost2, <- E6; apply (hcl5_P6_ok x25519); exact HH |].
  eapply hcl5_semax_cut with (Q := hcl5_S7 x25519 gv L FR0);
    [discriminate | rewrite hcl5_overridePost2, <- E7; apply (hcl5_P7_ok x25519); exact HH |].
  rewrite <- E8. apply (hcl5_P8_ok x25519); auto.
Qed.

End Main.
