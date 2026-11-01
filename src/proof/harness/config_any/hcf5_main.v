(* law config_any: main's body, from the prologue (initial globals, stack frame)
   and the phases. *)
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
Require Import WgNoise.proof.harness.config_any.hcf5_world.
Require Import WgNoise.proof.harness.config_any.hcf5_cut.
Require Import WgNoise.proof.harness.config_any.hcf5_spec.
Require Import WgNoise.proof.harness.config_any.hcf5_globals.
Require Import WgNoise.proof.harness.config_any.hcf5_defs.
Require Import WgNoise.proof.harness.config_any.hcf5_conv.
Require Import WgNoise.proof.harness.config_any.hcf5_sep.
Require Import WgNoise.proof.harness.config_any.hcf5_C.
Require Import WgNoise.proof.harness.config_any.hcf5_PA1.
Require Import WgNoise.proof.harness.config_any.hcf5_PA2.
Require Import WgNoise.proof.harness.config_any.hcf5_PK.
Require Import WgNoise.proof.harness.config_any.hcf5_PS.
Require Import WgNoise.proof.harness.config_any.hcf5_P1.
Require Import WgNoise.proof.harness.config_any.hcf5_P2.
Require Import WgNoise.proof.harness.config_any.hcf5_P3.
Require Import WgNoise.proof.harness.config_any.hcf5_P4.
Require Import WgNoise.proof.harness.config_any.hcf5_P5a.
Require Import WgNoise.proof.harness.config_any.hcf5_P5b.
Require Import WgNoise.proof.harness.config_any.hcf5_P5c.
Require Import WgNoise.proof.harness.config_any.hcf5_P6.
Require Import WgNoise.proof.harness.config_any.hcf5_PE.
Require WgNoise.harness.x_config_any.code.

#[local] Existing Instance W_config_any.
Local Open Scope Z_scope.

Section Main.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcf5_main_body :
  hcf5_hyps x25519 ->
  semax_body hcf5_V (hcf5_Gprog x25519) HF.f_main hcf5_main_spec.
Proof.
  intros HH.
  pose proof hcf5_sep_ok as HS.
  destruct (hcf5_C_ok x25519 HH) as (C1 & C2 & C3 & C4 & C5 & C6).
  unfold hcf5_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (shim_state gv hcf5_shim0 * noise_globals_raw gv zeros32 zeros32 Int64.zero *
                              wg_consts gv * hcf5_consts gv * TT)%logic);
    [apply hcf5_init_globals | reflexivity
    | apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; subst x; vm_compute; exact I | ].
  process_stackframe_of.
  set (FR0 := (TT * has_ext tt)%logic).
  set (L := mkLocF v_w v_it v_pt v_p v_q v_id v_hs0 v_hq v_ps0 v_ds v_ss v_raw0 v_raw v_pub v_qpub v_psk v_dh).
  eapply semax_pre with (P' := hcf5_S0 gv L FR0).
  { unfold hcf5_S0, hcf5_lvars, hcf5_pre, hcf5_X0. subst L.
    cbn [app l_w l_it l_pt l_p l_q l_id l_hs0 l_hq l_ps0 l_ds l_ss l_raw0 l_raw l_pub l_qpub l_psk l_dh].
    rewrite !hcf5_conv_dev, !hcf5_conv_itab, !hcf5_conv_ptab, !hcf5_conv_peer, !hcf5_conv_mident,
      !hcf5_conv_hsnap, !hcf5_conv_prsnap, !hcf5_conv_devsnap, !hcf5_conv_shimsnap, !hcf5_conv_bytes.
    sep_apply (create_mem_mgr gv). unfold FR0. entailer!. }
  rewrite hcf5_body_eq.
  destruct hcf5_phases_eq as (EA1 & EA2 & EK & ES & E1 & EC1 & E2 & EC2 & E3 & EC3 & E4 & EC4 & E5a & E5b & E5c &
                              EC5 & E6 & EC6 & EE).
  eapply semax_seq with (Q := FF); [| apply semax_ff].
  eapply hcf5_semax_cut with (Q := hcf5_SA1 x25519 gv L FR0);
    [discriminate | rewrite hcf5_overridePost2, <- EA1; apply (hcf5_PA1_ok x25519); exact HH |].
  eapply hcf5_semax_cut with (Q := hcf5_SA gv L FR0);
    [discriminate | rewrite hcf5_overridePost2, <- EA2; apply (hcf5_PA2_ok x25519); exact HH |].
  eapply hcf5_semax_cut with (Q := hcf5_SK gv L FR0);
    [discriminate | rewrite hcf5_overridePost2, <- EK; apply (hcf5_PK_ok x25519); exact HH |].
  eapply hcf5_semax_cut with (Q := hcf5_SX0 gv L FR0);
    [discriminate | rewrite hcf5_overridePost2, <- ES; apply (hcf5_PS_ok x25519); exact HH |].
  eapply hcf5_semax_cut with (Q := hcf5_SX1 x25519 gv L FR0);
    [discriminate | rewrite hcf5_overridePost2, <- E1; apply (hcf5_P1_ok x25519); exact HH |].
  eapply hcf5_semax_cut with (Q := hcf5_SX1 x25519 gv L FR0);
    [discriminate | rewrite hcf5_overridePost2, <- EC1; apply C1 |].
  eapply hcf5_semax_cut with (Q := hcf5_SX1 x25519 gv L FR0);
    [discriminate | rewrite hcf5_overridePost2, <- E2; apply (hcf5_P2_ok x25519); exact HH |].
  eapply hcf5_semax_cut with (Q := hcf5_SX1 x25519 gv L FR0);
    [discriminate | rewrite hcf5_overridePost2, <- EC2; apply C2 |].
  eapply hcf5_semax_cut with (Q := hcf5_SX1 x25519 gv L FR0);
    [discriminate | rewrite hcf5_overridePost2, <- E3; apply (hcf5_P3_ok x25519); exact HH |].
  eapply hcf5_semax_cut with (Q := hcf5_SX1 x25519 gv L FR0);
    [discriminate | rewrite hcf5_overridePost2, <- EC3; apply C3 |].
  eapply hcf5_semax_cut with (Q := hcf5_SX1 x25519 gv L FR0);
    [discriminate | rewrite hcf5_overridePost2, <- E4; apply (hcf5_P4_ok x25519); exact HH |].
  eapply hcf5_semax_cut with (Q := hcf5_SX1 x25519 gv L FR0);
    [discriminate | rewrite hcf5_overridePost2, <- EC4; apply C4 |].
  eapply hcf5_semax_cut with (Q := hcf5_S5a x25519 gv L FR0);
    [discriminate | rewrite hcf5_overridePost2, <- E5a; apply (hcf5_P5a_ok x25519); [exact HH | exact HS] |].
  eapply hcf5_semax_cut with (Q := hcf5_S5b x25519 gv L FR0);
    [discriminate | rewrite hcf5_overridePost2, <- E5b; apply (hcf5_P5b_ok x25519); exact HH |].
  eapply hcf5_semax_cut with (Q := hcf5_SX5 x25519 gv L FR0);
    [discriminate | rewrite hcf5_overridePost2, <- E5c; apply (hcf5_P5c_ok x25519); exact HH |].
  eapply hcf5_semax_cut with (Q := hcf5_SX5 x25519 gv L FR0);
    [discriminate | rewrite hcf5_overridePost2, <- EC5; apply C5 |].
  eapply hcf5_semax_cut with (Q := hcf5_SX5 x25519 gv L FR0);
    [discriminate | rewrite hcf5_overridePost2, <- E6; apply (hcf5_P6_ok x25519); exact HH |].
  eapply hcf5_semax_cut with (Q := hcf5_SX5 x25519 gv L FR0);
    [discriminate | rewrite hcf5_overridePost2, <- EC6; apply C6 |].
  rewrite <- EE. apply (hcf5_PE_ok x25519); [exact HH | exact HS].
Qed.

End Main.
