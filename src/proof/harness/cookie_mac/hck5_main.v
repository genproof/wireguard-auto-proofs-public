(* law cookie_mac: main's body from the prologue (initial globals, stack frame) and the fourteen
   phases of hck5_cut.v.  Port of v1's hck3_main.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_cut.
Require Import WgNoise.proof.harness.cookie_mac.hck5_spec.
Require Import WgNoise.proof.harness.cookie_mac.hck5_defs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_conv.
Require Import WgNoise.proof.harness.cookie_mac.hck5_globals.
Require Import WgNoise.proof.harness.cookie_mac.hck5_free.
Require Import WgNoise.proof.harness.cookie_mac.hck5_P1.
Require Import WgNoise.proof.harness.cookie_mac.hck5_P1b.
Require Import WgNoise.proof.harness.cookie_mac.hck5_P2.
Require Import WgNoise.proof.harness.cookie_mac.hck5_P3.
Require Import WgNoise.proof.harness.cookie_mac.hck5_P4.
Require Import WgNoise.proof.harness.cookie_mac.hck5_P5a.
Require Import WgNoise.proof.harness.cookie_mac.hck5_P5.
Require Import WgNoise.proof.harness.cookie_mac.hck5_P5c.
Require Import WgNoise.proof.harness.cookie_mac.hck5_P6.
Require Import WgNoise.proof.harness.cookie_mac.hck5_P6b.
Require Import WgNoise.proof.harness.cookie_mac.hck5_P6c.
Require Import WgNoise.proof.harness.cookie_mac.hck5_P7.
Require Import WgNoise.proof.harness.cookie_mac.hck5_P7b.
Require Import WgNoise.proof.harness.cookie_mac.hck5_P8.
Require WgNoise.harness.x_cookie_mac.code.

#[local] Existing Instance W_cookie_mac.
Local Open Scope Z_scope.

Section Main.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hck5_main_body :
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax_body hck5_V (hck5_Gprog x25519 aead_enc aead_dec xaead_enc xaead_dec) HK.f_main hck5_main_spec.
Proof.
  intros HH. pose proof (hck5_free_ok x25519) as HF.
  unfold hck5_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (shim_state4 gv hck5_shim0 hck5_w0 * noise_globals_raw gv zeros32 zeros32 Int64.zero *
                              wg_consts gv * hck5_consts gv * TT)%logic);
    [apply hck5_init_globals | reflexivity
    | apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction; subst x; vm_compute; exact I | ].
  process_stackframe_of.
  set (FR0 := (TT * has_ext tt)%logic).
  set (L := mkLoc5 v_wa v_wb v_ita v_itb v_pta v_ptb v_p v_ib v_cs v_hs0 v_ps0 v_da v_db v_sks v_ss v_skb
              v_raw_a v_raw_b v_pub v_k v_mac1 v_mac2 v_cookie__1 v_secret).
  eapply semax_pre with (P' := hck5_S0 gv L FR0).
  { unfold hck5_S0, hck5_lvars, hck5_snaps0. subst L.
    cbn [l_wa l_wb l_ita l_itb l_pta l_ptb l_p l_ib l_cs l_hs0 l_ps0 l_da l_db l_sks l_ss l_skb l_rawa l_rawb
         l_pub l_k l_mac1 l_mac2 l_cookie l_secret app].
    rewrite !hck5_conv_dev, !hck5_conv_itab, !hck5_conv_ptab, !hck5_conv_peer, !hck5_conv_mident,
      !hck5_conv_cksnap, !hck5_conv_skb, !hck5_conv_bytes, !hck5_conv_hsnap, !hck5_conv_prsnap,
      !hck5_conv_devsnap, !hck5_conv_skbsnap, !hck5_conv_shimsnap.
    sep_apply (create_mem_mgr gv). unfold FR0. entailer!. }
  rewrite hck5_body_eq.
  destruct hck5_phases_eq as (E1 & E1b & E2 & E3 & E4 & E5a & E5 & E5c & E6 & E6b & E6c & E7 & E7b & E8).
  eapply semax_seq with (Q := FF); [| apply semax_ff].
  eapply hck5_semax_cut with (Q := hck5_S1 x25519 gv L FR0);
    [discriminate | rewrite hck5_overridePost2, <- E1; apply hck5_P1_ok; exact HH |].
  eapply hck5_semax_cut with (Q := hck5_S1b x25519 gv L FR0);
    [discriminate | rewrite hck5_overridePost2, <- E1b; apply hck5_P1b_ok; exact HH |].
  eapply hck5_semax_cut with (Q := hck5_S2 x25519 gv L FR0);
    [discriminate | rewrite hck5_overridePost2, <- E2; apply hck5_P2_ok; [exact HH | exact HF] |].
  eapply hck5_semax_cut with (Q := hck5_S3 x25519 gv L FR0);
    [discriminate | rewrite hck5_overridePost2, <- E3; apply hck5_P3_ok; exact HH |].
  eapply hck5_semax_cut with (Q := hck5_S4 x25519 gv L FR0);
    [discriminate | rewrite hck5_overridePost2, <- E4; apply hck5_P4_ok; exact HH |].
  eapply hck5_semax_cut with (Q := hck5_S5a x25519 gv L FR0);
    [discriminate | rewrite hck5_overridePost2, <- E5a; apply hck5_P5a_ok; exact HH |].
  eapply hck5_semax_cut with (Q := hck5_S5 x25519 gv L FR0);
    [discriminate | rewrite hck5_overridePost2, <- E5; apply hck5_P5_ok; exact HH |].
  eapply hck5_semax_cut with (Q := hck5_S5c x25519 gv L FR0);
    [discriminate | rewrite hck5_overridePost2, <- E5c; apply hck5_P5c_ok; exact HH |].
  eapply hck5_semax_cut with (Q := hck5_S6a x25519 gv L FR0);
    [discriminate | rewrite hck5_overridePost2, <- E6; apply hck5_P6_ok; exact HH |].
  eapply hck5_semax_cut with (Q := hck5_S6b x25519 gv L FR0);
    [discriminate | rewrite hck5_overridePost2, <- E6b; apply hck5_P6b_ok; exact HH |].
  eapply hck5_semax_cut with (Q := hck5_S6 x25519 gv L FR0);
    [discriminate | rewrite hck5_overridePost2, <- E6c; apply hck5_P6c_ok; exact HH |].
  eapply hck5_semax_cut with (Q := hck5_S7 x25519 gv L FR0);
    [discriminate | rewrite hck5_overridePost2, <- E7; apply hck5_P7_ok; exact HH |].
  eapply hck5_semax_cut with (Q := hck5_S7b x25519 gv L FR0);
    [discriminate | rewrite hck5_overridePost2, <- E7b; apply hck5_P7b_ok; exact HH |].
  rewrite <- E8. apply hck5_P8_ok; [exact HH | exact HF].
Qed.

End Main.
