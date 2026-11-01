(* law cookie_reply: main's body, from the prologue (initial globals, stack frame) and the 14
   phases.  Port of v1's hcy4_main.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_globals.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_close.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_P1 WgNoise.proof.harness.cookie_reply.hcy5_P2
  WgNoise.proof.harness.cookie_reply.hcy5_P3 WgNoise.proof.harness.cookie_reply.hcy5_P4
  WgNoise.proof.harness.cookie_reply.hcy5_P5 WgNoise.proof.harness.cookie_reply.hcy5_P5b
  WgNoise.proof.harness.cookie_reply.hcy5_P6
  WgNoise.proof.harness.cookie_reply.hcy5_P7 WgNoise.proof.harness.cookie_reply.hcy5_P8
  WgNoise.proof.harness.cookie_reply.hcy5_P9 WgNoise.proof.harness.cookie_reply.hcy5_P10
  WgNoise.proof.harness.cookie_reply.hcy5_P11 WgNoise.proof.harness.cookie_reply.hcy5_P12
  WgNoise.proof.harness.cookie_reply.hcy5_P13.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

Section Main.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_main_body :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax_body hcy5_V (hcy5_Gprog x25519 aead_enc aead_dec xaead_enc xaead_dec) HY.f_main hcy5_main_spec.
Proof.
  intros HH. pose proof hcy5_close_ok as HC.
  unfold hcy5_main_spec, QPmain_spec_ext', NDmk_funspec.
  split3; [reflexivity | reflexivity | ]. intros Espec DTL gv.
  eapply (main_pre_InitGpred (shim_state4 gv hcy5_shim0 hcy5_w0 * noise_globals_raw gv zeros32 zeros32 Int64.zero *
                              wg_consts gv * hcy5_consts gv * TT)%logic);
    [apply hcy5_init_globals | reflexivity
    | apply Forall_forall; intros x Hx; vm_compute in Hx; repeat destruct Hx as [Hx|Hx]; try contradiction;
      subst x; vm_compute; exact I | ].
  process_stackframe_of.
  set (FR0 := (TT * has_ext tt)%logic).
  set (L := mkLoc v_wa v_wb v_ita v_itb v_pta v_ptb v_ib v_skb v_raw_a v_raw_b v_pub v_secret v_cookie__1 v_k
              v_enc v_img v_img2 v_peers v_da v_db v_sks v_ss v_pt).
  eapply semax_pre with (P' := hcy5_S0 gv L FR0).
  { unfold hcy5_S0, hcy5_lvars. subst L.
    cbn [l_wa l_wb l_ita l_itb l_pta l_ptb l_ib l_skb l_rawa l_rawb l_pub l_secret l_cookie l_k l_enc l_img
         l_img2 l_peers l_da l_db l_sks l_ss l_pt].
    sep_apply (create_mem_mgr gv). unfold FR0. entailer!. }
  rewrite hcy5_body_eq.
  destruct hcy5_phases_eq as (E1 & E2 & E3 & E4 & E5 & E5b & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13).
  eapply semax_seq with (Q := FF); [| apply semax_ff].
  eapply hcy5_semax_cut with (Q := hcy5_S1 x25519 gv L FR0);
    [discriminate | rewrite hcy5_overridePost2, <- E1; apply hcy5_P1_ok; exact HH |].
  eapply hcy5_semax_cut with (Q := hcy5_S2 x25519 gv L FR0);
    [discriminate | rewrite hcy5_overridePost2, <- E2; apply hcy5_P2_ok; auto |].
  eapply hcy5_semax_cut with (Q := hcy5_S3 x25519 gv L FR0);
    [discriminate | rewrite hcy5_overridePost2, <- E3; apply hcy5_P3_ok; exact HH |].
  eapply hcy5_semax_cut with (Q := hcy5_S4 x25519 xaead_enc gv L FR0);
    [discriminate | rewrite hcy5_overridePost2, <- E4; apply hcy5_P4_ok; exact HH |].
  eapply hcy5_semax_cut with (Q := hcy5_S5 x25519 xaead_enc gv L FR0);
    [discriminate | rewrite hcy5_overridePost2, <- E5; apply hcy5_P5_ok; exact HH |].
  eapply hcy5_semax_cut with (Q := hcy5_S5b x25519 xaead_enc gv L FR0);
    [discriminate | rewrite hcy5_overridePost2, <- E5b; apply hcy5_P5b_ok; exact HH |].
  eapply hcy5_semax_cut with (Q := hcy5_S6 x25519 xaead_enc gv L FR0);
    [discriminate | rewrite hcy5_overridePost2, <- E6; apply hcy5_P6_ok; exact HH |].
  eapply hcy5_semax_cut with (Q := hcy5_S7 x25519 xaead_enc gv L FR0);
    [discriminate | rewrite hcy5_overridePost2, <- E7; apply hcy5_P7_ok; auto |].
  eapply hcy5_semax_cut with (Q := hcy5_S8 x25519 xaead_enc gv L FR0);
    [discriminate | rewrite hcy5_overridePost2, <- E8; apply hcy5_P8_ok; exact HH |].
  eapply hcy5_semax_cut with (Q := hcy5_S9 x25519 xaead_enc gv L FR0);
    [discriminate | rewrite hcy5_overridePost2, <- E9; apply hcy5_P9_ok; exact HH |].
  eapply hcy5_semax_cut with (Q := hcy5_S10 x25519 xaead_enc xaead_dec gv L FR0);
    [discriminate | rewrite hcy5_overridePost2, <- E10; apply hcy5_P10_ok; exact HH |].
  eapply hcy5_semax_cut with (Q := hcy5_S11 x25519 xaead_enc xaead_dec gv L FR0);
    [discriminate | rewrite hcy5_overridePost2, <- E11; apply hcy5_P11_ok; exact HH |].
  eapply hcy5_semax_cut with (Q := hcy5_S11 x25519 xaead_enc xaead_dec gv L FR0);
    [discriminate | rewrite hcy5_overridePost2, <- E12; apply hcy5_P12_ok; exact HH |].
  rewrite <- E13. apply hcy5_P13_ok; auto.
Qed.

End Main.
