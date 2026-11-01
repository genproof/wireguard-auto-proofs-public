(* law handshake_receive, phase B3, branch kind 2, segment C:
   draw_macs(img, len, mk1, wd.cookie_checker.secret, &skb). *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K2_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K2_C_lem.

Section K2C.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_K2_C_ok {Espec: OracleKind} gv L FR :
  hrx5_B3_lem_stmt x25519 ->
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_K2_B x25519 gv L FR) hrx5_K2_SC
    (overridePost (hrx5_K2_C x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HLEM HY. unfold hrx5_Delta, hrx5_K2_B, hrx5_K2_St.
  Intros R sec birth S w NS PS T. Intros head nk KE st i kc lul q. Intros proto ip4 ip6 port mr img M IMG.
  unfold hrx5_K2_SC, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_K2_XM; cbn [app].
  unfold hrx5_skb_part, wg_consts. Intros dv lv. Intros.
  unfold hrx5_RB, hrx5_R.
  abbreviate_semax.
  match goal with Hc: rm_ok M /\ IMG = resp_bytes M |- _ => destruct Hc as [HM HI] | _ => idtac end.
  match goal with HI: IMG = resp_bytes M |- _ => subst IMG end.
  match goal with Hc: rm_ok M |- _ => rename Hc into HM end.
  set (D := hrx5_DL x25519 R L sec birth).
  rewrite (hrx5_k2c_dev_split Tsh (l_wd L) D).
  assert_PROP (@field_compatible Noise.CS t_dev [] (l_wd L)) as FCB by (unfold hrx5_k2c_drest; entailer!).
  rewrite (hrx5_k2c_cc_open Tsh (l_wd L) (d_cc D)) by exact FCB. Intros.
  match goal with Hc: cc_ok (d_cc D) |- _ => rename Hc into HCC end.
  assert (Hs: Zlength (cc_secret (d_cc D)) = 32) by (destruct HCC as (Hs & _); exact Hs).
  replace_SEP 28 (skb_src_rep Tsh (l_skb L) dv lv (mkSkb nullval Int.zero proto ip4 ip6 port)).
  { go_lower. rewrite <- (hrx5_k2c_skb_src dv lv proto ip4 ip6 port (l_skb L)) by auto. apply derives_refl. }
  assert (Hmk: Zlength (hrx5_mk1 x25519 R) = 32) by apply hrx5_k2c_mk1_len.
  assert (Hib: Zlength (resp_bytes M) = 92).
  { destruct HM as (L1 & L2 & L3 & L4). unfold resp_bytes.
    rewrite !Zlength_app, L1, L2, L3, L4. reflexivity. }
  forward_call (gv, Ews, img, resp_bytes M, Tsh, l_mk1 L, hrx5_mk1 x25519 R, Tsh, cc_addr (l_wd L),
                cc_secret (d_cc D), Tsh, l_skb L, mkSkb nullval Int.zero proto ip4 ip6 port, dv, lv).
  { rewrite Hib. go_lower. apply prop_right.
    unfold cc_addr, OFS_DEV_CHECKER. destruct (l_wd L); try contradiction. simpl.
    rewrite Ptrofs.add_assoc. reflexivity. }
  Intros IMG'.
  rewrite Hib in *.
  sep_apply (hrx5_k2c_cc_close Tsh (l_wd L) (d_cc D) FCB HCC).
  sep_apply (derives_refl' _ _ (eq_sym (hrx5_k2c_dev_split Tsh (l_wd L) D))).
  sep_apply (hrx5_k2c_skb_part L dv lv proto ip4 ip6 port).
  unfold hrx5_K2_C, hrx5_K2_St.
  Exists R sec birth S w NS PS T head. Exists nk KE st i kc lul q proto.
  Exists ip4 ip6 port mr img. Exists M IMG'.
  unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_K2_XM, wg_consts; cbn [app].
  go_lower.
  match goal with Hl: Zlength IMG' = 92, Hsub: sublist 0 (92 - 32) IMG' = _ |- _ =>
    assert (HC: rm_ok M /\ Zlength IMG' = 92 /\ sublist 0 60 IMG' = sublist 0 60 (resp_bytes M))
      by (split; [exact HM | split; [exact Hl | exact Hsub]]) end.
  apply andp_right;
    [apply prop_right; refine (conj H (conj H0 (conj H1 (conj H2 (conj H3 (conj HC _)))))); repeat split; auto;
     try lia; try (rewrite eqb_type_refl; reflexivity) |].
  cancel.
  apply derives_refl.
Qed.

End K2C.
