(* law handshake_receive, phase B3, branch kind 3, segment Z:
   stmts 7..9 (mc->header.type = draw_type(3); cookie_img(img, mc); skb.data = mc): hrx5_K3_F -> hrx5_B3_Q.
*)
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

Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K3_defs.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* helpers *)
(* ---------------------------------------------------------------------- *)

#[local] Instance k3z_cce : change_composite_env Cookie.CS W_handshake_receive.
Proof. make_cs_preserve Cookie.CS W_handshake_receive. Defined.

(* the cookie message struct at the world compspecs *)
Lemma k3z_cmsg_W sh m M :
  cmsg_rep sh m M = !! cm_ok M && @data_at W_handshake_receive sh t_cmsg (cmsg_val M) m.
Proof.
  unfold cmsg_rep.
  rewrite (@data_at_change_composite Cookie.CS W_handshake_receive _ sh t_cmsg _ _ (JMeq_refl _))
    by prove_cs_preserve_type.
  reflexivity.
Qed.

Lemma k3z_skb_cs sh (dv lv pv: val) (a b c: list val) p :
  @data_at Cookie.CS sh t_skb (dv, (lv, (pv, (a, (b, c))))) p =
  @data_at W_handshake_receive sh t_skb (dv, (lv, (pv, (a, (b, c))))) p.
Proof.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite Cookie.CS W_handshake_receive _); [apply JMeq_refl | reflexivity].
Qed.

Lemma k3z_skbd L dp lv proto ip4 ip6 port :
  0 <= proto <= 65535 -> Zlength ip4 = 4 -> Zlength ip6 = 16 -> Zlength port = 2 ->
  @data_at W_handshake_receive Tsh t_skb (dp, (lv, (Vint (Int.repr proto), (bytes ip4, (bytes ip6, bytes port)))))
    (l_skb L) |-- hrx5_B3_skbd L dp proto ip4 ip6 port.
Proof.
  intros. unfold hrx5_B3_skbd. rewrite <- k3z_skb_cs. Exists lv. entailer!.
Qed.

Lemma k3z_len M : cm_ok M -> Zlength (cookie_msg_bytes M) = 64.
Proof.
  intros (H1 & H2). unfold cookie_msg_bytes. rewrite !Zlength_app, !prot_rep3_le32_len. lia.
Qed.

Section K3Z.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_K3_Z_ok {Espec: OracleKind} gv L FR :
  hrx5_B3_lem_stmt x25519 ->
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_K3_F x25519 gv L FR) hrx5_K3_SZ
    (overridePost (hrx5_B3_Q x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HLEM HY. unfold hrx5_Delta, hrx5_K3_F, hrx5_K3_St.
  Intros R sec birth S w NS PS T head. Intros nk KE st i kc lul q proto.
  Intros ip4 ip6 port mc img M.
  unfold hrx5_K3_SZ, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_K3_XF; cbn [app].
  unfold hrx5_RB, hrx5_R.
  abbreviate_semax.
  forward_call (Int.repr 3).
  Intros r. rewrite k3z_cmsg_W. Intros. forward.
  set (M2 := mkCM r (cm_receiver M) (cm_nonce M) (cm_enc M)).
  assert (HM2: cm_ok M2) by exact H4.
  change (Vint r, snd (cmsg_val M)) with (cmsg_val M2).
  sep_apply (derives_refl' _ _ (eq_sym (k3z_cmsg_W Ews mc M2))). { exact HM2. }
  rewrite <- hrx5_conv_bytes.
  forward_call (Ews, img, Ews, mc, M2).
  unfold hrx5_skb_part. Intros dv lv. rewrite k3z_skb_cs.
  forward.
  try match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_B3_Q x25519 gv L FR) end.
  sep_apply (k3z_skbd L mc lv proto ip4 ip6 port H5 H6 H7 H8).
  unfold hrx5_B3_Q.
  Exists R sec birth S w NS PS T. Exists head nk KE st i kc lul q.
  Exists proto ip4 ip6 port (OCookie M2) mc img.
  unfold obj_rep, img_rep, obj_bytes, obj_kind, hrx5_ptrs, obj_ok.
  rewrite (k3z_len M2 HM2).
  unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
  clear HLEM. go_lower. apply andp_right.
  { apply prop_right.
    refine (conj H (conj H0 (conj H1 (conj H2 (conj HM2 (conj H3 _)))))).
    repeat split; auto. }
  cancel.
Qed.

End K3Z.
