(* law handshake_receive, phase B3, branch kind 2, segment T:
   mr->header.type = draw_type(2); resp_img(img, mr). *)
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

(* the response struct at the world compspecs *)
#[local] Instance hrx5_k2t_cceN : change_composite_env Noise.CS W_handshake_receive.
Proof. make_cs_preserve Noise.CS W_handshake_receive. Defined.

Lemma hrx5_k2t_resp_W sh m M :
  resp_rep sh m M = !! rm_ok M && @data_at W_handshake_receive sh t_resp (resp_val M) m.
Proof.
  unfold resp_rep.
  rewrite (@data_at_change_composite Noise.CS W_handshake_receive _ sh t_resp _ _ (JMeq_refl _))
    by prove_cs_preserve_type.
  reflexivity.
Qed.

Section K2T.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_K2_T_ok {Espec: OracleKind} gv L FR :
  hrx5_B3_lem_stmt x25519 ->
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_K2_F x25519 gv L FR) hrx5_K2_ST
    (overridePost (hrx5_K2_B x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HLEM HY. unfold hrx5_Delta, hrx5_K2_F, hrx5_K2_St. Intros R sec birth S w NS PS T head.
  Intros nk KE st i kc lul q proto. Intros ip4 ip6 port mr img M IMG.
  unfold hrx5_K2_ST, hrx5_K2_XF, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
  abbreviate_semax.
  forward_call (Int.repr 2).
  Intros r. rewrite hrx5_k2t_resp_W. Intros. forward.
  set (M2 := mkRM r (rm_sender M) (rm_receiver M) (rm_eph M) (rm_encn M) (rm_mac1 M) (rm_mac2 M)).
  assert (HM2: rm_ok M2) by exact H4.
  change (Vint r, snd (resp_val M)) with (resp_val M2).
  sep_apply (derives_refl' _ _ (eq_sym (hrx5_k2t_resp_W Ews mr M2))). { exact HM2. }
  rewrite <- hrx5_conv_bytes.
  forward_call (Ews, img, Ews, mr, M2).
  match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_K2_B x25519 gv L FR) end.
  unfold hrx5_K2_B, hrx5_K2_St.
  Exists R sec birth S w NS PS T head.
  Exists nk KE st i kc lul q proto. Exists ip4 ip6 port mr img M2 (resp_bytes M2).
  unfold hrx5_K2_XM, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
  clear HLEM. go_lower. apply andp_right.
  { apply prop_right.
    refine (conj H (conj H0 (conj H1 (conj H2 (conj H3 (conj (conj HM2 eq_refl) _)))))).
    repeat split; auto. }
  cancel.
Qed.

End K2T.
