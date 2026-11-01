(* law handshake_receive: phase B8, branch C
   of statement 41. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_ilem.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_C_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_C_K.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_C_T.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_C_W.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_C_F.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_C_P.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Lemma hrx5_B8C_post_over {Espec: OracleKind} {cs: compspecs} Delta P c Q1 Q2 R :
  semax Delta P c (overridePost Q1 R) -> ENTAIL Delta, Q1 |-- Q2 -> semax Delta P c (overridePost Q2 R).
Proof.
  intros H E. eapply semax_post; [| | | | exact H]; destruct R; simpl; intros;
    try (apply andp_left2; apply derives_refl).
  revert x; exact E.
Qed.

Lemma hrx5_B8_C_ok : hrx5_B8_C_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port o dp img tg ai ar d HY HX.
  eapply semax_pre; [apply (hrx5_B8C_entry_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); assumption |].
  apply extract_exists_pre; intros M. apply extract_exists_pre; intros a.
  apply extract_exists_pre; intros P. apply extract_exists_pre; intros pt.
  destruct hrx5_B8C_K_ok as [K0 K1]. pose proof hrx5_B8C_C2_ok as K2. pose proof hrx5_B8C_C3_ok as K3.
  unfold hrx5_B8C_C0_stmt, hrx5_B8C_C1_stmt, hrx5_B8C_C2_stmt, hrx5_B8C_C3_stmt, hrx5_B8C_seg in *.
  eapply hrx5_B8C_post_over.
  - apply hrx5_B8C_cut; [apply (K0 _ _ aead_enc) | apply (K1 _ _ aead_enc) | apply (K2 _ _ aead_enc) | apply (K3 _ _ aead_enc)]; exact HY.
  - apply (hrx5_B8C_fold_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HY.
Qed.
