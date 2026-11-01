(* law handshake_receive, phase B3: the branch of kind 3: mc = malloc, img = malloc (continue on failure, both freed), fill_cookie_msg, maybe a receiver index from a walk over itd's list, maybe a reply that decrypts for a picked node (hnodes_pick; its handshake entry inserted if not hashed; have_sent_mac1 = true; nondet_bytes ck; xchacha20poly1305_encrypt; the world changes: use hrx5_B3_lem_stmt), header.type = draw_type(3), cookie_img; skb.data = mc.
   From hrx5_B3_P 3 to hrx5_B3_Q, or continue -> hrx5_SC (hrx5_B3_defs.v). *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K3_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K3_A.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K3_F.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K3_W.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K3_P.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K3_Z.
Local Open Scope logic.

Section K3.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_B3_K3_ok {Espec: OracleKind} gv L FR :
  hrx5_B3_lem_stmt x25519 ->
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B3_P x25519 3 gv L FR) hrx5_B3_K3
    (overridePost (hrx5_B3_Q x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HLEM HY. apply hrx5_K3_eq.
  eapply semax_seq with (Q := hrx5_K3_A x25519 gv L FR);
    [rewrite hrx5_overridePost2; apply (hrx5_K3_A_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); auto |].
  eapply semax_seq with (Q := hrx5_K3_F x25519 gv L FR);
    [rewrite hrx5_overridePost2; apply (hrx5_K3_F_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); auto |].
  eapply semax_seq with (Q := hrx5_K3_F x25519 gv L FR);
    [rewrite hrx5_overridePost2; apply (hrx5_K3_W_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); auto |].
  eapply semax_seq with (Q := hrx5_K3_F x25519 gv L FR);
    [rewrite hrx5_overridePost2; apply (hrx5_K3_P_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); auto |].
  apply (hrx5_K3_Z_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); auto.
Qed.

End K3.
