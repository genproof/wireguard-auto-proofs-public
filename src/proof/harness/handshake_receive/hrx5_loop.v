(* law handshake_receive: main's packet loop (statement
   20: i = 0; for (; i < steps; i++) BODY) from hrx5_SE to hrx5_SX, the body from the nine segments B1 .. B9. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B1.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B2.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B5.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B6.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B7.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B9.

#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Section Loop.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_RB_override gv L FR : overridePost (hrx5_SC x25519 gv L FR) (hrx5_RB x25519 gv L FR) = hrx5_RB x25519 gv L FR.
Proof. reflexivity. Qed.

Lemma hrx5_RA_normal_override (Q: environ -> mpred) (R: ret_assert) : RA_normal (overridePost Q R) = Q.
Proof. destruct R; reflexivity. Qed.

Lemma hrx5_body_ok {Espec: OracleKind} gv L FR :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_SC x25519 gv L FR) hrx5_body
    (hrx5_RB x25519 gv L FR).
Proof.
  intros HH. unfold hrx5_body.
  destruct hrx5_bphases_eq as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
  eapply hrx5_semax_cut with (Q := hrx5_S1 x25519 gv L FR);
    [discriminate | rewrite <- E1; apply (hrx5_B1_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH |].
  eapply hrx5_semax_cut with (Q := hrx5_S2 x25519 gv L FR);
    [discriminate | rewrite <- E2; apply (hrx5_B2_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH |].
  eapply hrx5_semax_cut with (Q := hrx5_S3 x25519 gv L FR);
    [discriminate | rewrite <- E3; apply (hrx5_B3_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH |].
  eapply hrx5_semax_cut with (Q := hrx5_S4 x25519 aead_dec xaead_dec gv L FR);
    [discriminate | rewrite <- E4; apply (hrx5_B4_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH |].
  eapply hrx5_semax_cut with (Q := hrx5_S5 x25519 aead_dec xaead_enc xaead_dec gv L FR);
    [discriminate | rewrite <- E5; apply (hrx5_B5_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH |].
  eapply hrx5_semax_cut with (Q := hrx5_S6 x25519 aead_dec xaead_enc xaead_dec gv L FR);
    [discriminate | rewrite <- E6; apply (hrx5_B6_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH |].
  eapply hrx5_semax_cut with (Q := hrx5_S6 x25519 aead_dec xaead_enc xaead_dec gv L FR);
    [discriminate | rewrite <- E7; apply (hrx5_B7_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH |].
  eapply hrx5_semax_cut with (Q := hrx5_S8 x25519 gv L FR);
    [discriminate | rewrite <- E8; apply (hrx5_B8_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH |].
  rewrite <- E9, <- hrx5_RB_override. apply (hrx5_B9_ok x25519 aead_enc aead_dec xaead_enc xaead_dec); exact HH.
Qed.

Lemma hrx5_PL_ok {Espec: OracleKind} gv L FR :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_SE x25519 gv L FR) hrx5_PL
    (overridePost (hrx5_SX x25519 gv L FR) (hrx5_R gv)).
Proof.
  intros HH. unfold hrx5_PL.
  eapply semax_seq with (Q := hrx5_SL x25519 gv L FR).
  - rewrite hrx5_overridePost2.
    unfold hrx5_SE, hrx5_init, hrx5_Delta. abbreviate_semax.
    Intros R sec birth S w NS PS T head nk KE st.
    forward.
    match goal with |- _ |-- RA_normal ?X => change (RA_normal X) with (hrx5_SL x25519 gv L FR) end.
    unfold hrx5_SL, hrx5_SLc.
    Exists R sec birth S w NS PS T. Exists head nk KE st 0 Int64.zero Int64.zero.
    unfold hrx5_ltemps, hrx5_lvars; cbn [app]. entailer!.
  - eapply semax_loop with (Q' := hrx5_SC x25519 gv L FR).
    + pose proof (hrx5_body_ok gv L FR HH) as HB. unfold hrx5_RB in HB.
      eapply semax_seq; [| exact HB].
      unfold hrx5_SL, hrx5_SLc, hrx5_guard, hrx5_Delta. abbreviate_semax.
      Intros R sec birth S w NS PS T. Intros head nk KE st i kc lul.
      unfold hrx5_ltemps.
      forward_if.
      * forward. unfold hrx5_SC, hrx5_SLc.
        Exists R sec birth S w NS PS T. Exists head nk KE st i kc lul.
        unfold hrx5_ltemps, hrx5_lvars; cbn [app]. entailer!.
      * forward. unfold hrx5_SX, hrx5_SLc.
        Exists R sec birth S w NS PS T. Exists head nk KE st i kc lul.
        unfold hrx5_ltemps, hrx5_lvars; cbn [app]. entailer!.
    + unfold hrx5_SC, hrx5_SLc, hrx5_incr, hrx5_Delta. abbreviate_semax.
      Intros R sec birth S w NS PS T. Intros head nk KE st i kc lul.
      unfold hrx5_ltemps.
      forward.
      unfold hrx5_SL, hrx5_SLc.
      Exists R sec birth S w NS PS T. Exists head nk KE st (i + 1) kc lul.
      unfold hrx5_ltemps, hrx5_lvars; cbn [app]. entailer!.
Qed.

End Loop.
