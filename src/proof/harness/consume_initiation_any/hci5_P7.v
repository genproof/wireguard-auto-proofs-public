(* law consume_initiation_any: main's phase P7, statements 29..30: target = NULL; the harness's model (ib.ok, m_consume_initiation_1, the first-match loop over the nodes, m_precomputed, m_consume_initiation_2, m_ts_newer, m_not_flood).
   (states: hci5_defs.v).
   harness/consume_initiation_any/hci3_*.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_cut.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_model.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_globals.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_conv.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_pure.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_sep.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_A.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_B.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_L.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_D.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_E1.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_E2a.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_E2b.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_E3.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p7_E4.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

Section P7.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_P7_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> 
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_S6 x25519 aead_dec gv L FR) hci5_P7
    (overridePost (hci5_S7 x25519 aead_dec gv L FR) (hci5_R gv)).
Proof.
  intros HH. unfold hci5_S6.
  apply extract_exists_pre; intro R. apply extract_exists_pre; intro S.
  apply extract_exists_pre; intro w. apply extract_exists_pre; intro NS.
  apply extract_exists_pre; intro PS. apply extract_exists_pre; intro T.
  apply extract_exists_pre; intro head. apply extract_exists_pre; intro na.
  apply extract_exists_pre; intro KE. apply extract_exists_pre; intro m.
  apply extract_exists_pre; intro M.
  rewrite hci5_p7_P7_eq. apply <- seq_assoc.
  eapply semax_seq.
  { rewrite overridePost_overridePost.
    eapply semax_pre; [ | apply (hci5_p7_A_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R S w NS PS T head na KE m M HH)].
    unfold hci5_p7_st, hci5_scr, hci5_world, hci5_globs, hci5_lvars. cbn [app].
    entailer!. }
  apply (hci5_p7_B_ok x25519 aead_enc aead_dec).
  intros s key ck1 h1 Hc1.
  rewrite hci5_p7_body_eq. apply <- seq_assoc.
  eapply semax_seq; [ rewrite overridePost_overridePost; apply (hci5_p7_L_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R S w NS PS T head na KE m M s key ck1 h1 HH Hc1) | ].
  apply (hci5_p7_D_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R S w NS PS T head na KE m M s key ck1 h1 HH Hc1).
  intros a P Hpk.
  rewrite hci5_p7_x_eq.
  eapply semax_seq; [ rewrite overridePost_overridePost; apply (hci5_p7_E1_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R S w NS PS T head na KE m M s key ck1 h1 a P HH Hc1 Hpk) | ].
  eapply semax_seq; [ | apply (hci5_p7_E4_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R S w NS PS T head na KE m M s key ck1 h1 a P HH Hc1 Hpk) ].
  rewrite overridePost_overridePost.
  eapply semax_seq; [ | apply (hci5_p7_E3_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R S w NS PS T head na KE m M s key ck1 h1 a P HH Hc1 Hpk) ].
  rewrite overridePost_overridePost.
  eapply semax_seq; [ | apply (hci5_p7_E2b_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R S w NS PS T head na KE m M s key ck1 h1 a P HH Hc1 Hpk) ].
  rewrite overridePost_overridePost.
  apply (hci5_p7_E2a_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R S w NS PS T head na KE m M s key ck1 h1 a P HH Hc1 Hpk).
Qed.

End P7.
