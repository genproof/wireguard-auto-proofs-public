(* law handshake: main's phase P4, statements 77..100: B's response (fill_resp, create_response + model + completeness 2; !ok2 returns), CHECKs, add_mac.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_conv.
Require Import WgNoise.proof.harness.handshake.hhs3_p4_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_p4_A.
Require Import WgNoise.proof.harness.handshake.hhs3_p4_BC.
Require Import WgNoise.proof.harness.handshake.hhs3_p4_D.
Require Import WgNoise.proof.harness.handshake.hhs3_p4_E1.
Require Import WgNoise.proof.harness.handshake.hhs3_p4_E2.
Require Import WgNoise.proof.harness.handshake.hhs3_p4_F.
Require Import WgNoise.proof.harness.handshake.hhs3_p4_pa1.
Require Import WgNoise.proof.harness.handshake.hhs3_p4_agree.
Require Import WgNoise.proof.harness.handshake.hhs3_p4_free.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Section P4.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_P4_ok {Espec: OracleKind} gv L FR :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_S3 x25519 aead_enc aead_dec gv L FR) hhs3_P4
    (overridePost (hhs3_S4 x25519 aead_enc aead_dec gv L FR) (hhs3_R gv)).
Proof.
  intros HH.
  assert (HF: hhs3_p4_free_stmt x25519) by (apply (hhs3_p4_free_ok x25519); destruct HH as (_ & _ & _ & _ & Hr); exact Hr).
  assert (HP: hhs3_p4_pa1_stmt x25519 aead_dec) by apply (hhs3_p4_pa1_ok x25519 aead_dec).
  assert (HA: hhs3_p4_agree_stmt x25519 aead_enc) by apply (hhs3_p4_agree_ok x25519 aead_enc).
  destruct hhs3_p4_segs_eq as (EA & EBC & ED & EE1 & EE2 & EF).
  destruct hhs3_phases_eq as (_ & _ & _ & E4 & _).
  rewrite E4, hhs3_p4_split.
  eapply hhs3_p4_cut with (Q := hhs3_p4_SA x25519 aead_enc aead_dec gv L FR); [discriminate | discriminate | rewrite <- EA; apply hhs3_p4_A_ok; assumption |].
  eapply hhs3_p4_cut with (Q := hhs3_p4_SC x25519 aead_enc aead_dec gv L FR); [discriminate | discriminate | rewrite hhs3_overridePost2, <- EBC; apply hhs3_p4_BC_ok; assumption |].
  eapply hhs3_p4_cut with (Q := hhs3_p4_SD x25519 aead_enc aead_dec gv L FR); [discriminate | discriminate | rewrite hhs3_overridePost2, <- ED; apply hhs3_p4_D_ok; assumption |].
  eapply hhs3_p4_cut with (Q := hhs3_p4_SE x25519 aead_enc aead_dec gv L FR); [discriminate | discriminate | rewrite hhs3_overridePost2, <- EE1; apply hhs3_p4_E1_ok; assumption |].
  eapply hhs3_p4_cut with (Q := hhs3_p4_SE x25519 aead_enc aead_dec gv L FR); [discriminate | discriminate | rewrite hhs3_overridePost2, <- EE2; apply hhs3_p4_E2_ok; assumption |].
  rewrite <- EF. apply hhs3_p4_F_ok; assumption.
Qed.

End P4.
