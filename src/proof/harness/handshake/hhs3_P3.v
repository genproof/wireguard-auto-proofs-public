(* law handshake: main's phase P3, statements 66..76: B consumes the initiation (acc1, CHECKs, wg_peer_put; completeness 1; !acc1 returns).
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
Require Import WgNoise.proof.harness.handshake.hhs3_p3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_p3_A.
Require Import WgNoise.proof.harness.handshake.hhs3_p3_B.
Require Import WgNoise.proof.harness.handshake.hhs3_p3_C.
Require Import WgNoise.proof.harness.handshake.hhs3_p3_D.
Require Import WgNoise.proof.harness.handshake.hhs3_p3_E.
Require Import WgNoise.proof.harness.handshake.hhs3_p3_F.
Require Import WgNoise.proof.harness.handshake.hhs3_p3_acc.
Require Import WgNoise.proof.harness.handshake.hhs3_p3_crypto.
Require Import WgNoise.proof.harness.handshake.hhs3_p3_free.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Section P3.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_P3_ok {Espec: OracleKind} gv L FR :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_S2 x25519 aead_enc gv L FR) hhs3_P3
    (overridePost (hhs3_S3 x25519 aead_enc aead_dec gv L FR) (hhs3_R gv)).
Proof.
  intros HH.
  assert (HF: hhs3_p3_free_stmt x25519) by (apply (hhs3_p3_free_ok x25519); destruct HH as (_ & _ & _ & _ & Hr); exact Hr).
  assert (HA: hhs3_p3_acc_stmt x25519 aead_dec) by apply (hhs3_p3_acc_ok x25519 aead_dec).
  assert (HC: hhs3_p3_crypto_stmt x25519 aead_enc aead_dec) by apply (hhs3_p3_crypto_ok x25519 aead_enc aead_dec).
  destruct hhs3_p3_segs_eq as (EA & EB & EC & ED & EE & EF).
  destruct hhs3_phases_eq as (_ & _ & E3 & _).
  rewrite E3, hhs3_p3_split.
  eapply hhs3_p3_cut with (Q := hhs3_p3_SA x25519 aead_enc aead_dec gv L FR); [discriminate | discriminate | rewrite <- EA; apply hhs3_p3_A_ok; exact HH |].
  eapply hhs3_p3_cut with (Q := hhs3_p3_SB x25519 aead_enc aead_dec gv L FR); [discriminate | discriminate | rewrite hhs3_overridePost2, <- EB; apply hhs3_p3_B_ok; assumption |].
  eapply hhs3_p3_cut with (Q := hhs3_p3_SC x25519 aead_enc aead_dec gv L FR); [discriminate | discriminate | rewrite hhs3_overridePost2, <- EC; apply hhs3_p3_C_ok; assumption |].
  eapply hhs3_p3_cut with (Q := hhs3_p3_SD x25519 aead_enc aead_dec gv L FR); [discriminate | discriminate | rewrite hhs3_overridePost2, <- ED; apply hhs3_p3_D_ok; assumption |].
  eapply hhs3_p3_cut with (Q := hhs3_p3_SE x25519 aead_enc aead_dec gv L FR); [discriminate | discriminate | rewrite hhs3_overridePost2, <- EE; apply hhs3_p3_E_ok; assumption |].
  rewrite <- EF. apply hhs3_p3_F_ok; assumption.
Qed.

End P3.
