(* law handshake: main's phase P5, statements 101..110: A consumes the response (acc2, CHECKs, wg_peer_put; completeness 3; !acc2 returns).
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
Require Import WgNoise.proof.harness.handshake.hhs3_p5_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_A.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_B.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_C.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_D.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_E.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_F.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_acc.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_crypto.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_free.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Section P5.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_P5_ok {Espec: OracleKind} gv L FR :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_S4 x25519 aead_enc aead_dec gv L FR) hhs3_P5
    (overridePost (hhs3_S5 x25519 aead_enc aead_dec gv L FR) (hhs3_R gv)).
Proof.
  intros HH.
  assert (HF: hhs3_p5_free_stmt x25519) by (apply (hhs3_p5_free_ok x25519); destruct HH as (_ & _ & _ & _ & Hr); exact Hr).
  assert (HA: hhs3_p5_acc_stmt x25519 aead_enc aead_dec) by apply (hhs3_p5_acc_ok x25519 aead_enc aead_dec).
  assert (HC: hhs3_p5_crypto_stmt x25519 aead_enc aead_dec) by apply (hhs3_p5_crypto_ok x25519 aead_enc aead_dec).
  destruct hhs3_p5_segs_eq as (EA & EB & EC & ED & EE & EF).
  destruct hhs3_phases_eq as (_ & _ & _ & _ & E5 & _).
  rewrite E5, hhs3_p5_split.
  eapply hhs3_p5_cut with (Q := hhs3_p5_SA x25519 aead_enc aead_dec gv L FR); [discriminate | discriminate | rewrite <- EA; apply hhs3_p5_A_ok; assumption |].
  eapply hhs3_p5_cut with (Q := hhs3_p5_SB x25519 aead_enc aead_dec gv L FR); [discriminate | discriminate | rewrite hhs3_overridePost2, <- EB; apply hhs3_p5_B_ok; assumption |].
  eapply hhs3_p5_cut with (Q := hhs3_p5_SC x25519 aead_enc aead_dec gv L FR); [discriminate | discriminate | rewrite hhs3_overridePost2, <- EC; apply hhs3_p5_C_ok; assumption |].
  eapply hhs3_p5_cut with (Q := hhs3_p5_SD x25519 aead_enc aead_dec gv L FR); [discriminate | discriminate | rewrite hhs3_overridePost2, <- ED; apply hhs3_p5_D_ok; assumption |].
  eapply hhs3_p5_cut with (Q := hhs3_p5_SD x25519 aead_enc aead_dec gv L FR); [discriminate | discriminate | rewrite hhs3_overridePost2, <- EE; apply hhs3_p5_E_ok; assumption |].
  rewrite <- EF. apply hhs3_p5_F_ok; assumption.
Qed.

End P5.
