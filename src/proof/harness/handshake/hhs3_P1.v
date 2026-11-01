(* law handshake: main's phase P1, statements 0..36: setup (boot clock, wg_noise_init, raw keys, psk, devices, identities, peers, their CHECKs, the two mallocs, all_ok).
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
Require Import WgNoise.proof.harness.handshake.hhs3_p1_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_p1_A.
Require Import WgNoise.proof.harness.handshake.hhs3_p1_B.
Require Import WgNoise.proof.harness.handshake.hhs3_p1_C.
Require Import WgNoise.proof.harness.handshake.hhs3_p1_D.
Require Import WgNoise.proof.harness.handshake.hhs3_p1_E.
Require Import WgNoise.proof.harness.handshake.hhs3_p1_F.
Require Import WgNoise.proof.harness.handshake.hhs3_p1_G.
Require Import WgNoise.proof.harness.handshake.hhs3_p1_free.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Section P1.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_P1_ok {Espec: OracleKind} gv L FR :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_S0 gv L FR) hhs3_P1
    (overridePost (hhs3_S1 x25519 gv L FR) (hhs3_R gv)).
Proof.
  intros HH.
  assert (HF: hhs3_p1_free_stmt x25519) by (apply hhs3_p1_free_ok; destruct HH as (_ & _ & _ & _ & Hr); exact Hr).
  destruct hhs3_p1_segs_eq as (EA & EB & EC & ED & EE & EF & EG).
  destruct hhs3_phases_eq as (E1 & _).
  rewrite E1, hhs3_p1_split.
  eapply hhs3_p1_cut with (Q := hhs3_p1_SA gv L FR); [discriminate | discriminate | rewrite <- EA; apply hhs3_p1_A_ok; exact HH |].
  eapply hhs3_p1_cut with (Q := hhs3_p1_SB x25519 gv L FR); [discriminate | discriminate | rewrite hhs3_overridePost2, <- EB; apply hhs3_p1_B_ok; exact HH |].
  eapply hhs3_p1_cut with (Q := hhs3_p1_SB x25519 gv L FR); [discriminate | discriminate | rewrite hhs3_overridePost2, <- EC; apply hhs3_p1_C_ok; exact HH |].
  eapply hhs3_p1_cut with (Q := hhs3_p1_SD x25519 gv L FR); [discriminate | discriminate | rewrite hhs3_overridePost2, <- ED; apply hhs3_p1_D_ok; exact HH |].
  eapply hhs3_p1_cut with (Q := hhs3_p1_SE x25519 gv L FR); [discriminate | discriminate | rewrite hhs3_overridePost2, <- EE; apply hhs3_p1_E_ok; exact HH |].
  eapply hhs3_p1_cut with (Q := hhs3_p1_SE x25519 gv L FR); [discriminate | discriminate | rewrite hhs3_overridePost2, <- EF; apply hhs3_p1_F_ok; exact HH |].
  rewrite <- EG. apply hhs3_p1_G_ok; assumption.
Qed.

End P1.
