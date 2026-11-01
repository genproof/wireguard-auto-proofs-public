(* law handshake: main's phase P6, statements 111..120: begin_session A and B, keypairs_clear, final CHECKs, frees, return 0.
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
Require Import WgNoise.proof.harness.handshake.hhs3_p6_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_p6_A.
Require Import WgNoise.proof.harness.handshake.hhs3_p6_B.
Require Import WgNoise.proof.harness.handshake.hhs3_p6_C1.
Require Import WgNoise.proof.harness.handshake.hhs3_p6_C2.
Require Import WgNoise.proof.harness.handshake.hhs3_p6_D.
Require Import WgNoise.proof.harness.handshake.hhs3_p6_E.
Require Import WgNoise.proof.harness.handshake.hhs3_p6_F1.
Require Import WgNoise.proof.harness.handshake.hhs3_p6_F2.
Require Import WgNoise.proof.harness.handshake.hhs3_p6_G.
Require Import WgNoise.proof.harness.handshake.hhs3_p6_H.
Require Import WgNoise.proof.harness.handshake.hhs3_p6_factsA.
Require Import WgNoise.proof.harness.handshake.hhs3_p6_factsB.
Require Import WgNoise.proof.harness.handshake.hhs3_p6_ck.
Require Import WgNoise.proof.harness.handshake.hhs3_p6_model.
Require Import WgNoise.proof.harness.handshake.hhs3_p6_free.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Section P6.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_P6_ok {Espec: OracleKind} gv L FR :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_S5 x25519 aead_enc aead_dec gv L FR) hhs3_P6
    (overridePost (FF) (hhs3_R gv)).
Proof.
  intros HH.
  assert (HP: hhs3_p6_pure x25519 aead_enc aead_dec).
  { split; [apply hhs3_p6_factsA_ok | split; [apply hhs3_p6_factsB_ok | split;
      [apply hhs3_p6_ck_ok | apply hhs3_p6_model_ok]]]. }
  assert (HF: hhs3_p6_free_stmt x25519).
  { apply hhs3_p6_free_ok. destruct HH as (_ & _ & _ & _ & Hr). exact Hr. }
  unfold hhs3_S5.
  apply extract_exists_pre; intro R. apply extract_exists_pre; intro S.
  apply extract_exists_pre; intro m1. apply extract_exists_pre; intro m2.
  apply extract_exists_pre; intro a0. apply extract_exists_pre; intro f0.
  apply extract_exists_pre; intro l0. apply extract_exists_pre; intro I.
  apply extract_exists_pre; intro M1. apply extract_exists_pre; intro H1.
  apply extract_exists_pre; intro MI. apply extract_exists_pre; intro nowb.
  apply extract_exists_pre; intro PA1. apply extract_exists_pre; intro CI1.
  apply extract_exists_pre; intro CI2. apply extract_exists_pre; intro Q.
  apply extract_exists_pre; intro M2. apply extract_exists_pre; intro H2.
  apply extract_exists_pre; intro MR. apply extract_exists_pre; intro nowa.
  apply extract_exists_pre; intro PB2. apply extract_exists_pre; intro ST2.
  apply semax_extract_PROP; intro C1. apply semax_extract_PROP; intro C2.
  apply semax_extract_PROP; intro C3. apply semax_extract_PROP; intro C4.
  apply semax_extract_PROP; intro C5. apply semax_extract_PROP; intro C6.
  apply semax_extract_PROP; intro C7.
  pose (V := mkW6 R S m1 m2 a0 f0 l0 I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR nowa PB2 ST2).
  assert (HC: hhs3_p6_ctx x25519 aead_enc aead_dec L V) by exact (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 C7)))))).
  clear C1 C2 C3 C4 C5 C6 C7.
  change (semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p6_S5 x25519 gv L FR V)
            hhs3_P6 (overridePost FF (hhs3_R gv))).
  clearbody V.
  eapply (semax_unfold_Ssequence _ hhs3_P6 (eq_sym hhs3_p6_flat)).
  eapply semax_seq; [apply hhs3_p6_A_ok; assumption |].
  eapply semax_seq; [rewrite hhs3_overridePost2; apply hhs3_p6_B_ok; assumption |].
  eapply semax_seq; [rewrite hhs3_overridePost2; apply hhs3_p6_C1_ok; assumption |].
  eapply semax_seq; [rewrite hhs3_overridePost2; apply hhs3_p6_C2_ok; assumption |].
  eapply semax_seq; [rewrite hhs3_overridePost2; apply hhs3_p6_D_ok; assumption |].
  eapply semax_seq; [rewrite hhs3_overridePost2; apply hhs3_p6_E_ok; assumption |].
  eapply semax_seq; [rewrite hhs3_overridePost2; apply hhs3_p6_F1_ok; assumption |].
  eapply semax_seq; [rewrite hhs3_overridePost2; apply hhs3_p6_F2_ok; assumption |].
  eapply semax_seq; [rewrite hhs3_overridePost2; apply hhs3_p6_G_ok; assumption |].
  apply hhs3_p6_H_ok; assumption.
Qed.

End P6.
