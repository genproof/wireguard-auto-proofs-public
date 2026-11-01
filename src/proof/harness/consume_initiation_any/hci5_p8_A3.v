(* law consume_initiation_any, phase P8, segment A3: the else branch's statements 5..12: the CHECKs of the handshake's fields, CHECK(target->p->refcount.refcount == target->refs && pr_same(&target->rest, target->p)).
   States and statements: hci5_p8_defs.v; (section P8).  The statement is
*)
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
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_s5.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_s6.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_s7.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_s8.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_s9.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_s10.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_s11.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_s12.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_p8_A3_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_QA1 x25519 aead_dec gv L FR) hci5_p8_A3
    (overridePost (hci5_p8_Q2 x25519 gv L FR) (hci5_R gv)).
Proof.
  intros HH. apply hci5_p8_A3_cut; try rewrite hci5_overridePost2.
  - exact (hci5_p8_A3_s5_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR HH).
  - exact (hci5_p8_A3_s6_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR HH).
  - exact (hci5_p8_A3_s7_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR HH).
  - exact (hci5_p8_A3_s8_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR HH).
  - exact (hci5_p8_A3_s9_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR HH).
  - exact (hci5_p8_A3_s10_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR HH).
  - exact (hci5_p8_A3_s11_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR HH).
  - exact (hci5_p8_A3_s12_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR HH).
Qed.

End Seg.
