(* law consume_initiation_any, phase P8, segment a: statements 31..32: init_img(img_after, msg); CHECK(bytes_eq(img, img_after, 148)).
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
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

Lemma hci5_p8_a_len M : im_ok M -> Zlength (init_bytes M) = 148.
Proof.
  intros (H1 & H2 & H3 & H4 & H5). unfold init_bytes, le32.
  rewrite !Zlength_app, H1, H2, H3, H4, H5. reflexivity.
Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_p8_a_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_S7 x25519 aead_dec gv L FR) hci5_p8_s3132
    (overridePost (hci5_p8_Q1 x25519 aead_dec gv L FR) (hci5_R gv)).
Proof.
  intros HH. unfold hci5_S7, hci5_Delta, hci5_R, hci5_p8_s3132. simplify_func_tycontext. abbreviate_semax.
  Intros R S w NS PS T head na KE m M.
  unfold hci5_lvars, hci5_world, hci5_globs; cbn [app].
  forward_call (Tsh, l_imga L, Ews, m, M).
  pose proof (hci5_p8_a_len M H1) as Hlen.
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  - entailer!.
  - forward_call (Tsh, l_img L, init_bytes M, Tsh, l_imga L, init_bytes M).
    { rewrite Hlen. entailer!. }
    assert (Hb: bytes_eqb (init_bytes M) (init_bytes M) = true) by (unfold bytes_eqb; destruct list_eq_dec; congruence).
    rewrite Hb.
    forward_if True; [discriminate | forward; entailer! |].
    forward. entailer!.
  - unfold hci5_p8_Q1. Exists R S w NS PS T head na KE m M.
    unfold hci5_lvars, hci5_p8_scr, hci5_world, hci5_globs; cbn [app].
    entailer!.
Qed.

End Seg.
