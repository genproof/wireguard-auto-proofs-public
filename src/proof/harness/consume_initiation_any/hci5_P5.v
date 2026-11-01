(* law consume_initiation_any: main's phase P5, statements 15..19: fill_init(msg); mode = nondet_u8() % 3; the mode block (A's initiation, optionally one byte changed); the replay boundary (A's latest timestamp = ts or one below / above); init_img(img, msg).
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
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p5_A.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p5_B.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

Section P5.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_P5_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> 
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_S4 x25519 gv L FR) hci5_P5
    (overridePost (hci5_S5 x25519 gv L FR) (hci5_R gv)).
Proof.
  intros HH. rewrite hci5_p5_cut.
  apply (hci5_seql_app _ _ (hci5_p5_Q17 x25519 gv L FR)); [vm_compute; congruence | vm_compute; congruence | |].
  { rewrite hci5_overridePost2. exact (hci5_p5_A_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR HH). }
  apply (hci5_seql_app _ _ (hci5_p5_Q18 x25519 gv L FR)); [vm_compute; congruence | vm_compute; congruence | |].
  { rewrite hci5_overridePost2. exact (hci5_p5_B_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR HH). }
  match goal with |- semax _ _ ?c _ =>
    let c' := eval cbv beta iota delta [hci5_seql hci5_l firstn skipn hci5_stmts] in c in change c with c' end.
  unfold hci5_p5_Q18, hci5_Delta, hci5_R. simplify_func_tycontext. abbreviate_semax.
  Intros R S w NS PS T head na KE m M.
  unfold hci5_lvars, hci5_scr, hci5_world, hci5_globs, hci5_snaps0; cbn [app].
  forward_call (Tsh, l_img L, Ews, m, M).
  unfold hci5_S5. Exists R S w NS PS T head na KE m M.
  unfold hci5_lvars, hci5_scr, hci5_world, hci5_globs, hci5_snaps0; cbn [app].
  entailer!.
Qed.

End P5.
