(* law consume_initiation_any, phase P7, segment B: if (t'28) body else skip (body given as a hypothesis).  Port of v1's hci3_p7_B.v. *)
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
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_p7_B_ok {Espec: OracleKind} gv L FR R S w NS PS T head na KE m M :
  (forall s key ck1 h1, hci5_p7_c1 x25519 aead_dec (hci5_IB x25519 R) M = Some (s, key, ck1, h1) ->
     semax (hci5_Delta x25519 aead_enc aead_dec)
       (hci5_p7_Q2 x25519 aead_dec gv L FR R S w NS PS T head na KE m M s key ck1 h1) hci5_p7_body
       (overridePost (hci5_S7 x25519 aead_dec gv L FR) (hci5_R gv))) ->
  semax (hci5_Delta x25519 aead_enc aead_dec)
    (hci5_p7_Q1 x25519 aead_dec gv L FR R S w NS PS T head na KE m M) hci5_p7_if2
    (overridePost (hci5_S7 x25519 aead_dec gv L FR) (hci5_R gv)).
Proof.
  intros HB.
  destruct (hci5_p7_c1 x25519 aead_dec (hci5_IB x25519 R) M) as [[[[s key] ck1] h1]|] eqn:Hc1.
  - specialize (HB s key ck1 h1 eq_refl).
    unfold hci5_p7_Q1, hci5_p7_if2. rewrite Hc1. cbn [hci5_p7_ok1].
    eapply semax_pre; [ | apply semax_ifthenelse_PQR' with (v := Vint Int.one)].
    + unfold hci5_p7_st, hci5_lvars, hci5_world, hci5_globs. cbn [app]. apply andp_left2, now_later.
    + reflexivity.
    + unfold hci5_p7_st, hci5_lvars, hci5_world, hci5_globs. cbn [app]. entailer!.
    + unfold hci5_p7_st, hci5_lvars, hci5_world, hci5_globs. cbn [app]. entailer!.
    + eapply semax_pre; [ | exact HB].
      unfold hci5_p7_Q2, hci5_p7_st, hci5_lvars, hci5_world, hci5_globs. cbn [app]. Intros. entailer!.
    + unfold hci5_p7_st, hci5_lvars, hci5_world, hci5_globs. cbn [app]. Intros. hci5_p7_absurd.
  - unfold hci5_p7_Q1, hci5_p7_if2. rewrite Hc1. cbn [hci5_p7_ok1].
    eapply semax_pre; [ | apply semax_ifthenelse_PQR' with (v := Vint Int.zero)].
    + unfold hci5_p7_st, hci5_lvars, hci5_world, hci5_globs. cbn [app]. apply andp_left2, now_later.
    + reflexivity.
    + unfold hci5_p7_st, hci5_lvars, hci5_world, hci5_globs. cbn [app]. entailer!.
    + unfold hci5_p7_st, hci5_lvars, hci5_world, hci5_globs. cbn [app]. entailer!.
    + unfold hci5_p7_st, hci5_lvars, hci5_world, hci5_globs. cbn [app]. Intros. hci5_p7_absurd.
    + unfold hci5_p7_st, hci5_lvars, hci5_world, hci5_globs. cbn [app]. Intros.
      unfold hci5_Delta. simplify_func_tycontext. forward.
      unfold hci5_S7. Exists R S w NS PS T head na KE m M.
      rewrite (hci5_p7_tgt_none1 x25519 aead_dec _ _ _ _ Hc1).
      unfold hci5_lvars, hci5_world, hci5_globs. cbn [hci5_tnode hci5_ci_rep hci5_p7_ci1 app].
      entailer!.
Qed.

End Seg.
