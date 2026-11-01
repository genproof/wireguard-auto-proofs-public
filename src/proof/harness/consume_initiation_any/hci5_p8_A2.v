(* law consume_initiation_any, phase P8, segment A2: the else branch's statement 4: CHECK(hnodes_same_except(peers, target->p)).
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
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A2_pure.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A2_sep.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_p8_A2_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_QA1 x25519 aead_dec gv L FR) hci5_p8_A2
    (overridePost (hci5_p8_QA1 x25519 aead_dec gv L FR) (hci5_R gv)).
Proof.
  intros HH. unfold hci5_p8_QA1 at 1, hci5_Delta, hci5_R, hci5_p8_A2. simplify_func_tycontext. abbreviate_semax.
  Intros R S w NS PS T head na KE m M. Intros a P t ck2 h2 key spub.
  unfold hci5_lvars, hci5_world, hci5_globs, hci5_p8_scr, hci5_snaps0; cbn [app].
  assert_PROP (itable_wf T) as HwfT by (unfold itable; entailer!).
  match goal with Hi: hci5_inv _ _ _ _ _ _ _ _ _, Ht: hci5_tgt _ _ _ _ _ _ = Some _ |- _ =>
    destruct (hci5_p8_A2_facts x25519 aead_dec R L NS PS KE T head na _ M (s_boot S) a P t ck2 h2 Hi HwfT Ht)
      as ((NS1 & N & NS2 & HNS & HNa & HNp) & Hvo & Hq1 & Hq2 & Hq3 & Hq4 & Hq5 & Hq6 & Hq7 & Hq8 & Hq9 & Hq10 & Hsame) end.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { assert_PROP (is_pointer_or_null (hci5_head NS)) as Hhd.
    { sep_apply (hci5_p8_A2_hn_pn (hci5_head NS) (hnodes_snapped4 T NS PS)). entailer!. }
    forward.
    assert (HinN: In N (hnodes_snapped4 T NS PS)) by (rewrite HNS; apply in_or_app; right; left; reflexivity).
    pose proof (hci5_p8_A2_node_acc (hci5_head NS) _ N HinN) as A1. unfold hci5_p8_A2_acc in A1. sep_apply A1. clear A1. flatten_sepcon_in_SEP.
    rewrite <- HNa.
    forward.
    rewrite HNp.
    sep_apply wand_frame_elim.
    sep_apply (hci5_p8_A2_vo Tsh (l_wb L) (hci5_DB x25519 R L) (hci5_khead KE) (map (kent_snapped T) KE)).
    forward_call (hci5_head NS, hnodes_snapped4 T NS PS, supd PS a (hci5_p8_put P M (s_boot S) t ck2 h2),
                  hci5_p8_A2_sns T PS, hci5_p8_A2_rs PS, hci5_p8_A2_prs PS, a, Tsh, l_itb L, T,
                  hci5_p8_A2_VO x25519 R L T KE).
    rewrite Hsame.
    forward_if.
    { exfalso. apply Int.one_not_zero. assumption. }
    forward. rewrite HNa. unfold hci5_p8_A2_VO. rewrite <- hci5_p8_A2_vo. entailer!. }
  { forward. apply ENTAIL_refl. }
  unfold hci5_p8_QA1.
  Exists R S w NS PS T head na KE m M. Exists a P t ck2 h2 key spub.
  unfold hci5_lvars, hci5_world, hci5_globs, hci5_p8_scr, hci5_snaps0; cbn [app].
  entailer!.
Qed.

End Seg.
