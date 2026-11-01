(* law consume_initiation_any, phase P8, segment A3, statement s6 (port of v1's hci3_p8_A3_s6.v):
     CHECK(bytes_eq(h->remote_ephemeral, msg->unencrypted_ephemeral, 32))
   Shared: hci5_p8_A3_defs.v (statements, cut), hci5_p8_A3_pure.v
   (hci5_p8_A3_facts), hci5_p8_A3_sep.v (accessors). *)
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
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_pure.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p8_A3_sep.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_p8_A3_s6_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_QA1 x25519 aead_dec gv L FR)
    hci5_p8_A3_s6 (overridePost (hci5_p8_QA1 x25519 aead_dec gv L FR) (hci5_R gv)).
Proof.
  intros HH. destruct HH as (Hx & Ha & Hxa & Hrep).
  unfold hci5_p8_QA1, hci5_Delta, hci5_R, hci5_p8_A3_s6. simplify_func_tycontext.
  Intros R S w NS PS T head na KE m M. Intros a P t ck2 h2 key spub.
  unfold hci5_lvars, hci5_world, hci5_globs, hci5_snaps0, hci5_p8_scr; cbn [app].
  abbreviate_semax.
  assert_PROP (itable_wf T) as Hwf by (unfold itable; entailer!).
  destruct (hci5_p8_A3_facts x25519 aead_enc aead_dec R L NS PS KE T head na M (s_boot S) a P t ck2 h2 Ha H0 Hwf H1 H3)
    as (NS1 & N & NS2 & PS1 & PS2 & HNS & Hna & Hnp & Hsn & Hnr & Hnrest & HPS & Hdel & Hsf & Hin & Hpok & HinT & Hep
        & Hpkn & Hslot & Lt & Lck & Lh).
  rewrite (hci5_p8_A3_peers PS a Ews P (hci5_p8_put P M (s_boot S) t ck2 h2) Hsf). Intros.
  sep_apply (hci5_p8_A3_peer_fc Ews a (hci5_p8_put P M (s_boot S) t ck2 h2)). Intros.
  sep_apply (hci5_p8_A3_pk_reph Ews a (hci5_p8_put P M (s_boot S) t ck2 h2)). Intros.
  sep_apply (hci5_p8_A3_msg_eph Ews m M). Intros.
  assert_PROP (isptr m) as Pm by (unfold hbytes; entailer!; match goal with Hf: field_compatible _ _ (offset_val _ m) |- _ =>
    exact (@field_compatible_offset_isptr _ _ _ _ _ Hf) end).
  pose proof (field_compatible_isptr _ _ _ H6) as Pa.
  rewrite (hci5_p8_A3_put_reph P M (s_boot S) t ck2 h2).
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
  - apply ENTAIL_refl.
  - forward_call (Ews, offset_val 168 a, im_eph M, Ews, offset_val 8 m, im_eph M).
    + entailer!.
      simpl. destruct H1 as (L1 & _). rewrite L1. unfold hs_addr. rewrite offset_offset_val. reflexivity.
    + destruct H1 as (L1 & _). rewrite L1. rep_lia.
    + rewrite hci5_p8_A3_bytes_eqb_refl.
      forward_if True.
      { exfalso; match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
      { forward. entailer!. }
      forward. entailer!.
  - sep_apply (hci5_p8_A3_mp (hbytes Ews (im_eph M) (offset_val 8 m)) (init_rep Ews m M)).
    sep_apply (hci5_p8_A3_mp (hbytes Ews (im_eph M) (offset_val 168 a))
      (peer_rep Ews a (hci5_p8_put P M (s_boot S) t ck2 h2))).
    Exists R S w NS PS T head na KE m M. Exists a P t ck2 h2 key spub.
    unfold hci5_lvars, hci5_world, hci5_globs, hci5_snaps0, hci5_p8_scr; cbn [app].
    rewrite (hci5_p8_A3_peers PS a Ews P (hci5_p8_put P M (s_boot S) t ck2 h2) Hsf).
    entailer!.
Qed.

End Seg.
