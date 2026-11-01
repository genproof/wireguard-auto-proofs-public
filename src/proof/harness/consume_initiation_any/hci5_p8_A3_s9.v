(* law consume_initiation_any, phase P8, segment A3, statement s9 (port of v1's hci3_p8_A3_s9.v):
     CHECK(h->remote_index == msg->sender_index)
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

(* msg->sender_index as one field at the world compspecs (a load from the whole @data_at W t_init doubles the Qed) *)
Section S9M.
#[local] Existing Instance Noise.CS.
Lemma hci5_p8_A3_s9_msgN sh m M : init_rep sh m M |--
  @field_at Noise.CS sh t_init [StructField prot_repr3.I._sender_index] (Vint (im_sender M)) m *
  (@field_at Noise.CS sh t_init [StructField prot_repr3.I._sender_index] (Vint (im_sender M)) m -* init_rep sh m M).
Proof.
  unfold init_rep. Intros.
  assert_PROP (field_compatible t_init [] m) by entailer!. unfold_data_at (data_at _ _ _ m).
  cancel.
  rewrite <- wand_sepcon_adjoint. apply andp_right; [apply prop_right; auto | cancel].
Qed.
End S9M.

Lemma hci5_p8_A3_s9_msg sh m M : init_rep sh m M |--
  @field_at W sh t_init [StructField prot_repr3.I._sender_index] (Vint (im_sender M)) m *
  (@field_at W sh t_init [StructField prot_repr3.I._sender_index] (Vint (im_sender M)) m -* init_rep sh m M).
Proof.
  rewrite <- (hci5_p8_A3_fW sh t_init [StructField prot_repr3.I._sender_index] (Vint (im_sender M))
    (Vint (im_sender M)) m (JMeq_refl _)) by (vm_compute; reflexivity).
  apply hci5_p8_A3_s9_msgN.
Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hci5_p8_A3_s9_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_p8_QA1 x25519 aead_dec gv L FR)
    hci5_p8_A3_s9 (overridePost (hci5_p8_QA1 x25519 aead_dec gv L FR) (hci5_R gv)).
Proof.
  intros HH. destruct HH as (Hx & Ha & Hxa & Hrep).
  unfold hci5_p8_QA1, hci5_Delta, hci5_R, hci5_p8_A3_s9. simplify_func_tycontext.
  Intros R S w NS PS T head na KE m M. Intros a P t ck2 h2 key spub.
  unfold hci5_lvars, hci5_world, hci5_globs, hci5_snaps0, hci5_p8_scr; cbn [app].
  abbreviate_semax.
  assert_PROP (itable_wf T) as Hwf by (unfold itable; entailer!).
  destruct (hci5_p8_A3_facts x25519 aead_enc aead_dec R L NS PS KE T head na M (s_boot S) a P t ck2 h2 Ha H0 Hwf H1 H3)
    as (NS1 & N & NS2 & PS1 & PS2 & HNS & Hna & Hnp & Hsn & Hnr & Hnrest & HPS & Hdel & Hsf & Hin & Hpok & HinT & Hep
        & Hpkn & Hslot & Lt & Lck & Lh).
  rewrite (hci5_p8_A3_peers PS a Ews P (hci5_p8_put P M (s_boot S) t ck2 h2) Hsf). Intros.
  sep_apply (hci5_p8_A3_pk_rindex Ews a (hci5_p8_put P M (s_boot S) t ck2 h2)). Intros.
  rewrite (hci5_p8_A3_put_rindex P M (s_boot S) t ck2 h2).
  sep_apply (hci5_p8_A3_s9_msg Ews m M). Intros.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
  - apply ENTAIL_refl.
  - forward. forward.
    forward_if True.
    + exfalso. rewrite Int.eq_true in *. discriminate.
    + forward. entailer!.
    + forward. entailer!.
  - sep_apply (hci5_p8_A3_mp
      (@field_at W_consume_initiation_any Ews t_hs [StructField prot_repr3.I._remote_index] (Vint (im_sender M)) (hs_addr a))
      (peer_rep Ews a (hci5_p8_put P M (s_boot S) t ck2 h2))).
    sep_apply (hci5_p8_A3_mp
      (@field_at W_consume_initiation_any Ews t_init [StructField prot_repr3.I._sender_index] (Vint (im_sender M)) m)
      (init_rep Ews m M)).
    Exists R S w NS PS T head na KE m M. Exists a P t ck2 h2 key spub.
    unfold hci5_lvars, hci5_world, hci5_globs, hci5_snaps0, hci5_p8_scr; cbn [app].
    rewrite (hci5_p8_A3_peers PS a Ews P (hci5_p8_put P M (s_boot S) t ck2 h2) Hsf).
    entailer!.
Qed.

End Seg.
