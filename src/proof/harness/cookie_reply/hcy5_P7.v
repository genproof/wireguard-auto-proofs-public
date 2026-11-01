(* law cookie_reply: phase P7 of main, statements
   51: the loop over the peers: peer_randomize_rest, maybe insert the handshake entry, a cnode (NULL: return).

   (+ its children's files). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p7_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p7_pure.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p7_cn.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p7_seg.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

#[local] Hint Resolve hcy5_p7_vp : valid_pointer.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_P7_ok {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hcy5_closeH ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_S6 x25519 xaead_enc gv L FR) hcy5_P7
    (overridePost (hcy5_S7 x25519 xaead_enc gv L FR) (hcy5_R gv)).
Proof.
  intros HH HC. unfold hcy5_S6, hcy5_R.
  Intros R S m c rp Q nonce rr CK CM. Intros NS PS T np.
  apply hcy5_post_canon.
  rewrite hcy5_p7_P7_eq.
  apply semax_seq with (Q := hcy5_p7_Inv x25519 gv L FR R Q m c rp rr CK CM np NS PS).
  - (* it = peers *)
    unfold hcy5_Delta, hcy5_p7_s0. simplify_func_tycontext.
    unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars.
    simpl app.
    assert_PROP (is_pointer_or_null (hcy5_head NS)) as Hpn.
    { sep_apply (hcy5_p7_pn (hcy5_head NS) NS). entailer!. }
    forward.
    unfold frame_ret_assert, function_body_ret_assert; cbn beta iota.
    unfold hcy5_p7_Inv.
    Exists (@nil hnode4) NS (@nil (val * share * peer)) (@nil (val * share * peer)) PS.
    Exists T S (@nil (val * val * option cookie)) (hcy5_head NS).
    unfold hcy5_p7_lc, hcy5_p7_F, hcy5_p7_Fl, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0,
      hcy5_lvars;
      cbn [app fold_right_sepcon hcy5_cns hcy5_chead hcy5_p7_seg].
    entailer!.
    split; [destruct H0 as (_ & Hnp & _); exact Hnp |].
    split; [split; [reflexivity | constructor] | constructor].
  - (* the loop *)
    apply semax_loop with (Q' := hcy5_p7_Cont x25519 gv L FR R Q m c rp rr CK CM np NS PS).
    + apply (hcy5_p7_body_ok x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R Q m c rp nonce rr CK CM np
               NS PS); auto.
    + apply hcy5_p7_incr_ok.
Qed.

End Phase.
