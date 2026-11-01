(* law cookie_reply: phase P4 of main, statements
   30..35: fill_cookie_msg(reply), secret_birth, secret, dev_take(&db, &wb), skb_take(&sks, &skb), wg_cookie_message_create.

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
Require WgNoise.harness.x_cookie_reply.code.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p4_lemmas.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

Lemma hcy5_p4_drest_close sh wg D : @field_compatible Noise.CS t_dev [] wg ->
  @field_at Noise.CS sh t_dev [StructField I._dev] (d_dev D) wg *
  identity_rep sh (id_addr wg) (d_id D) *
  @field_at Noise.CS sh t_dev [StructField I._peer_hashtable] (d_ptab D) wg *
  @field_at Noise.CS sh t_dev [StructField I._index_hashtable] (d_itab D) wg |-- hcy5_drest sh wg D.
Proof. intros FC. unfold hcy5_drest. entailer!. Qed.

Lemma hcy5_p4_dev_in x25519 R L CC :
  hcy5_drest Tsh (l_wb L) (hcy5_DB x25519 R L) * checker_rep Tsh (cc_addr (l_wb L)) CC |--
  device_rep Tsh (l_wb L) (hcy5_DBc x25519 R L CC).
Proof. rewrite hcy5_p4_dev_fold. apply derives_refl. Qed.

Lemma hcy5_p4_dev_out x25519 R L CC :
  device_rep Tsh (l_wb L) (hcy5_DBc x25519 R L CC) |--
  hcy5_drest Tsh (l_wb L) (hcy5_DB x25519 R L) * checker_rep Tsh (cc_addr (l_wb L)) CC.
Proof. rewrite hcy5_p4_dev_fold. apply derives_refl. Qed.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_P4_ok {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_S3 x25519 gv L FR) hcy5_P4
    (overridePost (hcy5_S4 x25519 xaead_enc gv L FR) (hcy5_R gv)).
Proof.
  intros HH. unfold hcy5_S3, hcy5_Delta, hcy5_R, hcy5_P4. simplify_func_tycontext. abbreviate_semax.
  Intros R S m c rp Q.
  unfold hcy5_aside0, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrA, hcy5_snaps0, hcy5_globs, hcy5_lvars. cbv [app].
  (* fill_cookie_msg(reply): any contents, overwritten by message_create *)
  forward_call (Ews, rp).
  Intros M0. sep_apply (hcy5_p4_cmsg_ Ews rp M0).
  (* secret_birth = wb.cookie_checker.secret_birthdate; bytes_copy(secret, wb.cookie_checker.secret, 32) *)
  unfold hcy5_drest. Intros.
  rewrite (hcy5_p4_cc_open Tsh (l_wb L) (hcy5_CC1 x25519 R L)) by auto. Intros.
  forward.
  assert (Hs: Zlength (cc_secret (hcy5_CC1 x25519 R L)) = 32) by (destruct H4 as [? _]; auto).
  forward_call (Tsh, l_secret L, Tsh, cc_addr (l_wb L), cc_secret (hcy5_CC1 x25519 R L)).
  { rewrite Hs. entailer!. unfold cc_addr, OFS_DEV_CHECKER. destruct (l_wb L); try contradiction. simpl.
    rewrite Ptrofs.add_assoc. reflexivity. }
  { rewrite Hs. cancel. }
  sep_apply (hcy5_p4_cc_close Tsh (l_wb L) (hcy5_CC1 x25519 R L) H3 H4).
  (* dev_take(&db, &wb): B whole *)
  sep_apply (hcy5_p4_drest_close Tsh (l_wb L) (hcy5_DB x25519 R L) H3).
  sep_apply (hcy5_p4_dev_in x25519 R L (hcy5_CC1 x25519 R L)).
  rewrite (hcy5_p4_devsnap_ Tsh (l_db L)).
  assert_PROP (isptr (l_wb L) /\ isptr (l_ptb L) /\ isptr (l_itb L)) as Hptrs by entailer!.
  forward_call (Tsh, l_db L, Tsh, l_wb L, hcy5_DBc x25519 R L (hcy5_CC1 x25519 R L), Tsh, nullval).
  { destruct Hptrs as (P1 & P2 & P3). unfold hcy5_DBc, hcy5_CC1, hcy5_DB, setup_dev; simpl.
    repeat constructor; first [discriminate | intro E; rewrite E in *; contradiction]. }
  change (d_ptab (hcy5_DBc x25519 R L (hcy5_CC1 x25519 R L))) with (l_ptb L).
  sep_apply (hcy5_p4_dev_out x25519 R L (hcy5_CC1 x25519 R L)).
  (* skb_take(&sks, &skb) *)
  rewrite (hcy5_p4_skbsnap_ Tsh (l_sks L)).
  assert_PROP (m <> Vundef) as Hm. { unfold hcy5_tok. entailer!. }
  forward_call (Tsh, l_sks L, Tsh, l_skb L, hcy5_skb Q m).
  (* wg_cookie_message_create(reply, &skb, index, &wb.cookie_checker) *)
  rewrite (hcy5_p4_msg_eq Ews (q_msg Q) m).
  pose proof H0 as (Hn1 & Hn2 & Hn3 & Hn4 & Hn5 & Hn6 & Hn7).
  forward_call (gv, S, hcy5_w0, Ews, rp, Tsh, l_skb L, hcy5_skb Q m, Ews, q_msg Q, q_index Q, Tsh,
                cc_addr (l_wb L), hcy5_CC1 x25519 R L).
  { change (sk_data (hcy5_skb Q m)) with m. cancel. }
  { simpl. rewrite Int.unsigned_repr by lia. lia. }
  Intros vret. destruct vret as [nonce rr].
  change (fst (nonce, rr)) with nonce in *; change (snd (nonce, rr)) with rr in *.
  change (sk_data (hcy5_skb Q m)) with m.
  rewrite (hcy5_p4_mc_snd xaead_enc), H1. rewrite <- (hcy5_p4_msg_eq Ews (q_msg Q) m).
  unfold hcy5_S4.
  Exists R S m c rp Q nonce rr
    (fst (mc_res xaead_enc (hcy5_CC1 x25519 R L) (hcy5_skb Q m) (q_index Q) nonce (q_msg Q) S rr)).
  unfold hcy5_aside0, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_globs, hcy5_lvars, hcy5_S4shim, hcy5_CC2. cbv [app].
  entailer!.
  change (cc_secret (hcy5_CC1 x25519 R L)) with (r_secret R).
  cancel.
Qed.

End Phase.
