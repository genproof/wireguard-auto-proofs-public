(* law cookie_reply, phase P9, segment BA2b.  np->p->latest_cookie.have_sent_mac1 = true; bytes_copy(.. last_mac1_sent, msg + len - 32, 16).
   Port of v1's *)
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
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p9_defs.
Require WgNoise.harness.x_cookie_reply.code.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p9_BA2b_lemmas.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_p9_BA2b_ok {Espec: OracleKind} gv L FR R S m c rp Q nonce rr CK CM NS PS T np CL KE md N a P CM' :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr CK CM -> hcy5_lists_ok L (map ke_addr KE) NS PS ->
  In (N, (a, Ews, P)) (combine NS PS) -> hn_addr N = np ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcy5_p9_PA x25519 gv L FR R S m c rp Q rr CK NS PS T np CL KE CM' md [] [temp HY._h (hs_addr a)])
    hcy5_p9_BA2b
    (normal_ret_assert
      (hcy5_p9_PA x25519 gv L FR R S m c rp Q rr CK NS (hcy5_p9_PS PS a P Q) T np CL KE CM' md [] [])).
Proof.
  intros HH Hr Hl HIn HN.
  unfold hcy5_Delta, hcy5_p9_PA, hcy5_p9_loc, hcy5_p9_sep, hcy5_p9_BA2b.
  simplify_func_tycontext.
  abbreviate_semax.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars; simpl app.
  pose proof Hr as (HR & HQ & _).
  pose proof HQ as (Hn & Hmsg & _).
  pose proof Hl as (_ & Hnp & Hnd & _).
  destruct (hcy5_p9_BA2b_pos NS PS N (a, Ews, P) HIn Hnp) as (HinN & HinP & Hpa).
  cbn [peer_addr4] in Hpa. subst np.
  sep_apply (hcy5_p9_BA2b_node (hcy5_head NS) NS N a HinN Hpa).
  sep_apply (hcy5_p9_BA2b_peers PS a Ews P (hcy5_p9_peer P Q) Hnd HinP).
  sep_apply (hcy5_p9_BA2b_peer_open Ews a P). Intros lk.
  (* t'117 = np->p; t'117->latest_cookie.have_sent_mac1 = 1; t'116 = np->p *)
  forward. forward. forward.
  (* bytes_copy(t'116->latest_cookie.last_mac1_sent, msg + len - 32, 16) *)
  assert_PROP (@field_compatible HCS (tarray tuchar (Zlength (q_msg Q))) [] m) as FCm.
  { sep_apply (hcy5_p9_BA2b_hbytes_fc Ews (q_msg Q) m). entailer!. }
  rewrite (hcy5_p9_BA2b_split3 Ews (q_msg Q) (q_n Q - 32) (q_n Q - 16) m) by (lia || exact FCm).
  fold (hcy5_mac1 Q).
  assert (LM1: Zlength (hcy5_mac1 Q) = 16) by (unfold hcy5_mac1; rewrite Zlength_sublist; lia).
  replace (hout Ews 16 (offset_val 386 a)) with (hout Ews (Zlength (hcy5_mac1 Q)) (offset_val 386 a))
    by (rewrite LM1; reflexivity).
  repeat flatten_sepcon_in_SEP.
  forward_call (Ews, offset_val 386 a, Ews, offset_val (q_n Q - 32) m, hcy5_mac1 Q).
  { destruct FCm as [Pm _]. destruct m; try contradiction. split; exact I. }
  { entailer!. rewrite LM1. destruct FCm as [Pm _]. destruct m; try contradiction. simpl.
    rewrite hcy5_p9_BA2b_ptr by rep_lia. rewrite offset_offset_val. reflexivity. }
  (* the post: rejoin the message, fold the peer, the peers, the node list *)
  change (hbytes Ews (hcy5_mac1 Q) (offset_val (q_n Q - 32) m))
    with (hbytes Ews (sublist (q_n Q - 32) (q_n Q - 16) (q_msg Q)) (offset_val (q_n Q - 32) m)).
  sep_apply (derives_refl' _ _ (eq_sym (hcy5_p9_BA2b_split3 Ews (q_msg Q) (q_n Q - 32) (q_n Q - 16) m
                                          ltac:(lia) ltac:(lia) FCm))).
  sep_apply (hcy5_p9_BA2b_peer_close a P lk (hcy5_mac1 Q) H LM1).
  change (p_set_cookie P (hcy5_p9_ck (p_cookie P) (hcy5_mac1 Q))) with (hcy5_p9_peer P Q).
  sep_apply (modus_ponens_wand (peer_rep Ews a (hcy5_p9_peer P Q)) (peers_rep (supd PS a (hcy5_p9_peer P Q)))).
  sep_apply (modus_ponens_wand (field_at Ews t_hnode4 (DOT HC._p) a (hn_addr N)) (hnodes_rep4 W (hcy5_head NS) NS)).
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars, hcy5_p9_PS.
  rewrite hcy5_p9_BA2b_phead. cbn [app].
  entailer!.
Qed.

End Seg.
